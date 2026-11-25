(* ::Package:: *)

(* ::Package:: *)

(* :Title: SolitonDST *)
(* :Context: SolitonDST` *)
(* :Summary: Core algorithms for the Discrete Spectrum Transform (DST). *)
(* :Author: [Your Name] *)
(* :License: MIT *)

BeginPackage["SolitonDST`"];

(* ::Section:: *)
(* Usage Messages *)

ZetaFunction::usage = 
  "ZetaFunction[x, A] computes the spectral function zeta(x, A) = -Sqrt[A^2 - x^2].";

AuxiliaryParameter::usage = 
  "AuxiliaryParameter[l, A, precision] computes the auxiliary parameter pp(l) for a given spectral parameter l.";

BOa::usage = 
  "BOa[p, zeta, q0, deltaF, Np] computes the transfer matrix for the given potential data q0.";

aDS::usage = 
  "ADS[zeta, A, p, qidata, deltaInt, Np, L, phiM, phiP] computes the DST coefficient a(zeta).";

BOe::usage = 
  "BOe[p, zeta, q0, deltaF, Np] computes the extended transfer matrix (with derivatives) for the phase/norming constants.";

RhoDS::usage = 
  "RhoDS[zeta, A, p, qidata, deltaInt, Np, L, phiM, phiP] computes the DST coefficient rho(zeta).";


Begin["`Private`"];

(* ::Section:: *)
(* 1. Auxiliary Functions *)

ZetaFunction[x_, A_] := -Sqrt[-(A^2) + x^2];

AuxiliaryParameter[l_, A_, precision_] := SetPrecision[I * (l + ZetaFunction[l, A]) / A, precision];


(* ::Section:: *)
(* 2. Core DST Algorithms *)

BOa[p_?NumberQ, zeta_?NumberQ, q0_?ArrayQ, deltaF_?ArrayQ, Np_?NumberQ] := 
  Module[{zetaF, qi0 = q0, u, k, co, lim, u11, u12, u21, u22, S, i, qi, qic, dx, deltaFF = deltaF},
    zetaF = SetPrecision[zeta, p];
    S = {{1, 0}, {0, 1}};
    
    For[i = 1, i <= Np, i++,
      qi = qi0[[i]];
      qic = Conjugate[qi];
      dx = deltaFF[[i]];
      
      k = (Abs[qi]^2 - zetaF^2)^(1/2);
      lim = SetPrecision[Sinh[k * dx] / k, p];
      co = SetPrecision[Cosh[k * dx], p];
      
      u11 = SetPrecision[co + (-I * zetaF) * lim, p];
      u12 = SetPrecision[(qi) * lim, p];
      u21 = SetPrecision[(qic) * lim, p];
      u22 = SetPrecision[co - (-I * zetaF) * lim, p];
      
      u = SetPrecision[{{u11, u12}, {u21, u22}}, p];
      S = u . S;
    ];
    S
  ];

aDS[zeta_?NumberQ, A_, p_, qidata_, deltaInt_, Np_, L_, phiM_, phiP_] := 
  Module[{zeta0 = zeta, mat, chi, S11, S12, S21, S22, e1, e2, e3, aa},
    mat = BOa[p, zeta0, qidata, deltaInt, Np];
    
    S11 = mat[[1, 1]]; S12 = mat[[1, 2]];
    S21 = mat[[2, 1]]; S22 = mat[[2, 2]];
    
    e1 = SetPrecision[Exp[-I * phiP], p];
    e2 = SetPrecision[Exp[I * phiP], p];
    e3 = SetPrecision[Exp[-I * phiM], p];
    
    chi = SetPrecision[I * (zeta0 + ZetaFunction[zeta0, A]) / A, p];
    
    a = SetPrecision[
      Exp[-I * L * ZetaFunction[zeta0, A]] * 
      (S11 + S12 * chi * e3 + S21 * chi * e2 + S22 * chi^2 * e2 * e3) / 
      (1 + chi^2), p
    ];
    a
  ];

BOe[p_?NumberQ, zeta_?NumberQ, q0_?ArrayQ, deltaF_?ArrayQ, Np_?NumberQ] := 
  Module[{zetaF, qi0 = q0, u, k, co, lim, u11, u12, u21, u22, u11z, u21z, u12z, u22z, S, i, qi, qic, dx, deltaFF = deltaF},
    zetaF = SetPrecision[zeta, p];
    S = IdentityMatrix[4];
    
    For[i = 1, i <= Np, i++,
      qi = qi0[[i]];
      qic = Conjugate[qi];
      dx = deltaFF[[i]];
      
      k = (Abs[qi]^2 - zetaF^2)^(1/2);
      lim = SetPrecision[Sinh[k * dx] / k, p];
      co = SetPrecision[Cosh[k * dx], p];
      
      u11 = SetPrecision[co + (-I * zetaF) * lim, p];
      u12 = SetPrecision[(qi) * lim, p];
      u21 = SetPrecision[(qic) * lim, p];
      u22 = SetPrecision[co - (-I * zetaF) * lim, p];
      
      u11z = SetPrecision[(I * dx * zetaF^2 * co) / k^2 - (I * zetaF^2 * Sinh[dx * k]) / k^3 - 
                           (I * Sinh[dx * k]) / k - (dx * zetaF * Sinh[dx * k]) / k, p];
      u12z = SetPrecision[-((qi * dx * zetaF * Cosh[dx * k]) / k^2) + (qi * zetaF * Sinh[dx * k]) / k^3, p];
      u21z = SetPrecision[-((qic * dx * zetaF * Cosh[dx * k]) / k^2) + (qic * zetaF * Sinh[dx * k]) / k^3, p];
      u22z = SetPrecision[-((I * dx * zetaF^2 * Cosh[dx * k]) / k^2) + (I * zetaF^2 * Sinh[dx * k]) / k^3 + 
                           (I * Sinh[dx * k]) / k - (dx * zetaF * Sinh[dx * k]) / k, p];
      
      u = SetPrecision[{{u11, u12, 0, 0}, {u21, u22, 0, 0}, {u11z, u12z, u11, u12}, {u21z, u22z, u21, u22}}, p];
      S = u . S;
    ];
    S
  ];

RhoDS[zeta_?NumberQ, A_, p_, qidata_, deltaInt_, Np_, L_, phiM_, phiP_] := 
  Module[{zeta0 = zeta, mat, chi, S11, S12, S21, S22, S31, S32, S41, S42, e1, e2, e3, bb, aux1, ad, rhoc},
    mat = BOe[p, zeta0, qidata, deltaInt, Np];
    
    S11 = mat[[1, 1]]; S12 = mat[[1, 2]];
    S21 = mat[[2, 1]]; S22 = mat[[2, 2]];
    S31 = mat[[3, 1]]; S32 = mat[[3, 2]];
    S41 = mat[[4, 1]]; S42 = mat[[4, 2]];
    
    e1 = SetPrecision[Exp[-I * phiP], p];
    e2 = SetPrecision[Exp[I * phiP], p];
    e3 = SetPrecision[Exp[-I * phiM], p];
    
    chi = SetPrecision[I * (zeta0 + ZetaFunction[zeta0, A]) / A, p];
    
    b = SetPrecision[(-S11 * chi * e1 - S12 * chi^2 * e3 * e1 + S21 + S22 * chi * e3) / (1 + chi^2), p];
    
    aux = SetPrecision[
      Exp[-I * L * ZetaFunction[zeta0, A]] / (1 + chi^2) * 
      (S11 + S12 * chi * e3 + S21 * chi * e2 + S22 * chi^2 * e2 * e3), p
    ];
    
    ad = SetPrecision[
      (-I * L * zeta0 / ZetaFunction[zeta0, A] - 2 * chi^2 / (ZetaFunction[zeta0, A] * (1 + chi^2))) * aux1 + 
      Exp[-I * L * ZetaFunction[zeta0, A]] / (1 + chi^2) * 
      (S31 + S32 * chi * e3 + S41 * chi * e2 + S42 * chi^2 * e2 * e3 + 
       chi / ZetaFunction[zeta0, A] * (S12 * e3 + S21 * e2 + 2 * S22 * chi * e2 * e3)), p
    ];
    
    rho = b / ad;
    rho
  ];

End[];
EndPackage[];
