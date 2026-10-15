-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighContourVector
-- name    : TaoFivePrimes_RHHighContourVector
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T06:18:43.682996+00:00
-- url     : https://prove2.me/theorems/d623488b-8ba5-4d0e-886f-ee6a0e6f5558
-- title:
--   Sparse polynomial contour spectrum and exact chirped input program
-- statement:
--   Transparent generic functions decoding a2049-word proposed coefficient table into a sparse16384-entry spectrum, complex80-bit values, and exact160-bit chirped products. This definition makes no arithmetic, analytic, sign, count or RH assertion and imports no height-specific chirp data.
-- source:
--   Existing Platt Fourier construction and Bluestein convolution, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
set_option autoImplicit false
namespace RHHighContourVector
noncomputable def decode (p : Nat) : Int×Int :=
  (((p%2^96:Nat):Int)-2^95,((p/2^96%2^96:Nat):Int)-2^95)
noncomputable def coefficient (v : List Nat) (positive : Bool) (m : Nat) : Int×Int :=
  decode ((v[if positive then 1024+m else m]?).getD 0)
noncomputable def vector (v : List Nat) (j : Nat) : Int×Int :=
  if j=0 then decode ((v[0]?).getD 0) else if j≤1024 then coefficient v false j
    else if 15360≤j then coefficient v true (16384-j) else (0,0)
noncomputable def value (p : Int×Int) : ℂ := ((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^80
noncomputable def raw (v : List Nat) (c : Nat→Int×Int) (j : Nat) : Int×Int :=
  let m:=vector v j
  let q:=c j
  (m.1*q.1+m.2*q.2,m.2*q.1-m.1*q.2)
end RHHighContourVector
noncomputable def TaoFivePrimes_RHHighContourVector : Nat := 16384


