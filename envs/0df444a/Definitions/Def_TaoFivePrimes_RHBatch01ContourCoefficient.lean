-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01ContourCoefficient
-- name    : TaoFivePrimes_RHBatch01ContourCoefficient
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T18:06:18.266492+00:00
-- url     : https://prove2.me/theorems/a92f8a6f-dcf1-45cb-835f-d567e4efbf6e
-- title:
--   Exact rational contour coefficient reference and comparison program
-- statement:
--   Transparent128-bit rational reference coefficients for three contour starting points and Taylor orders. Reuses the certified negative exponential cache, reciprocal, eighth roots, and the existing Fourier polynomial coefficients. Defines a finite comparison against proposed80-bit spectra. This definition asserts no analytic approximation, sign, winding, count, or RH result.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01ContourReference
import Definitions.Def_TaoFivePrimes_RHHighContourUnit
import Definitions.Def_TaoFivePrimes_RHBatch01FourierPolynomial
set_option autoImplicit false
namespace RHBatch01ContourCoefficientData
abbrev D : Nat := 2^128
noncomputable def mul (a b : Int×Int) : Int×Int :=
  ((a.1*b.1-a.2*b.2)/(D:Int),(a.1*b.2+a.2*b.1)/(D:Int))
noncomputable def divide (a : Int×Int) (n : Nat) : Int×Int :=
  (a.1/(n:Int),a.2/(n:Int))
noncomputable def rootIndex (t : Fin 3) (positive : Bool) (m : Nat) : Nat :=
  if t.val=1 then 0 else if (t.val=2)=positive then m else 7*m
noncomputable def amplitude (m : Nat) (positive : Bool) : Nat :=
  if positive then (RHBatch01ContourReference.lookup m).amplitude else (RHBatch01ContourReference.lookup m).inverse
noncomputable def inputCoefficient (m : Nat) (positive : Bool) : Int×Int :=
  (RHBatch01FourierPolynomial.realInteger m*2^48,
   (if positive then RHBatch01FourierPolynomial.imagInteger m else -RHBatch01FourierPolynomial.imagInteger m)*2^48)
noncomputable def seed (t : Fin 3) (positive : Bool) (m : Nat) : Int×Int :=
  mul (mul (inputCoefficient m positive) (RHHighContourUnit.pair (rootIndex t positive m)))
    ((amplitude m positive:Int),0)
noncomputable def frequency (m : Nat) (positive : Bool) : Int×Int :=
  (0,if positive then ((RHBatch01ContourReference.lookup m).x:Int) else -((RHBatch01ContourReference.lookup m).x:Int))
noncomputable def coefficient (t : Fin 3) (positive : Bool) (m : Nat) : Nat→Int×Int
  | 0 => seed t positive m
  | k+1 => divide (mul (coefficient t positive m k) (frequency m positive)) (k+1)
noncomputable def decode (p : Nat) : Int×Int :=
  (((p%2^96:Nat):Int)-2^95,((p/2^96%2^96:Nat):Int)-2^95)
noncomputable def proposed (v : List Nat) (positive : Bool) (m : Nat) : Int×Int :=
  decode ((v[if positive then 1024+m else m]?).getD 0)
noncomputable def comparison (v : List Nat) (t : Fin 3) (k : Nat) : Bool :=
  decide (v.length=2049) && (List.range 1024).all (fun j=>[false,true].all (fun positive=>
    let a:=coefficient t positive (j+1) k
    let b:=proposed v positive (j+1)
    decide (|a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52)))
end RHBatch01ContourCoefficientData
noncomputable def TaoFivePrimes_RHBatch01ContourCoefficient : Nat := 8


