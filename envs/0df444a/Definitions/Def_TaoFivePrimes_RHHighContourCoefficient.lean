-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighContourCoefficient
-- name    : TaoFivePrimes_RHHighContourCoefficient
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T04:52:49.631613+00:00
-- url     : https://prove2.me/theorems/47902c2c-7bca-4536-ab62-bb437264a50b
-- title:
--   Exact rational contour coefficient reference and comparison program
-- statement:
--   Transparent128-bit rational reference coefficients for three contour starting points and Taylor orders. Reuses the certified negative exponential cache, reciprocal, eighth roots, and the existing Fourier polynomial coefficients. Defines a finite comparison against proposed80-bit spectra. This definition asserts no analytic approximation, sign, winding, count, or RH result.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighContourReference
import Definitions.Def_TaoFivePrimes_RHHighContourUnit
import Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial
set_option autoImplicit false
namespace RHHighContourCoefficientData
abbrev D : Nat := 2^128
noncomputable def mul (a b : Int×Int) : Int×Int :=
  ((a.1*b.1-a.2*b.2)/(D:Int),(a.1*b.2+a.2*b.1)/(D:Int))
noncomputable def divide (a : Int×Int) (n : Nat) : Int×Int :=
  (a.1/(n:Int),a.2/(n:Int))
noncomputable def rootIndex (t : Fin 3) (positive : Bool) (m : Nat) : Nat :=
  if t.val=1 then 0 else if (t.val=2)=positive then m else 7*m
noncomputable def amplitude (m : Nat) (positive : Bool) : Nat :=
  if positive then (RHHighContourReference.lookup m).amplitude else (RHHighContourReference.lookup m).inverse
noncomputable def inputCoefficient (m : Nat) (positive : Bool) : Int×Int :=
  (RHHighFourierPolynomial.realInteger m*2^48,
   (if positive then RHHighFourierPolynomial.imagInteger m else -RHHighFourierPolynomial.imagInteger m)*2^48)
noncomputable def seed (t : Fin 3) (positive : Bool) (m : Nat) : Int×Int :=
  mul (mul (inputCoefficient m positive) (RHHighContourUnit.pair (rootIndex t positive m)))
    ((amplitude m positive:Int),0)
noncomputable def frequency (m : Nat) (positive : Bool) : Int×Int :=
  (0,if positive then ((RHHighContourReference.lookup m).x:Int) else -((RHHighContourReference.lookup m).x:Int))
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
end RHHighContourCoefficientData
noncomputable def TaoFivePrimes_RHHighContourCoefficient : Nat := 8


