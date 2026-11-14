-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_BinarySignedAddition
-- name    : InfoLossLAR_Native_AFT_BinarySignedAddition
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:17:48.152492+00:00
-- url     : https://prove2.me/theorems/efb04724-8160-46a4-a581-2f11673eb6ac
-- title:
--   Addition of signed binary integers
-- statement:
--   A signed digit pair $(s,a)$ represents the integer $(-1)^s v(a)$. The signed-addition routine returns a sign, magnitude digits, and a native charge, with the exact specification
--
--   $$\operatorname{decode}(\operatorname{signedAdd}(s,a,t,b))=(-1)^s v(a)+(-1)^t v(b).$$
--
--   It combines magnitude addition and borrow subtraction to handle both signs of each operand.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BinarySignedAddition.lean; migrated native SHA256 382d7ef5725daa96617c1d348f867a1a0df72ea117ea5384eb555385388b5898; retained source units selected by Lean oracle.

import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalData
import Mathlib


/-! Signed-magnitude addition, implemented by the Boolean ripple algorithms. -/
namespace AFT.BinaryArithmetic

structure SignedResult where
  negative : Bool
  digits : List Bool
  work : ℕ

def signedAdd (firstSign secondSign : Bool) (first second : List Bool) : SignedResult :=
  if firstSign==secondSign then
    let sum := add false first second
    ⟨firstSign,sum.digits,sum.work+3⟩
  else
    let diff := subtract false first second
    if diff.borrow then
      let reverse := subtract false second first
      ⟨secondSign,reverse.digits,diff.work+reverse.work+4⟩
    else ⟨firstSign,diff.digits,diff.work+4⟩

theorem signedAdd_value (firstSign secondSign : Bool) (first second : List Bool) :
    signedValue (signedAdd firstSign secondSign first second).negative
      (signedAdd firstSign secondSign first second).digits =
      signedValue firstSign first+signedValue secondSign second := by
  have hadd := add_value first second false
  simp only [Bool.toNat_false,Nat.add_zero] at hadd
  by_cases he : firstSign=secondSign
  · subst secondSign
    simp only [signedAdd,beq_self_eq_true,ite_true,signedValue,hadd]
    cases firstSign <;> simp
    omega
  · have hbeq : (firstSign==secondSign)=false := by simpa using he
    simp only [signedAdd,hbeq,Bool.false_eq_true,ite_false]
    cases hb : (subtract false first second).borrow with
    | true =>
      have hlt := (subtract_borrow first second).mp hb
      have hv := subtract_value second first hlt.le
      simp only [ite_true,signedValue,hv]
      cases firstSign <;> cases secondSign <;> simp_all <;> omega
    | false =>
      have hle : value second ≤ value first := by
        have hh := (subtract_borrow first second)
        simp only [hb,Bool.false_eq_true,false_iff] at hh
        omega
      have hv := subtract_value first second hle
      simp only [Bool.false_eq_true,ite_false,signedValue,hv]
      cases firstSign <;> cases secondSign <;> simp_all <;> omega





end AFT.BinaryArithmetic


