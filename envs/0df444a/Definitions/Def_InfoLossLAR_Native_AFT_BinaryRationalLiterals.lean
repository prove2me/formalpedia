-- Prove2me | Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalLiterals
-- name    : InfoLossLAR_Native_AFT_BinaryRationalLiterals
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:18:46.40141+00:00
-- url     : https://prove2.me/theorems/101fe431-c843-4642-8ef7-e18e6bfc1682
-- title:
--   Copying finite binary strings and rational literals
-- statement:
--   The copy operations traverse an existing Boolean digit list or canonical rational encoding and return a new result carrying the same data:
--
--   $$\operatorname{copy}(a).\mathrm{digits}=a,\qquad\operatorname{decode}(\operatorname{copy}(e))=\operatorname{decode}(e).$$
--
--   Each operation records its native charge. These definitions concern finite stored data, so they do not assume an oracle that converts an arbitrary rational value into digits during execution.
-- source:
--   Local manuscript repository commit 5c3becb254daaa8738368b474349766c1769c2a0; lean/AFT/BinaryRationalLiterals.lean; migrated native SHA256 c14c1158fce6f7b5f1f369ed14c63a9011a74199203fb7163ad2425dd57f7b62; retained source units selected by Lean oracle.

import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalIntegers
import Mathlib


/-! Finite stored literals and explicit copying. `exists_code` is a semantic
encoding theorem; it is not a runtime rational-to-bits oracle. Programs store
its finite Boolean literals before execution. -/
namespace AFT.BinaryArithmetic

def copy : List Bool → Result
  | [] => ⟨[],1⟩
  | bit::tail => let previous := copy tail;⟨bit::previous.digits,previous.work+2⟩

theorem copy_digits (digits : List Bool) : (copy digits).digits=digits := by
  induction digits with
  | nil => rfl
  | cons bit tail ih => simp only [copy,ih]





namespace RationalBits

def copy (input : RationalBits) : RationalResult :=
  let num := BinaryArithmetic.copy input.numerator
  let den := BinaryArithmetic.copy input.denominator
  ⟨{negative := input.negative,numerator := num.digits,denominator := den.digits
    numerator_normal := by simpa only [num,copy_digits] using input.numerator_normal
    denominator_normal := by simpa only [den,copy_digits] using input.denominator_normal
    denominator_positive := by simpa only [den,copy_digits] using input.denominator_positive
    coprime := by simpa only [num,den,copy_digits] using input.coprime},num.work+den.work+2⟩

theorem copy_value (input : RationalBits) : (copy input).data.decode=input.decode := by
  rw [decode_fraction,decode_fraction]
  simp only [copy,copy_digits]





end RationalBits
end AFT.BinaryArithmetic


