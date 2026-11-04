-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCarryCode
-- name    : Submission_ThreeSum_TernaryCarryCode
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:16.677296+00:00
-- url     : https://prove2.me/theorems/cda3003d-9f93-419b-8ad0-8151cf5c2ea3
-- title:
--   Ternary Carry Code
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Theorems.Thm_ThreeSum_TernarySignedDigits_digit_lt

set_option autoImplicit false
namespace ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset
def carryFromCode (J q : ℕ) : CarryWord J := fun i =>
  if h : i.val<J then ⟨digit 2 q i.val,by exact digit_lt (by decide) _ _⟩ else 0
def codeOfCarry {J : ℕ} (c : CarryWord J) : ℕ :=
  Nat.ofDigits 2 (List.ofFn fun i : Fin J => (c i.castSucc).val)
def codeCatalog (J : ℕ) : Finset ℕ := (range (2^J)).filter fun q => digit 2 q 0=0
end ThreeSum.TernaryCarryCode


