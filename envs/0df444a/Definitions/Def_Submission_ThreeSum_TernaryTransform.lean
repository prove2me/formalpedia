-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryTransform
-- name    : Submission_ThreeSum_TernaryTransform
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:38:48.035013+00:00
-- url     : https://prove2.me/theorems/ac0192d8-0ccf-4a78-804e-15dfd8c3c7af
-- title:
--   Ternary Transform
-- statement:
--   Definitions and structural lemmas for Ternary Transform, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTransform.lean

import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryTransform
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryEuler
def kernel {N : ℕ} (s : Finset (Fin N)) (R A : TritWord N) : ℤ :=
  ∏ i, if i ∈ s then digitChoose (R i) (A i) else if A i = R i then 1 else 0
def stageSum {N : ℕ} (s : Finset (Fin N)) (f : TritWord N → ℤ) (R : TritWord N) : ℤ :=
  ∑ A, kernel s R A * f A
end ThreeSum.TernaryTransform


