-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
-- name    : Submission_ThreeSum_TernaryPartialEuler
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:18:20.853082+00:00
-- url     : https://prove2.me/theorems/9ecdd766-6871-42a3-bbc8-b1cd5952f938
-- title:
--   Ternary Partial Euler
-- statement:
--   Definitions and structural lemmas for Ternary Partial Euler, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean

import Definitions.Def_Submission_ThreeSum_TernaryTransform
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000
def restrictedWeight {N : ℕ} (S : Finset (Fin N)) (R : TritWord N) (i : Fin N) : ℤ :=
  if i∈S then (R i).val else 0
def safePredecessor {N : ℕ} (S : Finset (Fin N)) (R dummy : TritWord N)
    (i : Fin N) : TritWord N :=
  if i∈S ∧ 0<(R i).val then predecessor R i else dummy
end ThreeSum.TernaryPartialEuler


