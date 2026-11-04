-- Prove2me | Definitions.Def_Submission_Weighted_FrozenQueryCost
-- name    : Submission_Weighted_FrozenQueryCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:11:18.652809+00:00
-- url     : https://prove2.me/theorems/8c242e44-0da1-48f8-9361-0df17adabc59
-- title:
--   Frozen Query Cost
-- statement:
--   Definitions and structural lemmas for Frozen Query Cost, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
set_option autoImplicit false
namespace ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration
def c : Fin 3 → ℕ := ![0,512,1025]
def cacheCost {N : ℕ} (R : Word N) : ℕ := cost c R
def caps {N : ℕ} (coords : List (Fin N)) (R : Word N) : List ℕ :=
  coords.map (fun i => (R i).val)
def work {N : ℕ} (T : ℕ) : List (Fin N) → Word N → ℕ
  | [], _ => 1
  | i :: rest, R => if cacheCost R ≤ T then 1 else
      1 + ∑ d : Fin 3, if d ≤ R i then work T rest (Function.update R i d) else 0
def capWord {N : ℕ} (coords : List (Fin N)) (R : Word N) : Word coords.length :=
  TernaryFrozenQueryCost.capWord coords R
end ThreeSum.WeightedFrozenQueryCost


