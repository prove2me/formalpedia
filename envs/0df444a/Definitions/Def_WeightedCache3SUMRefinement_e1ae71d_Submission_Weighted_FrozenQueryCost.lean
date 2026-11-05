-- Prove2me | Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
-- name    : WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:08:17.864911+00:00
-- url     : https://prove2.me/theorems/de75506f-a072-4fff-9ee0-f141b8006559
-- title:
--   FrozenQueryCost
-- statement:
--   Definitions and structural lemmas for FrozenQueryCost, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrozenQueryCost.lean

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
set_option autoImplicit false
namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
namespace ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration
def c : Fin 3 → ℕ := ![0,1369,2740]
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
end WeightedCache3SUMRefinement_e1ae71d


