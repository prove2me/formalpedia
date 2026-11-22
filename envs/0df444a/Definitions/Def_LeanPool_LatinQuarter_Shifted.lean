-- Prove2me | Definitions.Def_LeanPool_LatinQuarter_Shifted
-- name    : LeanPool_LatinQuarter_Shifted
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:20:56.879418+00:00
-- url     : https://prove2.me/theorems/baf52544-e913-47f0-ab7c-c5ac2c116f09
-- title:
--   Shifted
-- statement:
--   Definitions and structural lemmas for Shifted, from Richard Bean; LeanPool contributors's pinned Critical sets in Latin squares development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Shifted.lean

module
public import Definitions.Def_LeanPool_LatinQuarter_Vanishing
public import Definitions.Def_LeanPool_LatinQuarter_Tags
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LatinQuarter
open scoped BigOperators Matrix
noncomputable def markedConstant {N : Type*} {k h : ℕ}
    (e : Fin k ⊕ Fin h ≃ N) (c s : N) : ZMod 2 := by
  classical
  exact if (e.symm c).isLeft ∧ c = s then 1 else 0
noncomputable def shiftedTags {N : Type*} {k h : ℕ}
    (e : Fin k ⊕ Fin h ≃ N) : Matrix N N (TagRing (N × N)) :=
  fun c s => tag (c, s) + algebraMap (ZMod 2) _ (markedConstant e c s)
end LatinQuarter


