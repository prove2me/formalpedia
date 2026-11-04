-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverTupleCount
-- name    : Submission_ThreeSum_TernaryCoverTupleCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:59:34.623478+00:00
-- url     : https://prove2.me/theorems/1d74deea-254b-4523-84ad-0c9a6bd76d35
-- title:
--   Ternary Cover Tuple Count
-- statement:
--   Definitions and structural lemmas for Ternary Cover Tuple Count, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverTupleCount.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep
import Mathlib.Data.Fin.Tuple.Basic
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCoverTupleCount
open Finset TernaryCoverRankFibers TernaryCoverPairStep
variable {K E ι : Type*} [Field K] [Fintype E] [Fintype ι] [DecidableEq K]
def tupleColumn (left right : E → ι → K) {n : ℕ} (es : Fin n → E) (i : ι) : Fin n → K × K :=
  fun j => (left (es j) i, right (es j) i)
def tupleSet (left right : E → ι → K) (n : ℕ) (S : Submodule K (Fin n → K × K)) :
    Finset (Fin n → E) := by
  classical
  exact univ.filter fun es => ∀ i, tupleColumn left right es i ∈ S
def splitRows (n : ℕ) : (Fin (n+1) → K × K) ≃ₗ[K] ((Fin n → K × K) × (K × K)) where
  toFun f := (Fin.tail f, f 0)
  invFun p := Fin.cons p.2 p.1
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_add' f g := rfl
  map_smul' a f := rfl
end ThreeSum.TernaryCoverTupleCount


