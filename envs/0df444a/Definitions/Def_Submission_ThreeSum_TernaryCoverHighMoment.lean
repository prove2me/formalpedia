-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverHighMoment
-- name    : Submission_ThreeSum_TernaryCoverHighMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:03:27.308683+00:00
-- url     : https://prove2.me/theorems/bf51c5ee-2f39-4f8f-ab5f-4be7502a55bb
-- title:
--   Ternary Cover High Moment
-- statement:
--   Definitions and structural lemmas for Ternary Cover High Moment, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHighMoment.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverTupleCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Definitions.Def_Submission_ThreeSum_TernaryCoverMoments
import Mathlib.Logic.Equiv.Fin.Basic
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverRelations_span_mem_possibleSpans
attribute [local simp] ThreeSum.HashFamily.hashMap_apply


set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCoverHighMoment
open Finset TernaryCoverRankFibers TernaryCoverTupleCount
open TernaryCoverRelations TernaryCoverUniformRank TernaryCoverMoments
open scoped BigOperators
variable {K E σ : Type*} [Field K] [Fintype E] [Fintype σ] [DecidableEq σ]
def flattenPairs (k : ℕ) : (Fin k → K × K) ≃ₗ[K] (Fin (k*2) → K) where
  toFun v j := if (finProdFinEquiv.symm j).2 = 0 then
    (v (finProdFinEquiv.symm j).1).1 else (v (finProdFinEquiv.symm j).1).2
  invFun w j := (w (finProdFinEquiv (j,0)), w (finProdFinEquiv (j,1)))
  left_inv v := by
    funext j
    apply Prod.ext <;> simp
  right_inv w := by
    funext j
    obtain ⟨ab, rfl⟩ := finProdFinEquiv.surjective j
    obtain ⟨a,b⟩ := ab
    fin_cases b <;> simp
  map_add' v w := by funext j; dsimp only [Pi.add_apply]; split_ifs <;> rfl
  map_smul' a v := by funext j; dsimp only [Pi.smul_apply]; split_ifs <;> rfl
@[simp] theorem flattenPairs_apply (k : ℕ) (v : Fin k → K × K) (j : Fin (k*2)) :
    flattenPairs k v j = if (finProdFinEquiv.symm j).2 = 0 then
      (v (finProdFinEquiv.symm j).1).1 else (v (finProdFinEquiv.symm j).1).2 := rfl
@[simp] theorem flattenPairs_prod_zero (k : ℕ) (v : Fin k → K × K) (j : Fin k) :
    flattenPairs k v (finProdFinEquiv (j,0)) = (v j).1 := by
  rw [flattenPairs_apply, Equiv.symm_apply_apply]
  rfl
@[simp] theorem flattenPairs_prod_one (k : ℕ) (v : Fin k → K × K) (j : Fin k) :
    flattenPairs k v (finProdFinEquiv (j,1)) = (v j).2 := by
  rw [flattenPairs_apply, Equiv.symm_apply_apply]
  simp
def castWord (v : σ → Fin 3) : σ → K := fun i => ((v i).val : K)
def rows (left right : E → σ → Fin 3) {k : ℕ} (es : Fin k → E) : Fin (k*2) → σ → K :=
  fun j i => flattenPairs k (tupleColumn (fun e => castWord (left e)) (fun e => castWord (right e)) es i) j
def digitColumns (left right : E → σ → Fin 3) {k : ℕ} (es : Fin k → E) :
    σ → Fin (k*2) → Fin 3 :=
  fun i j => if (finProdFinEquiv.symm j).2 = 0 then
    left (es (finProdFinEquiv.symm j).1) i else right (es (finProdFinEquiv.symm j).1) i
theorem columnSpan_rows (left right : E → σ → Fin 3) {k : ℕ} (es : Fin k → E) :
    columnSpan (rows (K := K) left right es) =
      Submodule.span K (Set.range fun i => digitVector (K := K) (digitColumns left right es i)) := by
  congr 2
  funext i j
  unfold rows
  rw [flattenPairs_apply]
  unfold tupleColumn castWord digitColumns digitVector
  dsimp only
  split_ifs <;> rfl
def classify (left right : E → σ → Fin 3) {k : ℕ} (es : Fin k → E) :
    (possibleSpans K (k*2)) :=
  ⟨columnSpan (rows left right es), by
    rw [columnSpan_rows]
    exact span_mem_possibleSpans (digitColumns left right es)⟩
variable [Fintype K] [DecidableEq K]
def rawEvents (left right : E → σ → Fin 3) (a b : K) (e : E) : Finset (σ → K) :=
  univ.filter fun w => (∑ i, castWord (left e) i * w i) = a ∧
    (∑ i, castWord (right e) i * w i) = b
end ThreeSum.TernaryCoverHighMoment


