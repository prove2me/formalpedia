-- Prove2me | solution 1 for Auto.aux_discreteAverage_congr_on
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:50:28.225908+00:00
-- url     : https://prove2.me/submissions/d2b65db7-0d2a-43cf-976a-984963ba0473

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {n : ℕ} (N : ℕ)
    (F G : Fin n → (Fin n → ℕ) → ℝ) (k : Fin n → ℕ)
    (h : ∀ i m, m ∈ Finset.range N →
      F i (k + aux_coordinate i m) = G i (k + aux_coordinate i m)) :
    aux_discreteAverage N F k = aux_discreteAverage N G k := by
  unfold aux_discreteAverage
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.prod_congr rfl
  intro i hi
  exact h i m hm
end Auto
