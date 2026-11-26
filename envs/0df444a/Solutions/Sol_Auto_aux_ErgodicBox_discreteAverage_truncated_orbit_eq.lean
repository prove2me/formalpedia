-- Prove2me | solution 1 for Auto.aux_ErgodicBox.discreteAverage_truncated_orbit_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:54:49.810838+00:00
-- url     : https://prove2.me/submissions/4852013c-f754-4125-9524-816f56d36e42

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_add_coordinate_mem_box

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Auto.aux_ErgodicBox
theorem _root_.solution {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {n L M N : ℕ}
    (S : ErgodicSystem X μ n) (f : Fin n → X → ℝ) (x : X)
    (k : Fin n → ℕ) (hk : k ∈ box n L) (hN : N ≤ M) :
    aux_discreteAverage N
      (fun i ↦ truncOrbit
        (box n (L + M)) (aux_orbit S.transformation) (f i) x) k =
      aux_discreteAverage N (aux_orbitFunction S f x) k := by
  unfold aux_discreteAverage
  change (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
    ∏ i, truncOrbit
      (box n (L + M)) (aux_orbit S.transformation) (f i) x
      (k + aux_coordinate i m) =
      (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
        ∏ i, aux_orbitFunction S f x i (k + aux_coordinate i m)
  apply congrArg (fun z : ℝ ↦ (N : ℝ)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.prod_congr rfl
  intro i hi
  rw [truncOrbit, Set.indicator_of_mem]
  · rfl
  · apply add_coordinate_mem_box k hk i m
    exact Finset.mem_range.mp hm |>.trans_le hN
end Auto.aux_ErgodicBox
