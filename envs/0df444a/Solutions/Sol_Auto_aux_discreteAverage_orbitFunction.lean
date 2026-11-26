-- Prove2me | solution 1 for Auto.aux_discreteAverage_orbitFunction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:48:08.593916+00:00
-- url     : https://prove2.me/submissions/dd4b02fc-9ebc-488d-abc0-5701ba44ce83

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_orbit_add_coordinate_apply

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {n : ℕ}
    (S : ErgodicSystem X μ n) (f : Fin n → X → ℝ) (x : X)
    (k : Fin n → ℕ) (N : ℕ) :
    aux_discreteAverage N (aux_orbitFunction S f x) k =
      realErgodicAverage S N f (aux_orbit S.transformation k x) := by
  apply congrArg (fun z : ℝ ↦ (N : ℝ)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (f i) (aux_orbit_add_coordinate_apply S k i m x)
end Auto
