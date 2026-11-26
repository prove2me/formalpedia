-- Prove2me | solution 1 for Auto.aux_continuousLinearMap_pi_injective_of_iInf_ker_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:49:25.366393+00:00
-- url     : https://prove2.me/submissions/0421138e-2491-4e5d-86a9-3cf2a55f7983

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution
    {ι : Type*} {m l : ℕ} {d : ι → ℕ}
    (pi : ∀ i, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin (d i)))
    (hker : ⨅ i, LinearMap.ker (pi i).toLinearMap = ⊥) :
    Function.Injective (ContinuousLinearMap.pi pi) := by
  let A : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →ₗ[ℝ]
      (∀ i, EuclideanSpace ℝ (Fin (d i))) :=
    LinearMap.pi (fun i ↦ (pi i).toLinearMap)
  have hA : Function.Injective A := LinearMap.ker_eq_bot.mp (by
    rw [LinearMap.ker_pi]
    exact hker)
  intro x y hxy
  apply hA
  change (fun i ↦ pi i x) = fun i ↦ pi i y
  exact hxy
end Auto
