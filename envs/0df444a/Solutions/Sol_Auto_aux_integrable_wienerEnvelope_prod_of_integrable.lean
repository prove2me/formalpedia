-- Prove2me | solution 1 for Auto.aux_integrable_wienerEnvelope_prod_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:53:24.972948+00:00
-- url     : https://prove2.me/submissions/5bb9e49f-dd0c-4591-81a8-770b357160f7

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_exists_finite_closedBall_cover
public import Theorems.Thm_Auto_aux_wienerEnvelope_le_sum_of_cover
public import Theorems.Thm_Auto_Integrable_aux_comp_add_right_prod

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {m l : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : Continuous f) {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hfr : Integrable (wienerEnvelope f r)) :
    Integrable (wienerEnvelope f s) := by
  classical
  obtain ⟨t, ht⟩ :=
    aux_exists_finite_closedBall_cover
      (E := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) r hr s
  have hsum : Integrable (fun x ↦ ∑ z ∈ t, wienerEnvelope f r (x + z)) := by
    apply integrable_finsetSum
    intro z hz
    exact Integrable.aux_comp_add_right_prod hfr z
  refine hsum.mono_nonneg (continuous_wienerEnvelope hf s).aestronglyMeasurable
    (ae_of_all _ fun x ↦ aux_wienerEnvelope_nonneg hf hs x) (ae_of_all _ fun x ↦ ?_)
  exact aux_wienerEnvelope_le_sum_of_cover hf (le_of_lt hr) hs t ht x
end Auto
