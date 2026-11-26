-- Prove2me | solution 1 for Auto.aux_integral_wienerEnvelope_integral_slice_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:56:53.939175+00:00
-- url     : https://prove2.me/submissions/0e13b34a-80f5-4265-8823-4b91122e16fb

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_norm_le_wienerEnvelope_of_mem_closedBall
public import Theorems.Thm_Auto_MemW0_aux_integrable
public import Theorems.Thm_Auto_MemW0_aux_mem_wienerEnvelope_prod
public import Theorems.Thm_Auto_MemW0_aux_memW0_slice
public import Theorems.Thm_Auto_aux_continuous_integral_slice
public import Theorems.Thm_Auto_MemW0_aux_integral_slice

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {m l : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) :
    (∫ u, wienerEnvelope (fun u ↦ ∫ v, f (u, v)) 1 u) ≤
      ∫ p, wienerEnvelope f 1 p := by
  let F : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → ℝ :=
    wienerEnvelope f 1
  have hF : MemW0 F := hf.aux_mem_wienerEnvelope_prod zero_le_one
  have hF_slice (u : EuclideanSpace ℝ (Fin m)) : Integrable (fun v ↦ F (u, v)) :=
    (hF.aux_memW0_slice u).aux_integrable
  have hf_slice (u : EuclideanSpace ℝ (Fin m)) : Integrable (fun v ↦ f (u, v)) :=
    (hf.aux_memW0_slice u).aux_integrable
  have hcont : Continuous (fun u ↦ ∫ v, f (u, v)) := aux_continuous_integral_slice hf
  have hH : Integrable (fun u ↦ ∫ v, F (u, v)) := hf.2.integral_prod_left
  have hpoint : ∀ u, wienerEnvelope (fun u ↦ ∫ v, f (u, v)) 1 u ≤ ∫ v, F (u, v) := by
    intro u
    unfold wienerEnvelope
    apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
    rintro _ ⟨w, hw, rfl⟩
    change ‖∫ v, f (u + w, v)‖ ≤ ∫ v, F (u, v)
    calc
      ‖∫ v, f (u + w, v)‖ ≤ ∫ v, ‖f (u + w, v)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ v, F (u, v) := by
        apply integral_mono (hf_slice (u + w)).norm (hF_slice u)
        intro v
        change ‖f (u + w, v)‖ ≤ wienerEnvelope f 1 (u, v)
        apply aux_norm_le_wienerEnvelope_of_mem_closedBall hf.1
        apply Metric.mem_closedBall.mpr
        rw [Prod.dist_eq]
        apply max_le
        · simpa [Metric.mem_closedBall, dist_eq_norm] using hw
        · simp
  calc
    (∫ u, wienerEnvelope (fun u ↦ ∫ v, f (u, v)) 1 u) ≤ ∫ u, ∫ v, F (u, v) :=
      integral_mono (MemW0.aux_integral_slice hf).2 hH hpoint
    _ = ∫ p, F p := integral_integral hf.2
    _ = ∫ p, wienerEnvelope f 1 p := rfl
end Auto
