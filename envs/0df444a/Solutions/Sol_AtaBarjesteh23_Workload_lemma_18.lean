-- Prove2me | solution 1 for AtaBarjesteh23.Workload.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:59:50.454299+00:00
-- url     : https://prove2.me/submissions/c8218fad-ed4e-4c70-86cf-95aead52a549

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control
import Theorems.Thm_AtaBarjesteh23_Workload_lemma_19

open MeasureTheory Set Filter Topology

open AtaBarjesteh23.Workload in
theorem solution (M : Model) (hM : M.Standing) (wbar : ℝ) (hwbar : 0 < wbar) (v : ℝ → ℝ)
    (hv0 : v 0 = -M.kappa)
    (hode : ∀ w ∈ Icc 0 wbar, HasDerivWithinAt v
      (M.a / (2 * M.σ ^ 2) * (v w ^ 2 - M.kappa ^ 2) - 2 * M.μ / M.σ ^ 2 * (v w + M.kappa)
        + 2 * M.bStar / M.σ ^ 2 * w) (Icc 0 wbar) w) :
    ∀ w ∈ Icc 0 wbar, -M.kappa ≤ v w := by
  have h19 := lemma_19 M hM wbar hwbar v hv0 hode
  have hcont : ContinuousOn v (Icc 0 wbar) := fun w hw => (hode w hw).continuousWithinAt
  have hmono : MonotoneOn v (Icc 0 wbar) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 wbar) hcont
      (f' := fun w => derivWithin v (Icc 0 wbar) w) ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx ⊢
      have hxI : x ∈ Icc 0 wbar := Ioo_subset_Icc_self hx
      rw [(hode x hxI).derivWithin (uniqueDiffOn_Icc hwbar x hxI)]
      exact (hode x hxI).mono Ioo_subset_Icc_self
    · intro x hx
      rw [interior_Icc] at hx
      exact (h19 x ⟨hx.1, hx.2.le⟩).le
  intro w hw
  rw [← hv0]
  exact hmono ⟨le_rfl, hwbar.le⟩ hw hw.1
