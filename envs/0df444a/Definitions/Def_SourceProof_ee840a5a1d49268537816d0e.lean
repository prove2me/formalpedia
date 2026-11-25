-- Prove2me | Definitions.Def_SourceProof_ee840a5a1d49268537816d0e
-- name    : SourceProof_ee840a5a1d49268537816d0e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:45:59.082302+00:00
-- url     : https://prove2.me/theorems/844e6014-df32-4ee7-8887-71e6f3335446
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLocalMartingale.martingale_of_integrable_envelope

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_SourceProof_49a22f8c8626f92746c475a0
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Dominated local martingales are martingales

The proof takes limits in the defining set-integral identities of the masked
fundamental sequence. Thus it does not require continuous-time optional
sampling or a semimartingale decomposition.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {τ : ℕ → Ω → WithTop ℝ≥0}

namespace IsLocalMartingale

theorem _root_.Prove2MeSourceProof.h_ee840a5a1d49268537816d0e
    [SigmaFiniteFiltration P F] (hX : IsLocalMartingale X F P)
    (hdom : ∀ T : ℝ≥0, ∃ R : Ω → ℝ, Integrable R P ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, ‖X t ω‖ ≤ R ω) : Martingale X F P := by
  choose R hR hb using hdom
  obtain ⟨τ, hτ⟩ := hX.2.2
  let Y : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦
    stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n)
  have hYm : ∀ n, Martingale (Y n) F P := fun n ↦ (hτ.2.2 n).1
  have hYbound : ∀ n t, ∀ᵐ ω ∂P, ‖Y n t ω‖ ≤ R t ω := by
    intro n t
    filter_upwards [hb t] with ω hω
    change ‖stoppedProcess (fun s ↦ {ω | 0 < τ n ω}.indicator (X s)) (τ n) t ω‖ ≤ R t ω
    rw [stoppedProcess_indicator_comm]
    exact (norm_indicator_le_norm_self _ _).trans
      (hω _ (WithTop.untopA_le (min_le_left (t : WithTop ℝ≥0) (τ n ω))))
  have hXint : ∀ t, Integrable (X t) P := fun t ↦ (hR t).mono'
    ((hX.1 t).mono (F.le t) le_rfl).aestronglyMeasurable
    ((hb t).mono fun _ hω ↦ hω t le_rfl)
  have hconv : ∀ t A, Tendsto (fun n ↦ ∫ ω in A, Y n t ω ∂P) atTop
      (𝓝 (∫ ω in A, X t ω ∂P)) := by
    intro t A
    apply tendsto_integral_of_dominated_convergence (R t)
    · intro n
      exact ((hYm n).stronglyAdapted t).mono (F.le t) |>.aestronglyMeasurable.restrict
    · exact (hR t).integrableOn
    · intro n
      exact ae_restrict_of_ae (hYbound n t)
    · apply ae_restrict_of_ae
      filter_upwards [(_root_.Prove2MeSourceProof.h_49a22f8c8626f92746c475a0 (X := X) hτ.1) t] with ω hω
      apply tendsto_const_nhds.congr'
      filter_upwards [hω] with n hn
      exact hn.symm
  refine ⟨hX.1.stronglyAdapted, fun s t hst ↦ ?_⟩
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hXint t)
    (fun _ _ _ ↦ (hXint s).integrableOn) ?_
    (hX.1.stronglyAdapted s).aestronglyMeasurable).symm
  intro A hA _
  have heq : (fun n ↦ ∫ ω in A, Y n s ω ∂P) = fun n ↦ ∫ ω in A, Y n t ω ∂P :=
    funext fun n ↦ (hYm n).setIntegral_eq hst hA
  exact tendsto_nhds_unique (hconv s A) (heq ▸ hconv t A)
end IsLocalMartingale

end ProbabilityTheory


