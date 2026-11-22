-- Prove2me | Definitions.Def_SourceProof_000cd4ee6b13d23947f0c539
-- name    : SourceProof_000cd4ee6b13d23947f0c539
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:49:41.254184+00:00
-- url     : https://prove2.me/theorems/7d196f24-ce6e-46ef-86e2-ffd76629aa0d
-- title:
--   LevyStochCalc source module: SourceProof_000cd4ee6b13d23947f0c539
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.solvesOn_globalPatch` comes from the `LevyStochCalc.Ito.PicardGlobal` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F001
import Definitions.Def_SourceProof_217f44132bf28379085aa30a
import Definitions.Def_SourceProof_bb3bc292bcc4870943aee2a2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From window solutions to a solution on `[0, ∞)`

The Bielecki contraction produces a solution on each finite window. Uniqueness on the shorter of
two windows makes the family consistent, and right-continuity upgrades that to an almost-sure
agreement of whole paths, so the windows can be glued along `⌈t⌉₊` into a single path map that
restricts to a window solution on every `[0, T]`.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Right-continuity upgrades per-time equality to path equality -/

/-! ### The glued path map -/

/-! ### Consistency of a family of window solutions -/

section Glue

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)


theorem _root_.Prove2MeSourceProof.h_000cd4ee6b13d23947f0c539
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hYm : ∀ k, Measurable (Function.uncurry (Y k)))
    (hYa : ∀ k, ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y k s ω i)
    (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
      globalPatch Y t ω = Y k t ω)
    (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hYsol : ∀ k : ℕ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ (Y k) ((k : ℝ) + 1)) (T : ℝ) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ (globalPatch Y) T := by
  have hpm := LevyStochCalc.Ito.Picard.measurable_globalPatch hYm
  have hpa := fun i => _root_.Prove2MeSourceProof.h_bb3bc292bcc4870943aee2a2 hYa i
  have hpS := LevyStochCalc.Ito.Picard.lintegral_sq_iSup_globalPatch_lt_top hagree hYS
  refine ⟨LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hpm,
    LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hpa,
    LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hpm hpS,
    LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hpm,
    LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hpa,
    LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hpm hpS, ?_⟩
  intro t ht
  have htk : t ≤ (⌈t⌉₊ : ℝ) + 1 := (Nat.le_ceil t).trans (by linarith)
  have heqn := (hYsol ⌈t⌉₊).eqn t ⟨ht.1, htk⟩
  rcases ht.1.lt_or_eq with ht0 | ht0
  · have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
        Y ⌈t⌉₊ s ω = LevyStochCalc.Ito.Picard.globalPatch Y s ω := by
      filter_upwards [hagree] with ω hω
      refine (ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun s hs => ?_)
      exact (hω ⌈t⌉₊ s ⟨hs.1, hs.2.trans htk⟩).symm
    have hcongr := LevyStochCalc.Ito.Picard.picardStep_congr_ae W N ℱ hℱW hℱN coeffs (Y ⌈t⌉₊) (LevyStochCalc.Ito.Picard.globalPatch Y) x₀
      (hYsol ⌈t⌉₊).h_σ_meas (hYsol ⌈t⌉₊).h_σ_progMeas (hYsol ⌈t⌉₊).h_σ_sq
      (hYsol ⌈t⌉₊).h_γ_meas (hYsol ⌈t⌉₊).h_γ_progMeas (hYsol ⌈t⌉₊).h_γ_sq
      (LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hpm)
      (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hpa)
      (LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hpm hpS)
      (LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hpm)
      (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hpa)
      (LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hpm hpS) ht0 hae
    filter_upwards [heqn, hagree, hcongr] with ω h1 h2 h3
    intro i
    rw [h2 ⌈t⌉₊ t ⟨ht.1, htk⟩, h1 i, h3]
  · subst ht0
    filter_upwards [heqn, hagree,
      _root_.Prove2MeSourceProof.h_217f44132bf28379085aa30a W N ℱ hℱW hℱN coeffs (Y ⌈(0 : ℝ)⌉₊) x₀
        (hYsol ⌈(0 : ℝ)⌉₊).h_σ_meas (hYsol ⌈(0 : ℝ)⌉₊).h_σ_progMeas
        (hYsol ⌈(0 : ℝ)⌉₊).h_σ_sq (hYsol ⌈(0 : ℝ)⌉₊).h_γ_meas
        (hYsol ⌈(0 : ℝ)⌉₊).h_γ_progMeas (hYsol ⌈(0 : ℝ)⌉₊).h_γ_sq,
      _root_.Prove2MeSourceProof.h_217f44132bf28379085aa30a W N ℱ hℱW hℱN coeffs (LevyStochCalc.Ito.Picard.globalPatch Y) x₀
        (LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hpm)
        (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hpa)
        (LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hpm hpS)
        (LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hpm)
        (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hpa)
        (LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hpm hpS)] with ω h1 h2 h3 h4
    intro i
    rw [h2 ⌈(0 : ℝ)⌉₊ 0 ⟨le_rfl, htk⟩, h1 i, h3 i, h4 i]
end Glue

end LevyStochCalc.Ito.Picard


