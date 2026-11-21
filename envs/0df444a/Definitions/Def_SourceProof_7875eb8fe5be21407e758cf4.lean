-- Prove2me | Definitions.Def_SourceProof_7875eb8fe5be21407e758cf4
-- name    : SourceProof_7875eb8fe5be21407e758cf4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:35:51.519175+00:00
-- url     : https://prove2.me/theorems/23567c59-2736-4117-a215-e8c5cad5526e
-- title:
--   LevyStochCalc source module: SourceProof_7875eb8fe5be21407e758cf4
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.picardStep_rawStop_congr_ae` comes from the `LevyStochCalc.Ito.PicardWindow` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardWindow_F001
import Definitions.Def_SourceProof_217f44132bf28379085aa30a

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Solutions of the SDE on a window

`SolvesOn` records that a path map satisfies the jump-diffusion integral equation at every time
of `[0, T]`, in the `picardStep` form; the integrand hypotheses that make the two stochastic
integrals well-typed are bundled existentially, as in
`LevyStochCalc.Ito.Setting.JumpDiffusion.is_solution`, so that a solution can be re-read with any
proof of them. Two solutions on a common window and a common filtration agree, by the Bielecki
contraction.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### From an `S²` bound to the time-integrated energy -/

/-! ### Auxiliary Bielecki facts -/

/-! ### Solutions on a window -/

section Solves

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (x₀ : Fin n → ℝ)

end Solves

/-! ### The canonical integrand hypotheses along a process with a finite `S²` norm -/

section Canonical

variable {ν : Measure E}
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}

end Canonical

/-! ### The window fixed point is a solution -/

section FixedPoint

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)


theorem _root_.Prove2MeSourceProof.h_7875eb8fe5be21407e758cf4
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤)
    (hZS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hT : 0 ≤ T) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∀ᵐ ω ∂P,
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT x₀ t ω
        = picardStep W N ℱ hℱW hℱN coeffs Z x₀
            (measurable_sigma_comp_state coeffs hReg hZm)
            (progressivelyMeasurable_sigma_comp_state coeffs hReg hZa)
            (lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
            (measurable_gamma_comp_state coeffs hReg hZm)
            (markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hZa)
            (lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
            t ω := by
  have hfrozenm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z (min s T) ω) :=
    hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  rcases ht0.lt_or_eq with ht0' | ht0'
  swap
  · subst ht0'
    filter_upwards [_root_.Prove2MeSourceProof.h_217f44132bf28379085aa30a W N ℱ hℱW hℱN coeffs (fun s ω => Z (min s T) ω) x₀
        (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg hZm T)
        (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
        (fun i j _ hb => _root_.Prove2MeSourceProof.h_bdaa282fd363a3be48f8fdce coeffs hReg hLip
          (Z := fun s ω => Z (min s T) ω) hfrozenm
          (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT) i j hb)
        (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg hZm T)
        (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
        (fun i _ hb => _root_.Prove2MeSourceProof.h_e554e55fb9c1def6b7e8b55b coeffs hReg hLip
          (Z := fun s ω => Z (min s T) ω) hfrozenm
          (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT) i hb),
      _root_.Prove2MeSourceProof.h_217f44132bf28379085aa30a W N ℱ hℱW hℱN coeffs Z x₀
        (LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hZm)
        (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hZa)
        (LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
        (LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hZm)
        (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hZa)
        (LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)] with ω h1 h2
    funext i
    rw [h2 i]
    exact h1 i
  have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      (fun (s : ℝ) (ω : Ω) => Z (min s T) ω) s ω = Z s ω := by
    refine Filter.Eventually.of_forall fun ω => ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    simp only [min_eq_left (hs.2.trans htT)]
  exact LevyStochCalc.Ito.Picard.picardStep_congr_ae W N ℱ hℱW hℱN coeffs (fun s ω => Z (min s T) ω) Z x₀
    (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i j _ hb => _root_.Prove2MeSourceProof.h_bdaa282fd363a3be48f8fdce coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hfrozenm (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT) i j hb)
    (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i _ hb => _root_.Prove2MeSourceProof.h_e554e55fb9c1def6b7e8b55b coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hfrozenm (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT) i hb)
    (LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hZm)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hZa)
    (LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
    (LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hZm)
    (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hZa)
    (LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
    ht0' hae
end FixedPoint

end LevyStochCalc.Ito.Picard


