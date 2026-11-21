-- Prove2me | Definitions.Def_SourceProof_c28516e04cb432d3ac50eea0
-- name    : SourceProof_c28516e04cb432d3ac50eea0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:37:11.795172+00:00
-- url     : https://prove2.me/theorems/acee6346-6596-4a70-b651-759c03290111
-- title:
--   LevyStochCalc source module: SourceProof_c28516e04cb432d3ac50eea0
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnStop_sub_rawStop_le` comes from the `LevyStochCalc.Ito.PicardContractionEstimate` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardLimit_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputStepDiff_F000
import Definitions.Def_SourceProof_69f8ae19d7aa20df82811c65
import Definitions.Def_SourceProof_c94cbdb36d9b3fa8f9bc948b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Picard contraction estimate

The contraction estimate of `bieleckiNorm_picardStep_diff_le` is stated for the Picard step along
two raw path maps. Along two processes of the space its hypotheses are supplied by the frozen
integrand lemmas, and the Bielecki norm of a difference is unchanged by freezing at the horizon, so
the estimate transfers to `picardStepOnStop`, from there through the modification
`picardSelfMap_ae_eq` to `picardSelfMap` itself, and in the same way to the step taken against a
raw state process. The iterates `picardIter` of the self-map are consequently geometrically
Bielecki-Cauchy, and at a weight making the contraction rate `< 1` they converge to
`bieleckiLimit`.

## Main statements

* `bieleckiNorm_picardStepOnStop_diff_le` — the estimate for the step along frozen processes.
* `bieleckiNorm_picardSelfMap_diff_le` — the estimate for the self-map.
* `bieleckiNorm_picardIter_sub_bieleckiLimit_le` — the iterates converge to `bieleckiLimit`.
* `bieleckiNorm_picardStepOnStop_sub_rawStop_le` — the estimate against a raw state process.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

/-! ### The difference of two frozen processes -/

/-! ### The contraction estimate for the step and the self-map -/

/-! ### The Picard iterates and their limit -/

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)

/-! ### The limit of the iterates -/

/-! ### Bielecki bookkeeping for the fixed point -/

/-! ### The step against a raw state process -/

omit [ℱ'.IsRightContinuous] in

theorem _root_.Prove2MeSourceProof.h_c28516e04cb432d3ac50eea0 {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X : SBoundedProcess (n := n) P ℱ' T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
          - picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Z t ω i) := by
  have hZsm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z (min s T) ω) :=
    hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have hXe : ∀ c : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) c,
      ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun c =>
    lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_ba444e4a7f686c4937645db3 X hT.le c)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top X.sup_L2))
  have hZe : ∀ c : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) c,
      ∑ i, (‖Z (min s T) ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le
  have hdiffm : Measurable
      (Function.uncurry fun (ω : Ω) (s : ℝ) => X.stop.X s ω - Z (min s T) ω) :=
    (X.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst)).sub
      (hZsm.comp (measurable_snd.prodMk measurable_fst))
  have hrhs : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T
      (fun t ω i => X.stop.X t ω i - Z (min t T) ω i)
      = LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Z t ω i) :=
    LevyStochCalc.Ito.Picard.bieleckiNorm_min (P := P) β T fun t ω i => X.X t ω i - Z t ω i
  rw [← hrhs]
  exact _root_.Prove2MeSourceProof.h_c94cbdb36d9b3fa8f9bc948b W N ℱ' hℱW hℱN coeffs hLip X.stop.X
    (fun s ω => Z (min s T) ω) x₀
    (fun i j => LevyStochCalc.Ito.Picard.measurable_sigma_stop coeffs hReg X i j)
    (fun i j => LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_stop coeffs hReg X i j)
    (fun i j _ hT' => LevyStochCalc.Ito.Picard.lintegral_sq_sigma_stop_lt_top coeffs hReg hLip X hT.le i j hT')
    (fun i => LevyStochCalc.Ito.Picard.measurable_gamma_stop coeffs hReg X i)
    (fun i => LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_stop coeffs hReg X i)
    (fun i _ hT' => LevyStochCalc.Ito.Picard.lintegral_sq_gamma_stop_lt_top coeffs hReg hLip X hT.le i hT')
    (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i j _ hT' => _root_.Prove2MeSourceProof.h_bdaa282fd363a3be48f8fdce coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hZsm hZe i j hT')
    (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i _ hT' => _root_.Prove2MeSourceProof.h_e554e55fb9c1def6b7e8b55b coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hZsm hZe i hT')
    (fun i => LevyStochCalc.Ito.Picard.measurable_mu_stop coeffs hReg X i)
    (LevyStochCalc.Ito.Picard.measurable_mu_rawStop coeffs hReg hZm T)
    hdiffm.norm
    (fun i b hb => LevyStochCalc.Ito.Picard.lintegral_sq_mu_stop_lt_top coeffs hReg hLip X hT.le i hb)
    (fun i b hb => _root_.Prove2MeSourceProof.h_946b446a671aae16e8dcf40a coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hZe i hb)
    (fun b _ => _root_.Prove2MeSourceProof.h_69f8ae19d7aa20df82811c65 X.stop.measurable_path hZsm hXe hZe b)
    hdiffm hβ hT
end LevyStochCalc.Ito.Picard


