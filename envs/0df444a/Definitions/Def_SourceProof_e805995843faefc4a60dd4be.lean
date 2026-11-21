-- Prove2me | Definitions.Def_SourceProof_e805995843faefc4a60dd4be
-- name    : SourceProof_e805995843faefc4a60dd4be
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:49:11.289177+00:00
-- url     : https://prove2.me/theorems/fb463773-f93b-43d3-ba9f-53397ed80556
-- title:
--   LevyStochCalc source module: SourceProof_e805995843faefc4a60dd4be
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnRawStop_diff_le` comes from the `LevyStochCalc.Ito.PicardContractionFixedPoint` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F002
import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F004

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The fixed point of the Picard step

The limit `picardLimit` of the Picard iterates is jointly measurable, progressively measurable and
of finite Bielecki norm, and the Bielecki distance between the step taken along it and the limit
itself vanishes, so the step and the limit agree almost surely at every time of the window. The
step contracts between two raw state processes and therefore respects almost sure equality of its
input, which promotes that agreement to the statement that the process built over the limit solves
the Picard equation along its own path.

## Main statements

* `picardLimit` — the limit of the Picard iterates.
* `bieleckiNorm_picardStepOnRawStop_picardLimit_eq_zero` — the limit is a fixed point in norm.
* `picardSelfMapRaw_picardLimit_ae_eq` — the fixed point is realised by a process of the space.
* `picardSelfMapRaw_isFixedPoint` — the fixed point solves its own Picard equation.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)

/-! ### The fixed point -/

variable {L : ℝ}
  (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
  (x₀ : Fin n → ℝ)

/-! ### The step respects almost sure equality of its input -/

omit [ℱ'.IsRightContinuous] in

theorem _root_.Prove2MeSourceProof.h_e805995843faefc4a60dd4be
    {Z₁ : ℝ → Ω → (Fin n → ℝ)} (h₁m : Measurable (Function.uncurry Z₁))
    (h₁a : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₁ s ω i)
    (h₁b : bieleckiNorm (P := P) 0 T Z₁ < ⊤)
    {Z₂ : ℝ → Ω → (Fin n → ℝ)} (h₂m : Measurable (Function.uncurry Z₂))
    (h₂a : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₂ s ω i)
    (h₂b : bieleckiNorm (P := P) 0 T Z₂ < ⊤)
    {β : ℝ} (hβ : 0 < β) (hT : 0 < T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ t ω i
          - picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => Z₁ t ω i - Z₂ t ω i) := by
  have h₁sm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z₁ (min s T) ω) :=
    h₁m.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have h₂sm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z₂ (min s T) ω) :=
    h₂m.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have h₁e := LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top h₁m h₁b hT.le
  have h₂e := LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top h₂m h₂b hT.le
  have hdiffm : Measurable
      (Function.uncurry fun (ω : Ω) (s : ℝ) => Z₁ (min s T) ω - Z₂ (min s T) ω) :=
    (h₁sm.comp (measurable_snd.prodMk measurable_fst)).sub
      (h₂sm.comp (measurable_snd.prodMk measurable_fst))
  have hrhs : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T
      (fun t ω i => Z₁ (min t T) ω i - Z₂ (min t T) ω i)
      = LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => Z₁ t ω i - Z₂ t ω i) :=
    LevyStochCalc.Ito.Picard.bieleckiNorm_min (P := P) β T fun t ω i => Z₁ t ω i - Z₂ t ω i
  rw [← hrhs]
  exact _root_.Prove2MeSourceProof.h_c94cbdb36d9b3fa8f9bc948b W N ℱ' hℱW hℱN coeffs hLip
    (fun s ω => Z₁ (min s T) ω) (fun s ω => Z₂ (min s T) ω) x₀
    (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg h₁m T)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg h₁a T)
    (fun i j _ hT' => _root_.Prove2MeSourceProof.h_bdaa282fd363a3be48f8fdce coeffs hReg hLip
      (Z := fun s ω => Z₁ (min s T) ω) h₁sm h₁e i j hT')
    (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg h₁m T)
    (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg h₁a T)
    (fun i _ hT' => _root_.Prove2MeSourceProof.h_e554e55fb9c1def6b7e8b55b coeffs hReg hLip
      (Z := fun s ω => Z₁ (min s T) ω) h₁sm h₁e i hT')
    (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg h₂m T)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg h₂a T)
    (fun i j _ hT' => _root_.Prove2MeSourceProof.h_bdaa282fd363a3be48f8fdce coeffs hReg hLip
      (Z := fun s ω => Z₂ (min s T) ω) h₂sm h₂e i j hT')
    (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg h₂m T)
    (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg h₂a T)
    (fun i _ hT' => _root_.Prove2MeSourceProof.h_e554e55fb9c1def6b7e8b55b coeffs hReg hLip
      (Z := fun s ω => Z₂ (min s T) ω) h₂sm h₂e i hT')
    (LevyStochCalc.Ito.Picard.measurable_mu_rawStop coeffs hReg h₁m T)
    (LevyStochCalc.Ito.Picard.measurable_mu_rawStop coeffs hReg h₂m T)
    hdiffm.norm
    (fun i b hb => _root_.Prove2MeSourceProof.h_946b446a671aae16e8dcf40a coeffs hReg hLip
      (Z := fun s ω => Z₁ (min s T) ω) h₁e i hb)
    (fun i b hb => _root_.Prove2MeSourceProof.h_946b446a671aae16e8dcf40a coeffs hReg hLip
      (Z := fun s ω => Z₂ (min s T) ω) h₂e i hb)
    (fun b _ => _root_.Prove2MeSourceProof.h_69f8ae19d7aa20df82811c65 h₁sm h₂sm h₁e h₂e b)
    hdiffm hβ hT
/-! ### The fixed point solves its own Picard equation -/

end LevyStochCalc.Ito.Picard


