-- Prove2me | Definitions.Def_SourceProof_e264a15a5a2a191954307942
-- name    : SourceProof_e264a15a5a2a191954307942
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:52:24.440208+00:00
-- url     : https://prove2.me/theorems/156e80b2-1cd4-4a22-bb65-d730a483454d
-- title:
--   LevyStochCalc source module: SourceProof_e264a15a5a2a191954307942
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.measurable_picardStepOnRawStop_slice` comes from the `LevyStochCalc.Ito.PicardContractionFixedPoint` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F002
import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F004
import Definitions.Def_SourceProof_08e35a25f567af421cb39bf8

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

omit [ℱ'.IsRightContinuous] in

theorem _root_.Prove2MeSourceProof.h_e264a15a5a2a191954307942
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) (hT : 0 ≤ T) (t : ℝ) (i : Fin n) :
    Measurable fun ω =>
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT x₀ t ω i :=
  _root_.Prove2MeSourceProof.h_08e35a25f567af421cb39bf8 W N ℱ' hℱW hℱN coeffs (fun s ω => Z (min s T) ω) x₀
    (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i' j _ hT' => _root_.Prove2MeSourceProof.h_bdaa282fd363a3be48f8fdce coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT) i' j hT')
    (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i' _ hT' => _root_.Prove2MeSourceProof.h_e554e55fb9c1def6b7e8b55b coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT) i' hT')
    (LevyStochCalc.Ito.Picard.measurable_mu_rawStop coeffs hReg hZm T) t i
/-! ### The step respects almost sure equality of its input -/

/-! ### The fixed point solves its own Picard equation -/

end LevyStochCalc.Ito.Picard


