-- Prove2me | Definitions.Def_SourceProof_1f315702e69a962a8644d530
-- name    : SourceProof_1f315702e69a962a8644d530
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:10:18.583176+00:00
-- url     : https://prove2.me/theorems/09712521-2dc0-497b-a724-3b2d3e9bf314
-- title:
--   LevyStochCalc source module: SourceProof_1f315702e69a962a8644d530
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.picardSelfMapRaw_isFixedPoint` comes from the `LevyStochCalc.Ito.PicardContractionFixedPoint` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F001
import Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F002

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

/-! ### The fixed point solves its own Picard equation -/


theorem _root_.Prove2MeSourceProof.h_1f315702e69a962a8644d530 {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i,
      (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
          (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
          (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
            x₀ hT X₀)
          (_root_.Prove2MeSourceProof.h_34982f0b1ca1f7510c2d1e94 W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
            hβ hT X₀ hq)).X t ω i
        = picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip
            (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
              (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
              (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
                x₀ hT X₀)
              (_root_.Prove2MeSourceProof.h_34982f0b1ca1f7510c2d1e94 W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
                hβ hT X₀ hq)).measurable_path
            (fun i' =>
              (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
                (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
                (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg
                  hLip x₀ hT X₀)
                (_root_.Prove2MeSourceProof.h_34982f0b1ca1f7510c2d1e94 W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
                  x₀ hβ hT X₀ hq)).adapted i')
            (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
              (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
              (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
                x₀ hT X₀)
              (_root_.Prove2MeSourceProof.h_34982f0b1ca1f7510c2d1e94 W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
                hβ hT X₀ hq)).sup_L2
            hT.le x₀ t ω i := by
  have hYm := LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hYa := LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
    x₀ hT X₀
  have hYb := _root_.Prove2MeSourceProof.h_34982f0b1ca1f7510c2d1e94 W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
    hβ hT X₀ hq
  set Xhat := LevyStochCalc.Ito.Picard.picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hYm hYa hYb
    with hXhat
  have heq : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i,
      LevyStochCalc.Ito.Picard.picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ u ω i
        = Xhat.X u ω i := by
    intro u hu
    filter_upwards [LevyStochCalc.Ito.Picard.picardSelfMapRaw_picardLimit_ae_eq W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg
      hLip x₀ hβ hT X₀ hq hu] with ω hω i
    exact (hω i).symm
  have hcongr := LevyStochCalc.Ito.Picard.picardStepOnRawStop_congr_ae W N ℱ' hℱW hℱN coeffs hReg hLip x₀
    hYm hYa hYb Xhat.measurable_path (fun i' => Xhat.adapted i') Xhat.sup_L2 heq hβ hT ht
  filter_upwards [_root_.Prove2MeSourceProof.h_b732528cf57a7c0dad8dceb7 W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
    hYm hYa hYb t, hcongr] with ω hmod hc i
  rw [congrFun hmod i]
  exact hc i
end LevyStochCalc.Ito.Picard


