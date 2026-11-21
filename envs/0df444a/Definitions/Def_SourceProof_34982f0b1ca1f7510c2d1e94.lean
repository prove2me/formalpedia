-- Prove2me | Definitions.Def_SourceProof_34982f0b1ca1f7510c2d1e94
-- name    : SourceProof_34982f0b1ca1f7510c2d1e94
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:58:39.486362+00:00
-- url     : https://prove2.me/theorems/e93408c3-f8ef-410e-94eb-8c7751b01c66
-- title:
--   LevyStochCalc source module: SourceProof_34982f0b1ca1f7510c2d1e94
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.bieleckiNorm_picardLimit_lt_top` comes from the `LevyStochCalc.Ito.PicardContractionFixedPoint` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F000
import Definitions.Def_SourceProof_ccebe3794d4ea7bf9fc96cf0

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


theorem _root_.Prove2MeSourceProof.h_34982f0b1ca1f7510c2d1e94 {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1) :
    bieleckiNorm (P := P) 0 T
      (picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀) < ⊤ := by
  have hYm := LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hbase : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T X₀.X < ⊤ :=
    lt_of_le_of_lt (LevyStochCalc.Ito.Picard.bieleckiNorm_le_bieleckiNorm_zero hβ.le T X₀.X) X₀.sup_L2
  have hsub := LevyStochCalc.Ito.Picard.bieleckiNorm_picardIter_sub_bieleckiLimit_le W N ℱ' hℱW hℱN hℱ0 hnull coeffs
    hReg hLip x₀ hβ hT X₀ hq 0
  have hfin : ((1 - (ENNReal.ofReal
        ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
          / (2 * β))) ^ ((1 : ℝ) / 2))⁻¹
      * LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i =>
          (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
            - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X t ω i))
      ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hq).ne')
      (_root_.Prove2MeSourceProof.h_65bedb6096fb4f69009cb5ba ℱ' hβ.le _ _).ne
  have hd : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X₀.X t ω i
      - LevyStochCalc.Ito.Picard.picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ t ω i) < ⊤ := by
    refine lt_of_le_of_lt hsub ?_
    rw [pow_zero, one_mul]
    exact lt_top_iff_ne_top.mpr hfin
  refine lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_ccebe3794d4ea7bf9fc96cf0 (P := P) hβ.le _)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact LevyStochCalc.Ito.Picard.bieleckiNorm_lt_top_of_approx β T
    (fun t i => LevyStochCalc.Ito.Picard.measurable_slice_of_uncurry X₀.measurable_path t i)
    (fun t i => LevyStochCalc.Ito.Picard.measurable_slice_of_uncurry hYm t i) hbase hd
/-! ### The step respects almost sure equality of its input -/

/-! ### The fixed point solves its own Picard equation -/

end LevyStochCalc.Ito.Picard


