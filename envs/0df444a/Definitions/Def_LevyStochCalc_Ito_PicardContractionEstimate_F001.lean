-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F001
-- name    : LevyStochCalc_Ito_PicardContractionEstimate_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:38:13.256184+00:00
-- url     : https://prove2.me/theorems/eb0e9fa3-66fe-4230-90d0-c4d4f39fd6b5
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardContractionEstimate
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardContractionEstimate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F000
import Definitions.Def_SourceProof_69f8ae19d7aa20df82811c65
import Definitions.Def_SourceProof_6c43802417fce8ac3ae3997a
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

/-- The energy of the difference of two frozen processes is finite on every window. -/
theorem lintegral_sq_stop_sub_lt_top (X Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T)
    (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖X.stop.X s ω - Y.stop.X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  _root_.Prove2MeSourceProof.h_69f8ae19d7aa20df82811c65 X.stop.measurable_path Y.stop.measurable_path
    (fun c => lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_ba444e4a7f686c4937645db3 X hT c)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top X.sup_L2)))
    (fun c => lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_ba444e4a7f686c4937645db3 Y hT c)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top Y.sup_L2))) b
/-- Freezing at the horizon does not change the Bielecki norm of a difference. -/
theorem bieleckiNorm_stop_sub (β : ℝ) (X Y : SBoundedProcess (n := n) P ℱ T) :
    bieleckiNorm (P := P) β T (fun t ω i => X.stop.X t ω i - Y.stop.X t ω i)
      = bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) :=
  bieleckiNorm_min (P := P) β T fun t ω i => X.X t ω i - Y.X t ω i
/-! ### The contraction estimate for the step and the self-map -/

/-- **The Picard step along frozen processes is a Bielecki contraction**, with the rate of
`bieleckiNorm_picardStep_diff_le`. -/
theorem bieleckiNorm_picardStepOnStop_diff_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X Y : SBoundedProcess (n := n) P ℱ T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
          - picardStepOnStop W N hℱW hℱN coeffs hReg hLip Y hT.le x₀ t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) := by
  rw [← bieleckiNorm_stop_sub β X Y]
  exact _root_.Prove2MeSourceProof.h_c94cbdb36d9b3fa8f9bc948b W N ℱ hℱW hℱN coeffs hLip X.stop.X Y.stop.X x₀
    (fun i j => measurable_sigma_stop coeffs hReg X i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg X i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip X hT.le i j hT')
    (fun i => measurable_gamma_stop coeffs hReg X i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg X i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip X hT.le i hT')
    (fun i j => measurable_sigma_stop coeffs hReg Y i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg Y i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT.le i j hT')
    (fun i => measurable_gamma_stop coeffs hReg Y i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg Y i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT.le i hT')
    (fun i => measurable_mu_stop coeffs hReg X i)
    (fun i => measurable_mu_stop coeffs hReg Y i)
    (measurable_uncurry_stop_sub_norm X Y)
    (fun i b hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip X hT.le i hb)
    (fun i b hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip Y hT.le i hb)
    (fun b _ => lintegral_sq_stop_sub_lt_top X Y hT.le b)
    (measurable_uncurry_stop_sub X Y) hβ hT
/-- **The Picard self-map is a Bielecki contraction.** The self-map is a modification of the step
along the frozen process, and the Bielecki norm is unchanged under modification. -/
theorem bieleckiNorm_picardSelfMap_diff_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X Y : SBoundedProcess (n := n) P ℱ' T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X).X t ω i
          - (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y).X t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) := by
  have hcongr : bieleckiNorm (P := P) β T (fun t ω i =>
        (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X).X t ω i
          - (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y).X t ω i)
      = bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
          - picardStepOnStop W N hℱW hℱN coeffs hReg hLip Y hT.le x₀ t ω i) := by
    refine bieleckiNorm_congr_ae (P := P) β T fun t => ?_
    filter_upwards [_root_.Prove2MeSourceProof.h_6c43802417fce8ac3ae3997a W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X t,
      _root_.Prove2MeSourceProof.h_6c43802417fce8ac3ae3997a W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y t] with ω hX hY
    funext i
    rw [hX, hY]
  rw [hcongr]
  exact bieleckiNorm_picardStepOnStop_diff_le W N hℱW hℱN coeffs hReg hLip x₀ hβ hT X Y
/-! ### The Picard iterates and their limit -/

/-- A positive Bielecki weight only shrinks the norm on `[0, T]`. -/
theorem bieleckiNorm_le_bieleckiNorm_zero {β : ℝ} (hβ : 0 ≤ β) (T : ℝ)
    (Z : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) β T Z ≤ bieleckiNorm (P := P) 0 T Z := by
  refine iSup₂_le fun t ht => ?_
  have hw : ENNReal.ofReal (Real.exp (-β * t)) ≤ ENNReal.ofReal (Real.exp (-0 * t)) := by
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have : 0 ≤ β * t := mul_nonneg hβ ht.1
    nlinarith
  exact le_trans (mul_le_mul' hw le_rfl)
    (le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-0 * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) t ht)
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)

/-- **The Picard iterates** of a starting process under the self-map. -/
noncomputable def picardIter {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) (hT : 0 < T) (X₀ : SBoundedProcess (n := n) P ℱ' T) :
    ℕ → SBoundedProcess (n := n) P ℱ' T
  | 0 => X₀
  | k + 1 => picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
      (picardIter hLip x₀ hT X₀ k)
/-- The Picard iterates are geometrically Bielecki-Cauchy at the contraction rate. -/
theorem bieleckiNorm_picardIter_step_le {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T) (k : ℕ) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i
          - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k).X t ω i)
      ≤ ((ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)) ^ k
        * bieleckiNorm (P := P) β T (fun t ω i =>
            (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
              - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X t ω i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine le_trans (bieleckiNorm_picardSelfMap_diff_le W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg
      hLip x₀ hβ hT _ _) ?_
    refine le_trans (mul_le_mul' le_rfl ih) (le_of_eq ?_)
    rw [← mul_assoc, ← pow_succ']
/-! ### The limit of the iterates -/

/-! ### Bielecki bookkeeping for the fixed point -/

/-! ### The step against a raw state process -/

end LevyStochCalc.Ito.Picard


