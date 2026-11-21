-- Prove2me | Definitions.Def_SourceProof_7ac7f2227657b4f9e275e978
-- name    : SourceProof_7ac7f2227657b4f9e275e978
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:01:28.586556+00:00
-- url     : https://prove2.me/theorems/1f3e24b7-06ff-4c52-8970-e42d14421c91
-- title:
--   LevyStochCalc source module: SourceProof_7ac7f2227657b4f9e275e978
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnRawStop_picardLimit_eq_zero` comes from the `LevyStochCalc.Ito.PicardContractionFixedPoint` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_34982f0b1ca1f7510c2d1e94
import Definitions.Def_SourceProof_c28516e04cb432d3ac50eea0
import Definitions.Def_SourceProof_e264a15a5a2a191954307942

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


theorem _root_.Prove2MeSourceProof.h_7ac7f2227657b4f9e275e978 {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip
            (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
            (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
              x₀ hT X₀)
            (_root_.Prove2MeSourceProof.h_34982f0b1ca1f7510c2d1e94 W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
              hβ hT X₀ hq)
            hT.le x₀ t ω i
          - picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ t ω i) = 0 := by
  set q := (ENNReal.ofReal
      ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
        / (2 * β))) ^ ((1 : ℝ) / 2) with hqdef
  set Y := LevyStochCalc.Ito.Picard.picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ with hYdef
  have hYm := LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hYa := LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
    x₀ hT X₀
  have hYb := _root_.Prove2MeSourceProof.h_34982f0b1ca1f7510c2d1e94 W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
    hβ hT X₀ hq
  set Φ := LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hYm hYa hYb hT.le x₀ with hΦdef
  set D := (1 - q)⁻¹ * LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i =>
      (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
        - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X t ω i)
    with hDdef
  have hDfin : D ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hq).ne')
      (_root_.Prove2MeSourceProof.h_65bedb6096fb4f69009cb5ba ℱ' hβ.le _ _).ne
  have hiter := fun k => LevyStochCalc.Ito.Picard.bieleckiNorm_picardIter_sub_bieleckiLimit_le W N ℱ' hℱW hℱN hℱ0 hnull
    coeffs hReg hLip x₀ hβ hT X₀ hq k
  have hbound : ∀ k : ℕ, LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => Φ t ω i - Y t ω i)
      ≤ q ^ (k + 1) * D + q ^ (k + 1) * D := by
    intro k
    have hXm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω =>
        (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i :=
      fun t i => LevyStochCalc.Ito.Picard.measurable_slice_of_uncurry
        (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
          (k + 1)).measurable_path t i
    have hΦm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Φ t ω i := fun t i =>
      _root_.Prove2MeSourceProof.h_e264a15a5a2a191954307942 W N ℱ' hℱW hℱN coeffs hReg hLip x₀
        hYm hYa hYb hT.le t i
    have hYsl : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Y t ω i :=
      fun t i => LevyStochCalc.Ito.Picard.measurable_slice_of_uncurry hYm t i
    have hEq : (fun t ω i => Φ t ω i - Y t ω i)
        = fun t (ω : Ω) =>
          (fun i => Φ t ω i
            - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
          + fun i =>
            (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i
              - Y t ω i := by
      funext t ω i
      simp [Pi.add_apply, sub_add_sub_cancel]
    have hadd := _root_.Prove2MeSourceProof.h_1a604e3d857ca06f911ef6c7 (P := P) β T
      (fun t ω => fun i => Φ t ω i
        - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
      (fun t ω => fun i =>
        (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i
          - Y t ω i)
      (LevyStochCalc.Ito.Picard.bieleckiNorm_inner_aemeasurable_of_slice fun t i => (hΦm t i).sub (hXm t i))
      (LevyStochCalc.Ito.Picard.bieleckiNorm_inner_aemeasurable_of_slice fun t i => (hXm t i).sub (hYsl t i))
    have hcongr : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => Φ t ω i
          - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
        = LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i =>
            LevyStochCalc.Ito.Picard.picardStepOnStop W N hℱW hℱN coeffs hReg hLip
              (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k) hT.le x₀ t ω i
              - Φ t ω i) := by
      rw [LevyStochCalc.Ito.Picard.bieleckiNorm_sub_comm (P := P) β T]
      refine LevyStochCalc.Ito.Picard.bieleckiNorm_congr_ae (P := P) β T fun t => ?_
      filter_upwards [_root_.Prove2MeSourceProof.h_6c43802417fce8ac3ae3997a W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
        (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k) t] with ω hω
      funext i
      have hunfold : (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
            (k + 1)).X t ω
          = (LevyStochCalc.Ito.Picard.picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
              (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k)).X t ω := rfl
      rw [hunfold, hω]
    have hfirst : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => Φ t ω i
          - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
        ≤ q ^ (k + 1) * D := by
      rw [hcongr]
      refine le_trans (_root_.Prove2MeSourceProof.h_c28516e04cb432d3ac50eea0 W N ℱ' hℱW hℱN
        coeffs hReg hLip hYm hYa hYb x₀ hβ hT _) ?_
      refine le_trans (mul_le_mul' le_rfl (hiter k)) (le_of_eq ?_)
      rw [← mul_assoc, ← pow_succ']
    rw [hEq]
    exact hadd.trans (add_le_add hfirst (hiter (k + 1)))
  have htend : Filter.Tendsto (fun k : ℕ => q ^ (k + 1) * D + q ^ (k + 1) * D)
      Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun k : ℕ => q ^ (k + 1)) Filter.atTop (nhds 0) :=
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq).comp (Filter.tendsto_add_atTop_nat 1)
    have hm : Filter.Tendsto (fun k : ℕ => q ^ (k + 1) * D) Filter.atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.mul_const hp (Or.inr hDfin)
    simpa using hm.add hm
  exact le_antisymm (ge_of_tendsto' htend hbound) zero_le
/-! ### The step respects almost sure equality of its input -/

/-! ### The fixed point solves its own Picard equation -/

end LevyStochCalc.Ito.Picard


