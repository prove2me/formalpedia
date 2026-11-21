-- Prove2me | Definitions.Def_SourceProof_eb0e2237c948399f92e4f8c8
-- name    : SourceProof_eb0e2237c948399f92e4f8c8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:50:59.54105+00:00
-- url     : https://prove2.me/theorems/341229c1-3099-447a-b11d-190aee306ab8
-- title:
--   LevyStochCalc source module: SourceProof_eb0e2237c948399f92e4f8c8
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.ae_eq_zero_of_bieleckiNorm_eq_zero` comes from the `LevyStochCalc.Ito.PicardContractionFixedPoint` module. The staged Lean declaration includes its source proof and dependency references.
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

omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg hLip in

theorem _root_.Prove2MeSourceProof.h_eb0e2237c948399f92e4f8c8 {β T : ℝ} {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZs : ∀ (u : ℝ) (i : Fin n), Measurable fun ω => Z u ω i)
    (h : bieleckiNorm (P := P) β T Z = 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i, Z t ω i = 0 := by
  have hterm : ENNReal.ofReal (Real.exp (-β * t))
      * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← h]
    exact le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-β * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) t ht
  have hexp : ENNReal.ofReal (Real.exp (-β * t)) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, Real.exp_pos]
  have hrpow : (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) = 0 :=
    (mul_eq_zero.mp hterm).resolve_left hexp
  have hint : ∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := by
    rcases ENNReal.rpow_eq_zero_iff.mp hrpow with ⟨h0, _⟩ | ⟨_, hneg⟩
    · exact h0
    · exact absurd hneg (by norm_num)
  have hmeas : AEMeasurable (fun ω => ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2) P :=
    (Finset.measurable_sum _ fun i _ =>
      (ENNReal.continuous_coe.measurable.comp (hZs t i).nnnorm).pow_const 2).aemeasurable
  filter_upwards [(lintegral_eq_zero_iff' hmeas).mp hint] with ω hω i
  have hle : (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 = 0 :=
    le_antisymm (le_of_le_of_eq (Finset.single_le_sum
      (f := fun j => (‖Z t ω j‖₊ : ℝ≥0∞) ^ 2) (fun _ _ => zero_le) (Finset.mem_univ i)) hω)
      zero_le
  simpa using hle
/-! ### The step respects almost sure equality of its input -/

/-! ### The fixed point solves its own Picard equation -/

end LevyStochCalc.Ito.Picard


