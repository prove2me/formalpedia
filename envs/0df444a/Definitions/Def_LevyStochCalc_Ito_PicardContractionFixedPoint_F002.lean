-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F002
-- name    : LevyStochCalc_Ito_PicardContractionFixedPoint_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:54:44.940483+00:00
-- url     : https://prove2.me/theorems/164da875-be1b-449d-be3a-d39aef0093a7
-- title:
--   LevyStochCalc source module: LevyStochCalc.Ito.PicardContractionFixedPoint
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Ito.PicardContractionFixedPoint in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F002
import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F004
import Definitions.Def_SourceProof_e264a15a5a2a191954307942
import Definitions.Def_SourceProof_e805995843faefc4a60dd4be
import Definitions.Def_SourceProof_eb0e2237c948399f92e4f8c8

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

omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg hLip in
/-- A path map vanishing almost surely at every time of the window has zero Bielecki norm. -/
theorem bieleckiNorm_eq_zero_of_ae (β T : ℝ) {Z : ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i, Z t ω i = 0) :
    bieleckiNorm (P := P) β T Z = 0 := by
  refine le_antisymm (iSup₂_le fun t ht => ?_) zero_le
  have hz : (fun ω => ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2) =ᵐ[P] 0 := by
    filter_upwards [h t ht] with ω hω
    simp [hω]
  rw [lintegral_congr_ae hz]
  simp
omit [ℱ'.IsRightContinuous] in
/-- **The Picard step respects almost sure equality of its input.** -/
theorem picardStepOnRawStop_congr_ae
    {Z₁ : ℝ → Ω → (Fin n → ℝ)} (h₁m : Measurable (Function.uncurry Z₁))
    (h₁a : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₁ s ω i)
    (h₁b : bieleckiNorm (P := P) 0 T Z₁ < ⊤)
    {Z₂ : ℝ → Ω → (Fin n → ℝ)} (h₂m : Measurable (Function.uncurry Z₂))
    (h₂a : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₂ s ω i)
    (h₂b : bieleckiNorm (P := P) 0 T Z₂ < ⊤)
    (heq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i, Z₁ t ω i = Z₂ t ω i)
    {β : ℝ} (hβ : 0 < β) (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i,
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ t ω i
        = picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ t ω i := by
  have hin : bieleckiNorm (P := P) β T (fun u ω i => Z₁ u ω i - Z₂ u ω i) = 0 := by
    refine bieleckiNorm_eq_zero_of_ae (P := P) β T fun u hu => ?_
    filter_upwards [heq u hu] with ω hω i
    rw [hω i, sub_self]
  have hout : bieleckiNorm (P := P) β T (fun u ω i =>
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ u ω i
        - picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ u ω i) = 0 := by
    refine le_antisymm ?_ zero_le
    refine le_trans (_root_.Prove2MeSourceProof.h_e805995843faefc4a60dd4be W N ℱ' hℱW hℱN coeffs hReg hLip
      x₀ h₁m h₁a h₁b h₂m h₂a h₂b hβ hT) ?_
    rw [hin, mul_zero]
  have hslice : ∀ (u : ℝ) (i : Fin n), Measurable fun ω =>
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ u ω i
        - picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ u ω i :=
    fun u i => (_root_.Prove2MeSourceProof.h_e264a15a5a2a191954307942 W N ℱ' hℱW hℱN coeffs hReg hLip x₀
      h₁m h₁a h₁b hT.le u i).sub
      (_root_.Prove2MeSourceProof.h_e264a15a5a2a191954307942 W N ℱ' hℱW hℱN coeffs hReg hLip x₀
        h₂m h₂a h₂b hT.le u i)
  filter_upwards [_root_.Prove2MeSourceProof.h_eb0e2237c948399f92e4f8c8 (P := P) hslice hout ht] with ω hω i
  exact sub_eq_zero.mp (hω i)
/-! ### The fixed point solves its own Picard equation -/

end LevyStochCalc.Ito.Picard


