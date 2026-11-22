-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F000
-- name    : LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:14:42.303056+00:00
-- url     : https://prove2.me/theorems/90ee3429-521f-497d-9a05-0d81b385695b
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaFiniteActivityJumpSide
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaFiniteActivityJumpSide. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump side of the finite-activity Itô–Lévy formula

Capping the arrival times of a mark set at the horizon leaves an increasing chain of stopping
times starting at the origin, and strictly between two consecutive capped arrival times the
accumulated jumps are constant, so the jump path is its continuous part translated by them. The
jump sum of the telescope over that chain is therefore the sum, over the strictly monotone
enumeration of the window's atom times, of the increments of the state function across the jumps,
read at the left limits of the path, both for the state coordinates themselves and after
prepending coordinates to them.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section CappedChain

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (A : Set E)

/-- The `k`-th arrival time of a mark set capped at the horizon. -/
noncomputable def cappedJumpTime (T : ℝ) (k : ℕ) (ω : Ω) : WithTop ℝ :=
  min (LevyStochCalc.Poisson.jumpTime N A k ω) ((T : ℝ) : WithTop ℝ)
/-- The capped chain starts at the origin. -/
theorem cappedJumpTime_zero {T : ℝ} (hT : 0 ≤ T) (ω : Ω) :
    cappedJumpTime N A T 0 ω = ((0 : ℝ) : WithTop ℝ) := by
  rw [cappedJumpTime, LevyStochCalc.Poisson.jumpTime_zero, min_eq_left]
  exact_mod_cast hT
/-- The capped chain increases with the index. -/
theorem cappedJumpTime_le_succ (T : ℝ) (k : ℕ) (ω : Ω) :
    cappedJumpTime N A T k ω ≤ cappedJumpTime N A T (k + 1) ω :=
  min_le_min (LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω) le_rfl
/-- The capped chain passes the horizon exactly where the arrival times do. -/
theorem le_cappedJumpTime_iff (T : ℝ) (m : ℕ) (ω : Ω) :
    ((T : ℝ) : WithTop ℝ) ≤ cappedJumpTime N A T m ω
      ↔ ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω := by
  simp [cappedJumpTime]
/-- Clipping at the horizon does not distinguish the capped chain from the arrival times. -/
theorem clipTime_cappedJumpTime (T : ℝ) (k : ℕ) (ω : Ω) :
    LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T k) T ω
      = LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Poisson.jumpTime N A k) T ω := by
  simp only [LevyStochCalc.Brownian.Ito.clipTime, cappedJumpTime]
  by_cases h : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω
  · simp only [min_eq_right h, if_pos le_rfl, if_pos h]
  · simp only [min_eq_left (le_of_lt (not_le.mp h)), if_neg h]
/-- **The chain data of the capped arrival times.** For a filtration whose time-zero
`σ`-algebra contains the `P`-null sets and a mark set of finite intensity, the arrival times
capped at the horizon are stopping times, they increase with the index, and the zeroth is the
origin. -/
theorem cappedJumpTime_chain_of_complete {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {T : ℝ} (hT : 0 ≤ T) :
    (∀ k : ℕ, MeasureTheory.IsStoppingTime ℱ (cappedJumpTime N A T k))
      ∧ (∀ (k : ℕ) (ω : Ω), cappedJumpTime N A T k ω ≤ cappedJumpTime N A T (k + 1) ω)
      ∧ ∀ ω : Ω, cappedJumpTime N A T 0 ω = ((0 : ℝ) : WithTop ℝ) :=
  ⟨fun k =>
      (_root_.Prove2MeSourceProof.h_fd667ca169170e4cdeb4bb71 N A hℱ hA hAν hnull k).min_const T,
    cappedJumpTime_le_succ N A T, cappedJumpTime_zero N A hT⟩
variable {N A}

end CappedChain

section JumpSideAssembly

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

end JumpSideAssembly

section MarkIdentificationAe

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

end MarkIdentificationAe

end LevyStochCalc.Ito.JumpFormula


