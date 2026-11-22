-- Prove2me | Definitions.Def_SourceProof_0d088112759d60f13f10d2df
-- name    : SourceProof_0d088112759d60f13f10d2df
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:17:00.492896+00:00
-- url     : https://prove2.me/theorems/9fd55500-8518-476b-b7b6-da4715bd6f99
-- title:
--   LevyStochCalc source module: SourceProof_0d088112759d60f13f10d2df
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.sum_range_jumpTerm_eq_sum_atomEnum_of_shift` comes from the `LevyStochCalc.Ito.JumpFormulaFiniteActivityJumpSide` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F000
import Definitions.Def_SourceProof_379e72f3a97bdebd31826097

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


theorem _root_.Prove2MeSourceProof.h_0d088112759d60f13f10d2df {N' : ℕ} (f : (Fin N' → ℝ) → ℝ)
    {V Y : ℝ → Ω → Fin N' → ℝ} {c : ℕ → Ω → Fin N' → ℝ} {jump : Fin K → Fin N' → ℝ} {m : ℕ}
    (hmonoθ : StrictMono θ) (hmemθ : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T)
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    (hV : Continuous fun t => V t ω)
    (hstrict : ∀ i : ℕ, LevyStochCalc.Poisson.jumpTime N A (i + 1) ω ≤ ((T : ℝ) : WithTop ℝ) →
      LevyStochCalc.Poisson.jumpTime N A i ω < LevyStochCalc.Poisson.jumpTime N A (i + 1) ω)
    (hshift : ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω → V s ω + c k ω = Y s ω)
    (hczero : ∀ k : ℕ, ((T : ℝ) : WithTop ℝ) < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω →
      c (k + 1) ω = c k ω)
    (hcinc : ∀ k : ℕ, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ) →
      ∃ j : Fin K, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω = ((θ j : ℝ) : WithTop ℝ)
        ∧ c (k + 1) ω = c k ω + jump j)
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω) :
    (∑ k ∈ Finset.range m,
        (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + c (k + 1) ω)
          - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + c k ω)))
      = ∑ j : Fin K, (f (Function.leftLim (fun s => Y s ω) (θ j) + jump j)
          - f (Function.leftLim (fun s => Y s ω) (θ j))) := by
  classical
  have hrw : (∑ k ∈ Finset.range m,
        (f (V (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Ito.JumpFormula.cappedJumpTime N A T (k + 1)) T ω) ω
              + c (k + 1) ω)
          - f (V (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Ito.JumpFormula.cappedJumpTime N A T (k + 1)) T ω) ω
              + c k ω)))
      = ∑ k ∈ Finset.range m,
        (if LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ) then
          f (V (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Ito.JumpFormula.cappedJumpTime N A T (k + 1)) T ω) ω
              + c (k + 1) ω)
            - f (V (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Ito.JumpFormula.cappedJumpTime N A T (k + 1)) T ω) ω
                + c k ω)
          else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ)
    · rw [if_pos hp]
    · rw [if_neg hp, hczero k (not_le.mp hp), sub_self]
  rw [hrw]
  refine _root_.Prove2MeSourceProof.h_379e72f3a97bdebd31826097 hmonoθ hmemθ hrange
    (fun i j hij => LevyStochCalc.Poisson.jumpTime_mono N A hij ω)
    (LevyStochCalc.Poisson.jumpTime_zero N A ω) hstrict hm _ _ ?_
  · intro k hp
    obtain ⟨j, hj, hinc⟩ := hcinc k hp
    refine ⟨j, hj, ?_⟩
    have hkle : LevyStochCalc.Poisson.jumpTime N A k ω ≤ ((T : ℝ) : WithTop ℝ) :=
      le_of_lt (lt_of_lt_of_le (hstrict k hp) hp)
    have hcap1 : LevyStochCalc.Ito.JumpFormula.cappedJumpTime N A T (k + 1) ω = ((θ j : ℝ) : WithTop ℝ) := by
      rw [LevyStochCalc.Ito.JumpFormula.cappedJumpTime, min_eq_left hp, hj]
    have hltcap : LevyStochCalc.Ito.JumpFormula.cappedJumpTime N A T k ω < LevyStochCalc.Ito.JumpFormula.cappedJumpTime N A T (k + 1) ω := by
      simp only [LevyStochCalc.Ito.JumpFormula.cappedJumpTime, min_eq_left hkle, min_eq_left hp]
      exact hstrict k hp
    have hsub : c (k + 1) ω - c k ω = jump j := by
      rw [hinc]
      abel
    rw [LevyStochCalc.Brownian.Ito.jumpTerm_eq_leftLim_increment f hV hcap1 (hmemθ j).2
      hltcap (fun s h1 h2 => hshift k s h1 h2), hsub]
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


