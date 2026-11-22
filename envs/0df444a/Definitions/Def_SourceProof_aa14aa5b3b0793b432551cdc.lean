-- Prove2me | Definitions.Def_SourceProof_aa14aa5b3b0793b432551cdc
-- name    : SourceProof_aa14aa5b3b0793b432551cdc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:19:05.190871+00:00
-- url     : https://prove2.me/theorems/9ad5ba1e-4965-465c-a69e-196e564a162a
-- title:
--   LevyStochCalc source module: SourceProof_aa14aa5b3b0793b432551cdc
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.ae_forall_jumpSum_eq_cappedJumpSum` comes from the `LevyStochCalc.Ito.JumpFormulaFiniteActivityJumpSide` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F000

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


theorem _root_.Prove2MeSourceProof.h_aa14aa5b3b0793b432551cdc
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      ∀ i : Fin n, LevyStochCalc.Ito.JumpSplitting.jumpSum X A s ω i
        = cappedJumpSum X A T k ω i := by
  classical
  filter_upwards [_root_.Prove2MeSourceProof.h_2d73a2b6df3c10b500c2eec5 N A hA hAν T]
    with ω hω
  obtain ⟨K, θ, ε, -, hrange, hmem, hsum⟩ := hω
  intro k s h1 h2 i
  -- Below the horizon the capped time is the arrival time itself.
  have hkT : LevyStochCalc.Poisson.jumpTime N A k ω < ((T : ℝ) : WithTop ℝ) := by
    by_contra hcon
    have hk : LevyStochCalc.Ito.JumpFormula.cappedJumpTime N A T k ω = ((T : ℝ) : WithTop ℝ) :=
      min_eq_right (not_lt.mp hcon)
    have hk1 : LevyStochCalc.Ito.JumpFormula.cappedJumpTime N A T (k + 1) ω = ((T : ℝ) : WithTop ℝ) :=
      min_eq_right ((not_lt.mp hcon).trans
        (LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω))
    rw [hk] at h1
    rw [hk1] at h2
    exact absurd (h1.trans h2) (lt_irrefl _)
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp
    (lt_trans hkT (WithTop.coe_lt_top T)).ne
  have hqT : q < T := by
    have := hkT
    rw [← hq] at this
    exact_mod_cast this
  have hkeq : LevyStochCalc.Ito.JumpFormula.cappedJumpTime N A T k ω = ((q : ℝ) : WithTop ℝ) := by
    rw [LevyStochCalc.Ito.JumpFormula.cappedJumpTime, ← hq, min_eq_left (le_of_lt (by exact_mod_cast hqT))]
  have hqs : q < s := by
    rw [hkeq] at h1
    exact_mod_cast h1
  have hsucc : ((s : ℝ) : WithTop ℝ) < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω :=
    lt_of_lt_of_le h2 (min_le_left _ _)
  have hsT : s ≤ T := by
    have := lt_of_lt_of_le h2 (min_le_right _ _)
    exact le_of_lt (by exact_mod_cast this)
  have hqT' : q ≤ T := le_of_lt hqT
  -- The capped jump sum at index `k` is the jump sum at the arrival time.
  have hcap : LevyStochCalc.Ito.JumpFormula.cappedJumpSum X A T k ω i
      = LevyStochCalc.Ito.JumpSplitting.jumpSum X A q ω i := by
    rw [LevyStochCalc.Ito.JumpFormula.cappedJumpSum, LevyStochCalc.Brownian.Ito.clipTime_eq_min hq.symm,
      min_eq_right hqT']
  -- No enumerated atom time lies in the interval.
  have hkey : ∀ j : Fin K, θ j ≤ s ↔ θ j ≤ q := by
    intro j
    constructor
    · intro hjs
      have hmemj : θ j ∈ Set.range θ := Set.mem_range_self j
      rw [hrange] at hmemj
      obtain ⟨i', hi', -, -⟩ := hmemj
      rcases le_or_gt i' k with hik | hik
      · have := LevyStochCalc.Poisson.jumpTime_mono N A hik ω
        rw [hi', ← hq] at this
        exact_mod_cast this
      · have := LevyStochCalc.Poisson.jumpTime_mono N A (Nat.succ_le_of_lt hik) ω
        rw [hi'] at this
        exact absurd (lt_of_lt_of_le hsucc this) (not_lt.mpr (by exact_mod_cast hjs))
    · intro hjq
      exact le_of_lt (lt_of_le_of_lt hjq hqs)
  rw [hcap, _root_.Prove2MeSourceProof.h_1ccbf94d189a78e3d3f14cc3 X hA hmem hsum hsT i,
    _root_.Prove2MeSourceProof.h_1ccbf94d189a78e3d3f14cc3 X hA hmem hsum hqT' i]
  exact Finset.sum_congr rfl fun j _ => by
    by_cases hj : θ j ≤ s
    · rw [if_pos hj, if_pos ((hkey j).mp hj)]
    · rw [if_neg hj, if_neg (fun hc => hj ((hkey j).mpr hc))]
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


