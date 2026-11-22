-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F001
-- name    : LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:27:04.296411+00:00
-- url     : https://prove2.me/theorems/11913778-0851-448c-8247-7ec72e0d91ea
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaFiniteActivityJumpSide
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaFiniteActivityJumpSide. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F000
import Definitions.Def_SourceProof_379e72f3a97bdebd31826097
import Definitions.Def_SourceProof_598b50a90c7d4fa56597dde2
import Definitions.Def_SourceProof_aa14aa5b3b0793b432551cdc
import Definitions.Def_SourceProof_b6c4ec76c2b6be6bc88b92d3

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

/-- **The piecewise translation between consecutive capped arrival times.** Strictly between
consecutive capped arrival times the jump path is the continuous part translated by the capped
jump sum. -/
theorem ae_forall_add_cappedJumpSum_eq
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    {X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀} {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + LevyStochCalc.Ito.JumpSplitting.jumpSum X A t ω i)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSum X A T k ω = X.X s ω :=
  _root_.Prove2MeSourceProof.h_b6c4ec76c2b6be6bc88b92d3 hsplit
    (cappedJumpTime_zero N A hT) (cappedJumpTime_le_succ N A T)
    (_root_.Prove2MeSourceProof.h_aa14aa5b3b0793b432551cdc X hA hAν T)
end CappedChain

section JumpSideAssembly

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

/-- Past the horizon the capped jump sum does not move across an index. -/
theorem cappedJumpSum_succ_eq_of_horizon_lt (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    {k : ℕ} (hk : ((T : ℝ) : WithTop ℝ) < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω) :
    cappedJumpSum X A T (k + 1) ω = cappedJumpSum X A T k ω := by
  classical
  have h1 : cappedJumpSum X A T (k + 1) ω
      = LevyStochCalc.Ito.JumpSplitting.jumpSum X A T ω := cappedJumpSum_of_le X A hk.le
  by_cases hkT : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω
  · rw [h1, cappedJumpSum_of_le X A hkT]
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp
      (lt_trans (not_le.mp hkT) (WithTop.coe_lt_top T)).ne
    have hqT : q < T := by
      have hlt := not_le.mp hkT
      rw [← hq] at hlt
      exact_mod_cast hlt
    have h2 : cappedJumpSum X A T k ω
        = LevyStochCalc.Ito.JumpSplitting.jumpSum X A q ω := by
      rw [cappedJumpSum, LevyStochCalc.Brownian.Ito.clipTime_eq_min hq.symm,
        min_eq_right (le_of_lt hqT)]
    rw [h1, h2]
    funext i
    rw [_root_.Prove2MeSourceProof.h_1ccbf94d189a78e3d3f14cc3 X hA hmem hsum le_rfl i,
      _root_.Prove2MeSourceProof.h_1ccbf94d189a78e3d3f14cc3 X hA hmem hsum (le_of_lt hqT) i]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hjq : θ j ≤ q := by
      have hmemj : θ j ∈ Set.range θ := Set.mem_range_self j
      rw [hrange] at hmemj
      obtain ⟨i', hi', -, hjT⟩ := hmemj
      rcases le_or_gt i' k with hik | hik
      · have hle := LevyStochCalc.Poisson.jumpTime_mono N A hik ω
        rw [hi', ← hq] at hle
        exact_mod_cast hle
      · have hge := LevyStochCalc.Poisson.jumpTime_mono N A (Nat.succ_le_of_lt hik) ω
        rw [hi'] at hge
        exact absurd (lt_of_lt_of_le hk hge) (not_lt.mpr (by exact_mod_cast hjT))
    rw [if_pos (hmem j).1.2, if_pos hjq]
/-- **The telescope's jump sum is the atom sum of the increments of the state function across
the jumps.** Each in-window index contributes the increment of the state function at the left
limit of the path, and the indices past the horizon contribute nothing. -/
theorem sum_range_jumpTerm_eq_sum_atomEnum (f : (Fin n → ℝ) → ℝ)
    {V : ℝ → Ω → Fin n → ℝ} {m : ℕ} (hA : MeasurableSet A) (hmonoθ : StrictMono θ)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    (hV : Continuous fun t => V t ω)
    (hstrict : ∀ i : ℕ, LevyStochCalc.Poisson.jumpTime N A (i + 1) ω ≤ ((T : ℝ) : WithTop ℝ) →
      LevyStochCalc.Poisson.jumpTime N A i ω < LevyStochCalc.Poisson.jumpTime N A (i + 1) ω)
    (hshift : ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSum X A T k ω = X.X s ω)
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω) :
    (∑ k ∈ Finset.range m,
        (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSum X A T (k + 1) ω)
          - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSum X A T k ω)))
      = ∑ j : Fin K, (f (Function.leftLim (fun s => X.X s ω) (θ j)
            + coeffs.γ (θ j) (X.X (θ j) ω) (ε j))
          - f (Function.leftLim (fun s => X.X s ω) (θ j))) := by
  classical
  have hrw : (∑ k ∈ Finset.range m,
        (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSum X A T (k + 1) ω)
          - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSum X A T k ω)))
      = ∑ k ∈ Finset.range m,
        (if LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ) then
          f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSum X A T (k + 1) ω)
            - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                + cappedJumpSum X A T k ω)
          else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ)
    · rw [if_pos hp]
    · rw [if_neg hp,
        cappedJumpSum_succ_eq_of_horizon_lt X hA hmem hsum hrange (not_le.mp hp), sub_self]
  rw [hrw]
  refine _root_.Prove2MeSourceProof.h_379e72f3a97bdebd31826097 hmonoθ (fun j => (hmem j).1) hrange
    (fun i j hij => LevyStochCalc.Poisson.jumpTime_mono N A hij ω)
    (LevyStochCalc.Poisson.jumpTime_zero N A ω) hstrict hm _ _ ?_
  intro k hp
  obtain ⟨j, hj, hinc⟩ := _root_.Prove2MeSourceProof.h_598b50a90c7d4fa56597dde2 X hA hmem hsum hmonoθ.injective
    hrange (hstrict k hp) hp
  refine ⟨j, hj, ?_⟩
  have hkle : LevyStochCalc.Poisson.jumpTime N A k ω ≤ ((T : ℝ) : WithTop ℝ) :=
    le_of_lt (lt_of_lt_of_le (hstrict k hp) hp)
  have hcap1 : cappedJumpTime N A T (k + 1) ω = ((θ j : ℝ) : WithTop ℝ) := by
    rw [cappedJumpTime, min_eq_left hp, hj]
  have hltcap : cappedJumpTime N A T k ω < cappedJumpTime N A T (k + 1) ω := by
    simp only [cappedJumpTime, min_eq_left hkle, min_eq_left hp]
    exact hstrict k hp
  have hsub : cappedJumpSum X A T (k + 1) ω - cappedJumpSum X A T k ω
      = coeffs.γ (θ j) (X.X (θ j) ω) (ε j) := by
    rw [hinc]
    abel
  rw [LevyStochCalc.Brownian.Ito.jumpTerm_eq_leftLim_increment f hV hcap1 (hmem j).1.2
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


