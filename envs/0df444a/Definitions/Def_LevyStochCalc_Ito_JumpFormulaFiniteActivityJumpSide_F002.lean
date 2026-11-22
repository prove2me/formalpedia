-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F002
-- name    : LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:31:06.183531+00:00
-- url     : https://prove2.me/theorems/521af31b-cfcb-4ad8-9c0d-59ad5e648bf7
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaFiniteActivityJumpSide
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaFiniteActivityJumpSide. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F001
import Definitions.Def_SourceProof_3b4c8aaeb3983333d32ff10f

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

end JumpSideAssembly

section MarkIdentificationAe

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- **The atoms of the window carry the increments of the capped jump sum.** Almost surely the
window of finite intensity carries a strictly increasing enumeration of its atoms which computes
every integral over the window, whose values sum to the jump sum over the window, and along
which the capped jump sum gains, between consecutive arrival times inside the window, exactly
the jump coefficient evaluated at the later arrival time and its mark. -/
theorem ae_exists_atomEnum_cappedJumpSum_succ
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      LevyStochCalc.Ito.JumpSplitting.jumpSum X A T ω
        = ∑ j : Fin K, coeffs.γ (θ j) (X.X (θ j) ω) (ε j) ∧
      ∀ k : ℕ, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ) →
        ∃ j : Fin K, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω = ((θ j : ℝ) : WithTop ℝ) ∧
          cappedJumpSum X A T (k + 1) ω
            = cappedJumpSum X A T k ω + coeffs.γ (θ j) (X.X (θ j) ω) (ε j) := by
  filter_upwards [_root_.Prove2MeSourceProof.h_2d73a2b6df3c10b500c2eec5 N A hA hAν T,
    _root_.Prove2MeSourceProof.h_3b4c8aaeb3983333d32ff10f N A hA hAν T] with ω hω hstrict
  obtain ⟨K, θ, ε, hmono, hrange, hmem, hsum⟩ := hω
  refine ⟨K, θ, ε, hmono, hmem, hsum,
    jumpSum_eq_sum_atomEnum_horizon X hA hmem hsum, fun k hk => ?_⟩
  exact _root_.Prove2MeSourceProof.h_598b50a90c7d4fa56597dde2 X hA hmem hsum hmono.injective hrange
    (hstrict k hk) hk
/-- **The telescope's jump sum against the atom enumeration, almost surely.** Almost surely the
window carries a strictly increasing enumeration of its atoms computing every integral over the
window, along which the telescope's jump sum over any range past the horizon is the sum of the
increments of the state function across the jumps, read at the left limits of the path. -/
theorem ae_exists_atomEnum_sum_range_jumpTerm (f : (Fin n → ℝ) → ℝ)
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    {V : ℝ → Ω → Fin n → ℝ} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (hV : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ),
      cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSum X A T k ω = X.X s ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E),
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
        (∑ k ∈ Finset.range m,
            (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSum X A T (k + 1) ω)
              - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSum X A T k ω)))
          = ∑ j : Fin K, (f (Function.leftLim (fun s => X.X s ω) (θ j)
                + coeffs.γ (θ j) (X.X (θ j) ω) (ε j))
              - f (Function.leftLim (fun s => X.X s ω) (θ j))) := by
  filter_upwards [_root_.Prove2MeSourceProof.h_2d73a2b6df3c10b500c2eec5 N A hA hAν T,
    _root_.Prove2MeSourceProof.h_3b4c8aaeb3983333d32ff10f N A hA hAν T, hV, hshift]
    with ω hω hstrict hVω hshiftω
  obtain ⟨K, θ, ε, hmonoθ, hrange, hmem, hsum⟩ := hω
  exact ⟨K, θ, ε, hmem, hsum, fun m hm =>
    sum_range_jumpTerm_eq_sum_atomEnum X f hA hmonoθ hmem hsum hrange hVω hstrict hshiftω hm⟩
end MarkIdentificationAe

end LevyStochCalc.Ito.JumpFormula


