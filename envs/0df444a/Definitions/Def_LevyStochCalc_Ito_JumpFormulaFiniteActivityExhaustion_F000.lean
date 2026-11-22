-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F000
-- name    : LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:02:31.546871+00:00
-- url     : https://prove2.me/theorems/8eadf749-3a08-40e2-a7be-ec91676d1844
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaFiniteActivityExhaustion
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaFiniteActivityExhaustion. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityDrift_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exhausting a finite-activity jump path by its arrival times

The jumps of a mark set accumulated up to the arrival times capped at the horizon no longer move
once the arrival time has passed the horizon, so a telescope over a chain of arrival times has
only in-window terms, and the in-window members of such a chain are matched one for one with the
entries of the strictly monotone enumeration of the window's atom times. On a mark set of finite
intensity almost every path has an arrival time beyond the horizon, so an identity holding almost
everywhere on each event where the chain has passed the horizon holds almost everywhere. Between
consecutive arrival times inside the window the accumulated jumps gain exactly the jump
coefficient carried by the later arrival time and the mark enumerated with it, and the progressive
measurability of the chain data and of the integrands passes to the right-continuous
regularisation of a filtration.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section CappedShift

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The jumps of a mark set accumulated up to the `k`-th arrival time capped at the horizon. -/
noncomputable def cappedJumpSum (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀)
    (A : Set E) (T : ℝ) (k : ℕ) (ω : Ω) : Fin n → ℝ :=
  LevyStochCalc.Ito.JumpSplitting.jumpSum X A
    (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Poisson.jumpTime N A k) T ω) ω
variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) (A : Set E)

/-- The capped jump sum at the zeroth arrival time vanishes. -/
theorem cappedJumpSum_zero {T : ℝ} (hT : 0 ≤ T) (ω : Ω) : cappedJumpSum X A T 0 ω = 0 := by
  funext i
  rw [cappedJumpSum,
    LevyStochCalc.Brownian.Ito.clipTime_eq_zero hT (LevyStochCalc.Poisson.jumpTime_zero N A ω),
    LevyStochCalc.Ito.JumpSplitting.jumpSum_zero]
  rfl
/-- Past the horizon the capped jump sum is the jump sum over the whole window. -/
theorem cappedJumpSum_of_le {T : ℝ} {k : ℕ} {ω : Ω}
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    cappedJumpSum X A T k ω = LevyStochCalc.Ito.JumpSplitting.jumpSum X A T ω := by
  rw [cappedJumpSum, LevyStochCalc.Brownian.Ito.clipTime_of_le hk]
/-- Past the horizon the capped jump sum no longer moves with the index. -/
theorem cappedJumpSum_succ_eq {T : ℝ} {k : ℕ} {ω : Ω}
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    cappedJumpSum X A T (k + 1) ω = cappedJumpSum X A T k ω := by
  rw [cappedJumpSum_of_le X A hk,
    cappedJumpSum_of_le X A
      (hk.trans (LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω))]
/-- Past the horizon the telescope's jump term vanishes. -/
theorem jumpTerm_eq_zero_of_le {T : ℝ} {k : ℕ} {ω : Ω} (f : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ)
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    f (y + cappedJumpSum X A T (k + 1) ω) - f (y + cappedJumpSum X A T k ω) = 0 := by
  rw [cappedJumpSum_succ_eq X A hk, sub_self]
/-- The chain of capped shifts reaches the whole jump sum at any index whose arrival time has
passed the horizon, so a path that splits at the horizon is the translated Itô path there. -/
theorem eq_add_cappedJumpSum_of_le {T : ℝ} {m : ℕ} {ω : Ω} {V : ℝ → Ω → Fin n → ℝ}
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω)
    (hsplit : ∀ i : Fin n, X.X T ω i
      = V T ω i + LevyStochCalc.Ito.JumpSplitting.jumpSum X A T ω i) (i : Fin n) :
    V T ω i + cappedJumpSum X A T m ω i = X.X T ω i := by
  rw [cappedJumpSum_of_le X A hm, hsplit i]
/-- Past the horizon index the telescope's jump sum no longer grows with the range. -/
theorem sum_range_jumpTerm_eq_of_le (f : (Fin n → ℝ) → ℝ) (Y : ℕ → Fin n → ℝ)
    {T : ℝ} {ω : Ω} {m m' : ℕ} (hmm : m ≤ m')
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω) :
    (∑ k ∈ Finset.range m', (f (Y k + cappedJumpSum X A T (k + 1) ω)
          - f (Y k + cappedJumpSum X A T k ω)))
      = ∑ k ∈ Finset.range m, (f (Y k + cappedJumpSum X A T (k + 1) ω)
          - f (Y k + cappedJumpSum X A T k ω)) := by
  refine (Finset.sum_subset (fun x hx => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hx) hmm)) fun k _ hk => ?_).symm
  have hmk : m ≤ k := not_lt.mp fun hc => hk (Finset.mem_range.mpr hc)
  exact jumpTerm_eq_zero_of_le X A f (Y k)
    (hm.trans (LevyStochCalc.Poisson.jumpTime_mono N A hmk ω))
end CappedShift

section Reindex

/-- **Reindexing the in-window arrival indices by the atom enumeration.** For a chain of times
starting at the origin, increasing with the index, strictly increasing at every index whose
successor lies inside the window, and passing the horizon at index `m`, a choice of atom index
carrying each in-window arrival time matches the in-window indices below `m` with the entries of
the strictly monotone enumeration of the window's atom times. -/
theorem sum_range_ite_eq_sum_atomEnum {K m : ℕ} {θ : Fin K → ℝ} {σ : ℕ → WithTop ℝ} {T : ℝ}
    (hθ : StrictMono θ) (hmemθ : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T)
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, σ i = ((v : ℝ) : WithTop ℝ) ∧ 0 < v ∧ v ≤ T})
    (hσmono : Monotone σ) (hσ0 : σ 0 = ((0 : ℝ) : WithTop ℝ))
    (hstrict : ∀ i : ℕ, σ (i + 1) ≤ ((T : ℝ) : WithTop ℝ) → σ i < σ (i + 1))
    (hm : ((T : ℝ) : WithTop ℝ) ≤ σ m) (idx : ℕ → Fin K)
    (hidx : ∀ k : ℕ, σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) →
      σ (k + 1) = ((θ (idx k) : ℝ) : WithTop ℝ)) (G : Fin K → ℝ) :
    (∑ k ∈ Finset.range m,
        if σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) then G (idx k) else 0)
      = ∑ j : Fin K, G j := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun k _ => idx k) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro a₁ ha₁ a₂ ha₂ hidxeq
    have hp₁ : σ (a₁ + 1) ≤ ((T : ℝ) : WithTop ℝ) := (Finset.mem_filter.mp ha₁).2
    have hp₂ : σ (a₂ + 1) ≤ ((T : ℝ) : WithTop ℝ) := (Finset.mem_filter.mp ha₂).2
    have heq : σ (a₁ + 1) = σ (a₂ + 1) := by
      rw [hidx a₁ hp₁, hidx a₂ hp₂, hidxeq]
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd heq
        (ne_of_lt (lt_of_le_of_lt (hσmono (Nat.succ_le_of_lt hlt)) (hstrict a₂ hp₂)))
    · exact absurd heq.symm
        (ne_of_lt (lt_of_le_of_lt (hσmono (Nat.succ_le_of_lt hlt)) (hstrict a₁ hp₁)))
  · intro j _
    have hmemj : θ j ∈ Set.range θ := Set.mem_range_self j
    rw [hrange] at hmemj
    obtain ⟨i, hi, hpos, -⟩ := hmemj
    have hi0 : i ≠ 0 := by
      intro hc
      rw [hc, hσ0] at hi
      exact absurd (by exact_mod_cast hi.symm : (θ j : ℝ) = 0) (ne_of_gt hpos)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    subst hk
    have hpk : σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) := by
      rw [hi]
      exact_mod_cast (hmemθ j).2
    have hkm : k < m := by
      by_contra hc
      have hmk : m ≤ k := not_lt.mp hc
      exact absurd (lt_of_lt_of_le (hstrict k hpk) (hpk.trans (hm.trans (hσmono hmk))))
        (lt_irrefl _)
    have hjeq : idx k = j := by
      have : ((θ (idx k) : ℝ) : WithTop ℝ) = ((θ j : ℝ) : WithTop ℝ) := by
        rw [← hidx k hpk, hi]
      exact hθ.injective (by exact_mod_cast this)
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkm, hpk⟩, hjeq⟩
  · intro _ _
    rfl
end Reindex

section RightContinuous

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end RightContinuous

section Exhaustion

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (A : Set E)

end Exhaustion

section MarkIdentification

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

end MarkIdentification

end LevyStochCalc.Ito.JumpFormula


