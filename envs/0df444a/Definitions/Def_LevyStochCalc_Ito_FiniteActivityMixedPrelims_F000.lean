-- Prove2me | Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F000
-- name    : LevyStochCalc_Ito_FiniteActivityMixedPrelims_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:35:36.343434+00:00
-- url     : https://prove2.me/theorems/b36b4411-f2c5-4b14-bc51-41edc9b26dbb
-- title:
--   Source declarations: LevyStochCalc.Ito.FiniteActivityMixedPrelims
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.FiniteActivityMixedPrelims. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoTimeAug_F001
import Definitions.Def_LevyStochCalc_Ito_CappedJumpSumMeasurable_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaMixedDictionary_F001
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathDecomposition_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathSums_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathSums_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Preliminaries for the finite-activity Itô–Lévy identity in the mixed form

The small facts the finite-activity identity along a truncated path assembles from: the
left-limit jump sum of the mark-cut coefficient bundle is the prescribed-path jump sum along the
left limits; the left limit of the time-augmented path; the value of a progressively measurable
vector process at a stopping time is known at that time; the drift reconciliation for the mixed
integrands asked at almost every time only; and the bounds on the partial derivatives of the
time-augmented representative of a state function with bounded derivatives.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.jumpSumLeftAt_markCutγ_eq_jumpSumAt_leftLimPath`
* `LevyStochCalc.Ito.JumpFormula.leftLim_timeAugProcess_eq_cons`
* `LevyStochCalc.Ito.JumpFormula.measurable_stoppingTime_eval_untopA`
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed_ae`
* `LevyStochCalc.Ito.JumpFormula.abs_coordDeriv_timeAug_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_coordDeriv₂_timeAug_mul_le`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Probability LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section JumpSum

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The left-limit jump sum over a mark set of the coefficient bundle cut to that set is the
prescribed-path jump sum along the left limits of the jump diffusion. -/
theorem jumpSumLeftAt_markCutγ_eq_jumpSumAt_leftLimPath (X : JumpDiffusion W N coeffs x₀)
    {B : Set E} (hB : MeasurableSet B) (t : ℝ) (ω : Ω) (i : Fin n) :
    JumpSplitting.jumpSumLeftAt (coeffs.markCutγ B) N X.X B t ω i
      = jumpSumAt X (JumpSplitting.leftLimPath X) B t ω i := by
  unfold JumpSplitting.jumpSumLeftAt jumpSumAt
  refine setIntegral_congr_fun (measurableSet_Ioc.prod hB) fun q hq => ?_
  rw [JumpDiffusionCoeffs.markCutγ_γ_apply, Set.indicator_of_mem hq.2]
  rfl
/-- The horizon clipped at an arrival time is the capped arrival time read back as a real. -/
theorem clipTime_jumpTime_eq_untopA (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (A : Set E) (T : ℝ) (k : ℕ) (ω : Ω) :
    clipTime (LevyStochCalc.Poisson.jumpTime N A k) T ω = (cappedJumpTime N A T k ω).untopA :=
  clipTime_eq_untopA_min _ _ _
end JumpSum

section LeftLimit

variable {Ω : Type u} {n : ℕ}

/-- The left limit of the time-augmented path is the time consed onto the left limit of the
path, at a time where every coordinate of the path has a left limit. -/
theorem leftLim_timeAugProcess_eq_cons (Z : ℝ → Ω → Fin n → ℝ) {ω : Ω} {t : ℝ}
    (h : ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Z s ω i) (𝓝[<] t) (𝓝 L)) :
    Function.leftLim (fun s => timeAugProcess Z s ω) t
      = Fin.cons t (JumpSplitting.leftLimPathAt Z t ω) := by
  refine leftLim_eq_of_tendsto ?_
  refine tendsto_pi_nhds.mpr fun p => ?_
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugProcess, Fin.cons_zero]
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  | succ q =>
    simp only [timeAugProcess, Fin.cons_succ]
    exact JumpSplitting.tendsto_nhdsLT_leftLimPathAt h q
/-- A path that is right continuous on `[0, ∞)` and has left limits at the positive times
differs from its left limits at countably many positive times only. -/
theorem countable_setOf_pos_leftLimPathAt_ne {Z : ℝ → Ω → Fin n → ℝ} {ω : Ω}
    (hright : ∀ t : ℝ, 0 ≤ t → Tendsto (fun s => Z s ω) (𝓝[>] t) (𝓝 (Z t ω)))
    (hleft : ∀ t : ℝ, 0 < t → ∀ i : Fin n,
      ∃ L : ℝ, Tendsto (fun s => Z s ω i) (𝓝[<] t) (𝓝 L)) :
    {s : ℝ | 0 < s ∧ JumpSplitting.leftLimPathAt Z s ω ≠ Z s ω}.Countable := by
  have h := _root_.Prove2MeSourceProof.h_27ffb6837c072f81fc480f19 (f := fun s => Z s ω)
    (g := fun s => JumpSplitting.leftLimPathAt Z s ω) hright
    (fun t ht i => JumpSplitting.tendsto_nhdsLT_leftLimPathAt (hleft t ht) i)
  refine h.mono fun s hs => ?_
  simp only [Set.mem_setOf_eq] at hs ⊢
  exact ⟨hs.1, fun heq => hs.2 heq.symm⟩
/-- Two processes that meet a pair of processes at all but countably many positive times each
meet them jointly at all but countably many positive times. -/
theorem countable_setOf_pos_ne_pair {α β : Type*} {Y₁ Z₁ : ℝ → Ω → α} {Y₂ Z₂ : ℝ → Ω → β}
    {ω : Ω} (h₁ : {s : ℝ | 0 < s ∧ Y₁ s ω ≠ Z₁ s ω}.Countable)
    (h₂ : {s : ℝ | 0 < s ∧ Y₂ s ω ≠ Z₂ s ω}.Countable) :
    {s : ℝ | 0 < s ∧ (Y₁ s ω, Y₂ s ω) ≠ (Z₁ s ω, Z₂ s ω)}.Countable := by
  refine (h₁.union h₂).mono fun s hs => ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_not] at hcon
  exact hs.2 (Prod.ext (hcon.1 hs.1) (hcon.2 hs.1))
end LeftLimit

section StoppingTime

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {n : ℕ} {ℱ : Filtration ℝ mΩ}

/-- The value of a progressively measurable vector process at a stopping time is measurable for
the σ-algebra of that stopping time. -/
theorem measurable_stoppingTime_eval_untopA {Y : ℝ → Ω → Fin n → ℝ}
    (hY : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
    {σ : Ω → WithTop ℝ} (hσ : IsStoppingTime ℱ σ) :
    Measurable[hσ.measurableSpace] fun ω => Y (σ ω).untopA ω := by
  letI : MeasurableSpace Ω := hσ.measurableSpace
  refine measurable_pi_lambda _ fun i => ?_
  exact measurable_stoppedValue (_root_.Prove2MeSourceProof.h_e303374519c4de703021a2f6 (hY i)) hσ
/-- Prepending a zero coordinate preserves measurability of a random vector. -/
theorem Measurable.finCons_zero {mΩ' : MeasurableSpace Ω} {c : Ω → Fin n → ℝ}
    (hc : Measurable[mΩ'] c) :
    Measurable[mΩ'] fun ω => (Fin.cons 0 (c ω) : Fin (n + 1) → ℝ) := by
  letI : MeasurableSpace Ω := mΩ'
  refine measurable_pi_lambda _ fun p => ?_
  induction p using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero]
    exact measurable_const
  | succ q =>
    simp only [Fin.cons_succ]
    exact (measurable_pi_apply q).comp hc
end StoppingTime

section MixedAe

variable {n : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

/-- Along a pair of paths the mixed compensator-drift integral over a time window is the
intensity integral of the mixed jump increment minus the first-order term, when the mark
integrability holds at almost every time of the window. -/
theorem setIntegral_mixedCompensatorDrift_eq_sub_ae (A : Set E) (y x : ℝ → Fin n → ℝ) (T : ℝ)
    (hγ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i : Fin n,
      IntegrableOn (fun e => γ s (x s) e i) A ν)
    (hΔ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      IntegrableOn (fun e => mixedJumpIncrement u γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume) :
    (∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, mixedCompensatorDriftIntegrand u γ s (y s) (x s) e ∂ν)
      = (∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν)
        - ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
            gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν := by
  rw [← integral_sub hΔt hgt]
  refine integral_congr_ae ?_
  filter_upwards [hγ, hΔ] with s hγs hΔs
  exact setIntegral_mixedCompensatorDriftIntegrand_eq_sub A s (y s) (x s) hγs hΔs
/-- The drift reconciliation for the mixed integrands, with the mark integrability asked at
almost every time of the window only. -/
theorem setIntegral_firstOrder_add_mixedCompensatorDrift_ae (A : Set E)
    (y x : ℝ → Fin n → ℝ) (T : ℝ)
    (hγ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i : Fin n,
      IntegrableOn (fun e => γ s (x s) e i) A ν)
    (hΔ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      IntegrableOn (fun e => mixedJumpIncrement u γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume) :
    (∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
          gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν)
        + ∫ s in Set.Icc (0 : ℝ) T,
            ∫ e in A, mixedCompensatorDriftIntegrand u γ s (y s) (x s) e ∂ν
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν := by
  have h := setIntegral_mixedCompensatorDrift_eq_sub_ae (u := u) (γ := γ) A y x T hγ hΔ hΔt hgt
  linarith
end MixedAe

section MixedAssemblyAe

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {coeffs : JumpDiffusionCoeffs n d E}

end MixedAssemblyAe

section TimeAugBounds

variable {Ω : Type u} {n d : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
  {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}

end TimeAugBounds

end LevyStochCalc.Ito.JumpFormula


