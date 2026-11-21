-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ProfileCharacter_F000
-- name    : LevyStochCalc_Poisson_ProfileCharacter_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:14:10.144173+00:00
-- url     : https://prove2.me/theorems/33251f44-2b13-4284-a184-ab818c2bf626
-- title:
--   Source declarations: LevyStochCalc.Poisson.ProfileCharacter
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ProfileCharacter. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleProfile_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character of a compensated step integral of a mark profile

The count of a Poisson random measure on a region of finite intensity is Poisson, so the
character of the compensated count carries the Lévy–Khintchine integrand `e^{iuc} - 1 - iuc`
at the coefficient `c`. A simple mark profile pairs pairwise-disjoint mark sets with constant
coefficients, so over a step its compensated integral is a sum of independent compensated
counts and its character is the product of the counts' characters,

  `E[exp (i u J(f))] = exp ((b - a) ∫ (exp (i u f) - 1 - i u f) dν)`.

The right-hand side is continuous along `L²(ν)` convergence of the profile, so the identity
transfers to a profile approximated by simple ones together with any `L²(P)` limit of their
compensated step integrals.

## Main definitions

* `LevyStochCalc.Poisson.levyCharIntegrand` — the integrand `e^{iux} - 1 - iux`.

## Main statements

* `LevyStochCalc.Poisson.integral_exp_I_mul_compensated` — the character of a compensated
  count on a region of finite intensity.
* `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral` — the character of the
  compensated step integral of a simple mark profile.
* `LevyStochCalc.Poisson.integrable_levyCharIntegrand` — integrability of the integrand at a
  square-integrable mark profile.
* `LevyStochCalc.Poisson.tendsto_integral_levyCharIntegrand` — continuity of the Lévy
  characteristic exponent along `L²(ν)` convergence of the profile.
* `LevyStochCalc.Poisson.integral_exp_I_mul_of_tendsto_stepIntegral` — the character of an
  `L²(P)` limit of the compensated step integrals of simple profiles converging in `L²(ν)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The Lévy–Khintchine integrand -/

/-- The integrand `e^{iux} - 1 - iux` of the Lévy characteristic exponent. -/
noncomputable def levyCharIntegrand (u x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) - 1 - Complex.I * ((u * x : ℝ) : ℂ)
@[simp] theorem levyCharIntegrand_zero (u : ℝ) : levyCharIntegrand u 0 = 0 := by
  simp [levyCharIntegrand]
theorem continuous_levyCharIntegrand (u : ℝ) : Continuous (levyCharIntegrand u) := by
  unfold levyCharIntegrand
  fun_prop
theorem measurable_levyCharIntegrand (u : ℝ) : Measurable (levyCharIntegrand u) :=
  (continuous_levyCharIntegrand u).measurable
/-- The Lévy characteristic integrand is bounded by three times the square of its argument. -/
theorem norm_levyCharIntegrand_le (u x : ℝ) :
    ‖levyCharIntegrand u x‖ ≤ 3 * (u * x) ^ 2 := by
  set t : ℝ := u * x with ht
  rcases le_or_gt |t| 1 with h | h
  · have hnorm : ‖Complex.I * ((t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact h
    have := Complex.norm_exp_sub_one_sub_id_le hnorm
    have hsq : ‖Complex.I * ((t : ℝ) : ℂ)‖ ^ 2 = t ^ 2 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [levyCharIntegrand, ← ht]
    calc ‖Complex.exp (Complex.I * (t : ℂ)) - 1 - Complex.I * (t : ℂ)‖
        ≤ ‖Complex.I * ((t : ℝ) : ℂ)‖ ^ 2 := this
      _ = t ^ 2 := hsq
      _ ≤ 3 * t ^ 2 := by nlinarith [sq_nonneg t]
  · have h1 : ‖Complex.exp (Complex.I * ((t : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp_I_mul_ofReal]
    have h2 : ‖Complex.I * ((t : ℝ) : ℂ)‖ = |t| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hle : ‖levyCharIntegrand u x‖ ≤ 1 + 1 + |t| := by
      rw [levyCharIntegrand, ← ht]
      refine (norm_sub_le _ _).trans ?_
      gcongr
      · exact (norm_sub_le _ _).trans (by rw [h1, norm_one])
      · exact h2.le
    have habs : |t| ≤ t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    have h1t : (1 : ℝ) ≤ t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    linarith
/-- A bound on the increment of the Lévy characteristic integrand between two arguments. -/
theorem norm_levyCharIntegrand_sub_le (u x y : ℝ) :
    ‖levyCharIntegrand u x - levyCharIntegrand u y‖
      ≤ 3 * (u * (x - y)) ^ 2 + u ^ 2 * |y| * |x - y| := by
  have hsplit : levyCharIntegrand u x - levyCharIntegrand u y
      = Complex.exp (Complex.I * ((u * y : ℝ) : ℂ)) * levyCharIntegrand u (x - y)
        + (Complex.exp (Complex.I * ((u * y : ℝ) : ℂ)) - 1)
          * (Complex.I * ((u * (x - y) : ℝ) : ℂ)) := by
    have hexp : Complex.exp (Complex.I * ((u * x : ℝ) : ℂ))
        = Complex.exp (Complex.I * ((u * y : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((u * (x - y) : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [levyCharIntegrand, levyCharIntegrand, levyCharIntegrand, hexp]
    push_cast
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖Complex.exp (Complex.I * ((u * y : ℝ) : ℂ)) * levyCharIntegrand u (x - y)‖
      ≤ 3 * (u * (x - y)) ^ 2 := by
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    exact norm_levyCharIntegrand_le u (x - y)
  have h2 : ‖(Complex.exp (Complex.I * ((u * y : ℝ) : ℂ)) - 1)
      * (Complex.I * ((u * (x - y) : ℝ) : ℂ))‖ ≤ u ^ 2 * |y| * |x - y| := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul]
    have hu : ‖Complex.exp (Complex.I * ((u * y : ℝ) : ℂ)) - 1‖ ≤ |u| * |y| := by
      refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
      rw [Real.norm_eq_abs, abs_mul]
    calc ‖Complex.exp (Complex.I * ((u * y : ℝ) : ℂ)) - 1‖ * (|u| * |x - y|)
        ≤ (|u| * |y|) * (|u| * |x - y|) := by
          gcongr
      _ = u ^ 2 * |y| * |x - y| := by
          rw [← sq_abs u]; ring
  linarith
/-! ### The character of a count and of a compensated count -/

/-- The character of a Poisson count on a region of finite intensity. -/
theorem integral_exp_I_mul_count (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (N.N ω B).toReal : ℝ) : ℂ)) ∂P
      = Complex.exp ((referenceIntensity ν B).toReal
          * (Complex.exp (Complex.I * (u : ℂ)) - 1)) := by
  classical
  set r : ℝ≥0 := (referenceIntensity ν B).toNNReal with hrdef
  have hrR : ((r : ℝ) : ℂ) = ((referenceIntensity ν B).toReal : ℂ) := rfl
  set g : ℝ≥0∞ → ℂ := fun x => Complex.exp (Complex.I * ((u * x.toReal : ℝ) : ℂ)) with hg
  have hgm : Measurable g := by
    rw [hg]
    fun_prop
  have hXm : Measurable fun ω => N.N ω B := N.measurable_eval hB
  have hstep1 : ∫ ω, g (N.N ω B) ∂P = ∫ x, g x ∂(P.map fun ω => N.N ω B) :=
    (integral_map hXm.aemeasurable hgm.aestronglyMeasurable).symm
  have hstep2 : ∫ x, g x ∂(P.map fun ω => N.N ω B)
      = ∫ n : ℕ, g ((n : ℝ≥0∞)) ∂(poissonMeasure r) := by
    rw [N.poisson_law hB hfin, poissonMeasureENN, ← hrdef]
    exact integral_map (by fun_prop) hgm.aestronglyMeasurable
  have hstep3 : ∫ n : ℕ, g ((n : ℝ≥0∞)) ∂(poissonMeasure r)
      = charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) u := by
    rw [charFun_apply_real,
      integral_map (by fun_prop : AEMeasurable (Nat.cast : ℕ → ℝ) (poissonMeasure r))
        (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((u : ℂ) * (x : ℂ)
          * Complex.I)) _)]
    refine integral_congr_ae (Eventually.of_forall fun n => ?_)
    rw [hg]
    simp only [ENNReal.toReal_natCast]
    congr 1
    push_cast
    ring
  rw [hstep1, hstep2, hstep3, charFun_map_cast_poissonMeasure, hrR]
  congr 2
  rw [mul_comm]
/-- The character of the compensated count on a region of finite intensity. -/
theorem integral_exp_I_mul_compensated (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * N.compensated B ω : ℝ) : ℂ)) ∂P
      = Complex.exp ((referenceIntensity ν B).toReal
          * (Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ))) := by
  have hfactor : ∀ ω, Complex.exp (Complex.I * ((u * N.compensated B ω : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((u * (N.N ω B).toReal : ℝ) : ℂ))
        * Complex.exp (-(Complex.I * ((u * (referenceIntensity ν B).toReal : ℝ) : ℂ))) := by
    intro ω
    rw [← Complex.exp_add]
    congr 1
    rw [PoissonRandomMeasure.compensated]
    push_cast
    ring
  simp_rw [hfactor]
  rw [integral_mul_const, integral_exp_I_mul_count N hB hfin u, ← Complex.exp_add]
  congr 1
  push_cast
  ring
/-! ### The character at a simple mark profile -/

namespace SimpleProfile

omit [SigmaFinite ν] in
/-- On one of its mark sets a simple profile takes the matching coefficient. -/
theorem toFun_of_mem (G : SimpleProfile E ν) {k : Fin G.K} {e : E} (he : e ∈ G.B k) :
    G.toFun e = G.c k := by
  classical
  rw [toFun]
  refine (Finset.sum_eq_single k (fun l _ hl => ?_)
    (fun h => absurd (Finset.mem_univ _) h)).trans ?_
  · rw [Set.indicator_of_notMem (fun hmem =>
      (Set.disjoint_left.1 (G.B_disjoint hl) hmem) he), mul_zero]
  · rw [Set.indicator_of_mem he, mul_one]
omit [SigmaFinite ν] in
/-- Outside all of its mark sets a simple profile vanishes. -/
theorem toFun_of_notMem (G : SimpleProfile E ν) {e : E} (he : ∀ k, e ∉ G.B k) :
    G.toFun e = 0 := by
  rw [toFun]
  exact Finset.sum_eq_zero fun k _ => by rw [Set.indicator_of_notMem (he k), mul_zero]
omit [SigmaFinite ν] in
/-- The Lévy characteristic integrand at a simple profile, through the indicators of its mark
sets. -/
theorem levyCharIntegrand_toFun (G : SimpleProfile E ν) (u : ℝ) (e : E) :
    levyCharIntegrand u (G.toFun e)
      = ∑ k, (G.B k).indicator (fun _ => levyCharIntegrand u (G.c k)) e := by
  classical
  by_cases h : ∃ k, e ∈ G.B k
  · obtain ⟨k, hk⟩ := h
    rw [G.toFun_of_mem hk, Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
      (fun l _ hl => Set.indicator_of_notMem
        (fun hmem => (Set.disjoint_left.1 (G.B_disjoint hl) hmem) hk) _),
      Set.indicator_of_mem hk]
  · simp only [not_exists] at h
    rw [G.toFun_of_notMem h, levyCharIntegrand_zero]
    exact (Finset.sum_eq_zero fun k _ => Set.indicator_of_notMem (h k) _).symm
omit [SigmaFinite ν] in
/-- The Lévy characteristic exponent of a simple profile, as a sum over its mark sets. -/
theorem integral_levyCharIntegrand_toFun (G : SimpleProfile E ν) (u : ℝ) :
    ∫ e, levyCharIntegrand u (G.toFun e) ∂ν
      = ∑ k, ((ν (G.B k)).toReal : ℂ) * levyCharIntegrand u (G.c k) := by
  classical
  have hint : ∀ k : Fin G.K, Integrable
      (fun e => (G.B k).indicator (fun _ => levyCharIntegrand u (G.c k)) e) ν := fun k =>
    memLp_one_iff_integrable.1
      (memLp_indicator_const 1 (G.B_measurable k) _ (Or.inr (G.B_finite k)))
  simp_rw [G.levyCharIntegrand_toFun u]
  rw [integral_finsetSum _ fun k _ => hint k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_indicator_const _ (G.B_measurable k), Complex.real_smul, measureReal_def]
end SimpleProfile

/-! ### Passage to a general square-integrable profile -/

end LevyStochCalc.Poisson


