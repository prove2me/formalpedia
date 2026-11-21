-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ProfileChaosExpansion_F001
-- name    : LevyStochCalc_Poisson_ProfileChaosExpansion_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:13:50.350235+00:00
-- url     : https://prove2.me/theorems/5a225f2f-1123-4aec-b303-2ed9e904da32
-- title:
--   Source declarations: LevyStochCalc.Poisson.ProfileChaosExpansion
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ProfileChaosExpansion. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileChaosExpansion_F000
import Definitions.Def_SourceProof_1ace97fa8da1f451121369a1

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The exponential vector of finitely many regions and its chaos expansion

For a finite pairwise disjoint family `B` of regions of finite intensity `λ_k = ν̂(B k)` and a
complex profile `c` constant on each region, the exponential vector of the family is the product
of the exponential vectors of the regions,

  `V(c; B) = ∏_k e^(-λ_k c_k) (1 + c_k) ^ N(B k)`,

and its chaos expansion is `V(c; B) = ∑_s D_s(c; B) / s!`, with `D_s(c; B)` the degree-`s` element
of the profile. Almost surely every count `N(B k)` is the value of a natural number; there the
element `D_s(c; B) / s!` is the coefficient of `X ^ s` in the product of the Charlier generating
series of the regions, each of which is absolutely summable at the scalar `1` with sum the
exponential vector of its region, and a finite Cauchy product of absolutely summable series is
absolutely summable with sum the product of the sums. The second moment of the modulus of
`D_s(c; B) / s!` is `(∑_k ‖c_k‖ ^ 2 λ_k) ^ s / s!`, so the `L²` norms are summable and the series
converges in `L²(P; ℂ)` to `V(c; B)`, which is therefore square integrable; the terms are
orthogonal across degrees, so `E‖V(c; B)‖ ^ 2 = exp (∑_k ‖c_k‖ ^ 2 λ_k)`.

At the profile `c_k = e^{i u h_k} − 1` of the values `h_k` of a simple mark profile `h` over the
strips `(a, b] ×ˢ A k`, the exponential vector of the family is almost surely the exponential
vector `exp (i u J(h)) · exp (−(b − a) ∫ ψ_u(h) dν)` of the step at `h`. The constants
`∫ ‖e^{i u h} − 1‖ ^ 2 dν` and `∫ (e^{i u h} − 1) ^ 2 dν` of a simple profile are the sums of the
corresponding values weighted by the intensities of its mark sets.

## Main definitions

* `LevyStochCalc.Poisson.markedExpVector` — the exponential vector of a finite family of regions.

## Main statements

* `LevyStochCalc.Poisson.hasSum_coeff_prod` — the finite Cauchy product of absolutely summable
  coefficient sequences.
* `LevyStochCalc.Poisson.hasSum_markedChaosDegreeC` — `∑_s D_s(c; B) / s! = V(c; B)` almost
  surely.
* `LevyStochCalc.Poisson.integral_norm_sq_markedChaosDegreeC_div` —
  `E‖D_s(c; B) / s!‖ ^ 2 = (∑_k ‖c_k‖ ^ 2 λ_k) ^ s / s!`.
* `LevyStochCalc.Poisson.memLp_two_markedExpVector` — `V(c; B)` is square integrable.
* `LevyStochCalc.Poisson.hasSum_toLp_markedChaosDegreeC` — the chaos expansion in `L²(P; ℂ)`.
* `LevyStochCalc.Poisson.integral_norm_sq_markedExpVector` —
  `E‖V(c; B)‖ ^ 2 = exp (∑_k ‖c_k‖ ^ 2 λ_k)`.
* `LevyStochCalc.Poisson.profileExpVector_ae_eq_markedExpVector` — at `c_k = e^{i u h_k} − 1` the
  exponential vector of the strips is the exponential vector of the step at the simple profile.
* `LevyStochCalc.Poisson.SimpleProfile.integral_comp_toFun` — the integral of a function of a
  simple profile vanishing at zero.
-/

open MeasureTheory ProbabilityTheory PowerSeries Finset Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

open LevyStochCalc.Probability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Finite Cauchy products -/

/-! ### The exponential vector of a family and its chaos expansion -/

/-- The scaled degree elements of a finite pairwise disjoint family of regions of finite
intensity lie in `L²`. -/
theorem memLp_two_markedChaosDegreeC_div (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (c : Fin p → ℂ) (s : ℕ) :
    MemLp (fun ω => markedChaosDegreeC N s B c ω / (s.factorial : ℂ)) 2 P := by
  simpa only [div_eq_mul_inv] using (memLp_two_markedChaosDegreeC N hB hd hfin s c).mul_const _
/-- The second moment of the modulus of a scaled degree element,
`E‖D_s(c; B) / s!‖ ^ 2 = (∑_k ‖c_k‖ ^ 2 λ_k) ^ s / s!`. -/
theorem integral_norm_sq_markedChaosDegreeC_div (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (c : Fin p → ℂ) (s : ℕ) :
    ∫ ω, ‖markedChaosDegreeC N s B c ω / (s.factorial : ℂ)‖ ^ 2 ∂P
      = (∑ k, ‖c k‖ ^ 2 * (referenceIntensity ν (B k)).toReal) ^ s / (s.factorial : ℝ) := by
  have hpt : ∀ ω, ‖markedChaosDegreeC N s B c ω / (s.factorial : ℂ)‖ ^ 2
      = ((s.factorial : ℝ) ^ 2)⁻¹ * ‖markedChaosDegreeC N s B c ω‖ ^ 2 := by
    intro ω
    rw [norm_div, Complex.norm_natCast, div_pow, inv_mul_eq_div]
  simp_rw [hpt]
  rw [integral_const_mul, _root_.Prove2MeSourceProof.h_0e25f759242a2bf97a35c0b8 N hB hd hfin s c]
  have hs : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast s.factorial_ne_zero
  field_simp
/-- The `L²` norms of the scaled degree elements are summable. -/
theorem summable_sqrt_integral_norm_sq_markedChaosDegreeC_div
    (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (c : Fin p → ℂ) :
    Summable fun s : ℕ =>
      Real.sqrt (∫ ω, ‖markedChaosDegreeC N s B c ω / (s.factorial : ℂ)‖ ^ 2 ∂P) := by
  refine (_root_.Prove2MeSourceProof.h_b750ef8bbdd7c269127a06e5
    (x := ∑ k, ‖c k‖ ^ 2 * (referenceIntensity ν (B k)).toReal) (by positivity)).congr
    fun s => ?_
  rw [integral_norm_sq_markedChaosDegreeC_div N hB hd hfin c s]
/-- The exponential vector of a finite pairwise disjoint family of regions of finite intensity
lies in `L²`. -/
theorem memLp_two_markedExpVector (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (c : Fin p → ℂ) :
    MemLp (markedExpVector N B c) 2 P :=
  memLp_two_of_hasSum_ae (memLp_two_markedChaosDegreeC_div N hB hd hfin c)
    (summable_sqrt_integral_norm_sq_markedChaosDegreeC_div N hB hd hfin c)
    ((_root_.Prove2MeSourceProof.h_1ace97fa8da1f451121369a1 N hB hfin c).mono fun _ h => h.2)
/-- **The chaos expansion of the exponential vector of a family.** The scaled degree elements
`D_s(c; B) / s!` of a finite pairwise disjoint family of regions of finite intensity sum in
`L²(P; ℂ)` to the exponential vector of the family. -/
theorem hasSum_toLp_markedChaosDegreeC (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (c : Fin p → ℂ) :
    HasSum (fun s : ℕ => (memLp_two_markedChaosDegreeC_div N hB hd hfin c s).toLp
        (fun ω => markedChaosDegreeC N s B c ω / (s.factorial : ℂ)))
      ((memLp_two_markedExpVector N hB hd hfin c).toLp (markedExpVector N B c)) :=
  hasSum_toLp_of_summable_norm _ _
    (summable_sqrt_integral_norm_sq_markedChaosDegreeC_div N hB hd hfin c)
    ((_root_.Prove2MeSourceProof.h_1ace97fa8da1f451121369a1 N hB hfin c).mono fun _ h => h.2)
/-- The second moment of the modulus of the exponential vector of a family,
`E‖V(c; B)‖ ^ 2 = exp (∑_k ‖c_k‖ ^ 2 λ_k)`. -/
theorem integral_norm_sq_markedExpVector (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (c : Fin p → ℂ) :
    ∫ ω, ‖markedExpVector N B c ω‖ ^ 2 ∂P
      = Real.exp (∑ k, ‖c k‖ ^ 2 * (referenceIntensity ν (B k)).toReal) := by
  have h1 := hasSum_integral_norm_sq_of_hasSum_toLp _ _ (fun s s' hss => ?_)
    (hasSum_toLp_markedChaosDegreeC N hB hd hfin c)
  · have h2 : HasSum (fun s : ℕ =>
        ∫ ω, ‖markedChaosDegreeC N s B c ω / (s.factorial : ℂ)‖ ^ 2 ∂P)
        (Real.exp (∑ k, ‖c k‖ ^ 2 * (referenceIntensity ν (B k)).toReal)) := by
      rw [Real.exp_eq_exp_ℝ]
      refine (NormedSpace.expSeries_div_hasSum_exp _).congr_fun fun s => ?_
      rw [integral_norm_sq_markedChaosDegreeC_div N hB hd hfin c s]
    exact h1.unique h2
  · have hpt : ∀ ω, (starRingEnd ℂ) (markedChaosDegreeC N s B c ω / (s.factorial : ℂ))
        * (markedChaosDegreeC N s' B c ω / (s'.factorial : ℂ))
        = ((s.factorial : ℂ) * (s'.factorial : ℂ))⁻¹
          * (markedChaosDegreeC N s B (fun k => (starRingEnd ℂ) (c k)) ω
            * markedChaosDegreeC N s' B c ω) := by
      intro ω
      rw [map_div₀, conj_markedChaosDegreeC, Complex.conj_natCast]
      field_simp
    simp_rw [hpt]
    rw [integral_const_mul, _root_.Prove2MeSourceProof.h_252ed50ad1c55539aff7f986 N hB hd hfin, if_neg hss, mul_zero]
/-! ### Simple profiles -/

namespace SimpleProfile

omit [SigmaFinite ν] in
/-- A function vanishing at zero, evaluated along a simple profile, through the indicators of its
mark sets. -/
theorem comp_toFun {V : Type*} [AddCommMonoid V] (G : SimpleProfile E ν) (F : ℝ → V)
    (hF : F 0 = 0) (e : E) :
    F (G.toFun e) = ∑ k, (G.B k).indicator (fun _ => F (G.c k)) e := by
  classical
  by_cases h : ∃ k, e ∈ G.B k
  · obtain ⟨k, hk⟩ := h
    rw [G.toFun_of_mem hk, Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
      (fun l _ hl => Set.indicator_of_notMem
        (fun hmem => (Set.disjoint_left.1 (G.B_disjoint hl) hmem) hk) _),
      Set.indicator_of_mem hk]
  · simp only [not_exists] at h
    rw [G.toFun_of_notMem h, hF]
    exact (Finset.sum_eq_zero fun k _ => Set.indicator_of_notMem (h k) _).symm
omit [SigmaFinite ν] in
/-- The integral of a function vanishing at zero along a simple profile, as a sum over its mark
sets weighted by their intensities. -/
theorem integral_comp_toFun {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (G : SimpleProfile E ν) (F : ℝ → V) (hF : F 0 = 0) :
    ∫ e, F (G.toFun e) ∂ν = ∑ k, (ν (G.B k)).toReal • F (G.c k) := by
  classical
  have hint : ∀ k : Fin G.K, Integrable
      (fun e => (G.B k).indicator (fun _ => F (G.c k)) e) ν := fun k =>
    memLp_one_iff_integrable.1
      (memLp_indicator_const 1 (G.B_measurable k) _ (Or.inr (G.B_finite k)))
  simp_rw [G.comp_toFun F hF]
  rw [integral_finsetSum _ fun k _ => hint k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_indicator_const _ (G.B_measurable k), measureReal_def]
end SimpleProfile

end LevyStochCalc.Poisson


