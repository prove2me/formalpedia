-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ProfileChaosExpansion_F000
-- name    : LevyStochCalc_Poisson_ProfileChaosExpansion_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:37:04.102171+00:00
-- url     : https://prove2.me/theorems/a90c70d7-a469-42b8-a9fb-e6c7b2965b5d
-- title:
--   Source declarations: LevyStochCalc.Poisson.ProfileChaosExpansion
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ProfileChaosExpansion. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ChaosExpansion_F000
import Definitions.Def_LevyStochCalc_Poisson_ProfileExpVector_F000
import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosRefine_F000
import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosRefine_F001
import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosRefine_F003

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

/-- **Finite Cauchy product.** If the coefficient sequences of finitely many power series over a
complete normed commutative ring are absolutely summable, so is the coefficient sequence of their
product, and its sum is the product of the sums. -/
theorem hasSum_coeff_prod {R : Type*} [NormedCommRing R] [CompleteSpace R] {ι : Type*}
    (s : Finset ι) (f : ι → PowerSeries R) (x : ι → R)
    (hs : ∀ i ∈ s, Summable fun n => ‖coeff n (f i)‖)
    (hx : ∀ i ∈ s, HasSum (fun n => coeff n (f i)) (x i)) :
    (Summable fun n => ‖coeff n (∏ i ∈ s, f i)‖)
      ∧ HasSum (fun n => coeff n (∏ i ∈ s, f i)) (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty, coeff_one]
    refine ⟨?_, hasSum_ite_eq 0 1⟩
    refine (hasSum_ite_eq 0 ‖(1 : R)‖).summable.congr fun n => ?_
    split_ifs <;> simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hs i (mem_insert_of_mem hi))
      (fun i hi => hx i (mem_insert_of_mem hi))
    have ha1 := hs a (mem_insert_self a s)
    have ha2 := hx a (mem_insert_self a s)
    simp only [prod_insert ha, coeff_mul]
    have hsum := summable_norm_sum_mul_antidiagonal_of_summable_norm ha1 ih1
    refine ⟨hsum, ?_⟩
    have hval := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha1 ih1
    rw [ha2.tsum_eq, ih2.tsum_eq] at hval
    rw [hval]
    exact hsum.of_norm.hasSum
/-! ### The exponential vector of a family and its chaos expansion -/

/-- The exponential vector of a finite family of regions carried by a complex profile constant on
each region, `∏_k e^(-λ_k c_k) (1 + c_k) ^ N(B k)` with `λ_k = ν̂(B k)`. -/
noncomputable def markedExpVector (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℂ) (ω : Ω) : ℂ :=
  ∏ k, poissonExpVector N (B k) (c k) ω
/-! ### Simple profiles -/

namespace SimpleProfile

end SimpleProfile

end LevyStochCalc.Poisson


