-- Prove2me | Definitions.Def_SourceProof_6585134b289c2b12a9b076df
-- name    : SourceProof_6585134b289c2b12a9b076df
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:15:47.368237+00:00
-- url     : https://prove2.me/theorems/20af188e-89ef-4c75-a195-cdb25c649092
-- title:
--   LevyStochCalc source module: SourceProof_6585134b289c2b12a9b076df
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.profileExpVector_ae_eq_markedExpVector` comes from the `LevyStochCalc.Poisson.ProfileChaosExpansion` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileChaosExpansion_F000
import Definitions.Def_SourceProof_42f85278a4a3a35e73d229e1

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

/-! ### Simple profiles -/

namespace SimpleProfile

end SimpleProfile


theorem _root_.Prove2MeSourceProof.h_6585134b289c2b12a9b076df (N : PoissonRandomMeasure.{u, v, w} P ν)
    (G : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : ℝ) :
    profileExpVector N G.toFun a b u
      =ᵐ[P] markedExpVector N (fun k => Set.Ioc a b ×ˢ G.B k)
        (fun k => Complex.exp (Complex.I * ((u * G.c k : ℝ) : ℂ)) - 1) := by
  have hBm : ∀ k, MeasurableSet (Set.Ioc a b ×ˢ G.B k) :=
    fun k => measurableSet_Ioc.prod (G.B_measurable k)
  have hBfin : ∀ k, LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ G.B k) ≠ ⊤ :=
    fun k => LevyStochCalc.Poisson.referenceIntensity_strip_ne_top ha (G.B_finite k)
  filter_upwards [_root_.Prove2MeSourceProof.h_42f85278a4a3a35e73d229e1 N G ha hab,
    ae_all_iff.2 fun k => N.integer_valued (hBm k) (hBfin k)] with ω hJ hω
  choose n hn using hω
  have hreal : ∀ k, (N.N ω (Set.Ioc a b ×ˢ G.B k)).toReal = (n k : ℝ) :=
    fun k => by rw [hn k]; simp
  have hcount : ∀ k, LevyStochCalc.Poisson.pointCount N (Set.Ioc a b ×ˢ G.B k) ω = n k := fun k => by
    rw [LevyStochCalc.Poisson.pointCount, hreal k, Nat.floor_natCast]
  have hfac : ∀ k, LevyStochCalc.Poisson.poissonExpVector N (Set.Ioc a b ×ˢ G.B k)
      (Complex.exp (Complex.I * ((u * G.c k : ℝ) : ℂ)) - 1) ω
      = Complex.exp (-((((b - a) * (ν (G.B k)).toReal : ℝ) : ℂ)
          * (Complex.exp (Complex.I * ((u * G.c k : ℝ) : ℂ)) - 1))
          + (n k : ℂ) * (Complex.I * ((u * G.c k : ℝ) : ℂ))) := by
    intro k
    rw [LevyStochCalc.Poisson.poissonExpVector, hcount k, LevyStochCalc.Poisson.referenceIntensity_strip_toReal ha hab, add_sub_cancel,
      ← Complex.exp_nat_mul, ← Complex.exp_add]
  rw [LevyStochCalc.Poisson.markedExpVector, Finset.prod_congr rfl fun k _ => hfac k, ← Complex.exp_sum,
    LevyStochCalc.Poisson.profileExpVector, ← Complex.exp_add, hJ, LevyStochCalc.Poisson.SimpleProfile.stepIntegral,
    LevyStochCalc.Poisson.SimpleProfile.integral_levyCharIntegrand_toFun]
  congr 1
  simp only [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated, hreal, LevyStochCalc.Poisson.levyCharIntegrand]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LevyStochCalc.Poisson.referenceIntensity_strip_toReal ha hab]
  push_cast
  ring
end LevyStochCalc.Poisson


