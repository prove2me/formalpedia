-- Prove2me | Definitions.Def_SourceProof_1ace97fa8da1f451121369a1
-- name    : SourceProof_1ace97fa8da1f451121369a1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:12:09.829049+00:00
-- url     : https://prove2.me/theorems/a5076c17-4790-4989-9b07-02537cd74af9
-- title:
--   LevyStochCalc source module: SourceProof_1ace97fa8da1f451121369a1
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.hasSum_markedChaosDegreeC` comes from the `LevyStochCalc.Poisson.ProfileChaosExpansion` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileChaosExpansion_F000

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


theorem _root_.Prove2MeSourceProof.h_1ace97fa8da1f451121369a1 (N : PoissonRandomMeasure P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (c : Fin p → ℂ) :
    ∀ᵐ ω ∂P, (Summable fun s : ℕ => ‖markedChaosDegreeC N s B c ω / (s.factorial : ℂ)‖)
      ∧ HasSum (fun s : ℕ => markedChaosDegreeC N s B c ω / (s.factorial : ℂ))
        (markedExpVector N B c ω) := by
  filter_upwards [ae_all_iff.2 fun k => N.integer_valued (hB k) (hfin k)] with ω hω
  choose n hn using hω
  have hreal : ∀ k, (N.N ω (B k)).toReal = (n k : ℝ) := fun k => by rw [hn k]; simp
  have hcount : ∀ k, LevyStochCalc.Poisson.pointCount N (B k) ω = n k := fun k => by
    rw [LevyStochCalc.Poisson.pointCount, hreal k, Nat.floor_natCast]
  have hterm : ∀ s : ℕ, LevyStochCalc.Poisson.markedChaosDegreeC N s B c ω / (s.factorial : ℂ)
      = coeff s (∏ k, LevyStochCalc.Probability.charlierSeries (LevyStochCalc.Poisson.referenceIntensity ν (B k)).toReal
          (N.N ω (B k)).toReal (c k)) := by
    intro s
    rw [_root_.Prove2MeSourceProof.h_24748d32159379e045f18228, mul_div_cancel_left₀ _
      (by exact_mod_cast s.factorial_ne_zero)]
  simp_rw [hterm]
  refine LevyStochCalc.Poisson.hasSum_coeff_prod univ _ _ (fun k _ => ?_) (fun k _ => ?_)
  · simp_rw [LevyStochCalc.Probability.coeff_charlierSeries, hreal k]
    exact _root_.Prove2MeSourceProof.h_ad3bbe38f517804cbaecc6ff _ (n k) (c k)
  · simp_rw [LevyStochCalc.Probability.coeff_charlierSeries, hreal k]
    rw [LevyStochCalc.Poisson.poissonExpVector, hcount k]
    exact _root_.Prove2MeSourceProof.h_cb218c1576ded71cb7df2cbc _ (n k) (c k)
/-! ### Simple profiles -/

namespace SimpleProfile

end SimpleProfile

end LevyStochCalc.Poisson


