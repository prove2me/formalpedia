-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ProfileExpProduct_F000
-- name    : LevyStochCalc_Poisson_ProfileExpProduct_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:10:44.160398+00:00
-- url     : https://prove2.me/theorems/1fa19d9b-5a5b-44a1-a36f-3c1344885610
-- title:
--   Source declarations: LevyStochCalc.Poisson.ProfileExpProduct
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ProfileExpProduct. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairing_F001
import Definitions.Def_SourceProof_aec4e41a820f1d64901b8fc3

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing of the character of a compensated profile integral with a compensated product

For mark profiles `f, g` whose product is square integrable, the compensated product over the
step `(a, b]` is `Q(f, g) = J(f) J(g) − J(f g) − (b − a) ∫ f g dν`, with `J` the compensated
integral over the step. For a square-integrable profile `h`, a real frequency `u` and
`γ_u = e^{iuh} − 1`,

  `E[e^{iuJ(h)} Q(f, g)] = (b − a)² ∫ γ_u f dν ∫ γ_u g dν · E[e^{iuJ(h)}]`.

It is the second-order pairing `E[e^{iuJ(h)} J(f) J(g)]` less the first-order pairing with
`J(f g)` and the constant: the diagonal term `(b − a) ∫ e^{iuh} f g dν` of the former splits as
`(b − a) ∫ γ_u f g dν`, the pairing with `J(f g)`, plus `(b − a) ∫ f g dν`, the constant. The
profile `h` is only square integrable; `f g` is square integrable when one of the two profiles is
bounded.

## Main statements

* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul_compensatedProduct` — the
  pairing with the compensated product.
* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul_compensatedProduct_of_bound`
  — the same when one of the two profiles is bounded.
-/

open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The pairing with the compensated product of a square-integrable mark profile and a bounded
square-integrable one. -/
theorem integral_exp_I_mul_compensatedProfile_mul_compensatedProduct_of_bound
    (N : PoissonRandomMeasure P ν) {h f g : E → ℝ} (hh : MemLp h 2 ν) (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) {Cg : ℝ} (hbg : ∀ e, |g e| ≤ Cg) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ))
        * (compensatedProduct N f g a b ω : ℂ) ∂P
      = ((b - a : ℝ) : ℂ) ^ 2
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (f e : ℂ) ∂ν)
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (g e : ℂ) ∂ν)
        * ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ)) ∂P :=
  _root_.Prove2MeSourceProof.h_aec4e41a820f1d64901b8fc3 N hh hf hg
    (hf.of_le_mul (c := Cg) (hf.1.mul hg.1) (Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm Cg]
      exact mul_le_mul_of_nonneg_left (hbg e) (abs_nonneg _))) ha hab u
end LevyStochCalc.Poisson


