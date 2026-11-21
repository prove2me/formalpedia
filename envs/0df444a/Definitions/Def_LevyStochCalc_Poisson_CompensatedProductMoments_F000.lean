-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProductMoments_F000
-- name    : LevyStochCalc_Poisson_CompensatedProductMoments_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:23:18.864467+00:00
-- url     : https://prove2.me/theorems/94eaf4b5-df2c-471f-9f0e-bd1b6f73662f
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProductMoments
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProductMoments. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProduct_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of the compensated product of two bounded mark profiles

For bounded square-integrable mark profiles `f, g : E → ℝ` and the compensated integral `J` over
the step `(a, b]` against a Poisson random measure with intensity `ν`, the compensated product
`Q(f, g) = J(f) J(g) − J(f g) − (b − a) ∫ f g dν` is square integrable and centred, it is
orthogonal in `L²(P)` to `J(h)` for every square-integrable profile `h`, and, with
`⟨u, v⟩ = ∫ u v dν`,

  `E[Q(f, g) Q(f', g')] = (b − a)² (⟨f, f'⟩ ⟨g, g'⟩ + ⟨f, g'⟩ ⟨g, f'⟩)`.

The profiles `f, g` are arbitrary bounded square-integrable functions; their supports may
overlap, and no independence of their compensated integrals enters.

Each of `f, g` is approximated in `L²(ν)` by simple profiles obeying the same bound, and at simple
profiles the identities hold by `Poisson/CompensatedProduct.lean`. The Gram at simple profiles
writes the `L²(P)` distance of two compensated products through `L²(ν)` pairings, so the
compensated products of the approximants form a Cauchy sequence in `L²(P)`. The compensated
integrals of the approximants and of their products converge in `L²(P)` by the isometry
`‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}` at square-integrable profiles; along a
subsequence all of them converge almost surely, which identifies the `L²(P)` limit with
`Q(f, g)`. The identities then pass to the limit by continuity of the `L²` pairing, so no third or
fourth moment of the compensated integral of a general profile is needed.

## Main statements

* `LevyStochCalc.Poisson.integral_compensatedProfile_sub_sq`,
  `LevyStochCalc.Poisson.eLpNorm_compensatedProfile_sub` — the isometry at square-integrable
  profiles.
* `LevyStochCalc.Poisson.memLp_compensatedProduct` — square integrability.
* `LevyStochCalc.Poisson.integral_compensatedProduct` — the mean.
* `LevyStochCalc.Poisson.integral_compensatedProduct_mul` — the Gram.
* `LevyStochCalc.Poisson.integral_compensatedProduct_mul_compensatedProfile` — orthogonality to
  the first chaos.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Probability

/-! ### `L²` facts -/

/-- The `L²` seminorm of a square-integrable real function through its second moment. -/
theorem eLpNorm_two_eq_ofReal_sqrt_integral_sq {α : Type*} [MeasurableSpace α]
    {m : Measure α} {F : α → ℝ} (hF : MemLp F 2 m) :
    eLpNorm F 2 m = ENNReal.ofReal (Real.sqrt (∫ x, F x ^ 2 ∂m)) := by
  rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    show (2 : ℝ≥0∞).toReal = 2 from by norm_num, Real.sqrt_eq_rpow, one_div]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_two, sq_abs]
/-- The second moment of a difference of square-integrable real functions, expanded. -/
theorem integral_sub_sq_of_memLp {α : Type*} [MeasurableSpace α] {m : Measure α}
    {F G : α → ℝ} (hF : MemLp F 2 m) (hG : MemLp G 2 m) :
    ∫ x, (F x - G x) ^ 2 ∂m
      = ∫ x, F x * F x ∂m - ∫ x, F x * G x ∂m - ∫ x, G x * F x ∂m + ∫ x, G x * G x ∂m := by
  have h11 : Integrable (fun x => F x * F x) m := hF.integrable_mul hF
  have h12 : Integrable (fun x => F x * G x) m := hF.integrable_mul hG
  have h21 : Integrable (fun x => G x * F x) m := hG.integrable_mul hF
  have h22 : Integrable (fun x => G x * G x) m := hG.integrable_mul hG
  have h1 : Integrable (fun x => F x * F x - F x * G x) m := h11.sub h12
  have h2 : Integrable (fun x => F x * F x - F x * G x - G x * F x) m := h1.sub h21
  rw [show (fun x => (F x - G x) ^ 2)
      = fun x => F x * F x - F x * G x - G x * F x + G x * G x from by funext x; ring,
    integral_add h2 h22, integral_sub h1 h21, integral_sub h11 h12]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end LevyStochCalc.Probability

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The isometry -/

/-! ### Passage to the limit -/

/-! ### The moments -/

end LevyStochCalc.Poisson


