-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProduct_F000
-- name    : LevyStochCalc_Poisson_CompensatedProduct_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:04:44.921717+00:00
-- url     : https://prove2.me/theorems/0bc7940c-d0b2-4c56-a247-9df5a500ee6e
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProduct
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProduct. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileMoments_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileMoments_F001
import Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F003
import Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F004

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated product of two mark profiles over a step

For a mark profile `f : E → ℝ` write `J(f)` for its compensated integral over the step `(a, b]`
against a Poisson random measure `N` with intensity `ν` (`compensatedProfile`). The compensated
product of two mark profiles `f, g` over the step is

  `Q(f, g) = J(f) J(g) − J(f g) − (b − a) ∫ f g dν`.

For bounded square-integrable profiles the product `f g` is again bounded and square integrable,
so each term is a compensated integral of a square-integrable profile.

This file treats simple profiles. The functions of finitely many simple mark profiles are carried
by the mark sets of one simple profile, however the mark sets of different profiles overlap. On
such a common family `A_k`, with coefficient vectors `c, c'`, the compensated product is almost
surely the quadratic element

  `(∑ c_k Ñ(B_k)) (∑ c'_k Ñ(B_k)) − ∑ c_k c'_k N(B_k)`

of the strips `B_k = (a, b] ×ˢ A_k` (`markedSecondChaos`), whose mean, Gram and orthogonality to
the compensated counts come from `Poisson/SecondChaos.lean` and `Poisson/SimpleChaos.lean`. So at
simple profiles `Q` is square integrable and centred, it is orthogonal in `L²(P)` to the
compensated integral of every simple profile, and, with `⟨u, v⟩ = ∫ u v dν`,

  `E[Q(u₁, u₂) Q(u₃, u₄)] = (b − a)² (⟨u₁, u₃⟩ ⟨u₂, u₄⟩ + ⟨u₁, u₄⟩ ⟨u₂, u₃⟩)`.

The profiles need not have disjoint supports, so their compensated integrals need not be
independent. `Poisson/CompensatedProductMoments.lean` extends the identities to bounded
square-integrable profiles.

## Main definitions

* `LevyStochCalc.Poisson.compensatedProduct` — the compensated product of two mark profiles over
  a step.
* `LevyStochCalc.Poisson.SimpleProfile.withCoeff` — the simple profile on the mark sets of a given
  one carrying new coefficients.

## Main statements

* `LevyStochCalc.Poisson.SimpleProfile.exists_refinement` — a common refinement of finitely many
  simple mark profiles.
* `LevyStochCalc.Poisson.SimpleProfile.compensatedProduct_withCoeff_ae_eq` — on a common family
  the compensated product is the quadratic element of the strips.
* `LevyStochCalc.Poisson.SimpleProfile.memLp_compensatedProduct`,
  `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct` — square integrability and the
  mean at simple profiles.
* `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct_mul` — the Gram at simple
  profiles.
* `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct_mul_compensatedProfile` —
  orthogonality to the first chaos at simple profiles.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The compensated product of two mark profiles over the step `(a, b]`,
`J(f) J(g) − J(f g) − (b − a) ∫ f g dν` with `J` the compensated integral over the step. It is
meant for bounded square-integrable profiles, whose product is again bounded and square
integrable. -/
noncomputable def compensatedProduct (N : PoissonRandomMeasure P ν) (f g : E → ℝ) (a b : ℝ)
    (ω : Ω) : ℝ :=
  compensatedProfile N f a b ω * compensatedProfile N g a b ω
    - compensatedProfile N (fun e => f e * g e) a b ω - (b - a) * ∫ e, f e * g e ∂ν
namespace SimpleProfile

/-- The simple mark profile on the mark sets of `H` carrying the coefficients `c`. -/
def withCoeff (H : SimpleProfile E ν) (c : Fin H.K → ℝ) : SimpleProfile E ν where
  K := H.K
  B := H.B
  B_measurable := H.B_measurable
  B_disjoint := H.B_disjoint
  B_finite := H.B_finite
  c := c
/-! ### The compensated product on a common family -/

/-! ### The compensated product of simple profiles -/

end SimpleProfile

end LevyStochCalc.Poisson


