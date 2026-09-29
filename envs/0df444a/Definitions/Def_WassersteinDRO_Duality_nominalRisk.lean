-- Prove2me | Definitions.Def_WassersteinDRO_Duality_nominalRisk
-- name    : WassersteinDRO_Duality_nominalRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:15:16.26309+00:00
-- url     : https://prove2.me/theorems/22d3580b-e296-43ad-972e-61e7326107ff
-- title:
--   Nominal risk of a loss function
-- statement:
--   The nominal risk of a loss function $\ell$ under a probability distribution $Q$ is the
--   expectation $R(Q,\ell) = \mathbb{E}_Q[\ell(\xi)]$, the Bochner integral of $\ell$ against
--   $Q$.
-- source:
--   Kuhn et al. 2019, notation used throughout Section 1, e.g. p. 2-3

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Duality

/-- The nominal risk of a loss function `ℓ` under a distribution `Q`, Kuhn et al. 2019,
implicit throughout Section 1 (e.g. Example 2, p. 3): `R(Q,ℓ) = E_Q[ℓ(ξ)]`, the Bochner
expectation of `ℓ` under `Q`. Every theorem that uses this definition also carries an
`Integrable` hypothesis on `ℓ`, so Mathlib's junk value `0` for a non-integrable integrand
never enters a faithfulness-relevant equation or bound. -/
noncomputable def nominalRisk {E : Type*} [MeasurableSpace E] (Q : Measure E) (ℓ : E → ℝ) : ℝ :=
  ∫ x, ℓ x ∂Q

end WassersteinDRO.Duality


