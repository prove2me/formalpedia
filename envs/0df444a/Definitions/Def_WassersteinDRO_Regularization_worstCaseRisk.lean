-- Prove2me | Definitions.Def_WassersteinDRO_Regularization_worstCaseRisk
-- name    : WassersteinDRO_Regularization_worstCaseRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:39:36.222985+00:00
-- url     : https://prove2.me/theorems/c1a3db9f-d3fe-4e77-9bb7-ffb90d76bdbf
-- title:
--   Worst-case risk over a Wasserstein ball
-- statement:
--   The worst-case risk of a loss function $\ell$ over the Wasserstein ambiguity set
--   $B_{\varepsilon,p}(\hat P_N)$ is $\sup_{Q \in B_{\varepsilon,p}(\hat P_N)} E_Q[\ell(\xi)]$,
--   valued in the extended reals and restricted to distributions under which $\ell$ is integrable.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, eq. (6), p. 6

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_ambiguitySet
import Definitions.Def_WassersteinDRO_Regularization_nominalRisk

open MeasureTheory

namespace WassersteinDRO.Regularization

/-- The worst-case risk, Kuhn et al. 2019, p. 6, eq. (6). Redefined locally in this
chapter's own namespace; see `Def_WassersteinDRO_Regularization_wassersteinDistance` for
why. Valued in `EReal` and guarded by `Integrable ℓ Q`, matching `01-duality`'s conventions
(avoids Mathlib's junk value `0` for an unbounded or non-integrable supremum). -/
noncomputable def worstCaseRisk {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (Ξ : Set E) (PN : Measure E) (ℓ : E → ℝ) : EReal :=
  ⨆ (Q : Measure E) (_ : Q ∈ ambiguitySet ε p Ξ PN) (_ : Integrable ℓ Q),
    (nominalRisk Q ℓ : EReal)

end WassersteinDRO.Regularization


