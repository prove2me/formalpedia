-- Prove2me | Definitions.Def_WassersteinDRO_Gelbrich_worstCaseRisk
-- name    : WassersteinDRO_Gelbrich_worstCaseRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:26:56.974776+00:00
-- url     : https://prove2.me/theorems/4b881681-a2da-42f4-a89c-6e6f82c47d23
-- title:
--   Worst-case risk over a Wasserstein ball
-- statement:
--   The worst-case risk of a loss function $\ell$ over the Wasserstein ambiguity set
--   $B_{\varepsilon,p}(\hat P_N)$ is $\sup_{Q \in B_{\varepsilon,p}(\hat P_N)} E_Q[\ell(\xi)]$,
--   valued in the extended reals and restricted to distributions under which $\ell$ is integrable.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, eq. (6), p. 6

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_ambiguitySet
import Definitions.Def_WassersteinDRO_Gelbrich_nominalRisk

open MeasureTheory

namespace WassersteinDRO.Gelbrich

/-- The worst-case risk, Kuhn et al. 2019, p. 6, eq. (6). Redefined locally in this chapter's
own namespace; see `Def_WassersteinDRO_Gelbrich_wassersteinDistance` for why. Valued in
`EReal` and guarded by `Integrable ℓ Q`, matching `01-duality`'s conventions (avoids Mathlib's
junk value `0` for an unbounded or non-integrable supremum). -/
noncomputable def worstCaseRisk {m : ℕ} (ε p : ℝ) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
    (PN : Measure (EuclideanSpace ℝ (Fin m))) (ℓ : EuclideanSpace ℝ (Fin m) → ℝ) : EReal :=
  ⨆ (Q : Measure (EuclideanSpace ℝ (Fin m))) (_ : Q ∈ ambiguitySet ε p Ξ PN) (_ : Integrable ℓ Q),
    (nominalRisk Q ℓ : EReal)

end WassersteinDRO.Gelbrich


