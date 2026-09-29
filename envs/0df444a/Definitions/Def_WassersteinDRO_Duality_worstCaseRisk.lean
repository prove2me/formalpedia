-- Prove2me | Definitions.Def_WassersteinDRO_Duality_worstCaseRisk
-- name    : WassersteinDRO_Duality_worstCaseRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:16:42.299829+00:00
-- url     : https://prove2.me/theorems/6216f6f7-9241-405f-9939-ed049cd3f13e
-- title:
--   Worst-case risk over a Wasserstein ambiguity set
-- statement:
--   The worst-case risk of a loss function $\ell$ over the Wasserstein ambiguity set
--   $B_{\varepsilon,p}(P_N)$ is
--   $$R_{\varepsilon,p}(P_N,\ell) = \sup_{Q \in B_{\varepsilon,p}(P_N)} R(Q,\ell),$$
--   the supremum of the nominal risk over the ambiguity set. It is valued in the extended
--   reals $[-\infty,\infty]$ so that an unbounded worst-case risk is recorded as $+\infty$
--   rather than collapsed to a finite junk value; among the candidate distributions $Q$ in
--   the ambiguity set, only those for which $\ell$ is $Q$-integrable contribute their
--   (well-defined) nominal risk to the supremum.
-- source:
--   Kuhn et al. 2019, p. 6, eq. (6)

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_ambiguitySet
import Definitions.Def_WassersteinDRO_Duality_nominalRisk

open MeasureTheory

namespace WassersteinDRO.Duality

/-- The worst-case risk, Kuhn et al. 2019, p. 6, eq. (6):
`Rε,p(PN,ℓ) = sup_{Q ∈ Bε,p(PN)} R(Q,ℓ)`, the supremum of the nominal risk over the
ambiguity set. Valued in `EReal` (rather than `ℝ`) so the supremum is a genuine least upper
bound with no junk value: Mathlib's real-valued `sSup`/`⨆` defaults to `0` on an unbounded or
empty family, which would silently misstate an unbounded worst-case risk as `0`. The
`Integrable` guard on `ℓ` under each candidate `Q` prevents Mathlib's separate junk value for
the Bochner integral of a non-integrable function (`0`) from contaminating the supremum. -/
noncomputable def worstCaseRisk {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (ε p : ℝ) (Ξ : Set E) (PN : Measure E) (ℓ : E → ℝ) : EReal :=
  ⨆ (Q : Measure E) (_ : Q ∈ ambiguitySet ε p Ξ PN) (_ : Integrable ℓ Q),
    (nominalRisk Q ℓ : EReal)

end WassersteinDRO.Duality


