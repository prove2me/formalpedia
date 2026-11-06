-- Prove2me | Definitions.Def_MaxMinFracSched_maxDensity
-- name    : MaxMinFracSched_maxDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:53.369446+00:00
-- url     : https://prove2.me/theorems/3c762a0c-4890-4293-930f-8ad463371572
-- title:
--   Maximal work density $\rho^\star$
-- statement:
--   The **maximal density** of an instance $J$ is
--   $$\rho^\star_J=\sup\{\rho_J([L,R]) : L<R\}.$$
--
--   For a valid instance the supremum is finite and attained (Corollary 3.4); an interval attaining it is a densest interval (Definition 3.2).
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Definition 3.2 and Corollary 3.4, pp.12–13 (PDF pp.14–15)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_workIn
import Definitions.Def_MaxMinFracSched_density

namespace MaxMinFracSched

/-- **The maximal density `ρ⋆`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Definition 3.2 (Densest interval), p.12 (PDF p.14): "An
interval I⋆ is called densest for an instance J if it maximizes ρJ(I) over all intervals I", and
Corollary 3.4, p.13: "the densest interval I⋆ has density ρ⋆".

`maxDensity J` is the supremum of `ρ_J([L, R])` over all nondegenerate intervals `L < R`.

**Formalization Note.** For a valid instance the set is bounded above (an interval containing a
job is at least as long as that job's window) and the supremum is attained (Corollary 3.4), so
`ρ⋆` is the maximal density. -/
noncomputable def maxDensity (J : Finset Job) : ℝ :=
  sSup {ρ : ℝ | ∃ L R : ℝ, L < R ∧ ρ = density J L R}

end MaxMinFracSched


