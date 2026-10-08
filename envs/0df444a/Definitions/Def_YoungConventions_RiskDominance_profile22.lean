-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_profile22
-- name    : YoungConventions_RiskDominance_profile22
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:29.191538+00:00
-- url     : https://prove2.me/theorems/1cb8d30e-4787-4305-8ee1-104c9dfd290a
-- title:
--   The strategy pair $(2,2)$
-- statement:
--   The strategy-tuple in which both Row and Column play strategy $2$.
--
--   **Formalization Note** Strategy $2$ is `1 : Fin 2`.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 70

import Mathlib
import Definitions.Def_YoungConventions_RiskDominance_Strat2

namespace YoungConventions.RiskDominance

/-- **The strategy pair `(2, 2)`.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 70 (PDF p. 15). Both players play the paper's
strategy `2`, which is `1 : Fin 2`. -/
def profile22 : (i : Fin 2) → Strat2 i := fun _ => (1 : Fin 2)

end YoungConventions.RiskDominance


