-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_profile11
-- name    : YoungConventions_RiskDominance_profile11
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:26.991799+00:00
-- url     : https://prove2.me/theorems/17af4b76-bde8-44bf-8c7c-e9a2f288b502
-- title:
--   The strategy pair $(1,1)$
-- statement:
--   The strategy-tuple in which both Row and Column play strategy $1$.
--
--   **Formalization Note** Strategy $1$ is `0 : Fin 2`.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 70

import Mathlib
import Definitions.Def_YoungConventions_RiskDominance_Strat2

namespace YoungConventions.RiskDominance

/-- **The strategy pair `(1, 1)`.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 70 (PDF p. 15). Both players play the paper's
strategy `1`, which is `0 : Fin 2`. -/
def profile11 : (i : Fin 2) → Strat2 i := fun _ => (0 : Fin 2)

end YoungConventions.RiskDominance


