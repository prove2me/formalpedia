-- Prove2me | Definitions.Def_LogRegretOCO_ONS_onsEps
-- name    : LogRegretOCO_ONS_onsEps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:57:43.493317+00:00
-- url     : https://prove2.me/theorems/1e428c78-fcb9-4ccf-bbe9-30f3f9addb37
-- title:
--   Online Newton Step regularization $\varepsilon = 1/(\beta^2 D^2)$
-- statement:
--   For real numbers $G, D, \alpha$, with $\beta = \tfrac12\min\{\tfrac{1}{4GD}, \alpha\}$, the **regularization parameter of Online Newton Step** is
--   $$
--   \varepsilon = \frac{1}{\beta^2 D^2}.
--   $$
--   It is the multiple of the identity added to the accumulated gradient outer products in the matrix $A_t$; the choice makes the initial term $\tfrac{\varepsilon}{2} D^2 \beta$ of the regret analysis equal to $\tfrac{1}{2\beta}$.
--
--   **Formalization Note** Real division; every theorem using $\varepsilon$ assumes $G, D, \alpha > 0$, so $\varepsilon > 0$.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Machine Learning 69 (2007) 169–192, doi:10.1007/s10994-007-5016-8, Fig. 2, p. 176 (PDF p. 8)

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_onsBeta

namespace LogRegretOCO.ONS

/-- **The ONS regularization `ε = 1/(β²D²)`.**
Hazan, Agarwal, Kale, *Logarithmic regret algorithms for online convex optimization*,
Machine Learning 69 (2007) 169–192, Fig. 2, p. 176: "ε = 1/(β²D²)", with `β = onsBeta G D α`.

**Formalization Note.** Real division; the theorems that use it assume `0 < G`, `0 < D`,
`0 < α`, so `β > 0` and `ε > 0`. -/
noncomputable def onsEps (G D α : ℝ) : ℝ :=
  1 / ((onsBeta G D α) ^ 2 * D ^ 2)

end LogRegretOCO.ONS


