-- Prove2me | Definitions.Def_LogRegretOCO_ONS_onsBeta
-- name    : LogRegretOCO_ONS_onsBeta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:57:16.140213+00:00
-- url     : https://prove2.me/theorems/493542f9-6d76-49a8-9a1f-95a452b512b3
-- title:
--   Online Newton Step parameter $\beta = \tfrac12\min\{1/(4GD), \alpha\}$
-- statement:
--   For real numbers $G, D, \alpha$, the **step parameter of Online Newton Step** is
--   $$
--   \beta = \tfrac12 \min\Bigl\{\tfrac{1}{4GD}, \alpha\Bigr\},
--   $$
--   where $G$ bounds the gradients of the losses, $D$ bounds the diameter of the decision set and $\alpha$ is the exp-concavity constant. It sets the length $1/\beta$ of the Newton step and enters the regret bound through $1/\beta \le 8(GD + 1/\alpha)$.
--
--   **Formalization Note** Real division; every theorem using $\beta$ assumes $G, D, \alpha > 0$, so $\beta > 0$.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Machine Learning 69 (2007) 169–192, doi:10.1007/s10994-007-5016-8, Fig. 2, p. 176 (PDF p. 8)

import Mathlib

namespace LogRegretOCO.ONS

/-- **The ONS parameter `β = ½ min{1/(4GD), α}`.**
Hazan, Agarwal, Kale, *Logarithmic regret algorithms for online convex optimization*,
Machine Learning 69 (2007) 169–192, Fig. 2, p. 176: "Let β = 1/2 min{1/(4GD), α}".

**Formalization Note.** Real division; the theorems that use `onsBeta G D α` assume
`0 < G`, `0 < D`, `0 < α`, so `1/(4GD)` is the true quotient and `β > 0`. -/
noncomputable def onsBeta (G D α : ℝ) : ℝ :=
  (1 / 2) * min (1 / (4 * G * D)) α

end LogRegretOCO.ONS


