-- Prove2me | Definitions.Def_StochIneqPO_DBar_meetPath
-- name    : StochIneqPO_DBar_meetPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:30:59.735423+00:00
-- url     : https://prove2.me/theorems/5eb521f6-7990-45ea-89dc-20af5b0e5108
-- title:
--   Proof of Theorem 8, p. 910 — coordinatewise meet of two real paths
-- statement:
--   For two real-valued paths $\omega_1,\omega_2$, their **coordinatewise meet** $\varphi(\omega_1,\omega_2)$ is
--
--   $$\varphi(\omega_1,\omega_2)^n=\min\{\omega_1^n,\omega_2^n\}\qquad(n\in\mathbb Z).$$
--
--   Pushing a stationary coupling forward through this map produces the common lower law used in Theorem 8.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), proof of Theorem 8, p. 910 (PDF p. 12)

import Mathlib

namespace StochIneqPO.DBar

/-- The coordinatewise minimum `φ` used on p. 910. -/
def meetPath (z : (ℤ → ℝ) × (ℤ → ℝ)) (n : ℤ) : ℝ := min (z.1 n) (z.2 n)

end StochIneqPO.DBar


