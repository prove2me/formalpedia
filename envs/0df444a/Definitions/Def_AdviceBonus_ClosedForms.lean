-- Prove2me | Definitions.Def_AdviceBonus_ClosedForms
-- name    : AdviceBonus_ClosedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:38.236759+00:00
-- url     : https://prove2.me/theorems/e50a6ad5-c9d3-4827-97cb-f8825b000c82
-- title:
--   The function $H$ of (17) and the liability threshold $w^*_f$ of (18)
-- statement:
--   For a posterior distribution with density $g$ and c.d.f. $G$, put
--   $$
--   H(q)=\frac{G(q)}{g(q)}+\frac{1}{4g(1/2)\,[1-G(q)]^2+g(q)}. \qquad(17)
--   $$
--   For a price $p$, a unit cost $c$ and the solution $\bar q$ of (15), the liability threshold is
--   $$
--   w^*_f=\frac{p-c}{2H(\bar q)}. \qquad(18)
--   $$
--
--   Both expressions are named in Lemma 4 and Proposition 2: below $w^*_f$ the equilibrium commission $p-c-2wH(\bar q)$ is positive.
--
--   **Formalization Note** $w^*_f$ takes $\bar q$ as an argument; the statements that use it require $\bar q$ to solve (15).
-- source:
--   Honda–Inderst–Ottaviani, When Liability is Not Enough, SSRN 4125013 (May 2022), eq. (17), p.18; eq. (18), p.19

import Mathlib
import Definitions.Def_AdviceBonus_Model

namespace AdviceBonus

/-- The function `H` of (17), p.18:
`H(q) = G(q)/g(q) + 1/(4 g(1/2) [1 − G(q)]² + g(q))`. -/
noncomputable def H (D : Dist) (q : ℝ) : ℝ :=
  D.G q / D.g q + 1 / (4 * D.g (1 / 2) * (1 - D.G q) ^ 2 + D.g q)

/-- The liability threshold (18), p.19: `w*_f = (p − c)/(2 H(q̄))`, where `q̄` is the solution
of (15) (passed as the argument `qbar`). -/
noncomputable def wStar (D : Dist) (p c qbar : ℝ) : ℝ := (p - c) / (2 * H D qbar)

end AdviceBonus


