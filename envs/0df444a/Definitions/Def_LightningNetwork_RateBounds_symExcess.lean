-- Prove2me | Definitions.Def_LightningNetwork_RateBounds_symExcess
-- name    : LightningNetwork_RateBounds_symExcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:47:40.395997+00:00
-- url     : https://prove2.me/theorems/a99d1067-5475-4bcb-bf36-8283d8c11040
-- title:
--   Excess cost $G(l_1,l_2)$ of a symmetric bidirectional channel over on-chain
-- statement:
--   For real parameters $\alpha$, $B$, $C$ and commitments $(l_1, l_2)$, let
--
--   $$
--   G(l_1,l_2) \;=\; l_1 + l_2 + \frac{B\,(\alpha^{l_1} + \alpha^{l_2})}{(\alpha^{l_1} - 1)(\alpha^{l_2} - 1)} - \frac{2C\alpha}{(\alpha-1)^2}.
--   $$
--
--   With $\alpha = \alpha_+ = \bigl(r + 2\lambda + \sqrt{r(4\lambda+r)}\bigr)/(2\lambda)$, $G$ is the cost of a symmetric bidirectional channel with commitments $l_1, l_2$ minus the on-chain cost $2C\lambda/r$ of the two payment streams.
--
--   **Formalization Note** $G$ is a function of the pair $(l_1, l_2) \in \mathbb R^2$ so that its convexity can be stated; powers are real powers.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), unnumbered display, p. 11

import Mathlib

namespace LightningNetwork.RateBounds

/-- **Excess cost of a symmetric bidirectional channel over on-chain settlement.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), unnumbered display, p. 11: "Subtracting from
such cost the cost of on-chain transactions instead, which is 2Cλ/r, and rewriting λ/r in terms of
α, the difference is l1 + l2 + B(α^{l1} + α^{l2})/((α^{l1} − 1)(α^{l2} − 1)) − 2Cα/(α − 1)²."

`symExcess α B C (l1, l2) = l1 + l2 + B(α^{l1} + α^{l2})/((α^{l1} − 1)(α^{l2} − 1)) − 2Cα/(α − 1)²`.

**Formalization Note.** A function of the pair `(l1, l2) : ℝ × ℝ`, so that convexity in
`(l1, l2)` can be stated; powers are `Real.rpow`. `α`, `B`, `C` are free real parameters; the
paper's `α = α₊ > 1`. -/
noncomputable def symExcess (α B C : ℝ) (l : ℝ × ℝ) : ℝ :=
  l.1 + l.2 + B * (α ^ l.1 + α ^ l.2) / ((α ^ l.1 - 1) * (α ^ l.2 - 1)) - 2 * C * α / (α - 1) ^ 2

end LightningNetwork.RateBounds


