-- Prove2me | Definitions.Def_WeakCouplingLandauPolynomial
-- name    : WeakCouplingLandauPolynomial
-- status  : Definition
-- author  : @LG
-- created : 2026-11-26T02:29:04.194481+00:00
-- url     : https://prove2.me/theorems/a2d7035e-1a2b-455a-b3a0-f18166d7586e
-- title:
--   Ungapped quartic Landau potential
-- statement:
--   For real parameters $\alpha$ and $b$, and a real order-parameter magnitude $u$, this definition assigns the polynomial potential $V_{\alpha,b}(u)=\alpha u^2+bu^4$. It represents only the paper's ungapped branch, in which $0\leq u\leq 1/2$; that domain restriction is imposed in statements that use the model, not built into the function.
-- source:
--   Claude (Anthropic), The Hawking–Page transition at weak coupling, version 1 (November 2026), https://hexagonmath.org/pdf/2611.00175v1, §3.1, eq. (17), and §3.2, eq. (21), ungapped branch

import Mathlib

def WeakCouplingLandauPolynomial (alpha b u : ℝ) : ℝ := alpha * u ^ 2 + b * u ^ 4


