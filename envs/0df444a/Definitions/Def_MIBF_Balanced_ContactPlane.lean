-- Prove2me | Definitions.Def_MIBF_Balanced_ContactPlane
-- name    : MIBF_Balanced_ContactPlane
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:58:00.940581+00:00
-- url     : https://prove2.me/theorems/c7847ea0-14e5-40da-a40a-77d67bcb7ed1
-- title:
--   The contact-plane gap $Q_c(x,y)=j(x,y)-c(y-x)+Ah(x)+Dh(y)$ (nats)
-- statement:
--   Natural logarithms throughout. For real coefficients $A$, $D$, $c$ and $x,y\in[0,1]$, the **contact-plane gap** is
--   $$Q_c(x,y)=j_e(x,y)-c\,(y-x)+A\,h(x)+D\,h(y),$$
--   where $h(t)=-t\ln t-(1-t)\ln(1-t)$ is the binary entropy in nats and $j_e$ is the extended Jeffreys cost in nats (`edgeCostNat`: the interior formula on $(0,1)^2$, $0$ at $(0,0)$ and $(1,1)$, $+\infty$ at every other boundary point). Thus $Q_c=+\infty$ at the boundary points other than the two diagonal corners. Geometrically $j_e(x,y)\ge c(y-x)-Ah(x)-Dh(y)$ says that a plane in the coordinates $(x,y,h(x),h(y))$ lies below the cost; integrating it against a law turns the pointwise coordinates into the four prescribed moments.
--
--   **Formalization Note** `contactGap A D c x y` is extended-real valued: the real part $-c(y-x)+Ah(x)+Dh(y)$ is added to the $[0,+\infty]$-valued cost, so no $\infty-\infty$ occurs.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), p. 12, Theorem 4.6, eq. (25)

import Mathlib
import Definitions.Def_MIBF_Balanced_EdgeValue

namespace MIBF.Balanced

/-- The contact-plane gap in nats,
`Q_c(x, y) = j(x, y) - c (y - x) + A h(x) + D h(y)`, with `j` the extended Jeffreys
cost `edgeCostNat` (so `Q_c = +∞` wherever `j = +∞`) and `h = Real.binEntropy`. -/
noncomputable def contactGap (A D c x y : ℝ) : EReal :=
  ((edgeCostNat x y : ENNReal) : EReal) +
    ((-(c * (y - x)) + A * Real.binEntropy x + D * Real.binEntropy y : ℝ) : EReal)

end MIBF.Balanced


