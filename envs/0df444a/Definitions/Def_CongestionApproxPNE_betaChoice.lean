-- Prove2me | Definitions.Def_CongestionApproxPNE_betaChoice
-- name    : CongestionApproxPNE_betaChoice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:12.667499+00:00
-- url     : https://prove2.me/theorems/c9d3c520-7608-438c-875a-60a3343e510e
-- title:
--   The coefficient of the parameter choice, $\beta=1/(d^{k/(2(k+1))}(1+w)^d)$
-- statement:
--   For an integer $d$, with $k=k_d$ and $w=\ln d/(2d)$, the coefficient of the non-hub costs in the parameter choice of the proof of Theorem 1 is
--
--   $$
--   \beta=\frac{1}{d^{\frac{k}{2(k+1)}}\,(1+w)^d}.
--   $$
--
--   **Formalization Note** $d^{k/(2(k+1))}$ is the real power `Real.rpow`.
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, proof of Theorem 1, p.6 (PDF p.7), choice of β

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd
import Definitions.Def_CongestionApproxPNE_wChoice

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **The coefficient of the parameter choice, `β = 1 / (d^{k/(2(k+1))} (1+w)^d)`.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, arXiv:2002.07466v3, proof of Theorem 1,
p.6, with `k = k_d` and `w = ln d/(2d)`.

**Formalization Note** `d^{k/(2(k+1))}` is the real power `Real.rpow`; `(1+w)^d` is a natural
power. -/
noncomputable def betaChoice (d : ℕ) : ℝ :=
  1 / ((d : ℝ) ^ ((kd d : ℝ) / (2 * ((kd d : ℝ) + 1))) * (1 + wChoice d) ^ d)

end CongestionApproxPNE


