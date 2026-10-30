-- Prove2me | Definitions.Def_LightningNetwork_RateBounds_uniCost
-- name    : LightningNetwork_RateBounds_uniCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:45:32.917+00:00
-- url     : https://prove2.me/theorems/1a0b0e22-c1aa-4676-b783-862b56abb983
-- title:
--   Cost of a unidirectional channel, Theorem 1(i), eq. (1)
-- statement:
--   Node 1 pays node 2 one unit at each arrival of a Poisson process of rate $\lambda > 0$. A **unidirectional channel** of size $l$ holds a balance $l$ committed by the payer; when the balance is exhausted the channel is reset at cost $B$ and reopened with the same balance, and committed capital costs interest at the continuously compounded rate $r > 0$. By Theorem 1(i) of the paper its expected discounted cost is
--
--   $$
--   c^{0,l}(0,\lambda) \;=\; l + B\left(\left(\frac{r+\lambda}{\lambda}\right)^{l} - 1\right)^{-1}.
--   $$
--
--   This closed form is the cost of a unidirectional channel throughout the mission; Theorem 2(i) compares it with the on-chain cost $C\lambda/r$.
--
--   **Formalization Note** The closed form (1) is taken as the definition; that it equals the expected discounted cost of the Poisson channel model is the content of Theorem 1, which is not formalized here. The power is a real power, so the size $l$ is a real number; for $\lambda, r > 0$ the base exceeds $1$ and for $l > 0$ the bracket is positive.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, Theorem 1(i), eq. (1), p. 6

import Mathlib

namespace LightningNetwork.RateBounds

/-- **Cost of a unidirectional channel**, Theorem 1(i), display (1).
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, Theorem 1(i), eq. (1), p. 6:
"A unidirectional channel costs c^{0,l2}(0, λ2) = l2 + B(((r + λ2)/λ2)^{l2} − 1)^{−1}."

`uniCost B r lam l = l + B · (((r + lam)/lam)^l − 1)⁻¹`: the expected discounted cost of a
unidirectional channel of size (commitment) `l` carrying a Poisson stream of payments of rate
`lam`, when resetting the channel costs `B` and the interest rate is `r`.

**Formalization Note.** This is the closed form of (1), taken as the definition of the channel's
cost; the stochastic content of Theorem 1 (that (1) is the expected discounted cost of the Poisson
channel model of §3) is not formalized. The power is `Real.rpow`, so the commitment `l` is real;
for `0 < lam`, `0 < r` the base `(r + lam)/lam` exceeds `1`, and for `0 < l` the bracket is
positive (no junk value). -/
noncomputable def uniCost (B r lam l : ℝ) : ℝ :=
  l + B * (((r + lam) / lam) ^ l - 1)⁻¹

end LightningNetwork.RateBounds


