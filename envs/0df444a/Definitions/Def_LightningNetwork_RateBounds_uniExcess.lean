-- Prove2me | Definitions.Def_LightningNetwork_RateBounds_uniExcess
-- name    : LightningNetwork_RateBounds_uniExcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:47:23.35099+00:00
-- url     : https://prove2.me/theorems/e3f64547-4e6d-49c9-8d85-5fec057e4497
-- title:
--   The function $F(m)$ of the proof of Theorem 2(i)
-- statement:
--   For real parameters $\kappa$, $B$, $C$ and a channel size $m$, let
--
--   $$
--   F(m) \;=\; \frac{C}{1 - e^{\kappa}} + \frac{B}{e^{\kappa m} - 1} + m.
--   $$
--
--   With $\kappa = \log(1 + r/\lambda)$, i.e. $\lambda/r = (e^\kappa - 1)^{-1}$, $F(m)$ is the cost of a unidirectional channel of size $m$ minus the on-chain cost $C\lambda/r$, so a channel of some size is cheaper than on-chain settlement exactly when $F$ takes a negative value.
--
--   **Formalization Note** $\kappa$, $B$, $C$ are free real parameters; for $\kappa > 0$ and $m > 0$ no denominator vanishes.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), unnumbered display, p. 11

import Mathlib

namespace LightningNetwork.RateBounds

/-- **The function F of the proof of Theorem 2(i).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(i), unnumbered display, p. 11: "To find such an
infimum, denote by λ/r = (e^κ − 1)^{−1}, which allows to rewrite the function to minimize as
F(m) = C/(1 − e^κ) + B/(e^{κm} − 1) + m."

`uniExcess κ B C m = C/(1 − e^κ) + B/(e^{κ m} − 1) + m`: the excess of the cost of a
unidirectional channel of size `m` over the on-chain cost, written with `κ = log(1 + r/λ)`.

**Formalization Note.** `κ`, `B`, `C` are free real parameters; the paper's `κ = log(1 + r/λ)`
is positive. For `κ > 0` and `m > 0` no denominator vanishes. -/
noncomputable def uniExcess (κ B C m : ℝ) : ℝ :=
  C / (1 - Real.exp κ) + B / (Real.exp (κ * m) - 1) + m

end LightningNetwork.RateBounds


