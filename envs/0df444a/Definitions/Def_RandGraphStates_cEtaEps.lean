-- Prove2me | Definitions.Def_RandGraphStates_cEtaEps
-- name    : RandGraphStates_cEtaEps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:58.204425+00:00
-- url     : https://prove2.me/theorems/7f1aff80-d557-4f4d-bec2-b2bdf7636c93
-- title:
--   The constant $c_{\eta,\varepsilon}$
-- statement:
--   With $H(x)=-x\log_2 x-(1-x)\log_2(1-x)$ the entropy function in bits (§2.1, p.4), for $0<\varepsilon<\eta<1/2$,
--   $$
--   c_{\eta,\varepsilon}:=\eta-\varepsilon-H(\varepsilon).
--   $$
--   It is the exponential rate in the estimate for middle-weight kernel vectors.
--
--   **Formalization Note** $H$ is the published binary entropy in bits `SquashedKey.h₂` (Mathlib's `Real.binEntropy`, in nats, divided by $\log 2$), referenced rather than redefined; the goal theorem uses the same `SquashedKey.h₂` for the equation of $x_0$.
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), §4.2.4, p.26

import Mathlib
import Definitions.Def_SquashedKey_KeyBoundFunction

set_option autoImplicit false

namespace RandGraphStates

/-- `c_{η,ε} := η - ε - H(ε)`, for `0 < ε < η < 1/2`, where `H` is the entropy function in bits,
`H(x) = -x log₂ x - (1 - x) log₂(1 - x)` (§2.1, p.4).

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript
(November 2026), §4.2.4, p.26.

**Formalization Note.** `H` is the published `SquashedKey.h₂` (Mathlib's `Real.binEntropy`, in nats,
divided by `log 2`), which is the same function in bits. -/
noncomputable def cEtaEps (η ε : ℝ) : ℝ := η - ε - SquashedKey.h₂ ε

end RandGraphStates


