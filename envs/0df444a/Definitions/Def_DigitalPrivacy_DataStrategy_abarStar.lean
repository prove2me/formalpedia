-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_abarStar
-- name    : DigitalPrivacy_DataStrategy_abarStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:03:28.295615+00:00
-- url     : https://prove2.me/theorems/5c28c1c4-58e7-4a20-9d5e-70ce3c575816
-- title:
--   Equilibrium activity $\bar a^*(\xi,C)$, display (3)
-- statement:
--   The equilibrium average users' activity is
--
--   $$\bar a^*(\xi,C)=\frac{C(1+\rho\xi)}{C(1-\beta)+\xi^2},$$
--
--   and $\bar a^*(0,C)=\frac1{1-\beta}$.
--
--   It is the users' activity the business anticipates when it chooses $(\xi,C)$; the business's profit is evaluated at it.
--
--   **Formalization Note** For $\xi=0$ the value is set to $1/(1-\beta)$, which equals (3) whenever $C>0$; at $(\xi,C)=(0,0)$ display (3) reads $0/0$, and the paper's proof uses the value $1/(1-\beta)$ there (profit $\pi_0$, p. 30; $\bar a_c$, p. 32). For $\xi\ne0$ it is (3) literally, which is $0$ at $C=0$.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), Proposition 1, display (3), p. 10 (PDF 11); value at ξ = 0 from App. A.2, p. 30 and App. A.3, p. 32

import Mathlib

namespace DigitalPrivacy.DataStrategy

/-- **Equilibrium users' activity `ā*(ξ, C) = C(1 + ρξ)/(C(1 − β) + ξ²)`, display (3).**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), Proposition 1, display (3), p. 10 (PDF 11): "ā∗(ξ, C) = C(1 + ρξ)/(C(1 − β) + ξ²)".

**Formalization Note.** At `ξ = 0` the value is set to `1/(1 − β)`. This equals (3) for every
`C > 0`; at `(ξ, C) = (0, 0)` display (3) is `0/0`, and the paper's proof gives that point the
profit `π₀ = (1 − P)/(1 − β)` (App. A.2, p. 30) and writes `ā_c = lim ā*(ξ*, C*) = 1/(1 − β)`
(App. A.3, p. 32): with `ξ = 0` users ignore the adversaries and play `ā = 1/(1 − β)`. For
`ξ ≠ 0` the value is (3) literally (it is `0` at `C = 0`, the limit of (3) as `C ↓ 0`). -/
noncomputable def abarStar (β ρ ξ C : ℝ) : ℝ :=
  if ξ = 0 then 1 / (1 - β) else C * (1 + ρ * ξ) / (C * (1 - β) + ξ ^ 2)

end DigitalPrivacy.DataStrategy


