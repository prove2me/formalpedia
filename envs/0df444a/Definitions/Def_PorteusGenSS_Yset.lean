-- Prove2me | Definitions.Def_PorteusGenSS_Yset
-- name    : PorteusGenSS_Yset
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:16:13.885569+00:00
-- url     : https://prove2.me/theorems/8951a7a3-25f2-499e-b03e-0946281b2a34
-- title:
--   Optimal order-up-to levels $Y_n(x)$
-- statement:
--   Given the ordering cost $c$ and a function $h$ (the expected cost-to-go $h_n$ after ordering), $Y_n(x)$ is the set of optimal levels after ordering from $x$:
--
--   $$
--   Y_n(x)=\{S\ge x:\ c(S-x)+h(S)\le c(y-x)+h(y)\ \text{for all } y\ge x\}.
--   $$
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §III, p. 414 (unnumbered)

import Mathlib

namespace PorteusGenSS

/-- **The set Yₙ(x) of optimal order-up-to levels.**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §III, p. 414 (unnumbered): "Let Yn(x) denote the set of optimal levels of inventory after
ordering when the level of inventory before ordering is x. That is, if S ∈ Yn(x), then S ≥ x and
c(S − x) + hn(S) ≤ c(y − x) + hn(y) for all y ≥ x."

`Yset c h x` is the set of `S ≥ x` with `c(S − x) + h(S) ≤ c(y − x) + h(y)` for every `y ≥ x`.
With `h = hₙ` it is the paper's `Yₙ(x)`.

**Formalization Note.** The set is defined for a general function `h`; the mission instantiates
`h` with `hₙ` (`hFn`). `c` is evaluated only at arguments `≥ 0`. -/
def Yset (c h : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {S | x ≤ S ∧ ∀ y : ℝ, x ≤ y → c (S - x) + h S ≤ c (y - x) + h y}

end PorteusGenSS


