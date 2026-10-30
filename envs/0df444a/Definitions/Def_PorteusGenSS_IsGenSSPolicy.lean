-- Prove2me | Definitions.Def_PorteusGenSS_IsGenSSPolicy
-- name    : PorteusGenSS_IsGenSSPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:15:59.143993+00:00
-- url     : https://prove2.me/theorems/6f52bfc6-6e0c-4c25-8709-3f5aacfdd740
-- title:
--   Generalized $(s,S)$ policy
-- statement:
--   An ordering policy $y:\mathbb R\to\mathbb R$ ($y(x)$ is the inventory level after ordering when the level before ordering is $x$) is a **generalized $(s,S)$ policy** if
--
--   1. $y(x)=x$ for $x\ge s$ (no order above $s$), and
--   2. $y(z)\ge y(x)\ge S\ge s$ whenever $z<x<s$ (below $s$, order up to at least $S$, and higher the lower the starting level).
--
--   An ordinary $(s,S)$ policy ($y\equiv S$ below $s$) is a special case.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 4, p. 415

import Mathlib

namespace PorteusGenSS

/-- **Generalized (s, S) policy (Definition 4).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 4, p. 415: "A generalized (s, S) policy is an ordering policy function y which
satisfies (i) y(x) = x for s ≤ x and (ii) y(z) ≥ y(x) ≥ S ≥ s for z < x < s."

`IsGenSSPolicy s S y` says `y x = x` for `x ≥ s`, and `y z ≥ y x ≥ S ≥ s` whenever
`z < x < s`.

**Formalization Note.** `y x` is the inventory level after ordering when the level before
ordering is `x`. The policy is not required to be measurable: by (ii) it is nonincreasing on
`(−∞, s)` and it is the identity on `[s, ∞)`, so it is measurable anyway (§X's convention). -/
def IsGenSSPolicy (s S : ℝ) (y : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, s ≤ x → y x = x) ∧
    ∀ z x : ℝ, z < x → x < s → y x ≤ y z ∧ S ≤ y x ∧ s ≤ S

end PorteusGenSS


