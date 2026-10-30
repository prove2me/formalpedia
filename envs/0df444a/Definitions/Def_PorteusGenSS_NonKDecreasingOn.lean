-- Prove2me | Definitions.Def_PorteusGenSS_NonKDecreasingOn
-- name    : PorteusGenSS_NonKDecreasingOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:07:59.528963+00:00
-- url     : https://prove2.me/theorems/711bfb76-c123-451e-bfca-51d24d6e6596
-- title:
--   Non-$K$-decreasing function on a set
-- statement:
--   Let $K\in\mathbb R$, $f:\mathbb R\to\mathbb R$ and $X\subseteq\mathbb R$. The function $f$ is **non-$K$-decreasing on $X$** if
--
--   $$
--   f(x)\le f(y)+K\qquad\text{for all }x,y\in X\text{ with }x\le y .
--   $$
--
--   For $K=0$ this is exactly "nondecreasing on $X$". The notion measures how far a function may drop when moving right, and is the basic regularity class behind (generalized) $(s,S)$ policies in inventory theory.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 1, p. 414

import Mathlib

namespace PorteusGenSS

/-- **Non-K-decreasing function (Definition 1).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 1, p. 414:
"A function f is non-K-decreasing on a domain X if f(x) ≤ f(y) + K for x, y ∈ X and x ≤ y."

`NonKDecreasingOn K f X` says `f x ≤ f y + K` whenever `x, y ∈ X` and `x ≤ y`.

**Formalization Note.** `K` is any real number, as in the definition; the paper uses it with
`K ≥ 0`. Functions are `ℝ → ℝ` (§X, p. 425: functions of a single real variable). -/
def NonKDecreasingOn (K : ℝ) (f : ℝ → ℝ) (X : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≤ y → f x ≤ f y + K

end PorteusGenSS


