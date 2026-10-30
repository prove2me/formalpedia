-- Prove2me | Definitions.Def_PorteusGenSS_QuasiKConvex
-- name    : PorteusGenSS_QuasiKConvex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:11:46.141925+00:00
-- url     : https://prove2.me/theorems/75ac6514-94bf-47fb-9235-deea679cdcdc
-- title:
--   Quasi-$K$-convex function on $\mathbb R$
-- statement:
--   Let $K\in\mathbb R$. A function $f:\mathbb R\to\mathbb R$ is **quasi-$K$-convex** if
--
--   $$
--   f(\lambda x+(1-\lambda)y)\le\max\big(f(x),\,f(y)+K\big)\qquad\text{for all }x\le y,\ 0\le\lambda\le1 .
--   $$
--
--   It extends both quasi-convexity ($K=0$) and Scarf's $K$-convexity, and is the shape that makes generalized $(s,S)$ policies optimal.
--
--   **Formalization Note** The paper defines it on a convex set $X$; only $X=\mathbb R$ is used.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 10, p. 423

import Mathlib

namespace PorteusGenSS

/-- **Quasi-K-convex function on ℝ (Definition 10).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 10, p. 423: "A function f is quasi-K-convex on a convex set X if x, y ∈ X,
x ≤ y, and 0 ≤ λ ≤ 1 imply that (27) f(λx + (1 − λ)y) ≤ max (f(x), f(y) + K)."

`QuasiKConvex K f` says `f(λx + (1 − λ)y) ≤ max (f x) (f y + K)` for all `x ≤ y` and
`0 ≤ λ ≤ 1`.

**Formalization Note.** The convex set `X` is `ℝ`, the only case the paper uses (Lemma 9). -/
def QuasiKConvex (K : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x ≤ y → ∀ l : ℝ, 0 ≤ l → l ≤ 1 → f (l * x + (1 - l) * y) ≤ max (f x) (f y + K)

end PorteusGenSS


