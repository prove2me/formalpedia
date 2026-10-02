-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexity_IntegrallyConvex
-- name    : DiscreteConvex_IntegralConvexity_IntegrallyConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:50:29.220975+00:00
-- url     : https://prove2.me/theorems/0f5a34d8-2192-4592-bb21-0b6bbe2d3657
-- title:
--   Integral convexity (Eq. 3.64)
-- statement:
--   $f : \mathbb Z^n \to \mathbb R \cup \{+\infty\}$ is **integrally convex** if its local convex extension $\tilde f$ agrees everywhere with its convex closure $\bar f$ (Eq. (3.64)): $\tilde f(x) = \bar f(x)$ for all $x \in \mathbb R^n$. This is the book's own equivalent restatement of "$\tilde f$ is convex on all of $\mathbb R^n$".
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.94, Eq. (3.64).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.94, Eq. (3.64)

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexity_ConvexClosure
import Definitions.Def_DiscreteConvex_IntegralConvexity_LocalConvexExtension

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.94, Eq. (3.64): a function is integrally
convex if its local convex extension agrees everywhere with its convex closure, in
`DiscreteConvex.IntegralConvexity`.
-/

namespace DiscreteConvex.IntegralConvexity

/-- `f : Zⁿ → R ∪ {+∞}` is **integrally convex** if its local convex extension `f̃` agrees with
its convex closure `f̄` at every real point (Eq. (3.64)): `f̃(x) = f̄(x)` for all `x ∈ Rⁿ`. This
is the book's own equivalent restatement of "`f̃` is convex on all of `Rⁿ`". -/
noncomputable def IntegrallyConvex {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : Fin n → ℝ, LocalConvexExtension f x = ConvexClosure f x

end DiscreteConvex.IntegralConvexity


