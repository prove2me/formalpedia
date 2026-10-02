-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
-- name    : DiscreteConvex_IntegralConvexityC_IntegrallyConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:11:16.82057+00:00
-- url     : https://prove2.me/theorems/0357c767-0bbd-4d17-bdd4-7a4ca4021bec
-- title:
--   Integral convexity of a function
-- statement:
--   $\tilde f(x)=\bar f(x)$ for all $x\in\mathbb R^n$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.94, Eq. (3.64).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.94, Eq. (3.64)

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ConvexClosure
import Definitions.Def_DiscreteConvex_IntegralConvexityC_LocalConvexExtension

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.94, Eq. (3.64): integral convexity of a
function, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `f` is **integrally convex** if `f̃(x) = f̄(x)` for all `x ∈ Rⁿ` (Eq. (3.64)). -/
noncomputable def IntegrallyConvex {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : Fin n → ℝ, LocalConvexExtension f x = ConvexClosure f x

end DiscreteConvex.IntegralConvexityC


