-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexity_ConvexExtensible
-- name    : DiscreteConvex_IntegralConvexity_ConvexExtensible
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:49:40.37256+00:00
-- url     : https://prove2.me/theorems/f727e3fd-0410-4e84-8009-8f828a79c4d9
-- title:
--   Convex extensibility (Eq. 3.57)
-- statement:
--   $f : \mathbb Z^n \to \mathbb R \cup \{+\infty\}$ is **convex extensible** if its convex closure $\bar f$ agrees with $f$ on every integer point (Eq. (3.57)): $\bar f(x) = f(x)$ for $x \in \mathbb Z^n$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.57).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.57)

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexity_ConvexClosure

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93, Eq. (3.57): a function is convex
extensible if its convex closure agrees with it on the integer lattice, in
`DiscreteConvex.IntegralConvexity`.
-/

namespace DiscreteConvex.IntegralConvexity

/-- `f : Zⁿ → R ∪ {+∞}` is **convex extensible** if its convex closure `f̄` agrees with `f` on
every integer point (Eq. (3.57)): `f̄(x) = f(x)` for `x ∈ Zⁿ`. -/
noncomputable def ConvexExtensible {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : Fin n → ℤ, ConvexClosure f (fun i => (x i : ℝ)) = WithBot.some (f x)

end DiscreteConvex.IntegralConvexity


