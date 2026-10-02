-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexity_HoleFree
-- name    : DiscreteConvex_IntegralConvexity_HoleFree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:48:41.018775+00:00
-- url     : https://prove2.me/theorems/de0a7985-5786-4330-93f7-24a231745817
-- title:
--   Hole-free discrete set (Eq. 3.50)
-- statement:
--   A discrete set $S \subseteq \mathbb Z^n$ is **hole free** (Eq. (3.50)) if $S = \bar S \cap \mathbb Z^n$: every integer point of the real convex hull of $S$ already belongs to $S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90, Eq. (3.50).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90, Eq. (3.50)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.90, Eq. (3.50): the hole-free property of a
discrete set, in `DiscreteConvex.IntegralConvexity`.
-/

namespace DiscreteConvex.IntegralConvexity

/-- A discrete set `S ⊆ Zⁿ` is **hole free** (Eq. (3.50)) if `S = S̄ ∩ Zⁿ`, i.e. every integer
point of the real convex hull of (the real embedding of) `S` already belongs to `S`. -/
def HoleFree {n : ℕ} (S : Set (Fin n → ℤ)) : Prop :=
  ∀ y : Fin n → ℤ,
    y ∈ S ↔ (fun i => (y i : ℝ)) ∈ convexHull ℝ ((fun z : Fin n → ℤ => (fun i => (z i : ℝ))) '' S)

end DiscreteConvex.IntegralConvexity


