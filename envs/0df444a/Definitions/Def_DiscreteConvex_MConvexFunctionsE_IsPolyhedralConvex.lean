-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsPolyhedralConvex
-- name    : DiscreteConvex_MConvexFunctionsE_IsPolyhedralConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:05:18.256634+00:00
-- url     : https://prove2.me/theorems/68d0f25f-e5d9-4a5b-9e08-e3740f05f693
-- title:
--   Polyhedral convexity of a function
-- statement:
--   $g$ is polyhedral convex: its epigraph $\{(x,t) : g(x)\le t\}$, read inside $\mathbb{R}^{V\cup\{*\}}$ with $*$ the value coordinate, is a polyhedron.
--
--   Theorems 6.63 and 6.64 are stated for the book's polyhedral class $M[\mathbb{R}\to\mathbb{R}]$, not for every function satisfying the bare exchange axiom (M-EXC[R]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §6.11.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §6.11

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsPolyhedronW

namespace DiscreteConvex.MConvexFunctionsE

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `g` is polyhedral convex: its epigraph, inside `(Option V) → ℝ` with `none` the value
coordinate, is a polyhedron. Murota, *Discrete Convex Analysis*, SIAM 2003, §6.11: Theorems 6.63
and 6.64 are about the polyhedral class `M[R→R]`, not about every function satisfying the bare
exchange axiom. -/
def IsPolyhedralConvex (g : (V → ℝ) → WithTop ℝ) : Prop :=
  IsPolyhedronW (W := Option V)
    {p : Option V → ℝ | g (fun v => p (some v)) ≤ ((p none : ℝ) : WithTop ℝ)}

end DiscreteConvex.MConvexFunctionsE


