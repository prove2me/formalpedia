-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsPolyhedralConvex
-- name    : DiscreteConvex_MConvexFunctionsD_IsPolyhedralConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:51:15.931326+00:00
-- url     : https://prove2.me/theorems/c7ef846e-e363-452f-aa27-eae64fee17f3
-- title:
--   Polyhedral convexity of a function
-- statement:
--   $g$ is polyhedral convex: its epigraph $\{(x,t) : g(x)\le t\}$, read inside $\mathbb{R}^{V\cup\{*\}}$ with $*$ the value coordinate, is a polyhedron.
--
--   Theorem 6.52 and Proposition 6.53 are stated for the book's polyhedral class $M[\mathbb{R}\to\mathbb{R}]$, not for every function satisfying the bare exchange axiom (M-EXC[R]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §6.11.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §6.11

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsPolyhedronW

namespace DiscreteConvex.MConvexFunctionsD

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `g` is polyhedral convex: its epigraph, inside `(Option V) → ℝ` with `none` the value
coordinate, is a polyhedron. Murota, *Discrete Convex Analysis*, SIAM 2003, §6.11 states
Theorem 6.52 and Proposition 6.53 for the polyhedral class `M[R→R]`, not for every function
satisfying the bare exchange axiom. -/
def IsPolyhedralConvex (g : (V → ℝ) → WithTop ℝ) : Prop :=
  IsPolyhedronW (W := Option V)
    {p : Option V → ℝ | g (fun v => p (some v)) ≤ ((p none : ℝ) : WithTop ℝ)}

end DiscreteConvex.MConvexFunctionsD


