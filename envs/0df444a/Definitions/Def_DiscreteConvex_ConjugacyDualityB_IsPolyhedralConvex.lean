-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsPolyhedralConvex
-- name    : DiscreteConvex_ConjugacyDualityB_IsPolyhedralConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:30:56.178678+00:00
-- url     : https://prove2.me/theorems/0d80e030-0d8c-45ce-93c1-256d803f48a2
-- title:
--   Polyhedral convexity of a function
-- statement:
--   $g$ is polyhedral convex: its epigraph $\{(x,t) : g(x)\le t\}$, read inside $\mathbb{R}^{V\cup\{*\}}$ with $*$ the value coordinate, is a polyhedron.
--
--   The conjugacy theorem is stated for *polyhedral* M-convex and L-convex functions; the bare axioms (M-EXC[R]), (SBF[R]) and (TRF[R]) do not even force closedness, and biconjugacy fails without it.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §8.1, Theorem 8.4.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §8.1, Theorem 8.4

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsPolyhedronW

namespace DiscreteConvex.ConjugacyDualityB

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `g` is polyhedral convex: its epigraph, inside `(Option V) → ℝ` with `none` the value
coordinate, is a polyhedron. Murota, *Discrete Convex Analysis*, SIAM 2003, §8.1 states the
conjugacy theorem for *polyhedral* M-convex and L-convex functions; the bare axioms
(M-EXC[R]), (SBF[R]) and (TRF[R]) do not even force closedness. -/
def IsPolyhedralConvex (g : (V → ℝ) → WithTop ℝ) : Prop :=
  IsPolyhedronW (W := Option V)
    {p : Option V → ℝ | g (fun v => p (some v)) ≤ ((p none : ℝ) : WithTop ℝ)}

end DiscreteConvex.ConjugacyDualityB


