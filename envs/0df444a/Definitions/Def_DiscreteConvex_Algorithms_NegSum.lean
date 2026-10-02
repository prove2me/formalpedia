-- Prove2me | Definitions.Def_DiscreteConvex_Algorithms_NegSum
-- name    : DiscreteConvex_Algorithms_NegSum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:23:25.650508+00:00
-- url     : https://prove2.me/theorems/8ba113d9-961c-480f-be45-8ae1ff8a9018
-- title:
--   The negative-part sum $x^-(V)$ (Eqs. 10.10-10.11)
-- statement:
--   $x^-(V) = \sum_v \min(0, x(v))$, used in the min-max relation for the base polyhedron (Eqs. (10.10)-(10.11)).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, Eqs. (10.10)-(10.11).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, Eqs. (10.10)-(10.11)

import Mathlib

namespace DiscreteConvex.Algorithms

/-- `x⁻(V) = Σ_v min(0, x(v))`, used in the min-max relation for the base polyhedron
(Eqs. (10.10)-(10.11)). -/
noncomputable def NegSum {V : Type*} [Fintype V] (x : V → ℝ) : ℝ :=
  ∑ v, min 0 (x v)

end DiscreteConvex.Algorithms


