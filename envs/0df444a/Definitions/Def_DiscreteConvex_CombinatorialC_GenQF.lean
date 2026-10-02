-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_GenQF
-- name    : DiscreteConvex_CombinatorialC_GenQF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:41:39.462499+00:00
-- url     : https://prove2.me/theorems/d51fc69e-4cc7-46aa-bf6a-7232fb2002bc
-- title:
--   Quadratic form restricted to a subspace
-- statement:
--   $g(p)=\tfrac12p^\top Lp$ for $p\in K$, $+\infty$ otherwise.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.73, Eqs. (2.24)-(2.25).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.73, Eqs. (2.24)-(2.25)

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_QF

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.73, Eqs. (2.24)-(2.25): the quadratic form
restricted to a subspace (`+∞` outside it), in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

open Classical in
/-- `g(p) = (1/2)pᵀLp` for `p ∈ K`, `+∞` otherwise (Eq. (2.24), also used for `f` in
Eq. (2.25) with `M`, `H` in place of `L`, `K`). -/
noncomputable def GenQF {V : Type*} [Fintype V] (L : Matrix V V ℝ) (K : Set (V → ℝ))
    (p : V → ℝ) : WithTop ℝ :=
  if p ∈ K then (QF L p : WithTop ℝ) else ⊤

end DiscreteConvex.CombinatorialC


