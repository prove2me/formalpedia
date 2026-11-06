-- Prove2me | Definitions.Def_MatchedUCLB_chainPrefix
-- name    : MatchedUCLB_chainPrefix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:02.668223+00:00
-- url     : https://prove2.me/theorems/50d7d5e9-e579-46d4-a0ce-012eea42e8fc
-- title:
--   The chain prefix $U_{j,b}=\mathrm{span}\{v_j,u_{j,1},\dots,u_{j,b}\}$
-- statement:
--   For a starting direction $v$, chain directions $u_1,\dots,u_m$ and $0\le b\le m$, the **chain prefix** is the subspace
--
--   $$
--   U_b=\operatorname{span}\{v,u_1,\dots,u_b\}.
--   $$
--
--   It is called short when $b\le\lfloor m/4\rfloor$.
--
--   **Formalization Note** With $0$-based chain directions, $u_1,\dots,u_b$ are the directions of index $<b$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Step 2.1, p.7

import Mathlib

namespace MatchedUCLB

/-- **The chain prefix `U_{j,b} = span{v_j, u_{j,1}, …, u_{j,b}}`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Step 2.1, p.7: "We
refer to the subspace `U_{j,b} := span{v_j, u_{j,1}, …, u_{j,b}}`, for `b ∈ {0, …, m}`, as a chain
prefix".

**Formalization Note.** With 0-based chain directions, `u_{j,1}, …, u_{j,b}` are `u i` for `i < b`. -/
def chainPrefix {d m : ℕ} (v : EuclideanSpace ℝ (Fin d)) (u : Fin m → EuclideanSpace ℝ (Fin d)) (b : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℝ (insert v (u '' {i | (i : ℕ) < b}))

end MatchedUCLB


