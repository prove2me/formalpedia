-- Prove2me | Definitions.Def_MatchedUCLB_frameVec
-- name    : MatchedUCLB_frameVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:31.4795+00:00
-- url     : https://prove2.me/theorems/1fd7add2-f198-4b72-a467-ae5c4c060ff2
-- title:
--   The phase directions $v_j,u_{j,i}$ as one family
-- statement:
--   Given starting directions $v_0,v_1,\dots$ and chain directions $u_{j,1},\dots,u_{j,m}$ for each phase $j$, the **phase frame family** indexed by pairs $(j,o)$ with $j<L$ and $o\in\{\mathrm{none}\}\cup\{1,\dots,m\}$ takes the value $v_j$ at $(j,\mathrm{none})$ and $u_{j,i}$ at $(j,i)$. It lists all directions of the blocks $E_j=\operatorname{span}\{v_j,u_{j,1},\dots,u_{j,m}\}$, $j<L$.
--
--   **Formalization Note** Chain directions are indexed from $0$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Step 2.1, p.7; Definition E.1, p.83

import Mathlib

namespace MatchedUCLB

/-- **The phase directions as one family.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Step 2.1, p.7: "we choose mutually orthogonal
blocks for `0 ≤ j < L`, `E_j = span{v_j, u_{j,1}, …, u_{j,m}}`, with orthonormal bases and starting
directions `v_j`"; Definition E.1, p.83.

`frameVec L v u (j, none) = v_j` and `frameVec L v u (j, some i) = u_{j,i+1}`, for `j < L`.

**Formalization Note.** `v : ℕ → ℝ^d` and `u : ℕ → Fin m → ℝ^d`; only the indices `j < L` enter.
Chain directions are 0-based. -/
def frameVec {d m : ℕ} (L : ℕ) (v : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin d)) : Fin L × Option (Fin m) → EuclideanSpace ℝ (Fin d) :=
  fun jo => Option.elim jo.2 (v (jo.1 : ℕ)) (u (jo.1 : ℕ))

end MatchedUCLB


