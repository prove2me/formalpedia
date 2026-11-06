-- Prove2me | Definitions.Def_MatchedUCLB_prefixSpace
-- name    : MatchedUCLB_prefixSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:43.762891+00:00
-- url     : https://prove2.me/theorems/e0afc065-a05f-4fe0-9298-0681179cdc92
-- title:
--   The current-prefix space $W_{j,b}=(\bigoplus_{k<j}E_k)\oplus U_{j,b}$
-- statement:
--   For a phase $j$ and $0\le b\le m$, the **current-prefix space** is
--
--   $$
--   W_{j,b}=\Bigl(\bigoplus_{k<j}E_k\Bigr)\oplus U_{j,b},
--   $$
--
--   the span of all directions of the completed phases $k<j$ together with $v_j,u_{j,1},\dots,u_{j,b}$. For $j=0$ the first summand is $\{0\}$. It contains every point an algorithm can have learned about after completing $j$ phases and $b$ chain directions of phase $j$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Sec. 4.4, p.10

import Mathlib

namespace MatchedUCLB

/-- **The current-prefix space `W_{j,b} = (⊕_{k<j} E_k) ⊕ U_{j,b}`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Sec. 4.4, p.10: "we
include those subspaces in the current-prefix space `W_{j,b} := (⊕_{k<j} E_k) ⊕ U_{j,b}`, for
`0 ≤ j < L` and `0 ≤ b ≤ m`. The sum over `k < j` is `{0}` when `j = 0`."

**Formalization Note.** `W_{j,b}` is the span of `v_k, u_{k,i}` for `k < j`, together with `v_j`
and `u_{j,1}, …, u_{j,b}` (0-based: `u j i` for `i < b`). For an orthonormal frame this span is the
orthogonal direct sum of the page. -/
def prefixSpace {d m : ℕ} (v : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin d)) (j b : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℝ ((⋃ k ∈ Finset.range j, insert (v k) (Set.range (u k))) ∪
    insert (v j) (u j '' {i | (i : ℕ) < b}))

end MatchedUCLB


