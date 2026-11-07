-- Prove2me | Definitions.Def_SparseDisc_InstDiscLE
-- name    : SparseDisc_InstDiscLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:26.706934+00:00
-- url     : https://prove2.me/theorems/fd86ccd3-03f4-4acf-8067-181b2307be4d
-- title:
--   Discrepancy at most $c$ of an instance
-- statement:
--   An instance $(g_v)_{v \in V}$ on $\iota$ has **discrepancy at most $c$** if some $x \in \{\pm1\}^{\iota}$ satisfies $|g_v(x)| \le c$ for every $v$; here $\operatorname{disc}(G) = \min_x \max_v |g_v(x)|$.
--
--   **Formalization Note** The minimum over the finite cube is attained, so the predicate is exactly $\operatorname{disc}(G) \le c$.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Definition 2.2, p.12

import Mathlib
import Definitions.Def_SparseDisc_Cube

namespace SparseDisc

/-- `InstDiscLE g c`: the instance `(g_v)` has **discrepancy at most `c`**, i.e. some `x ∈ {±1}^ι`
has `|g_v(x)| ≤ c` for every `v` (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive
Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), Definition 2.2, p.12:
`disc(G) = min_x max_v |g_v(x)|`).

**Formalization Note** The minimum over the finite cube is attained, so `disc(G) ≤ c` iff
`InstDiscLE g c`. -/
def InstDiscLE {V ι : Type} (g : V → Cube ι → ℝ) (c : ℝ) : Prop :=
  ∃ x : Cube ι, ∀ v, |g v x| ≤ c

end SparseDisc


