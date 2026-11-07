-- Prove2me | Definitions.Def_SparseDisc_pattern
-- name    : SparseDisc_pattern
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:51.556188+00:00
-- url     : https://prove2.me/theorems/0e944c98-5c81-48c2-8309-ad132bb4b182
-- title:
--   Pattern $H(F)$ of a 2-sparse family
-- statement:
--   The **pattern** $H(F)$ of a family $F = (f_v)_{v \in V}$ is the simple graph on $V$ in which two distinct functions $u, v$ are adjacent if some item is relevant to both:
--   $$
--   uv \in E(H(F)) \iff u \ne v \text{ and } R(f_u) \cap R(f_v) \ne \emptyset .
--   $$
--   For a 2-sparse family this is the simple graph underlying the item multigraph (every item relevant to two functions is an edge between them); parallel edges form the bundles, whose sizes are arbitrary.
--
--   **Formalization Note** The paper's edge set is $\{S : |S| = 2,\ B_S \ne \emptyset\}$, where $B_S$ is the set of items whose set of relevant functions is exactly $S$. On 2-sparse families an item relevant to both $u$ and $v$ has relevant set exactly $\{u, v\}$, so the two graphs coincide on the families where the pattern is used.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Definition 2.3 and 'The case t = 2', p.12; Section 1.1, p.3

import Mathlib
import Definitions.Def_SparseDisc_relevant

namespace SparseDisc

/-- The **pattern** `H(F)` of a family `f = (f_v)_{v ∈ V}`: the simple graph on `V` in which
distinct `u, v` are adjacent iff some item is relevant to both `f_u` and `f_v`
(Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission
manuscript (sha256 0f09ec60…25b81), Definition 2.3 and "The case t = 2", p.12: for a 2-sparse
family, `H(F)` is the simple graph underlying the item multigraph).

**Formalization Note** The paper's edge set is `{S : |S| = 2, B_S ≠ ∅}`, where `B_S` is the set
of items whose set of relevant functions is exactly `S`. For a 2-sparse family an item relevant to
both `u ≠ v` has relevant set exactly `{u, v}`, so the two graphs coincide on 2-sparse families,
the only families on which this graph is used. -/
def pattern {V ι : Type} [Fintype ι] [DecidableEq ι] (f : V → Finset ι → ℝ) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => ∃ j, j ∈ relevant (f u) ∧ j ∈ relevant (f v))

end SparseDisc


