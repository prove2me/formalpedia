-- Prove2me | Definitions.Def_AppliedComb_Graphs_IsIntervalGraph
-- name    : AppliedComb_Graphs_IsIntervalGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:00:39.700202+00:00
-- url     : https://prove2.me/theorems/670bd621-c652-4890-b4e5-1b6fc5b7cea5
-- title:
--   Interval graph (Section 5.4.3)
-- statement:
--   A graph $G = (V, E)$ is an **interval graph** if it is the intersection graph of an indexed family of closed intervals of the real line: there are real numbers $a_v \le b_v$, one closed interval $I(v) = [a_v, b_v]$ for each vertex $v$, such that for distinct vertices $u \ne v$,
--   $$uv \in E \iff I(u) \cap I(v) \ne \emptyset.$$
--
--   Distinct vertices may carry equal intervals, since the family is indexed by $V$.
--
--   **Formalization Note.** The intervals are `Set.Icc (a v) (b v)` with `a v ≤ b v`, so every interval is nonempty (a single point is allowed).
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 87, Section 5.4.3 (intersection graph, interval graph)

import Mathlib

namespace AppliedComb.Graphs

/-- Keller–Trotter, p. 87. `G` is an *interval graph* if it is the intersection graph of an
indexed family of closed intervals of the real line: there are reals `a v ≤ b v`, one closed
interval `[a v, b v]` per vertex `v`, such that distinct vertices `u, v` are adjacent exactly
when their intervals intersect. -/
def IsIntervalGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b : V → ℝ, (∀ v, a v ≤ b v) ∧
    ∀ u v : V, u ≠ v → (G.Adj u v ↔ (Set.Icc (a u) (b u) ∩ Set.Icc (a v) (b v)).Nonempty)

end AppliedComb.Graphs


