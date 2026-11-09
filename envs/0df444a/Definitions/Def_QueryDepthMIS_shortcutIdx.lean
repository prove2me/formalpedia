-- Prove2me | Definitions.Def_QueryDepthMIS_shortcutIdx
-- name    : QueryDepthMIS_shortcutIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:34.329508+00:00
-- url     : https://prove2.me/theorems/4c8992a1-d405-4958-abaa-190e74c2e7bc
-- title:
--   Shortcuts $C(P)$ on a path
-- statement:
--   For a path $P = (p_1, \dots, p_L)$, a **shortcut** is a position $p_i$ with $i \le L - 2$ such that $(\pi(p_i), \pi(p_{i+2})) \in E$; $C(P)$ is the set of shortcuts.
--
--   **Formalization Note** For a list of vertices $(v_1, \dots, v_L)$ this is the set of (0-based) indices $i$ with $i + 2 < L$ and $v_{i+1} \sim v_{i+3}$; its cardinality is the number of shortcuts, and its image under $i \mapsto p_{i+1}$ is $C(P)$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.13

import Mathlib

set_option autoImplicit false

namespace QueryDepthMIS

/-- Shortcuts on a path (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.13): "For a fixed permutation π and a query path
P = (p₁, …, p_L), a shortcut on P is a position p_i, with i ≤ L − 2, such that
(π(p_i), π(p_{i+2})) ∈ E. Denote the set of shortcuts on P by C(P)."

For a list of vertices `l = [v₁, …, v_L]`, the set of 0-based indices `i` with `i + 2 < L` and
`v_{i+1} ∼ v_{i+3}` (1-based `i + 1 ≤ L − 2`). The paper's `C(P)` is the image of this set under
`i ↦ p_{i+1}`; its cardinality is the number of shortcuts. -/
def shortcutIdx {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (l : List V) :
    Finset ℕ :=
  (Finset.range l.length).filter (fun i =>
    ∃ (h : i + 2 < l.length), G.Adj (l[i]'(by omega)) (l[i + 2]'h))

end QueryDepthMIS


