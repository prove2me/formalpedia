-- Prove2me | Definitions.Def_OnlineCAP_IsNode
-- name    : OnlineCAP_IsNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:42.46808+00:00
-- url     : https://prove2.me/theorems/fdd0a1fb-b17d-495d-a3d8-14622f16cbfe
-- title:
--   Nodes of the range tree
-- statement:
--   The **range tree** on the x-coordinates of $P$ is the balanced binary tree whose leaves are the sorted distinct x-coordinates $x_{(0)}<\dots<x_{(m-1)}$. Concretely, its nodes are the pairs $(h,j)$ with
--   $$h\le\lceil\log_2 m\rceil\qquad\text{and}\qquad j\cdot2^h<m ,$$
--   node $(h,j)$ representing the ranks $[j2^h,(j+1)2^h)$. Leaves are the nodes with $h=0$, the children of $(h,j)$ are $(h-1,2j)$ and $(h-1,2j+1)$, and the root is $(\lceil\log_2 m\rceil,0)$. The height is $\lceil\log_2 m\rceil=O(\log n)$, and every point lies in at most $\lceil\log_2 m\rceil+1$ nodes (one per level).
--
--   **Formalization Note** A concrete balanced binary tree with dyadic rank intervals; the paper's leaves are the canonical intervals between consecutive coordinates, which index the same points.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §4.1.2, p.17

import Mathlib

namespace OnlineCAP

/-- **Nodes of the range tree.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §4.1.2, p.17 (PDF p.17): "On this set as leaves, we
construct a balanced binary tree. Each node in this tree represents an interval, which is the
union of all the canonical intervals stored in its subtree. And the height of this tree is
O(log n)".

With `m` the number of distinct x-coordinates of `P`, the nodes are the pairs `(h, j)` with
`h ≤ ⌈log₂ m⌉` and `j · 2^h < m`; node `(h, j)` represents the x-ranks in
`[j · 2^h, (j + 1) · 2^h)`. Leaves are the nodes with `h = 0`; the children of `(h, j)`, `h ≥ 1`,
are `(h − 1, 2j)` (left) and `(h − 1, 2j + 1)` (right); the root is `(⌈log₂ m⌉, 0)`.

**Formalization Note.** A concrete balanced binary tree on the sorted x-coordinates (dyadic rank
intervals). Every point lies in exactly one node of each level, so in at most `⌈log₂ m⌉ + 1`
nodes. -/
noncomputable def IsNode (P : Finset (ℝ × ℝ)) (h j : ℕ) : Prop := by
  classical
  exact h ≤ Nat.clog 2 (P.image Prod.fst).card ∧ j * 2 ^ h < (P.image Prod.fst).card

end OnlineCAP


