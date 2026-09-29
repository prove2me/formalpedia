-- Prove2me | Definitions.Def_RobertsonSeymour1986_GM5_grid
-- name    : RobertsonSeymour1986_GM5_grid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:51:47.679934+00:00
-- url     : https://prove2.me/theorems/542297e0-b87f-4a72-9a32-6cd69705f9b8
-- title:
--   The $\theta$-grid
-- statement:
--   For an integer $\theta$, the **$\theta$-grid** is the simple graph with vertex set $\{v_{ij} : 1\le i,j\le\theta\}$ in which $v_{ij}$ and $v_{i'j'}$ are adjacent if and only if
--
--   $$|i-i'|+|j-j'|=1.$$
--
--   It is the $\theta\times\theta$ square lattice. Grids are the canonical planar graphs of large tree-width: every planar graph is a minor of a large enough grid.
--
--   **Formalization Note** The vertex $v_{ij}$ is the pair $(i-1,j-1)\in\{0,\dots,\theta-1\}^2$. The adjacency condition is computed literally in the integers.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), Sect. 1, p. 93 (PDF p. 2), definition of the θ-grid after (1.4); DOI 10.1016/0095-8956(86)90030-4

import Mathlib

namespace RobertsonSeymour1986.GM5

/-- The `θ`-grid.

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986),
Sect. 1, p. 93 (PDF p. 2), unnumbered: "When θ ≥ 2 is an integer, the *θ-grid* is the simple graph
with vertex set {v_ij : 1 ≤ i, j ≤ θ}, in which v_ij and v_{i′j′} are adjacent if
|i − i′| + |j − j′| = 1."

**Formalization Note** The vertex `v_ij` is the pair `(i - 1, j - 1) : Fin θ × Fin θ` (0-based
indices; the shift does not change the differences `i − i′`, `j − j′`). Adjacency is literally
`|i − i′| + |j − j′| = 1`, computed in `ℤ`. The definition makes sense for every `θ : ℕ`; the paper
uses it for `θ ≥ 2`, and this development only for even `θ ≥ 6`. -/
def grid (θ : ℕ) : SimpleGraph (Fin θ × Fin θ) where
  Adj a b := |((a.1 : ℕ) : ℤ) - ((b.1 : ℕ) : ℤ)| + |((a.2 : ℕ) : ℤ) - ((b.2 : ℕ) : ℤ)| = 1
  symm := ⟨fun a b h => by simpa [abs_sub_comm] using h⟩
  loopless := ⟨fun a h => by simp at h⟩

end RobertsonSeymour1986.GM5


