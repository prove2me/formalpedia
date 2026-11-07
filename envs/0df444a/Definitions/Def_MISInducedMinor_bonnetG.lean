-- Prove2me | Definitions.Def_MISInducedMinor_bonnetG
-- name    : MISInducedMinor_bonnetG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:26.934298+00:00
-- url     : https://prove2.me/theorems/e94b5c0c-4d58-47c2-9ec6-7785d9971c52
-- title:
--   The intermediate graph $G$ (rows, columns, sides)
-- statement:
--   For $R,C\in\mathbb N$, the **intermediate graph** $G_{R,C}$ has the vertices $(i,j,s)$ with row $i\in\{0,\dots,R-1\}$, column $j\in\{0,\dots,C-1\}$ and side $s\in\{0,1\}$, and two kinds of edges:
--
--   1. $(i,j,0)(i',j,1)$ for all rows $i,i'$ (including $i=i'$) and every column $j$, so each column $C_j$ induces a complete bipartite graph between its two sides;
--   2. $(i,j,s)(i,j',s')$ whenever $|j-j'|=1$, for all sides $s,s'$: along each row, all edges are present between consecutive columns.
--
--   For an $n$-vertex $m$-edge graph $F$, the paper's intermediate graph is
--
--   $$G=G_{2m,\,2n-1}.$$
--
--   All constructions of §3 live inside $G$; Lemma 3.1 shows that $G$ excludes the $5\times5$ grid as an induced minor.
--
--   **Formalization Note** Indices are 0-based. The graph is defined for every $R$ and $C$.
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), §3, p.6

import Mathlib

set_option autoImplicit false

namespace MISInducedMinor

/-- The **intermediate graph `G`** of §3 with `R` rows and `C` columns, on the vertices
`(i, j, s)` with row `i`, column `j` and side `s ∈ {0, 1}`. arXiv:2609.11285 (sha256 e378b906…),
§3, p.6:

`E(G) = {(i, j, 0)(i′, j, 1) : i, i′ ∈ [2m], j ∈ [2n − 1]} ∪ {(i, j, s)(i, j′, s′) : |j − j′| = 1}`.

So each column is a complete bipartite graph between its two sides (all rows, including
`i = i′`), and along each row all edges are present between consecutive columns.

**Formalization Note.** Indices are 0-based (`Fin R`, `Fin C`, `Fin 2`); the paper's `G` for an
`n`-vertex `m`-edge graph is `bonnetG (2 * m) (2 * n - 1)`. The graph is defined for every
`R, C`. -/
def bonnetG (R C : ℕ) : SimpleGraph (Fin R × Fin C × Fin 2) where
  Adj x y :=
    (x.2.1 = y.2.1 ∧ x.2.2 ≠ y.2.2) ∨
      (x.1 = y.1 ∧ (x.2.1.val + 1 = y.2.1.val ∨ y.2.1.val + 1 = x.2.1.val))
  symm := ⟨fun x y h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, Ne.symm h2⟩
    · exact Or.inr ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨fun x h => by
    rcases h with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2 rfl
    · omega⟩

end MISInducedMinor


