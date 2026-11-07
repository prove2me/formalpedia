-- Prove2me | Definitions.Def_BalancedKneser_rookLabelSets
-- name    : BalancedKneser_rookLabelSets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:28.019274+00:00
-- url     : https://prove2.me/theorems/fc0ac129-925c-4bbf-bfb9-19798e51a2bb
-- title:
--   Rook labels $A_i$ on the $3\times3$ array and the rook configurations in $[2n]$
-- statement:
--   Number a $3\times 3$ array by $1,\dots,9$ row by row and let $D$ be its set of cells. Let $A_i$ consist of the four other cells in the row or column of $i$; for example $A_1=\{2,3,4,7\}$.
--
--   A **rook configuration** in $[2n]$ places $D$ in $[2n]$, adjoins a fixed $(n-4)$-set $I$ disjoint from $D$, and uses the nine $n$-sets $I\cup A_i$; the **complemented configuration** uses their nine complements. The set `rookLabelSets n` collects, over all choices, the nine-element label families of both kinds. The rook cycle is the boundary of the simplex on such a family (Proposition 4.1).
--
--   **Formalization Note** Cell $i\in\mathrm{Fin}\,9$ is the source's cell $i+1$, in row $\lfloor i/3\rfloor$ and column $i \bmod 3$. The array is placed by an injection $e:\mathrm{Fin}\,9\hookrightarrow\mathrm{Fin}\,2n$; $|I|=n-4$ is written $|I|+4=n$. The module proves $|A_i|=4$.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §4.1, p.8 (PDF p.10): rook labels and configurations

import Mathlib
import Definitions.Def_BalancedKneser_configLabels

namespace BalancedKneser

/-- **Rook labels** (Alipour–Jafari, arXiv:2611.04486v1, §4.1, p.8 (PDF p.10): "Number a 3 × 3
array by 1, …, 9, row by row, and let D be its set of cells. Let Aᵢ consist of the four other
cells in the row or column of i"). Cell `i : Fin 9` (the source's cell `i + 1`) lies in row
`i / 3` and column `i % 3`; its label is the set of the four other cells in its row or column. -/
def rookA (i : Fin 9) : Finset (Fin 9) :=
  Finset.univ.filter (fun j => j ≠ i ∧ (j.val / 3 = i.val / 3 ∨ j.val % 3 = i.val % 3))

theorem rookA_card (i : Fin 9) : (rookA i).card = 4 := by
  revert i; decide

/-- **The rook configurations in `[2n]`** (arXiv:2611.04486v1, §4.1, p.8 (PDF p.10): "For
n ≥ 5, adjoining a fixed (n − 4)-set I disjoint from D gives a cycle in N(G_{n,3}) … Again
include the complemented configurations."). Each member is the set of nine `n`-subsets
`I ∪ e(Aᵢ)` of `[2n]` of one rook configuration (with `D` the image of an injection
`e : Fin 9 ↪ Fin (2n)`), or the set of their complements. -/
def rookLabelSets (n : ℕ) : Set (Finset (KSet (2 * n) n)) :=
  {L | ∃ (I : Finset (Fin (2 * n))) (e : Fin 9 ↪ Fin (2 * n)),
    I.card + 4 = n ∧ Disjoint I (Finset.univ.map e) ∧
    (L = configLabels n rookA I e ∨ L = configLabelsCompl n rookA I e)}

end BalancedKneser


