-- Prove2me | Definitions.Def_MinrankTW_Supplement_thm6Input
-- name    : MinrankTW_Supplement_thm6Input
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:05:29.393815+00:00
-- url     : https://prove2.me/theorems/6314b44f-1da5-4313-a0b0-c137a6f11185
-- title:
--   Input layout of Theorem 6: a fixed/free matrix, a path decomposition and a target rank
-- statement:
--   The RAM input of Theorem 6 encodes a square $n\times n$ fixed/free matrix, a path decomposition of its support graph on $N$ nodes and the target rank $r$. It is the published input layout of Theorem 2 (dimensions, the allowed set of every entry as a bitmask, the tree table, the bag table) with $m=n$, the allowed sets of the fixed/free matrix, the tree table of the path $0-1-\dots-(N-1)$, followed by one further cell holding $r$.
--
--   **Formalization Note** Every path decomposition can be relabelled so that its path visits the nodes in the order $0,1,\dots,N-1$; the layout writes that path explicitly.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 6, p.20; Theorem 2 input layout, p.3 and §1.2, p.5

import Mathlib
import Definitions.Def_MinrankTW_thm2Input
import Definitions.Def_MinrankTW_Supplement_fixedFree

namespace MinrankTW.Supplement

/-- The tree table of the path `0 – 1 – ⋯ – (N − 1)` on `N` nodes. -/
def pathTable (N : ℕ) : Fin N → Fin N → Bool :=
  fun s s' => decide ((s : ℕ) + 1 = s' ∨ (s' : ℕ) + 1 = s)

/-- The RAM input of Theorem 6 (Perles–Weinstein, *Efficient Algorithms for Minrank and Index
Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991),
Theorem 6, p.20: "an n × n matrix whose entries are each fixed or unrestricted … a given r … a
width-w path decomposition of its support graph is supplied"). It is the published layout
`MinrankTW.thm2Input` of the square fixed/free constraints `fixedFree A` (`m = n`), with the tree
table of the path `pathTable N` and the bag table `bag`, followed by the target rank `r` in the
first cell after that layout.

**Formalization Note** Every path decomposition can be relabelled so that its path is
`0 – 1 – ⋯ – (N − 1)`; the layout lists that path explicitly. -/
def thm6Input {F : Type*} [Fintype F] (e : F ≃ Fin (Fintype.card F)) (n N r : ℕ)
    (A : Fin n → Fin n → Option F) (bag : Fin N → Fin n ⊕ Fin n → Bool) : ℕ → ℕ := fun k =>
  if k = 3 + n * n + N * N + N * (n + n) then r
  else MinrankTW.thm2Input e n n N (fixedFree A) (pathTable N) bag k

end MinrankTW.Supplement


