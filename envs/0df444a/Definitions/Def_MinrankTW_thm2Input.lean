-- Prove2me | Definitions.Def_MinrankTW_thm2Input
-- name    : MinrankTW_thm2Input
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:47.052117+00:00
-- url     : https://prove2.me/theorems/372a31bd-2901-475d-9e9c-9bd3ac2a4345
-- title:
--   Input layout of Theorem 2
-- statement:
--   The memory on which the algorithm of Theorem 2 is started, for entry constraints $S$ on an $m\times n$ matrix over $\mathbb F_q$ (with a fixed encoding $e:\mathbb F_q\to\{0,\dots,q-1\}$), a tree table on $N$ nodes and a bag table over the support vertices:
--
--   1. cells $0,1,2$ hold $m,n,N$;
--   2. the next $mn$ cells hold, row by row, the bitmask $\sum_{a\in S_{ij}}2^{e(a)}$ of each allowed set;
--   3. the next $N^2$ cells hold the tree bits row by row;
--   4. the next $N(m+n)$ cells hold the bag bits node by node, rows first ($r_i$ at offset $i$, $c_j$ at offset $m+j$);
--   5. every other cell holds $0$.
--
--   This lists every allowed set (forced zeros as $\{0\}$), a dense form of the source's list of support edges and their allowed sets, of polynomial size.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 2, p.3 and Section 1.2, p.5

import Mathlib

namespace MinrankTW

/-- The RAM input layout of Theorem 2 (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), Theorem 2, p.3, and §1.2, p.5: "The input lists
the support edges and their allowed sets"). For entry constraints `S` on an `m × n` matrix
over `F` (with the fixed field encoding `e : F ≃ Fin q`), a tree table `tree` on `N` nodes
and a bag table `bag` over the support vertices: cells `0, 1, 2` hold `m, n, N`; the next
`m·n` cells hold, row by row, the bitmask `∑_{a ∈ S_ij} 2^{e(a)}` of each allowed set; the next
`N²` cells hold the bits `tree s s'` row by row; the next `N·(m + n)` cells hold the bits
`bag s u` node by node, rows first (`r_i` at offset `i`, `c_j` at offset `m + j`); every
other cell holds `0`.

**Formalization Note** Row-major offsets use `finProdFinEquiv`; the support vertices
`Fin m ⊕ Fin n` are numbered by `finSumFinEquiv` (`inl i ↦ i`, `inr j ↦ m + j`). The input
lists all `m·n` allowed sets (absent entries as `{0}`), a dense form of the paper's list of
support edges, of polynomial size. -/
def thm2Input {F : Type*} [Fintype F] (e : F ≃ Fin (Fintype.card F)) (m n N : ℕ)
    (S : Fin m → Fin n → Finset F) (tree : Fin N → Fin N → Bool)
    (bag : Fin N → Fin m ⊕ Fin n → Bool) : ℕ → ℕ := fun k =>
  if k = 0 then m else if k = 1 then n else if k = 2 then N else
  if h₁ : k - 3 < m * n then
    ∑ a ∈ S (finProdFinEquiv.symm ⟨k - 3, h₁⟩).1 (finProdFinEquiv.symm ⟨k - 3, h₁⟩).2,
      2 ^ (e a : ℕ)
  else if h₂ : k - 3 - m * n < N * N then
    (tree (finProdFinEquiv.symm ⟨k - 3 - m * n, h₂⟩).1
      (finProdFinEquiv.symm ⟨k - 3 - m * n, h₂⟩).2).toNat
  else if h₃ : k - 3 - m * n - N * N < N * (m + n) then
    (bag (finProdFinEquiv.symm ⟨k - 3 - m * n - N * N, h₃⟩).1
      (finSumFinEquiv.symm (finProdFinEquiv.symm ⟨k - 3 - m * n - N * N, h₃⟩).2)).toNat
  else 0

end MinrankTW


