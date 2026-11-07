-- Prove2me | Definitions.Def_MinrankTW_thm1Input
-- name    : MinrankTW_thm1Input
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:48.491936+00:00
-- url     : https://prove2.me/theorems/3223c995-1425-442d-8142-fcb916bab83d
-- title:
--   Input layout of Theorem 1
-- statement:
--   The memory on which the algorithm of Theorem 1 is started, for a graph given by a Boolean table $\mathrm{edge}$ on $n$ vertices and a tree decomposition given by a Boolean tree table $\mathrm{tree}$ on $N$ nodes and a Boolean bag-membership table $\mathrm{bag}$:
--
--   1. cell $0$ holds $n$ and cell $1$ holds $N$;
--   2. cells $2,\dots,1+n^2$ hold the bits $\mathrm{edge}(u,v)$ row by row ($(u,v)$ at offset $un+v$);
--   3. the next $N^2$ cells hold the bits $\mathrm{tree}(s,s')$ row by row;
--   4. the next $Nn$ cells hold the bits $\mathrm{bag}(s,v)$ node by node;
--   5. every other cell holds $0$.
--
--   The graph is the simple graph whose edges are the pairs $u\neq v$ with $\mathrm{edge}(u,v)$ or $\mathrm{edge}(v,u)$; the tree is read the same way, and bag $s$ is $\{v : \mathrm{bag}(s,v)\}$. The tables need not be symmetric or irreflexive, so every graph and every decomposition has an encoding.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 1, p.3

import Mathlib

namespace MinrankTW

/-- The RAM input layout of Theorem 1 (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), Theorem 1, p.3: "Given an n-vertex graph G and a
width-w tree decomposition of G"). For a graph table `edge` on `n` vertices, a tree table
`tree` on `N` nodes and a bag-membership table `bag`:
cell `0` holds `n`, cell `1` holds `N`; cells `2, …, 1 + n²` hold the bits `edge u v`
row by row (`(u, v)` at offset `u·n + v`); the next `N²` cells hold the bits `tree s s'`
row by row; the next `N·n` cells hold the bits `bag s v` node by node (`(s, v)` at offset
`s·n + v`); every other cell holds `0`. A bit is `1` for `true` and `0` for `false`.

**Formalization Note** Row-major offsets are computed with `finProdFinEquiv`
(`(a, b) ↦ b + (second dimension)·a`). The graph is read as `SimpleGraph.fromRel` of `edge`,
the tree as `SimpleGraph.fromRel` of `tree`, and bag `s` as `{v | bag s v}`; the tables
need not be symmetric or irreflexive. -/
def thm1Input (n N : ℕ) (edge : Fin n → Fin n → Bool) (tree : Fin N → Fin N → Bool)
    (bag : Fin N → Fin n → Bool) : ℕ → ℕ := fun k =>
  if k = 0 then n else if k = 1 then N else
  if h₁ : k - 2 < n * n then
    (edge (finProdFinEquiv.symm ⟨k - 2, h₁⟩).1 (finProdFinEquiv.symm ⟨k - 2, h₁⟩).2).toNat
  else if h₂ : k - 2 - n * n < N * N then
    (tree (finProdFinEquiv.symm ⟨k - 2 - n * n, h₂⟩).1
      (finProdFinEquiv.symm ⟨k - 2 - n * n, h₂⟩).2).toNat
  else if h₃ : k - 2 - n * n - N * N < N * n then
    (bag (finProdFinEquiv.symm ⟨k - 2 - n * n - N * N, h₃⟩).1
      (finProdFinEquiv.symm ⟨k - 2 - n * n - N * N, h₃⟩).2).toNat
  else 0

end MinrankTW


