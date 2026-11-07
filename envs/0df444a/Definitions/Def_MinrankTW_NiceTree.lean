-- Prove2me | Definitions.Def_MinrankTW_NiceTree
-- name    : MinrankTW_NiceTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:48.340553+00:00
-- url     : https://prove2.me/theorems/4d4afd11-716d-4d34-b448-3814f7476822
-- title:
--   Nice tree decomposition of a support graph
-- statement:
--   A **nice** decomposition of the support graph of entry constraints on $m\times n$ matrices has empty leaves and an empty root; each non-leaf node introduces one row or column, forgets one row or column, introduces one entry $(i,j)$ while both indices are in the bag, or joins two children with the same bag.
--
--   For a node $t$ the bag $B_t$ (its row and column vertices), the interior $I_t=V_t\setminus B_t$ (the rows and columns forgotten below $t$) and the set $\Omega_{\le t}$ of entry positions introduced below $t$ are computed bottom-up. The decomposition is **well formed** if
--
--   1. an introduced row or column is in neither the bag nor the interior of its child;
--   2. an introduced entry has both indices in the bag and was not introduced before;
--   3. a forgotten row or column is in the child's bag;
--   4. the two children of a join have equal bags, disjoint interiors and disjoint introduced entries.
--
--   **Formalization Note** The decomposition is a tree of operations (an inductive type); at a join the bag is that of the first child.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 3.2, p.10

import Mathlib

namespace MinrankTW

/-!
# Nice tree decompositions of a support graph

Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §3.2, p.10: a decomposition "in nice form, with empty leaves and root. Each nonleaf bag
introduces or forgets one row or column, introduces one entry while both indices are present, or
joins two children with the same vertex set. Introduce every support entry exactly once".

**Formalization Note** A nice decomposition is a tree of operations (`leaf` is an empty leaf).
The bag (rows `bagRows`, columns `bagCols`), the forgotten vertices (the interior
`I_t = V_t ∖ B_t`: `forgottenRows`, `forgottenCols`) and the introduced entry positions
`Ω_{≤t}` (`assigned`) are computed bottom-up; at a join the bag is the (common) bag of the
first child. `WF` is well-formedness: an introduced row/column is in neither the bag nor the
interior of its child; an introduced entry has both indices in the bag and was not introduced
before; a forgotten vertex is in the child bag; the two children of a join have equal bags,
disjoint interiors and disjoint introduced entries.
-/

/-- A nice tree decomposition over the support vertices `Fin m ⊕ Fin n`, as a tree of
operations. -/
inductive NiceTree (m n : ℕ) where
  | leaf
  | introRow (i : Fin m) (t : NiceTree m n)
  | introCol (j : Fin n) (t : NiceTree m n)
  | assign (i : Fin m) (j : Fin n) (t : NiceTree m n)
  | forgetRow (i : Fin m) (t : NiceTree m n)
  | forgetCol (j : Fin n) (t : NiceTree m n)
  | join (t₁ t₂ : NiceTree m n)

namespace NiceTree

variable {m n : ℕ}

/-- The row vertices of the bag. -/
def bagRows : NiceTree m n → Finset (Fin m)
  | leaf => ∅
  | introRow i t => insert i t.bagRows
  | introCol _ t => t.bagRows
  | assign _ _ t => t.bagRows
  | forgetRow i t => t.bagRows.erase i
  | forgetCol _ t => t.bagRows
  | join t₁ _ => t₁.bagRows

/-- The column vertices of the bag. -/
def bagCols : NiceTree m n → Finset (Fin n)
  | leaf => ∅
  | introRow _ t => t.bagCols
  | introCol j t => insert j t.bagCols
  | assign _ _ t => t.bagCols
  | forgetRow _ t => t.bagCols
  | forgetCol j t => t.bagCols.erase j
  | join t₁ _ => t₁.bagCols

/-- The interior rows (rows forgotten in the subtree). -/
def forgottenRows : NiceTree m n → Finset (Fin m)
  | leaf => ∅
  | introRow _ t => t.forgottenRows
  | introCol _ t => t.forgottenRows
  | assign _ _ t => t.forgottenRows
  | forgetRow i t => insert i t.forgottenRows
  | forgetCol _ t => t.forgottenRows
  | join t₁ t₂ => t₁.forgottenRows ∪ t₂.forgottenRows

/-- The interior columns (columns forgotten in the subtree). -/
def forgottenCols : NiceTree m n → Finset (Fin n)
  | leaf => ∅
  | introRow _ t => t.forgottenCols
  | introCol _ t => t.forgottenCols
  | assign _ _ t => t.forgottenCols
  | forgetRow _ t => t.forgottenCols
  | forgetCol j t => insert j t.forgottenCols
  | join t₁ t₂ => t₁.forgottenCols ∪ t₂.forgottenCols

/-- The entry positions `Ω_{≤t}` introduced in the subtree. -/
def assigned : NiceTree m n → Finset (Fin m × Fin n)
  | leaf => ∅
  | introRow _ t => t.assigned
  | introCol _ t => t.assigned
  | assign i j t => insert (i, j) t.assigned
  | forgetRow _ t => t.assigned
  | forgetCol _ t => t.assigned
  | join t₁ t₂ => t₁.assigned ∪ t₂.assigned

/-- Well-formedness of a nice decomposition. -/
def WF : NiceTree m n → Prop
  | leaf => True
  | introRow i t => t.WF ∧ i ∉ t.bagRows ∧ i ∉ t.forgottenRows
  | introCol j t => t.WF ∧ j ∉ t.bagCols ∧ j ∉ t.forgottenCols
  | assign i j t => t.WF ∧ i ∈ t.bagRows ∧ j ∈ t.bagCols ∧ (i, j) ∉ t.assigned
  | forgetRow i t => t.WF ∧ i ∈ t.bagRows
  | forgetCol j t => t.WF ∧ j ∈ t.bagCols
  | join t₁ t₂ => t₁.WF ∧ t₂.WF ∧ t₁.bagRows = t₂.bagRows ∧ t₁.bagCols = t₂.bagCols ∧
      Disjoint t₁.forgottenRows t₂.forgottenRows ∧ Disjoint t₁.forgottenCols t₂.forgottenCols ∧
      Disjoint t₁.assigned t₂.assigned

end NiceTree

end MinrankTW


