-- Prove2me | Definitions.Def_MinrankTW_completionCount
-- name    : MinrankTW_completionCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:00.411126+00:00
-- url     : https://prove2.me/theorems/121983f6-9091-463a-8f5a-9a0a9b8810d8
-- title:
--   Number of rank-$j$ completions
-- statement:
--   For entry constraints $S$ on $m\times n$ matrices over $\mathbb F_q$ and $j\in\mathbb N$, the number of completions of rank $j$:
--   $$
--   \#\{M\in\mathbb F_q^{m\times n} : M_{ij}\in S_{ij}\ \forall i,j,\ \operatorname{rank}M=j\}.
--   $$
--   It is the coefficient of $z^j$ in the rank enumerator $Z(z)$.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 1.2, p.5

import Mathlib
import Definitions.Def_MinrankTW_IsCompletion

namespace MinrankTW

/-- The number of completions of `S` of rank `j` (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §1.2, p.5: the coefficient of
`z^j` in the rank enumerator `Z(z)` "counts rank-`j` completions"). -/
noncomputable def completionCount {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m n : ℕ}
    (S : Fin m → Fin n → Finset F) (j : ℕ) : ℕ :=
  Nat.card {M : Matrix (Fin m) (Fin n) F // IsCompletion S M ∧ M.rank = j}

end MinrankTW


