-- Prove2me | Definitions.Def_MinrankTW_fitCount
-- name    : MinrankTW_fitCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:45.098021+00:00
-- url     : https://prove2.me/theorems/b499d12b-bd79-4133-b2ee-3485d28b4713
-- title:
--   Number of rank-$j$ normalized fitting matrices
-- statement:
--   For a finite field $\mathbb F_q$, a graph $G$ on $[n]$ and $j\in\mathbb N$, this is the number of normalized fitting matrices of $G$ of rank $j$:
--   $$
--   \#\{M\in\mathbb F_q^{n\times n} : M \text{ fits } G,\ M_{ii}=1\ \forall i,\ \operatorname{rank}M=j\}.
--   $$
--   It is the coefficient of $z^j$ in the rank enumerator $Z_G(z)$. Fitting matrices with arbitrary nonzero diagonal are $(q-1)^n$ times as many; they are not what is counted.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 1, p.3 and Section 1.2, p.5

import Mathlib
import Definitions.Def_MinrankTW_IsNormalizedFit

namespace MinrankTW

/-- The number of **normalized** fitting matrices of `G` of rank `j` over the finite field
`F` (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), Theorem 1, p.3: "the number of normalized fitting matrices of every rank"; it is
the coefficient of `z^j` in `Z_G(z)`, §1.2, p.5).

**Formalization Note** The cardinality of the (finite) subtype of `F^{n×n}` of matrices that
fit `G`, have unit diagonal and have rank `j`. Fitting matrices with arbitrary nonzero diagonal
are `(q − 1)^n` times as many (p.5); they are not what is counted here. -/
noncomputable def fitCount (F : Type*) [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (G : SimpleGraph (Fin n)) (j : ℕ) : ℕ :=
  Nat.card {M : Matrix (Fin n) (Fin n) F // IsNormalizedFit G M ∧ M.rank = j}

end MinrankTW


