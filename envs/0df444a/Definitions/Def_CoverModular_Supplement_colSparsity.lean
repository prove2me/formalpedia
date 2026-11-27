-- Prove2me | Definitions.Def_CoverModular_Supplement_colSparsity
-- name    : CoverModular_Supplement_colSparsity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:15:38.134582+00:00
-- url     : https://prove2.me/theorems/21b57a7b-8f30-5f45-8160-e01a4e142d70
-- title:
--   Column sparsity $\bar a=\max_j\sum_i a_{ij}$ of the constraint matrix
-- statement:
--   For a non-negative integral constraint matrix $A=[a_{ij}]$ with $m$ rows and $n$ columns, the **column sparsity** is
--
--   $$
--   \bar a=\max_{1\le j\le n}\ \sum_{1\le i\le m}a_{ij},
--   $$
--
--   the maximum sum of constraint coefficients over all variables. Theorem 2 shows that the LP-based set function $h$ of (17) is $\bar a$-cover modular.
--
--   **Formalization Note** The maximum is over all $n$ columns, not only over the columns in some $J_k$. It is a natural number, equal to $0$ when $n=0$ or $m=0$.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §5.1, p.23

import Mathlib

namespace CoverModular.Supplement

/-- The **column sparsity** `ā = max_j ∑_i a_ij` of the constraint matrix of (17) (DeValve,
Pekeč, Wei, *Approximate submodularity in network design problems*, SSRN 3844987, §5.1, p.23):
the maximum sum of constraint coefficients for any variable.

**Formalization Note** The maximum is over all `n` columns (not only those in some `J_k`), as a
`Finset.sup` of natural numbers; it is `0` when `n = 0` (and when `m = 0`). -/
def colSparsity {m n : ℕ} (a : Fin m → Fin n → ℕ) : ℕ :=
  Finset.univ.sup fun j => ∑ i, a i j

end CoverModular.Supplement


