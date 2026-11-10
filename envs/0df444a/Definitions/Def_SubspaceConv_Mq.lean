-- Prove2me | Definitions.Def_SubspaceConv_Mq
-- name    : SubspaceConv_Mq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:16:08.540727+00:00
-- url     : https://prove2.me/theorems/ea953f3b-e2ee-45eb-87c9-a23cff83afa0
-- title:
--   $M_q(n,k)$, the number of subspaces of dimension at most $k$
-- statement:
--   $$M_q(n,k)=\sum_{j=0}^{\min(k,n)}|\mathrm{Gr}_q(n,j)|,\qquad M_q(n,n)=N_q(n),$$
--   the number of subspaces of $\mathbb F_q^n$ of dimension at most $k$, i.e. the length of the tables of $Z_{n,k}$. Theorem 1 measures cost in terms of $M_q(n,k)$.
--
--   **Formalization Note** Defined as the cardinality of the set of subspaces of dimension at most $k$; the equality with the printed sum is the first clause of the milestone on eq. (11).
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.1, p.1 (definition of M_q(n,k))

import Mathlib
import Definitions.Def_SubspaceConv_SubLE

namespace SubspaceConv

/-- `M_q(n, k)`, the number of subspaces of `F_q^n` of dimension at most `k`
(Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.1, p.1: `M_q(n,k) = ∑_{j=0}^{min(k,n)} |Gr_q(n,j)|`).

**Formalization Note** Defined as the cardinality of `SubLE F n k`; that it equals the printed
sum is a clause of the milestone `SubspaceConv.eq_11`. -/
noncomputable def Mq (F : Type*) [Field F] (n k : ℕ) : ℕ :=
  Nat.card (SubLE F n k)

end SubspaceConv


