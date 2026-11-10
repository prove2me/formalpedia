-- Prove2me | Definitions.Def_SubspaceConv_zetaT
-- name    : SubspaceConv_zetaT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:16:08.68628+00:00
-- url     : https://prove2.me/theorems/ead606aa-46b6-45e9-8473-769476ccffcb
-- title:
--   The transpose $Z_{n,k}^{\mathsf T}$: sums over superspaces
-- statement:
--   The transpose of the truncated zeta transform sums over superspaces in the same table:
--   $$(Z_{n,k}^{\mathsf T}f)(W)=\sum_{\substack{U\ge W\\ \dim U\le k}}f(U),\qquad \dim W\le k.$$
--   Theorem 1 applies it, and its inverse, at the same cost as $Z_{n,k}$.
--
--   **Formalization Note** Same table type as $Z_{n,k}$.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.1, p.2 ("Its transpose sums over superspaces in the same table")

import Mathlib
import Definitions.Def_SubspaceConv_SubLE

namespace SubspaceConv

open Classical in
/-- The transpose `Z_{n,k}^T` of the truncated subspace zeta transform: it sums over
superspaces in the same table, `(Z_{n,k}^T f)(W) = ∑_{W ≤ U, dim U ≤ k} f(U)`
(Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.1, p.2: "Its transpose sums over superspaces in the same table").

**Formalization Note** Same table type as `SubspaceConv.zeta`. -/
noncomputable def zetaT {F : Type*} [Field F] [Finite F] {n k : ℕ} {A : Type*} [AddCommMonoid A]
    (f : SubLE F n k → A) (W : SubLE F n k) : A :=
  ∑ U : SubLE F n k, if W.1 ≤ U.1 then f U else 0

end SubspaceConv


