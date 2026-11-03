-- Prove2me | Definitions.Def_DCAExtrap_zseq
-- name    : DCAExtrap_zseq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:24.08369+00:00
-- url     : https://prove2.me/theorems/ea39dea6-cc9c-438f-91b3-4933e1849ce9
-- title:
--   Paired sequence $z^k = (x^k, x^{k-1})$
-- statement:
--   For iterates $(x^k)$ with $x^{-1}=x^0$, the paired sequence is $z^k=(x^k,x^{k-1})\in E\times E$.
--
--   **Formalization Note** $z^k$ lives in the Euclidean product `WithLp 2 (E × E)`.
-- source:
--   Phan, Le Thi, DCA based algorithm with extrapolation for nonconvex nonsmooth optimization, arXiv:2106.04743v1, proof of Theorem 3.2, p.8, Denote zk = (xk, xk−1)

import Mathlib
import Definitions.Def_DCAExtrap_prev

namespace DCAExtrap

/-- **The paired sequence** `z^k = (x^k, x^{k−1})` (Phan–Le Thi, arXiv:2106.04743v1, proof of
Theorem 3.2, p.8), with `x^{−1} = x^0`.

**Formalization Note.** `z^k` lives in the Euclidean product `WithLp 2 (E × E)`. -/
def zseq {E : Type*} (x : ℕ → E) (k : ℕ) : WithLp 2 (E × E) :=
  WithLp.toLp 2 (x k, prev x k)

end DCAExtrap


