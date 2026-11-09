-- Prove2me | Definitions.Def_OddPermSum_Evaluation_gradientCoefficient
-- name    : OddPermSum_Evaluation_gradientCoefficient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:40.74024+00:00
-- url     : https://prove2.me/theorems/77e3551a-891c-4bb4-ace6-371c56d550ca
-- title:
--   Coefficient matrix in the full-gradient formula
-- statement:
--   For equally sized square matrices $A,B$ over a commutative ring, define
--
--   $$C(A,B)_{p,j}=A_{p,j}^{\,2}B_{j,p}.$$
--
--   In Proposition 4.2, $B=A^{-1}$. The square belongs to the entry of $A$, and the entry of $B$ has reversed indices. This matrix is distinct from the collection of column-tree splits also denoted $\mathcal C$ in Section 3.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 11, Section 4.2, definition preceding Proposition 4.2

import Mathlib

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Section 4.2's C, not the column-tree split collection. -/
def gradientCoefficient {R : Type*} [CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  fun p j => (A p j)^2 * B j p

end OddPermSum.Evaluation


