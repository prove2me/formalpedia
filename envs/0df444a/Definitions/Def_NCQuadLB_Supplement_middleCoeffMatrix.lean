-- Prove2me | Definitions.Def_NCQuadLB_Supplement_middleCoeffMatrix
-- name    : NCQuadLB_Supplement_middleCoeffMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:46:48.526026+00:00
-- url     : https://prove2.me/theorems/8b3f9b57-653c-404b-b6b6-f098f74cf368
-- title:
--   The middle coefficient matrix $M_f^{d,d}$ of a noncommutative polynomial
-- statement:
--   Let $f\in\mathbb F\langle x_1,\dots,x_n\rangle$ be a noncommutative polynomial and let $d\in\mathbb N$. The **middle coefficient matrix** $M_f^{d,d}$ is the $n^d\times n^d$ matrix whose rows and columns are indexed by ordered degree-$d$ monomials $m,m'$ and whose entries are
--
--   $$
--   (M_f^{d,d})_{m,m'}=[mm']f,
--   $$
--
--   the coefficient of the concatenated word $mm'$ in $f$. Neither word is reversed or commutativized. This matrix is the coefficient-space complexity measure used in Theorem 5.1.
--
--   **Formalization Note** A degree-$d$ monomial is represented by a tuple in $(\mathrm{Fin}\,n)^d$, with indices starting at $0$. The module also defines the ordered word represented by such a tuple. Coefficients are read through the published `NCFactorClosure607.Circuits.coeff`.
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453f21da4d8e225baf84bf89c6cd2feb49797548f4efa6c67543940dcd8), §5, p.8

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Polynomials

namespace NCQuadLB

namespace Supplement

/-- The word `x_{i₁}⋯x_{i_d}` indexed by a tuple `i : Fin d → Fin n`. -/
def tupleWord {n d : ℕ} (i : Fin d → Fin n) : FreeMonoid (Fin n) :=
  FreeMonoid.ofList (List.ofFn i)

/-- The **middle coefficient matrix** `M_f^{d,d}` (Shastri–Willumsgaard,
*A Quadratic Lower Bound for Noncommutative Circuits*, arXiv:2604.20575, version of
November 2, 2026, sha256 34159453f21da4d8e225baf84bf89c6cd2feb49797548f4efa6c67543940dcd8,
§5, p.8). Its rows and columns are indexed by degree-`d` noncommutative monomials, and
the `(m,m')` entry is the coefficient of the concatenated word `mm'` in `f`.

**Formalization Note** A degree-`d` monomial is indexed by its ordered, 0-based tuple
`i : Fin d → Fin n`; hence the square matrix has `n^d` rows and columns. Neither tuple is
reversed or commutativized. Coefficients are read through the published
`NCFactorClosure607.Circuits.coeff`. -/
noncomputable def middleCoeffMatrix {F : Type*} [Field F] {n : ℕ} (d : ℕ)
    (f : FreeAlgebra F (Fin n)) : Matrix (Fin d → Fin n) (Fin d → Fin n) F :=
  fun i j => NCFactorClosure607.Circuits.coeff (tupleWord i * tupleWord j) f

end Supplement

end NCQuadLB


