-- Prove2me | Definitions.Def_linear_neumann_offdiag_bernstein
-- name    : linear_neumann_offdiag_bernstein
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-24T14:38:30.462491+00:00
-- url     : https://prove2.me/theorems/f0eb0283-853f-404c-8655-5846c5f5e5ee
-- statement:
--   Reusable vocabulary for Lemma 6.6 in the Candes--Recht proof of Lemma 4.5.
--
--   For a fixed output coordinate $w=(a,b)$, `linearNeumannOffDiagonalCoefficientBaseMatrix S w` is the fixed matrix
--   $$B^{(w)}_{a'b'}=\mathbf 1_{(a',b')\ne w}\,E_{a'b'}\,\langle P_T(e_{a'}e_{b'}^{\mathsf T}),e_a e_b^{\mathsf T}\rangle,$$
--   where $E=UV^{\mathsf T}$ is the sign matrix.  The scalar Bernstein argument in Candes--Recht equation (6.14) applies centered sampling to this fixed matrix to control the corresponding entry of the coefficient matrix $Q(E)$.
--
--   Source location: Candes--Recht, Section 6.2, equations (6.13)--(6.14), followed by Lemma 6.6.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann

/-!
Auxiliary base matrices for the scalar Bernstein proof of the off-diagonal
first Neumann coefficient bound.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Fixed matrix whose centered sampling fluctuation gives one entry of the
conditional coefficient matrix `Q(E)` from Candes--Recht equation (6.14).

For output coordinate `w = (a,b)`, this matrix has entries
`E_{a'b'} * <P_T(e_{a'b'}), e_ab>` away from the diagonal coordinate `w`, and
zero at `w` itself. -/
noncomputable def linearNeumannOffDiagonalCoefficientBaseMatrix
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (w : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  fun i j =>
    if (i, j) = w then 0
    else signMatrix S i j * tangentCoordinateKernel S i j w.1 w.2

end MatrixCompletion


