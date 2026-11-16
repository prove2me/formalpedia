-- Prove2me | Definitions.Def_ROLDescent_Supplement_lambdaMax
-- name    : ROLDescent_Supplement_lambdaMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:56:00.94321+00:00
-- url     : https://prove2.me/theorems/4fb4d650-0c78-457a-81fb-be8feb577ae3
-- title:
--   Largest real eigenvalue $\lambda_{\max}$ of a real square matrix
-- statement:
--   For a real square matrix $A$, $\lambda_{\max}(A)$ is the supremum of the real numbers $r$ for which there is a nonzero real vector $z$ with $Az=rz$.
--
--   The signed influence matrix is not symmetric but is similar to a real symmetric matrix, so all its eigenvalues are real with real eigenvectors; for such a matrix this supremum is the largest eigenvalue, the quantity $\lambda_{\max}(\Psi^{\mu_{S,s}})$ of eq. (115).
--
--   **Formalization Note** Defined as `sSup` of the set of real eigenvalues with real eigenvectors; it is not defined through a symmetric-matrix API.
-- source:
--   Hayakawa, Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local Spectral Expansion, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Theorem 6.4, eq. (115), p.50, and its proof, p.52 (PDF 50, 52)

import Mathlib

namespace ROLDescent.Supplement

/-- **Largest real eigenvalue** `λ_max` of a real square matrix.
Hayakawa, *Recursive Operator Localization and Spectral Gap Descent via the Geometry of Local
Spectral Expansion*, arXiv:2610.23695 (held version, sha256 702bd512…20bdd545), Theorem 6.4, eq. (115), p.50 and its proof, p.52 (PDF 50, 52): the signed influence matrix Ψ
is not symmetric, but "is similar to Σ̂ − I … Thus the influence matrix has real eigenvalues", and
(115) uses `λ_max(Ψ^{µS,s})`.

**Formalization Note** The supremum of the set of real `r` admitting a nonzero real eigenvector
`A z = r z`. For a real matrix similar to a real symmetric one (as Ψ is), every eigenvalue is real
with a real eigenvector, the set is the finite nonempty spectrum (index type nonempty), and the
supremum is its maximum. Not defined through a symmetric-matrix API. -/
noncomputable def lambdaMax {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ :=
  sSup {r : ℝ | ∃ z : ι → ℝ, z ≠ 0 ∧ A.mulVec z = r • z}

end ROLDescent.Supplement


