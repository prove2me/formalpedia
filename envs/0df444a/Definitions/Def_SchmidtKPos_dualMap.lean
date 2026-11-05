-- Prove2me | Definitions.Def_SchmidtKPos_dualMap
-- name    : SchmidtKPos_dualMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:23.749132+00:00
-- url     : https://prove2.me/theorems/7845d5a6-7113-4bc5-b5c1-27250aea206b
-- title:
--   The dual map $\Lambda^\dagger$ with $\operatorname{Tr}A^\dagger\Lambda(B)=\operatorname{Tr}\Lambda^\dagger(A^\dagger)B$
-- statement:
--   For a linear map $\Lambda:\mathcal M_n(\mathbb C)\to\mathcal M_m(\mathbb C)$, the dual map $\Lambda^\dagger:\mathcal M_m(\mathbb C)\to\mathcal M_n(\mathbb C)$ is defined by
--
--   $$
--   \operatorname{Tr}A^\dagger\Lambda(B)=\operatorname{Tr}\Lambda^\dagger(A^\dagger)B\qquad\text{for all } A,B .
--   $$
--
--   Writing $X=A^\dagger$, this is duality for the bilinear pairing $\operatorname{Tr}(XY)$. The map $\Lambda^\dagger$ is the witness produced in the proof of Theorem 1.
--
--   **Formalization Note** The Lean definition is the explicit entry formula $\Lambda^\dagger(X)_{ji}=\operatorname{Tr}(X\Lambda(E_{ij}))$, where $E_{ij}$ are the matrix units. The defining relation is a machine-checked sanity check.
-- source:
--   B. M. Terhal, P. Horodecki, A Schmidt number for density matrices, arXiv:quant-ph/9911117v4, Lemma 3, p. 4

import Mathlib
open scoped Matrix ComplexConjugate ComplexOrder

namespace SchmidtKPos

/-- B. M. Terhal, P. Horodecki, *A Schmidt number for density matrices*,
arXiv:quant-ph/9911117v4, Lemma 3, p.4: `Λ†`, defined by `Tr A†Λ(B) = Tr Λ†(A†)B` for all `A` and
`B`.

**Formalization Note.** Writing `X = A†`, the relation says `Tr X Λ(B) = Tr Λ†(X) B`, the dual for
the bilinear pairing `Tr(X·Y)`; so `Λ†` is complex-linear. Taking `B = E_ij` gives the explicit
entry `Λ†(X)_{ji} = Tr (X Λ(E_ij))`, which is the definition here; the defining relation is
machine-checked in `Solutions/verification/SchmidtKPos_sanity.lean`. -/
def dualMap {n m : ℕ} (Λ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := Matrix.of fun j i => (X * Λ (Matrix.single i j 1)).trace
  map_add' X Y := by
    ext j i
    simp [Matrix.add_mul, Matrix.trace_add]
  map_smul' c X := by
    ext j i
    simp [Matrix.trace_smul]

end SchmidtKPos


