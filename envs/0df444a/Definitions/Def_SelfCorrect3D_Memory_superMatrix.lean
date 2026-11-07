-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_superMatrix
-- name    : SelfCorrect3D_Memory_superMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:37.325903+00:00
-- url     : https://prove2.me/theorems/85e4fda0-e0ea-4910-8728-0bd6fd5a6cff
-- title:
--   Matrix of a superoperator on vectorized operators
-- statement:
--   A map $\mathcal T$ on $n$-qubit operators is represented by the matrix indexed by pairs of basis labels with entries
--
--   $$\bigl[\mathcal T\bigr]_{(x,y),(x',y')}=\bigl(\mathcal T(|x'\rangle\langle y'|)\bigr)_{xy}.$$
--
--   For linear $\mathcal T$, $\operatorname{vec}\mathcal T(\rho)=[\mathcal T]\operatorname{vec}\rho$ with $(\operatorname{vec}\rho)_{(x,y)}=\rho_{xy}$; this is used to write the time evolution as a matrix exponential.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, eq. (48), p. 21 (auxiliary)

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_Op

namespace SelfCorrect3D.Memory

/-- **Matrix of a superoperator** acting on vectorized operators: for `L : Op n → Op n`, the matrix
indexed by pairs of basis labels with entry `((x, y), (x', y')) = (L |x'⟩⟨y'|)_{x y}`.
Used to write the evolution `e^{t𝓛̂}` of Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, eq. (48), p. 21, as a
matrix exponential.

**Formalization Note.** For linear `L`, `vec (L ρ) = superMatrix L *ᵥ vec ρ` with
`vec ρ (x, y) = ρ x y`. -/
def superMatrix {n : ℕ} (L : Op n → Op n) :
    Matrix ((Fin n → ZMod 2) × (Fin n → ZMod 2)) ((Fin n → ZMod 2) × (Fin n → ZMod 2)) ℂ :=
  Matrix.of fun p q => L (Matrix.single q.1 q.2 1) p.1 p.2

end SelfCorrect3D.Memory


