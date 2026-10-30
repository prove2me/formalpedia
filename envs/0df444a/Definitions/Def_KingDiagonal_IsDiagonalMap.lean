-- Prove2me | Definitions.Def_KingDiagonal_IsDiagonalMap
-- name    : KingDiagonal_IsDiagonalMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:45.528929+00:00
-- url     : https://prove2.me/theorems/e026c063-d2d2-4cba-b63e-bc1dd5b117ca
-- title:
--   Diagonal map (Definition 3): $\Phi(\rho) = C * \rho$ with $C \succeq 0$
-- statement:
--   Let $n$ be a finite index set and $M_n$ the complex $n\times n$ matrices. Recall the Hadamard (entrywise) product $(A * B)_{ij} = A_{ij}B_{ij}$. A map $\Phi : M_n \to M_n$ is **diagonal** if there is a positive semidefinite matrix $C \in M_n$ such that
--
--   $$
--   \Phi(\rho) = C * \rho \qquad\text{for every } \rho \in M_n .
--   $$
--
--   This is the class of channels studied by Landau and Streater; King's Theorem 4 shows that the maximal output $p$-norm of such a map is multiplicative with every completely positive partner. Every diagonal map is completely positive (Schur product theorem), and it is trace preserving exactly when every $C_{ii} = 1$, which is **not** assumed.
--
--   **Formalization Note** The index set is an arbitrary finite type (possibly empty). Maps are plain functions `Superop n n` on matrices; the identity $\Phi(\rho) = C * \rho$ is required on all matrices. The Definition's word "CP map" is not a separate clause, since it follows from $C \succeq 0$.
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, Definition 3, eq. (6), p.3 (Hadamard product (5), p.3)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel

open QAlgorithms
open scoped ComplexOrder

namespace KingDiagonal

/-- King, *An application of a matrix inequality in quantum information theory*,
arXiv:quant-ph/0412046v1, Definition 3, eq. (6), p.3 (with the Hadamard product (5), p.3):
the map `Φ : M_n → M_n` is *diagonal* if there is a positive semidefinite matrix `C` with
`Φ(ρ) = C ∗ ρ` for every `ρ`, where `(C ∗ ρ)_{ij} = C_{ij} ρ_{ij}` is the Hadamard product.

**Formalization Note.** The index set `n` is an arbitrary finite type (possibly empty), not
`Fin n`. The identity is required on every matrix `ρ`, not only on states, which is the page's
`Φ(ρ) = C ∗ ρ`. Definition 3 calls `Φ` a CP map; complete positivity is not added as a separate
clause because every map `ρ ↦ C ∗ ρ` with `C ⪰ 0` is completely positive (Schur product
theorem), so the clause would exclude nothing. Trace preservation is not assumed (p.3). -/
def IsDiagonalMap {n : Type*} [Fintype n] (Φ : Superop n n) : Prop :=
  ∃ C : Matrix n n ℂ, C.PosSemidef ∧ ∀ ρ : Matrix n n ℂ, Φ ρ = Matrix.hadamard C ρ

end KingDiagonal


