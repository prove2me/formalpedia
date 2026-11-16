-- Prove2me | Definitions.Def_DistQuantumQuery_Supplement_schurChannel
-- name    : DistQuantumQuery_Supplement_schurChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:44:43.671949+00:00
-- url     : https://prove2.me/theorems/d8cec7c3-3d3b-4037-b784-963dc5657a79
-- title:
--   Hadamard map $E_G(X)=X\circ G^\top$ of a matrix $G$
-- statement:
--   For a complex $n\times n$ matrix $G$, the map $E_G:\mathrm L(\mathbb C^n)\to\mathrm L(\mathbb C^n)$ is
--   $$
--   E_G(X):=X\circ G^\top,\qquad E_G(X)(i,j)=X(i,j)\,G(j,i),
--   $$
--   the entrywise (Hadamard) product of $X$ with the transpose of $G$. It is linear in $X$.
--
--   Theorem 2.5 of the paper states that $E_G$ is a quantum channel whenever $G$ is a Gram matrix of unit vectors; such Hadamard channels are how the paper moves between Gram matrices of state families.
--
--   **Formalization Note** The index set $[n]$ is a finite type and the map is packaged as a $\mathbb C$-linear map. No condition on $G$ is built in: positive semidefiniteness and the unit diagonal are hypotheses of Theorem 2.5.
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), §2.3.3, Theorem 2.5, p.16

import Mathlib

open scoped Matrix

namespace DistQuantumQuery.Supplement

/-- The **Hadamard (Schur) map of a Gram matrix**, `E_G : L(ℂ^n) → L(ℂ^n)`,
`E_G(X) := X ∘ G^⊤`, the entrywise product of `X` with the transpose of `G`
(Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835, held version,
sha256 6334ffaf…, §2.3.3, Theorem 2.5, p.16).

**Formalization Note** `ℂ^n` is `ℂ^ι` for a finite index type `n`; the map is packaged as a
`ℂ`-linear map (linearity of the Hadamard product in its first argument). No condition on `G` is
built in; the hypotheses of Theorem 2.5 (positive semidefinite, unit diagonal) are binders of
that theorem. -/
def schurChannel {n : Type*} (G : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := X ⊙ Gᵀ
  map_add' X Y := by ext i j; simp [add_mul]
  map_smul' c X := by ext i j; simp [mul_assoc]

end DistQuantumQuery.Supplement


