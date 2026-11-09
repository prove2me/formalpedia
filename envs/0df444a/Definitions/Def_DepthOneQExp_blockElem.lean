-- Prove2me | Definitions.Def_DepthOneQExp_blockElem
-- name    : DepthOneQExp_blockElem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:07.386059+00:00
-- url     : https://prove2.me/theorems/64db740c-6044-4d94-b4c6-25827a80ca70
-- title:
--   Block elementary matrix $E_{a,b}(r) = I + r\,e_{a,b}$ in $\mathrm{SL}(3s;\mathbb F_2)$
-- statement:
--   For $r\in\mathrm{Mat}(s;\mathbb F_2)$ and block indices $a,b\in\{1,2,3\}$, the elementary matrix of $\mathrm{EL}(3;\mathrm{Mat}(s;\mathbb F_2))$ (Eq. (2.17)) is
--   $$
--   E_{a,b}(r) = I_{3s} + r\, e_{a,b},
--   $$
--   the identity plus the block $r$ in block position $(a,b)$ of the $3\times 3$ block matrix with blocks of size $s$. By Fact 2.8 these are elements of $\mathrm{SL}(3s;\mathbb F_2)$. The module proves that for $a\ne b$ the matrix squares to the identity and has determinant $1$.
--
--   **Formalization Note** Blocks are 0-based, and row $(a,i)$ of the block matrix is row $a\cdot s+i$ of the $3s\times 3s$ matrix (0-based), so block $(a,b)$ occupies rows $as,\dots,as+s-1$ and columns $bs,\dots,bs+s-1$, as in the proof of Theorem 2.3 (p.11).
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Eq. (2.17) and Fact 2.8, p.9

import Mathlib

namespace DepthOneQExp

/-- The elementary matrix `E_{a,b}(r) = I + r e_{a,b} ∈ EL(3; Mat(s; 𝔽₂))`, viewed as a
`3s × 3s` matrix over `𝔽₂` (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the
unitary group and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87,
Eq. (2.17), p.9, and Fact 2.8, p.9: `SL(3s; 𝔽₂) = EL(3; Mat(s; 𝔽₂))`): the identity plus the
`s × s` block `r` in block position `(a, b)`.

**Formalization Note** Blocks are 0-based (`a, b ∈ Fin 3` is the paper's `a + 1, b + 1`), and
row/column `(a, i)` of the block matrix is index `a·s + i` of `Fin (3s)` (Mathlib's
`finProdFinEquiv`), so block `(a, b)` occupies rows `a·s, …, a·s + s − 1` and columns
`b·s, …, b·s + s − 1`, as on p.11. For `a ≠ b` the matrix squares to the identity
(`blockElem_mul_self`) and has determinant `1` (`det_blockElem`). -/
def blockElem (s : ℕ) (a b : Fin 3) (r : Matrix (Fin s) (Fin s) (ZMod 2)) :
    Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    ((1 : Matrix (Fin 3 × Fin s) (Fin 3 × Fin s) (ZMod 2)) +
      Matrix.of fun p q => if p.1 = a ∧ q.1 = b then r p.2 q.2 else 0)

theorem blockElem_mul_self (s : ℕ) {a b : Fin 3} (hab : a ≠ b)
    (r : Matrix (Fin s) (Fin s) (ZMod 2)) : blockElem s a b r * blockElem s a b r = 1 := by
  unfold blockElem
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv]
  set N : Matrix (Fin 3 × Fin s) (Fin 3 × Fin s) (ZMod 2) :=
    Matrix.of fun p q => if p.1 = a ∧ q.1 = b then r p.2 q.2 else 0 with hN
  have hNN : N * N = 0 := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x.1 = b
    · have : ¬ (x.1 = a ∧ q.1 = b) := fun h => hab (h.1.symm.trans hx)
      simp [hN, this]
    · have : ¬ (p.1 = a ∧ x.1 = b) := fun h => hx h.2
      simp [hN, this]
  have h2 : N + N = 0 := by
    ext p q
    simp only [Matrix.add_apply, Matrix.zero_apply]
    generalize N p q = c
    revert c
    decide
  have : (1 + N) * (1 + N) = 1 := by
    have e : (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
    rw [e, hNN, h2, add_zero, add_zero]
  rw [this, Matrix.submatrix_one_equiv]

theorem det_blockElem (s : ℕ) {a b : Fin 3} (hab : a ≠ b)
    (r : Matrix (Fin s) (Fin s) (ZMod 2)) : (blockElem s a b r).det = 1 := by
  have h := congrArg Matrix.det (blockElem_mul_self s hab r)
  rw [Matrix.det_mul, Matrix.det_one] at h
  generalize (blockElem s a b r).det = c at h
  revert c
  decide

end DepthOneQExp


