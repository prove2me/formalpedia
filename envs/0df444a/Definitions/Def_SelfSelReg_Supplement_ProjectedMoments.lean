-- Prove2me | Definitions.Def_SelfSelReg_Supplement_ProjectedMoments
-- name    : SelfSelReg_Supplement_ProjectedMoments
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:14:16.036374+00:00
-- url     : https://prove2.me/theorems/07baa197-a09b-4328-9807-9d7366f58163
-- title:
--   Odd target $M_Q^{(s)}(b)$, projected moment estimates (Definition 6.2) and the projection-error condition
-- statement:
--   Fix regressors $w_1,\dots,w_k\in\mathbb R^n$, a threshold $T$, an order $s$ and a set $Q\subseteq[k]$. With the weights $\lambda_i^{(2s)}$, the unit regressors $u_i=w_i/\|w_i\|_2$ and the scaled regressors $a_i$ of Section 5, the paper sets, in (38),
--
--   $$
--   A_Q^{(s)}=\sum_{i\in Q}\lambda_i^{(2s)}\,u_i^{\otimes s}(u_i^{\otimes s})^\top,\qquad
--   M_Q^{(s)}(b)=\sum_{i\in Q}\lambda_i^{(2s)}\langle b,a_i\rangle\,u_i^{\otimes s}(u_i^{\otimes s})^\top\quad(b\in\mathbb R^n),
--   $$
--
--   both $n^s\times n^s$ matrices. The first is already published with the base mission; this bundle adds the second and the notions built on the pair.
--
--   1. **Definition 6.2.** Let $C_s\in\mathbb R^{p\times n^s}$ have orthonormal rows, $C_sC_s^\top=I_p$. Symmetric matrices $\widehat A,\widehat M_1,\dots,\widehat M_n\in\mathbb R^{p\times p}$ are an $\varepsilon$-estimate of the projected moment matrices for $Q$ relative to $C_s$ if
--   $$
--   \bigl\|\widehat A-C_sA_Q^{(s)}C_s^\top\bigr\|_F\le\varepsilon\,\operatorname{tr}(A_Q^{(s)})
--   $$
--   and, for every $b\in\mathbb R^n$,
--   $$
--   \Bigl\|\sum_{\ell=1}^n b_\ell\widehat M_\ell-C_sM_Q^{(s)}(b)C_s^\top\Bigr\|_F\le\varepsilon\,\operatorname{tr}(A_Q^{(s)})\,\|b\|_2 .
--   $$
--   2. **Projection error.** The condition $\|(I-C^\top C)A^{1/2}\|_{\mathrm{op}}^2\le\beta$ of Theorem 6.3 and (43), where $A^{1/2}$ is the positive semidefinite square root.
--   3. **Lifted Gram matrix.** The matrix $(\langle u_i^{\otimes s},u_j^{\otimes s}\rangle)_{i,j\in Q}$ of (42).
--
--   These are the interface between the moment-estimation routine (Theorem 6.3) and the observable-operator construction (Theorem 6.5).
--
--   **Formalization Note** Symmetry of the estimates and orthonormality of the rows of $C_s$ are clauses of the estimate predicate. The square root is expressed by a witness $S\succeq0$ with $S^2=A$, which exists exactly when $A\succeq0$ and is then unique. The norm $\|\cdot\|_{\mathrm{op}}$ is the spectral norm, $\|\cdot\|_F$ the Frobenius norm.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Eq. (38) and Definition 6.2 with (39), (40), p.29 (PDF p.32); (42), p.30 (PDF p.33); (43), p.31 (PDF p.34)

import Mathlib
import Definitions.Def_SelfSelReg_restrictedMoment

open scoped Matrix.Norms.L2Operator

namespace SelfSelReg

namespace Supplement

/-- The odd target matrix (38), p.29 (PDF p.32):
`M^{(s)}_Q(b) = Σ_{i∈Q} λ_i^{(2s)} ⟨b, a_i⟩ u_i^{⊗s}(u_i^{⊗s})ᵀ`, an `n^s × n^s` matrix, with `λ_i^{(2s)}`
the published `weight`, `a_i` the published `scaledReg` and `u_i` the published `unitReg`. The even
target `A^{(r)}_Q` of (38) is the published `evenTarget`. -/
noncomputable def oddTarget {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n)) (T : ℝ)
    (Q : Finset (Fin k)) (s : ℕ) (b : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin s → Fin n) (Fin s → Fin n) ℝ :=
  ∑ i ∈ Q, (weight w T i s * inner ℝ b (scaledReg w T s i)) •
    Matrix.vecMulVec (tensorPow (unitReg w i) s) (tensorPow (unitReg w i) s)

/-- `C` has orthonormal rows: `C Cᵀ = I_p` (Definition 6.2, "Let C_s : (ℝⁿ)^{⊗s} → ℝ^{p_s} have
orthonormal rows"). -/
def HasOrthonormalRows {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix (Fin p) ι ℝ) : Prop :=
  C * C.transpose = 1

/-- The projection-error condition `‖(I − CᵀC) A^{1/2}‖²_op ≤ bound` of Theorem 6.3 and (43), p.31
(PDF p.34).

**Formalization Note.** `A^{1/2}` is the positive semidefinite square root, written as a witness `S`
with `S` positive semidefinite and `S S = A`; such an `S` exists exactly when `A` is positive
semidefinite and is then unique. The norm is the spectral (`ℓ²` operator) norm. -/
def ProjectionError {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix (Fin p) ι ℝ) (A : Matrix ι ι ℝ) (bound : ℝ) : Prop :=
  ∃ S : Matrix ι ι ℝ, S.PosSemidef ∧ S * S = A ∧ ‖(1 - C.transpose * C) * S‖ ^ 2 ≤ bound

/-- **Definition 6.2** (Projected Moment Estimate).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Definition 6.2, p.29 (PDF p.32): "Let C_s : (ℝⁿ)^{⊗s} → ℝ^{p_s} have
orthonormal rows. For ε ≥ 0, we call symmetric matrices Â, M̂_1, …, M̂_n ∈ ℝ^{p_s×p_s} an ε-estimate of
the projected moment matrices for Q relative to C_s if the following bounds hold: (i) The even estimate
satisfies ‖Â − C_s A^{(s)}_Q C_sᵀ‖_F ≤ ε tr(A^{(s)}_Q) (39). (ii) For every b ∈ ℝⁿ, the odd estimates
satisfy ‖Σ_ℓ b_ℓ M̂_ℓ − C_s M^{(s)}_Q(b) C_sᵀ‖_F ≤ ε tr(A^{(s)}_Q) ‖b‖₂ (40)."

**Formalization Note.** Symmetry of `Â, M̂_ℓ` and orthonormality of the rows of `C` are clauses of the
predicate. The threshold `T` and the order `s` are explicit arguments (the paper fixes them by
Hyperparameters 4.1). The ranges `Q ≠ ∅` and `ε ≥ 0` are left to the theorems. -/
def IsProjectedMomentEstimate {n k p s : ℕ}
    (w : Fin k → EuclideanSpace ℝ (Fin n)) (T : ℝ) (Q : Finset (Fin k))
    (C : Matrix (Fin p) (Fin s → Fin n) ℝ) (Ahat : Matrix (Fin p) (Fin p) ℝ)
    (Mhat : Fin n → Matrix (Fin p) (Fin p) ℝ) (ε : ℝ) : Prop :=
  Ahat.IsHermitian ∧ (∀ l, (Mhat l).IsHermitian) ∧ HasOrthonormalRows C ∧
    matFrobNorm (Ahat - C * evenTarget w T Q s * C.transpose) ≤
      ε * Matrix.trace (evenTarget w T Q s) ∧
    ∀ b : EuclideanSpace ℝ (Fin n),
      matFrobNorm ((∑ l, b l • Mhat l) - C * oddTarget w T Q s b * C.transpose) ≤
        ε * Matrix.trace (evenTarget w T Q s) * ‖b‖

/-- The Gram matrix `(⟨u_i^{⊗s}, u_j^{⊗s}⟩)_{i,j∈Q}` of the lifted unit regressors, (42), p.30
(PDF p.33), indexed by the elements of `Q`. -/
noncomputable def liftedGram {n k : ℕ} (w : Fin k → EuclideanSpace ℝ (Fin n))
    (Q : Finset (Fin k)) (s : ℕ) : Matrix {i : Fin k // i ∈ Q} {i : Fin k // i ∈ Q} ℝ :=
  fun i j => frobInner (tensorPow (unitReg w i) s) (tensorPow (unitReg w j) s)

end Supplement

end SelfSelReg


