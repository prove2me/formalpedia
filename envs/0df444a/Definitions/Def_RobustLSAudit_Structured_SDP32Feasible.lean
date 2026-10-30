-- Prove2me | Definitions.Def_RobustLSAudit_Structured_SDP32Feasible
-- name    : RobustLSAudit_Structured_SDP32Feasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:01:07.708798+00:00
-- url     : https://prove2.me/theorems/976eb334-1ecc-47ed-abb5-ca8631ba536a
-- title:
--   Corrected SDP feasibility and global optimality for structured robust least squares
-- statement:
--   Let $A_0,\ldots,A_p\in\mathbb R^{n\times m}$ and $b_0,\ldots,b_p\in\mathbb R^n$ be arbitrary real data, with all dimensions finite. For $x\in\mathbb R^m$ put $a(x)=A_0x-b_0$ and $M(x)=[A_1x-b_1\ \cdots\ A_px-b_p]$. For $\lambda,\tau\in\mathbb R$, define corrected feasibility by
--
--   $$
--   \operatorname{Feas}(\lambda,\tau,x)\iff \tau\ge0\ \text{and}\ B(\lambda,\tau,x)=\begin{bmatrix}\lambda-\tau&0&a(x)^T\\0&\tau I_p&M(x)^T\\a(x)&M(x)&I_n\end{bmatrix}\succeq0.
--   $$
--
--   A triple is optimal precisely when it is feasible and $\lambda\le\lambda'$ for every feasible triple $(\lambda',\tau',x')$, with $x'$ ranging over all of $\mathbb R^m$.
--
--   These predicates retain the published matrix and add only the nonnegative multiplier from the S-procedure preamble. When $p\ge1$ that constraint is already implied by the matrix. For $p=0$, zero data would otherwise allow $\tau=\lambda<0$ with a PSD matrix and an objective unbounded below. The explicit constraint repairs that case. The predicates assume neither exactness nor existence of an optimum; those are theorem conclusions.
--
--   **Formalization Note** The source model is imported unchanged from `RobustLS_Structured_Core`. Zero dimensions, singular matrices, and nonunique solutions are permitted.
-- source:
--   El Ghaoui and Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), https://doi.org/10.1137/S0895479896298130, §4.1 Eq. (29) preamble and §4.2 Theorem 4.2, Eq. (32), printed pp. 1044–1045 / PDF pp. 10–11.

import Definitions.Def_RobustLS_Structured_Core

namespace RobustLSAudit.Structured

/-- Theorem 4.2, Eq. (32), El Ghaoui--Lebret (1997), printed p. 1045 / PDF p. 11.
Corrected feasibility retains the S-procedure's `τ ≥ 0` explicitly. For `p ≥ 1` this is
already implied by the published block matrix; for `p = 0` it repairs the printed SDP.
The matrix and all residual data are the published source objects, without rank assumptions. -/
def SDP32Feasible {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ)
    (b : Fin p → Fin n → ℝ) (lam τ : ℝ) (x : Fin m → ℝ) : Prop :=
  0 ≤ τ ∧ RobustLS.Structured.SDP32Feasible A0 A b0 b lam τ x

/-- A feasible triple whose objective `λ` is no greater than that of every corrected-feasible
triple, with the decision vector ranging over all of `ℝ^m`. No existence is built into
this predicate; existence is a conclusion of `srls_sdp_exact_attained`. -/
def SDP32Optimal {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ)
    (b : Fin p → Fin n → ℝ) (lam τ : ℝ) (x : Fin m → ℝ) : Prop :=
  SDP32Feasible A0 A b0 b lam τ x ∧
    ∀ (lam' τ' : ℝ) (x' : Fin m → ℝ), SDP32Feasible A0 A b0 b lam' τ' x' → lam ≤ lam'

end RobustLSAudit.Structured


