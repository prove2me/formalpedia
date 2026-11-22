-- Prove2me | Definitions.Def_SelfSelReg_Supplement_EigDecomp
-- name    : SelfSelReg_Supplement_EigDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:16:03.426855+00:00
-- url     : https://prove2.me/theorems/28e88a0a-4edd-4115-aa52-792dd569ab8b
-- title:
--   Eigendecomposition of a symmetric matrix: eigenvalues $\lambda_1\ge\dots\ge\lambda_p$ with orthonormal eigenvectors
-- statement:
--   Algorithms 6.2 and 6.3 contain the step "compute the eigenvalues $\widehat\lambda_1\ge\dots\ge\widehat\lambda_p$ and corresponding orthonormal eigenvectors $\widehat v_1,\dots,\widehat v_p$". For a real $p\times p$ matrix $M$, a pair $(\lambda,V)$ with $\lambda\in\mathbb R^p$ and $V\in\mathbb R^{p\times p}$ is an eigendecomposition of $M$ if
--
--   1. $\lambda_1\ge\lambda_2\ge\dots\ge\lambda_p$;
--   2. the rows $v_1,\dots,v_p$ of $V$ are orthonormal, $VV^\top=I_p$;
--   3. $Mv_h=\lambda_hv_h$ for every $h\in[p]$.
--
--   Equivalently $M=V^\top\operatorname{diag}(\lambda)V$; such a pair exists exactly when $M$ is symmetric. The eigenvalues are determined by $M$, the eigenvectors only up to sign and up to a rotation inside each eigenspace of a repeated eigenvalue.
--
--   The algorithm specifications of this supplement quantify over all eigendecompositions, so the theorems about them hold for every choice the pseudocode leaves open.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Algorithm 6.2, line 1, p.39 (PDF p.42); Algorithm 6.3, line 5, p.43 (PDF p.46)

import Mathlib

namespace SelfSelReg

namespace Supplement

/-- **An eigendecomposition in the sense of the pseudocode** of Algorithms 6.2 and 6.3.

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Algorithm 6.2, line 1, p.39 (PDF p.42): "Compute the eigenvalues
λ̂_1 ≥ ⋯ ≥ λ̂_{p_s} and corresponding orthonormal eigenvectors v̂_1, …, v̂_{p_s} of Â"; Algorithm 6.3,
line 5, p.43 (PDF p.46).

`IsEigDecomp M vals V`: `vals` is nonincreasing, the rows of `V` are orthonormal, and row `h` of `V`
is an eigenvector of the `p × p` matrix `M` for the eigenvalue `vals h`.

**Formalization Note.** The eigenvalues are determined by `M`; the eigenvectors are determined only
up to sign, and up to a rotation inside each eigenspace of a repeated eigenvalue. Every statement
using this predicate holds for every such choice. A matrix with an eigendecomposition is symmetric. -/
def IsEigDecomp {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (vals : Fin p → ℝ)
    (V : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  Antitone vals ∧ V * V.transpose = 1 ∧ ∀ h, M.mulVec (V h) = vals h • V h

end Supplement

end SelfSelReg


