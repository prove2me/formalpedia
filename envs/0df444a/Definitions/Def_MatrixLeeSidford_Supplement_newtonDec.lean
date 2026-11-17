-- Prove2me | Definitions.Def_MatrixLeeSidford_Supplement_newtonDec
-- name    : MatrixLeeSidford_Supplement_newtonDec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:14:29.994611+00:00
-- url     : https://prove2.me/theorems/cdc7f31a-703d-435a-b138-c7437ff26d77
-- title:
--   Newton decrement $\lambda_c(y)=\|\nabla\phi_c(y)\|_{\nabla^2F(y)^{-1}}$
-- statement:
--   Let $F=\alpha\Phi_p$ be the matrix Lee–Sidford barrier on $\Omega=\{y:S(y)\succ0\}$, with $s=2\lceil\log(2mn)\rceil$ and $\alpha=10^6s^2$. For an objective vector $c\in\mathbb R^m$, the **penalized objective** and its **Newton decrement** are
--   $$
--   \phi_c(y):=F(y)+c^\top y,\qquad \lambda_c(y):=\big\|\nabla\phi_c(y)\big\|_{\nabla^2F(y)^{-1}}=\sqrt{\nabla\phi_c(y)^\top\,\nabla^2F(y)^{-1}\,\nabla\phi_c(y)} .
--   $$
--   A point is centered for $c$ to tolerance $\delta$ when $\lambda_c(y)\le\delta$.
--
--   **Formalization Note** $F$ is the base mission's published barrier, $\nabla\phi_c$ is the Euclidean gradient, and the dual local norm is the published one (inverse of the Hessian matrix of $F$, positive definite on $\Omega$ by Theorem 2.1).
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Section 8.1, p.53

import Mathlib
import Definitions.Def_MatrixLeeSidford_barrierF
import Definitions.Def_DoublyOptBandit_LocalNorm

open Matrix

namespace MatrixLeeSidford.Supplement

/-- The **Newton decrement** `λ_c(y) := ‖∇ϕ_c(y)‖_{∇²F(y)⁻¹}` of the penalized objective
`ϕ_c(y) := F(y) + cᵀy`, with `F = αΦ_p` the matrix Lee–Sidford barrier (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Section 8.1, p.53).

**Formalization Note** `F` is the published `barrierF A C` (`s = sParam m n`, `α = alphaParam s`);
`∇ϕ_c(y)` is Mathlib's `gradient` on `EuclideanSpace ℝ (Fin m)` and `cᵀy` the Euclidean inner product;
the dual local norm is the published `DoublyOptBandit.dualLocalNorm`, `√(vᵀ H⁻¹ v)` with `H` the matrix
of `iteratedFDeriv ℝ 2 F y` (the paper's `∇²F(y)`, positive definite on `Ω` by Theorem 2.1(b)). -/
noncomputable def newtonDec {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (c y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  DoublyOptBandit.dualLocalNorm (barrierF A C) y
    (gradient (fun x : EuclideanSpace ℝ (Fin m) => barrierF A C x + inner ℝ c x) y)

end MatrixLeeSidford.Supplement


