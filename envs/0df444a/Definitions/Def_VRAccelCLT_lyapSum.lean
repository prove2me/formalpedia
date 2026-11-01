-- Prove2me | Definitions.Def_VRAccelCLT_lyapSum
-- name    : VRAccelCLT_lyapSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:13.082317+00:00
-- url     : https://prove2.me/theorems/35cd553b-c887-40a5-bb64-9a24257634ca
-- title:
--   Covariance series $\sum_{t\ge0}P^tC(P^t)^T$
-- statement:
--   For square matrices $P$ and $C$ of the same size, define
--
--   $$
--   \Sigma(P,C)=\sum_{t=0}^{\infty}P^{t}\,C\,(P^{t})^{T}.
--   $$
--
--   When $\rho(P)<1$ the series converges and $\Sigma$ is the unique solution of the discrete Lyapunov equation $\Sigma=P\Sigma P^T+C$. Lemma 7 uses $C=GS_0G^T$; Theorem 2 uses $C=\begin{pmatrix}S_0&0\\0&0\end{pmatrix}$.
--
--   **Formalization Note** The sum is an unconditional infinite sum of matrices. A non-summable series has sum $0$ in Lean, so each theorem using it also asserts summability.
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Lemma 7, p.16; Theorem 2, p.19

import Mathlib

namespace VRAccelCLT

/-- **The covariance series** `Σ ≜ Σ_{t=0}^∞ P^t C (P^t)^T`. Lei, Shanbhag, arXiv:2006.07769v3,
Lemma 7, p.16 (`C = G S₀ Gᵀ`), Theorem 1, p.16 and Theorem 2, p.19 (`C = diag(S₀, 0)`).

**Formalization Note.** This is a `tsum` in the space of matrices (entrywise topology). A `tsum` of
a non-summable series is `0` in Lean, so every theorem using `lyapSum` also asserts summability of
the series in its conclusion. -/
noncomputable def lyapSum {n : Type*} [Fintype n] [DecidableEq n] (P C : Matrix n n ℝ) :
    Matrix n n ℝ :=
  ∑' t : ℕ, P ^ t * C * (P ^ t).transpose

end VRAccelCLT


