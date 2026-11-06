-- Prove2me | Definitions.Def_PADMPriv_omegaA
-- name    : PADMPriv_omegaA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:55.975684+00:00
-- url     : https://prove2.me/theorems/9ee53b14-4f6a-4e4d-8284-c134d768d173
-- title:
--   $\omega_A$, the smallest eigenvalue of $AA^\top$
-- statement:
--   For $A \in \mathbb R^{m\times p}$, $\omega_A$ denotes the smallest eigenvalue of the symmetric positive semidefinite matrix $AA^\top \in \mathbb R^{m\times m}$:
--   $$
--   \omega_A := \min_{1\le i\le m} \lambda_i(AA^\top).
--   $$
--   If $A$ has full row rank and $m \ge 1$, then $\omega_A > 0$ and the spectral norm of $V = A^\top(AA^\top)^{-1}$ is $1/\sqrt{\omega_A}$. It enters every sensitivity and utility bound of the paper through $C = L/(\beta\sqrt{\omega_A})$.
--
--   **Formalization Note** The eigenvalues are Mathlib's eigenvalues of the Hermitian matrix $AA^{\mathsf H}$ ($=AA^\top$ for real $A$), and the minimum is an infimum over $\{1,\dots,m\}$; it is only used with $m \ge 1$.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Proposition 4.1, p.9

import Mathlib

namespace PADMPriv

/-- `ω_A`, the smallest eigenvalue of `AAᵀ` for `A ∈ ℝ^{m×p}` (Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d),
Proposition 4.1, p.9). It is positive when `A` has full row rank and `m ≥ 1`.

**Formalization Note** `AAᵀ` is written `A * Aᴴ` (for real matrices `Aᴴ = Aᵀ`), and its
eigenvalues are Mathlib's `Matrix.IsHermitian.eigenvalues`; `ω_A` is their infimum over
`Fin m`, which is the minimum for `m ≥ 1` (every use assumes `0 < m`; the value at `m = 0`
is the junk `0`). -/
noncomputable def omegaA {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ⨅ i : Fin m, (Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i

end PADMPriv


