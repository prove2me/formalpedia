-- Prove2me | Definitions.Def_LiqPremiaEq_phiCoeff
-- name    : LiqPremiaEq_phiCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:03.080015+00:00
-- url     : https://prove2.me/theorems/b33a97a8-2818-43b8-a65f-00555dbc8c5b
-- title:
--   The coefficient $(I\otimes\Lambda^{-1/2})F^\top(I\otimes\Lambda^{-1/2})$ and $\Psi(r;t)$
-- statement:
--   For $R=\Lambda^{1/2}$ (so $R^{-1}=\Lambda^{-1/2}$) and $F\in\mathbb R^{K(N-1)\times K(N-1)}$ the coefficient of the linear ODEs (4.9) and (7.7) is
--
--   $$(I_{N-1}\otimes\Lambda^{-1/2})\,F^\top\,(I_{N-1}\otimes\Lambda^{-1/2}),$$
--
--   and for a matrix function $\Phi$ the propagator of (4.10) is
--
--   $$\Psi(r;t)=(I_{N-1}\otimes\Lambda^{1/2})\,\Phi(r)\Phi^{-1}(t)\,(I_{N-1}\otimes\Lambda^{-1/2}).$$
--
--   $\Psi^\top$ appears in the explicit equilibrium positions (4.11).
--
--   **Formalization Note** The square root is passed as an argument `R`; every theorem using it assumes $R^\top=R$, $R$ positive definite and $RR=\Lambda$, which determine $R=\Lambda^{1/2}$ uniquely (footnote 5). Lean's matrix inverse is total ($\Phi(t)^{-1}=0$ if $\Phi(t)$ is singular), so the theorems also assert that $\Phi(t)$ is invertible.
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, eqs. (4.9) and (4.10), p.8; eq. (7.7), p.18

import Mathlib

open Matrix
open scoped Kronecker

namespace LiqPremiaEq

/-- The coefficient `(I_{N−1} ⊗ Λ^{−1/2}) Fᵀ (I_{N−1} ⊗ Λ^{−1/2})` of the linear matrix ODEs
(4.9) and (7.7), where `R = Λ^{1/2}` and so `R⁻¹ = Λ^{−1/2}`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (4.9), p.8, and eq. (7.7), p.18.

**Formalization Note** `R` is passed as an argument; the theorems that use this take `R` with
`Rᵀ = R`, `R` positive definite and `R * R = Λ`, which pins `R` down as the unique symmetric
positive definite square root `Λ^{1/2}` of footnote 5 (p.5). -/
noncomputable def phiCoeff {M K : ℕ} (R : Matrix (Fin K) (Fin K) ℝ)
    (F : Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ) : Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ :=
  ((1 : Matrix (Fin M) (Fin M) ℝ) ⊗ₖ R⁻¹) * Fᵀ * ((1 : Matrix (Fin M) (Fin M) ℝ) ⊗ₖ R⁻¹)

/-- `Ψ(r; t) = (I_{N−1} ⊗ Λ^{1/2}) Φ(r) Φ⁻¹(t) (I_{N−1} ⊗ Λ^{−1/2})`, with `R = Λ^{1/2}`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (4.10), p.8.

**Formalization Note** Lean's matrix inverse is total (`Φ(t)⁻¹ = 0` if `Φ(t)` is singular);
the theorems using `Psi` assert that `Φ(t)` is invertible. -/
noncomputable def Psi {M K : ℕ} (R : Matrix (Fin K) (Fin K) ℝ)
    (Φ : ℝ → Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ) (r t : ℝ) :
    Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ :=
  ((1 : Matrix (Fin M) (Fin M) ℝ) ⊗ₖ R) * Φ r * (Φ t)⁻¹ * ((1 : Matrix (Fin M) (Fin M) ℝ) ⊗ₖ R⁻¹)

end LiqPremiaEq


