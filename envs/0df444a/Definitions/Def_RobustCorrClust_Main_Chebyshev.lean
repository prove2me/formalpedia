-- Prove2me | Definitions.Def_RobustCorrClust_Main_Chebyshev
-- name    : RobustCorrClust_Main_Chebyshev
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:38:39.759442+00:00
-- url     : https://prove2.me/theorems/2c6e4849-cb5f-4a0e-a1ef-ea6b72b5b66e
-- title:
--   Chebyshev coefficients, the polynomial p_{ρ,N} and the spectral-norm bound (Definitions 8–9)
-- statement:
--   $T_k$ are the Chebyshev polynomials of the first kind: $T_0=1$, $T_1=x$, $T_{k+1}=2xT_k-T_{k-1}$ (Definition 8).
--
--   **Definition 9.** $c_0=1/\pi$, $c_1=1/2$, $c_{2m}=\frac2\pi\cdot\frac{(-1)^{m+1}}{4m^2-1}$ for $m\ge1$, and $c_k=0$ for odd $k\ge3$. For $\rho>0$, $N\ge1$,
--   $$p_{\rho,N}(t)=\rho\sum_{k=0}^{2N}c_k\,T_k(t/\rho),$$
--   a real polynomial, applied to a square matrix as a matrix polynomial (for symmetric $M=\sum_i\lambda_iw_iw_i^\top$ this is $\sum_ip_{\rho,N}(\lambda_i)w_iw_i^\top$, Fact 3.4).
--
--   $\|M\|_{\mathrm{op}}\le\rho$ means $\|Mx\|_2\le\rho\|x\|_2$ for every $x\in\mathbb R^n$ (spectral norm).
--
--   **Formalization Note.** $T_k$ is Mathlib's `Polynomial.Chebyshev.T ℝ k`; the spectral-norm bound is written with squared Euclidean norms.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), pp. 40-41, Definitions 8-9

import Mathlib

namespace RobustCorrClust.Main

open Finset Polynomial

/-! The Chebyshev approximation of the positive part (§5.8, pp. 40–41, Definitions 8–9). -/

/-- The coefficients of Definition 9 (p. 41): `c₀ = 1/π`, `c₁ = 1/2`,
`c_{2m} = (2/π)·(−1)^{m+1}/(4m² − 1)` for `m ≥ 1`, and `c_k = 0` for odd `k ≥ 3`. -/
noncomputable def chebCoeff (k : ℕ) : ℝ :=
  if k = 0 then 1 / Real.pi
  else if k = 1 then 1 / 2
  else if k % 2 = 0 then
    (2 / Real.pi) * (-1 : ℝ) ^ (k / 2 + 1) / (4 * ((k / 2 : ℕ) : ℝ) ^ 2 - 1)
  else 0

/-- Definition 9 (p. 41): `p_{ρ,N}(t) := ρ ∑_{k=0}^{2N} c_k T_k(t/ρ)`, as a real polynomial in `t`,
with `T_k` the Chebyshev polynomials of the first kind (Definition 8, p. 40). -/
noncomputable def chebPoly (ρ : ℝ) (N : ℕ) : ℝ[X] :=
  C ρ * ∑ k ∈ range (2 * N + 1),
    C (chebCoeff k) * (Chebyshev.T ℝ (k : ℤ)).comp (C ρ⁻¹ * X)

/-- `‖M‖_op ≤ ρ` for the spectral (ℓ²-operator) norm: `‖M x‖₂ ≤ ρ ‖x‖₂` for every `x`, written
with squared Euclidean norms (for `ρ ≥ 0`). -/
def OpNormLE {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, ∑ i, (M.mulVec x i) ^ 2 ≤ ρ ^ 2 * ∑ i, x i ^ 2

end RobustCorrClust.Main


