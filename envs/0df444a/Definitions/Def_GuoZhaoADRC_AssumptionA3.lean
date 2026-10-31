-- Prove2me | Definitions.Def_GuoZhaoADRC_AssumptionA3
-- name    : GuoZhaoADRC_AssumptionA3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:09.080559+00:00
-- url     : https://prove2.me/theorems/f940d778-d0ca-45b0-b492-569799ca648c
-- title:
--   Assumption A3 — the reference model: Lipschitz $\varphi_i$, $\varphi_i(0)=0$ and the Lyapunov pair $(V_2^i,W_2^i)$
-- statement:
--   Assumption A3 on the reference model (1.4), together with $\varphi_i(0,\dots,0)=0$ from (1.4). For every $1\le i\le m$, $\varphi_i:\mathbb R^{n_i}\to\mathbb R$ is globally Lipschitz with constant $L_i$, $|\varphi_i(x)-\varphi_i(y)|\le L_i\|x-y\|$, and the positive definite continuously differentiable functions $V_2^i,W_2^i:\mathbb R^{n_i}\to\mathbb R$ and constants $\lambda^i_{21},\dots,\lambda^i_{24},\beta^i_2$, with $\lambda^i_{21}>0$ and $\lambda^i_{23}>0$, satisfy for all $y\in\mathbb R^{n_i}$:
--
--   1. $\lambda^i_{21}\|y\|^2\le V_2^i(y)\le\lambda^i_{22}\|y\|^2$ and $\lambda^i_{23}\|y\|^2\le W_2^i(y)\le\lambda^i_{24}\|y\|^2$;
--   2. $$\sum_{j=1}^{n_i-1}y_{j+1}\frac{\partial V_2^i}{\partial y_j}(y)+\varphi_i(y_1,\dots,y_{n_i})\frac{\partial V_2^i}{\partial y_{n_i}}(y)\le-W_2^i(y);$$
--   3. $\Bigl|\dfrac{\partial V_2^i}{\partial y_{n_i}}(y)\Bigr|\le\beta^i_2\|y\|$.
--
--   So the reference system $\dot x^{i*}_j=x^{i*}_{j+1}$, $\dot x^{i*}_{n_i}=\varphi_i(x^{i*})$ is globally exponentially stable with Lyapunov function $V_2^i$.
--
--   **Formalization Note** Indices are 0-based. Reading: $\lambda^i_{21}>0$ and $\lambda^i_{23}>0$ are required (the page says only "constants"; the proof divides by $\min\lambda^i_{21}$ and $\lambda=\min\lambda^i_{23}$). Positive definite means $V(0)=0$ and $V(y)>0$ for $y\ne0$.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eq. (1.4), p.1728; Assumption A3, p.1730

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_partialDeriv

namespace GuoZhaoADRC

/-- **Assumption A3 (the reference model) and `φ_i(0) = 0` of (1.4).**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eq. (1.4), p.1728, and Assumption A3, p.1730.

For every `1 ≤ i ≤ m`, `φ_i(0, …, 0) = 0` ((1.4)), `φ_i` is globally Lipschitz with constant
`L_i`, `|φ_i(x) − φ_i(y)| ≤ L_i‖x − y‖`, and there exist constants
`λ^i_21, λ^i_22, λ^i_23, λ^i_24, β^i_2` and positive definite continuously differentiable
`V_2^i, W_2^i : ℝ^{n_i} → ℝ` with
(1) `λ^i_21‖y‖² ≤ V_2^i(y) ≤ λ^i_22‖y‖²`, `λ^i_23‖y‖² ≤ W_2^i(y) ≤ λ^i_24‖y‖²`;
(2) `∑_{j=1}^{n_i−1} y_{j+1} ∂V_2^i/∂y_j(y) + φ_i(y_1, …, y_{n_i}) ∂V_2^i/∂y_{n_i}(y) ≤ −W_2^i(y)`;
(3) `|∂V_2^i/∂y_{n_i}(y)| ≤ β^i_2‖y‖` for all `y ∈ ℝ^{n_i}`.

**Formalization Note.** Indices are 0-based (`Fin (n i)`). In (2) the `j`-th term carries
`y_{j+1}` when `j + 1 < n i` and `φ_i(y)` for the last index `j + 1 = n i`. Reading:
`λ^i_21 > 0` and `λ^i_23 > 0` (the proof divides by `min λ^i_21` and by `λ = min λ^i_23`).
"Positive definite" is `V(0) = 0` and `V(y) > 0` for `y ≠ 0`. -/
structure AssumptionA3 {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s) : Prop where
  /-- `φ_i(0) = 0`, from (1.4). -/
  φ_zero : ∀ i, D.φ i 0 = 0
  /-- `φ_i` is globally Lipschitz with constant `L_i`. -/
  φ_lipschitz : ∀ i, LipschitzWith (D.L i) (D.φ i)
  /-- `V_2^i` is continuously differentiable. -/
  V2_contDiff : ∀ i, ContDiff ℝ 1 (D.V2 i)
  /-- `W_2^i` is continuously differentiable. -/
  W2_contDiff : ∀ i, ContDiff ℝ 1 (D.W2 i)
  /-- `V_2^i` is positive definite. -/
  V2_posDef : ∀ i, D.V2 i 0 = 0 ∧ ∀ y, y ≠ 0 → 0 < D.V2 i y
  /-- `W_2^i` is positive definite. -/
  W2_posDef : ∀ i, D.W2 i 0 = 0 ∧ ∀ y, y ≠ 0 → 0 < D.W2 i y
  /-- `λ^i_21 > 0` (reading). -/
  lam21_pos : ∀ i, 0 < D.lam21 i
  /-- `λ^i_23 > 0` (reading). -/
  lam23_pos : ∀ i, 0 < D.lam23 i
  /-- A3 (1), first part. -/
  V2_bounds : ∀ i y, D.lam21 i * ‖y‖ ^ 2 ≤ D.V2 i y ∧ D.V2 i y ≤ D.lam22 i * ‖y‖ ^ 2
  /-- A3 (1), second part. -/
  W2_bounds : ∀ i y, D.lam23 i * ‖y‖ ^ 2 ≤ D.W2 i y ∧ D.W2 i y ≤ D.lam24 i * ‖y‖ ^ 2
  /-- A3 (2). -/
  V2_decrease : ∀ i (y : EuclideanSpace ℝ (Fin (n i))),
    ∑ j : Fin (n i),
      (if h : j.val + 1 < n i then y ⟨j.val + 1, h⟩ else D.φ i y) *
        partialDeriv (D.V2 i) j y ≤ -D.W2 i y
  /-- A3 (3): the partial derivative in the page's last coordinate `n_i`. -/
  V2_grad : ∀ i (y : EuclideanSpace ℝ (Fin (n i))) (j : Fin (n i)), j.val + 1 = n i →
    |partialDeriv (D.V2 i) j y| ≤ D.beta2 i * ‖y‖

end GuoZhaoADRC


