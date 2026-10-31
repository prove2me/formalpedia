-- Prove2me | Definitions.Def_GuoZhaoADRC_AssumptionA2
-- name    : GuoZhaoADRC_AssumptionA2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:59.094984+00:00
-- url     : https://prove2.me/theorems/a30f4403-0e49-4d28-8f38-e64f3fb4925a
-- title:
--   Assumption A2 — the extended state observer: bounds on $g^i_j$ and the Lyapunov pair $(V_1^i,W_1^i)$
-- statement:
--   Assumption A2 on the observer (1.5). For every $i\le m$ and every $r\in\mathbb R$, $|g^i_j(r)|\le\Lambda^i_j|r|$, and the positive definite continuously differentiable functions $V_1^i,W_1^i:\mathbb R^{n_i+1}\to\mathbb R$ and constants $\lambda^i_{11},\dots,\lambda^i_{14},\beta^i_1$, with $\lambda^i_{11}>0$, satisfy for all $y\in\mathbb R^{n_i+1}$:
--
--   1. $\lambda^i_{11}\|y\|^2\le V_1^i(y)\le\lambda^i_{12}\|y\|^2$ and $\lambda^i_{13}\|y\|^2\le W_1^i(y)\le\lambda^i_{14}\|y\|^2$;
--   2. $$\sum_{j=1}^{n_i}\bigl(y_{j+1}-g^i_j(y_1)\bigr)\frac{\partial V_1^i}{\partial y_j}(y)-g^i_{n_i+1}(y_1)\frac{\partial V_1^i}{\partial y_{n_i+1}}(y)\le-W_1^i(y);$$
--   3. $\max\Bigl\{\Bigl|\dfrac{\partial V_1^i}{\partial y_{n_i}}(y)\Bigr|,\Bigl|\dfrac{\partial V_1^i}{\partial y_{n_i+1}}(y)\Bigr|\Bigr\}\le\beta^i_1\|y\|$.
--
--   Condition 2 says that $V_1^i$ is a strict Lyapunov function of the observer error dynamics without disturbance; condition 3 controls how strongly the unknown total disturbance enters its derivative.
--
--   **Formalization Note** Indices are 0-based. Two readings of the printed text: the page's $|g^i_j(r)|\le\Lambda^i_jr$ is read as $\le\Lambda^i_j|r|$ (as printed it forces $g^i_j=0$ on a half-line, which excludes every linear gain $g^i_j(r)=kr$, $k\ne0$, and, when all $\Lambda^i_j$ have one sign, contradicts condition 2), and $\lambda^i_{11}>0$ is required (the page says only "constants"; the proof divides by $\min\lambda^i_{11}$). The page's domain "$\mathbb R^{n+1}$" in condition 1 is the domain $\mathbb R^{n_i+1}$ of $V_1^i$. Positive definite means $V(0)=0$ and $V(y)>0$ for $y\ne0$.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, Assumption A2, p.1729

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_partialDeriv

namespace GuoZhaoADRC

/-- **Assumption A2 (the extended state observer).**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), Assumption A2, p.1729.

For every `i ≤ m`, `|g^i_j(r)| ≤ Λ^i_j |r|` for all `r ∈ ℝ`, and there exist constants
`λ^i_11, λ^i_12, λ^i_13, λ^i_14, β^i_1` and positive definite continuously differentiable
`V_1^i, W_1^i : ℝ^{n_i+1} → ℝ` with
(1) `λ^i_11‖y‖² ≤ V_1^i(y) ≤ λ^i_12‖y‖²`, `λ^i_13‖y‖² ≤ W_1^i(y) ≤ λ^i_14‖y‖²`;
(2) `∑_{j=1}^{n_i} (y_{j+1} − g^i_j(y_1)) ∂V_1^i/∂y_j(y) − g^i_{n_i+1}(y_1) ∂V_1^i/∂y_{n_i+1}(y) ≤ −W_1^i(y)`;
(3) `max{|∂V_1^i/∂y_{n_i}(y)|, |∂V_1^i/∂y_{n_i+1}(y)|} ≤ β^i_1‖y‖`, for all `y ∈ ℝ^{n_i+1}`.

**Formalization Note.** Indices are 0-based (`Fin (n i + 1)`; the page's `y_1` is `y 0`, the
page's `y_{n_i+1}` is `y (Fin.last _)`). In (2) the `j`-th term (0-based `j < n i`) carries
`y_{j+1} − g^i_j(y_1)`, the last term `−g^i_{n_i+1}(y_1)`. In (3) the two indices are those
`j` with `n i ≤ j + 1`. Readings: the page's `|g^i_j(r)| ≤ Λ^i_j r` is read as
`≤ Λ^i_j |r|` (as printed it forces `g^i_j = 0` on a half-line, which excludes every linear
gain `g^i_j(r) = k r`, `k ≠ 0`, and, when all `Λ^i_j` have one sign, contradicts (2)); the page's "`∀ y ∈ ℝ^{n+1}`" in (1) is `ℝ^{n_i+1}`, the domain of
`V_1^i`; `λ^i_11 > 0` (the proof divides by `min λ^i_11`). "Positive definite" is `V(0) = 0`
and `V(y) > 0` for `y ≠ 0`. -/
structure AssumptionA2 {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s) : Prop where
  /-- `|g^i_j(r)| ≤ Λ^i_j |r|` (reading of the page's `≤ Λ^i_j r`). -/
  g_bound : ∀ i j (r : ℝ), |D.g i j r| ≤ D.Λ i j * |r|
  /-- `V_1^i` is continuously differentiable. -/
  V1_contDiff : ∀ i, ContDiff ℝ 1 (D.V1 i)
  /-- `W_1^i` is continuously differentiable. -/
  W1_contDiff : ∀ i, ContDiff ℝ 1 (D.W1 i)
  /-- `V_1^i` is positive definite. -/
  V1_posDef : ∀ i, D.V1 i 0 = 0 ∧ ∀ y, y ≠ 0 → 0 < D.V1 i y
  /-- `W_1^i` is positive definite. -/
  W1_posDef : ∀ i, D.W1 i 0 = 0 ∧ ∀ y, y ≠ 0 → 0 < D.W1 i y
  /-- `λ^i_11 > 0` (reading). -/
  lam11_pos : ∀ i, 0 < D.lam11 i
  /-- A2 (1), first part. -/
  V1_bounds : ∀ i y, D.lam11 i * ‖y‖ ^ 2 ≤ D.V1 i y ∧ D.V1 i y ≤ D.lam12 i * ‖y‖ ^ 2
  /-- A2 (1), second part. -/
  W1_bounds : ∀ i y, D.lam13 i * ‖y‖ ^ 2 ≤ D.W1 i y ∧ D.W1 i y ≤ D.lam14 i * ‖y‖ ^ 2
  /-- A2 (2). -/
  V1_decrease : ∀ i (y : EuclideanSpace ℝ (Fin (n i + 1))),
    ∑ j : Fin (n i + 1),
      (if h : j.val < n i then y ⟨j.val + 1, by omega⟩ - D.g i j (y 0) else -D.g i j (y 0)) *
        partialDeriv (D.V1 i) j y ≤ -D.W1 i y
  /-- A2 (3): the partial derivatives in the page's coordinates `n_i` and `n_i + 1`. -/
  V1_grad : ∀ i (y : EuclideanSpace ℝ (Fin (n i + 1))) (j : Fin (n i + 1)), n i ≤ j.val + 1 →
    |partialDeriv (D.V1 i) j y| ≤ D.beta1 i * ‖y‖

end GuoZhaoADRC


