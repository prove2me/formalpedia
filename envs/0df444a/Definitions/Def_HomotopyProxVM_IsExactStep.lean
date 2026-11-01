-- Prove2me | Definitions.Def_HomotopyProxVM_IsExactStep
-- name    : HomotopyProxVM_IsExactStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:21.050198+00:00
-- url     : https://prove2.me/theorems/adc75acd-7d3a-405e-815b-621c4ba653e4
-- title:
--   One exact step of the scheme (12)
-- statement:
--   Let $H\in\mathbb S^p_{++}$ and $\tau\in(0,1]$. The point $x^+$ is an **exact step** of the scheme (12) from $x$ if
--
--   $$
--   x^+=\operatorname{prox}^{H}_{\frac1\tau g}\Bigl(x-H^{-1}\bigl(\nabla f(x)-(\tfrac1\tau-1)\xi^0\bigr)\Bigr).
--   $$
--
--   In the paper's indexing, $x=x^k$, $x^+=x^{k+1}$, $H=H_k$ and $\tau=\tau_{k+1}$. Since the prox of $\frac1\tau g$ in the metric $H$ is taken at a point shifted by the fixed vector $\xi^0$, this is one proximal variable-metric step on the parametrized problem at $\tau$.
--
--   **Formalization Note** "Exact" means that ":≈" in (12) is equality. The prox is the published set of minimizers `OneStepProx.scaledProx` over the domain of $g$, so the Lean statement is membership; `prox_wellDefined` shows that set is a single point. $H^{-1}$ acts through `Matrix.toEuclideanLin`.
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Algorithm 1, (12), p.7; "exact scheme", Theorem 4, p.9

import Mathlib
import Definitions.Def_OneStepProx_scaledProx

namespace HomotopyProxVM

/-- One exact step of the scheme (12) at the value `τ` of the parameter and the metric `H`:
`x⁺ = prox^H_{(1/τ) g}( x − H⁻¹( ∇f(x) − (1/τ − 1) ξ⁰ ) )`
(Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Algorithm 1, (12), p.7, with `τ = τ_{k+1}`, `H = H_k`).

**Formalization Note.** "Exact" means that `:≈` in (12) is equality (p.8). `prox` is the published
set of minimizers `OneStepProx.scaledProx` over the domain `D` of `g`, so the step says that `xplus`
is a point of it; that set has exactly one point when `H ≻ 0`, `τ > 0` and `g` is proper, closed and
convex (`prox_wellDefined`). `H⁻¹` acts through `Matrix.toEuclideanLin`. -/
def IsExactStep {p : ℕ} (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin p))) (g : EuclideanSpace ℝ (Fin p) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin p)) (H : Matrix (Fin p) (Fin p) ℝ) (τ : ℝ)
    (x xplus : EuclideanSpace ℝ (Fin p)) : Prop :=
  xplus ∈ OneStepProx.scaledProx H D (fun u => 1 / τ * g u)
    (x - Matrix.toEuclideanLin H⁻¹ (gradient f x - (1 / τ - 1) • ξ))

end HomotopyProxVM


