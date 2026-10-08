-- Prove2me | Definitions.Def_RobustRegLasso_FeatureWise_Basic
-- name    : RobustRegLasso_FeatureWise_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:18.37799+00:00
-- url     : https://prove2.me/theorems/98566811-8c45-401d-9f7b-0822ccf5e6c5
-- title:
--   Feature-wise uncoupled uncertainty set (2), robust regression objective (1) and ℓ¹-regularized objective (3)
-- statement:
--   Fix integers $n$ (the number of samples) and $m$ (the number of features). The **observation matrix** $A \in \mathbb R^{n\times m}$ is given by its columns $a_1,\dots,a_m \in \mathbb R^n$ (the features), the **response** is $b\in\mathbb R^n$, and a **coefficient vector** is $x\in\mathbb R^m$, so that $Ax = \sum_{i=1}^m x_i a_i$. Throughout, $\|\cdot\|_2$ is the Euclidean norm on $\mathbb R^n$.
--
--   1. A **disturbance** of $A$ is $\Delta A = (\delta_1,\dots,\delta_m)$, one vector $\delta_i\in\mathbb R^n$ per column; the disturbed matrix $A+\Delta A$ has columns $a_i+\delta_i$, so $(A+\Delta A)x = \sum_i x_i(a_i+\delta_i)$.
--   2. Given budgets $c_1,\dots,c_m$, the **feature-wise uncoupled uncertainty set** (2) is
--   $$\mathcal U = \bigl\{(\delta_1,\dots,\delta_m) \;\big|\; \|\delta_i\|_2 \le c_i,\ i=1,\dots,m\bigr\}.$$
--   3. The **robust regression objective**, the inner problem of (1), is the worst-case residual norm
--   $$R(x) = \sup_{\Delta A\in\mathcal U} \|b-(A+\Delta A)x\|_2 ,$$
--   together with the set $\{\|b-(A+\Delta A)x\|_2 : \Delta A\in\mathcal U\}$ of residual norms whose supremum it is. Robust linear regression (1) minimizes $R$ over $x\in\mathbb R^m$.
--   4. The **ℓ¹-regularized regression objective** of problem (3) is
--   $$L(x) = \|b-Ax\|_2 + \sum_{i=1}^m c_i|x_i| .$$
--   The loss is the norm of the error, not its square.
--   5. For a vector $u\in\mathbb R^n$, the disturbance $\Delta A^* = (\delta_1^*,\dots,\delta_m^*)$ used in the proof of Theorem 1 is $\delta_i^* = -c_i\,\mathrm{sgn}(x_i)\,u$, with $\mathrm{sgn}(0)=0$.
--
--   These objects are shared by every statement of the mission: Theorem 1 says that minimizing $R$ and minimizing $L$ are the same problem.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, the columns are a family `a : Fin m → EuclideanSpace ℝ (Fin n)` (the paper's 1-based indices become `Fin m`), and $Ax$ is `matVec a x = ∑ i, x i • a i`. The paper writes "max" in (1); here $R$ is the supremum over $\mathcal U$ computed in the extended reals `EReal`, so it carries no junk value: it is $-\infty$ if $\mathcal U$ is empty and $+\infty$ if the residuals are unbounded. Whether the maximum is attained is stated separately (milestone "per-x identity"). The robust objective is defined as this supremum, not by its closed form. The budgets $c_i \ge 0$ are hypotheses of the theorems, not part of the definition.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 3, Notation, Eqs. (1)–(2); p. 4, Eq. (3) and proof of Theorem 1 (definition of δ*ᵢ)

import Mathlib

namespace RobustRegLasso.FeatureWise

/-- The product `A x = ∑ᵢ xᵢ aᵢ` of the observation matrix `A`, given by its columns
`a : Fin m → ℝⁿ` (the features), with a coefficient vector `x ∈ ℝᵐ`. -/
noncomputable def matVec {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (x : Fin m → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  ∑ i, x i • a i

/-- The feature-wise uncoupled uncertainty set (2) of arXiv:0811.1790v1, p. 3:
`U = {(δ₁, …, δₘ) | ‖δᵢ‖₂ ≤ cᵢ, i = 1, …, m}`. A disturbance `ΔA = (δ₁, …, δₘ)` is a family of
column perturbations `δ : Fin m → ℝⁿ`. -/
def uncertaintySet {n m : ℕ} (c : Fin m → ℝ) : Set (Fin m → EuclideanSpace ℝ (Fin n)) :=
  {δ | ∀ i, ‖δ i‖ ≤ c i}

/-- The residual norm `‖b − (A + ΔA)x‖₂` under the disturbance `ΔA = δ`; the perturbed matrix
`A + ΔA` has columns `aᵢ + δᵢ`. -/
noncomputable def perturbedResidual {n m : ℕ} (a δ : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (x : Fin m → ℝ) : ℝ :=
  ‖b - matVec (a + δ) x‖

/-- The set `{‖b − (A + ΔA)x‖₂ | ΔA ∈ U}` of residual norms over the uncertainty set (2). -/
def residualValues {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ) (x : Fin m → ℝ) : Set ℝ :=
  (fun δ => perturbedResidual a δ b x) '' uncertaintySet c

/-- The robust objective of problem (1): `R(x) = max_{ΔA ∈ U} ‖b − (A + ΔA)x‖₂`, defined as the
supremum over `U` computed in the extended reals `EReal` (so that it is `⊥` if `U` is empty and
`⊤` if the residuals are unbounded; no junk value). -/
noncomputable def robustObjective {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ) (x : Fin m → ℝ) : EReal :=
  ⨆ δ ∈ (uncertaintySet c : Set (Fin m → EuclideanSpace ℝ (Fin n))),
    ((perturbedResidual a δ b x : ℝ) : EReal)

/-- The objective of the ℓ¹-regularized regression problem (3):
`L(x) = ‖b − Ax‖₂ + ∑ᵢ cᵢ |xᵢ|` (the norm of the error, not its square). -/
noncomputable def l1RegularizedObjective {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (c : Fin m → ℝ) (x : Fin m → ℝ) : ℝ :=
  ‖b - matVec a x‖ + ∑ i, c i * |x i|

/-- The disturbance `ΔA* = (δ₁*, …, δₘ*)` of the proof of Theorem 1, p. 4:
`δᵢ* = −cᵢ sgn(xᵢ) u`, with `sgn` the real sign function (`sgn 0 = 0`). -/
noncomputable def worstCaseDisturbance {n m : ℕ} (c : Fin m → ℝ) (x : Fin m → ℝ)
    (u : EuclideanSpace ℝ (Fin n)) : Fin m → EuclideanSpace ℝ (Fin n) :=
  fun i => (-(c i * Real.sign (x i))) • u

end RobustRegLasso.FeatureWise


