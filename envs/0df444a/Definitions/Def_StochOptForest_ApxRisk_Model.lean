-- Prove2me | Definitions.Def_StochOptForest_ApxRisk_Model
-- name    : StochOptForest_ApxRisk_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:20.03903+00:00
-- url     : https://prove2.me/theorems/88ccc2ab-4e36-40e8-9ad5-4f4598a46be1
-- title:
--   §1, §2.1–2.3, pp. 1–10 — contextual stochastic optimization with regression cost c̄, region averages f_j, probabilities p_j, the oracle criterion (8) and the approximate risk criterion (13)
-- statement:
--   This file fixes the model of §2 (the unconstrained case) of Kallus and Mao, *Stochastic Optimization Forests*.
--
--   Features take values in $\mathbb R^p$ and decisions in $\mathbb R^d$, both with the Euclidean norm. The law of the features $X$ is a probability measure $\mu$ on $\mathbb R^p$. The **regression cost** is a function
--   $$\bar c(x,z)=\mathbb E[c(z;Y)\mid X=x],\qquad x\in\mathbb R^p,\ z\in\mathbb R^d .$$
--   For a region $R\subseteq\mathbb R^p$ define:
--
--   1. the **probability** $p_R=P(X\in R)=\mu(R)$;
--   2. the **region average** (eq. (9)) $$f_R(z)=\mathbb E[c(z;Y)\mid X\in R]=\frac{1}{\mu(R)}\int_R \bar c(x,z)\,d\mu(x);$$
--   3. the **gradient** $\nabla f(z)\in\mathbb R^d$ and the **Hessian** $\nabla^2 f(z)$, the derivative of the gradient, a linear map $\mathbb R^d\to\mathbb R^d$; the Hessian is **positive definite** at $z$ if $v^\top\nabla^2 f(z)v>0$ for all $v\neq0$;
--   4. $z$ is the **unique minimizer** of $f$ if $f(z)\le f(w)$ for all $w$ and every global minimizer of $f$ equals $z$;
--   5. the **optimal value** (eq. (69)) $v(f)=\inf_{z\in\mathbb R^d}f(z)$;
--   6. the second-order term $\nabla g(z)^\top(\nabla^2 f(z))^{-1}\nabla g(z)$.
--
--   For a region $R_0$ split into $R_1, R_2$, write $p_j, f_j$ for $j=0,1,2$. The **oracle splitting criterion** (eqs. (8), (10)) is
--   $$\mathcal C^{\mathrm{oracle}}(R_1,R_2)=p_1\min_{z}f_1(z)+p_2\min_z f_2(z),$$
--   and the **approximate risk criterion** (eq. (13)) at a point $z_0$ is
--   $$\mathcal C^{\mathrm{apx\text{-}risk}}(R_1,R_2)=-\frac12\sum_{j=1,2}p_j\,\nabla f_j(z_0)^\top\bigl(\nabla^2 f_0(z_0)\bigr)^{-1}\nabla f_j(z_0).$$
--
--   Two hypotheses used by the theorems are also named here. A function $g$ has **$\|g\|_{\mathcal F}\le N$** (eq. (70)) if $|g(z)|\le N$, $\|\nabla g(z)\|_2\le N$ and $\|\nabla^2 g(z)\|\le N$ for every $z$. The cost is **$x$-Lipschitz with constant $L$** if $\bar c(\cdot,z)$, $\nabla_z\bar c(\cdot,z)$ and $\nabla^2_z\bar c(\cdot,z)$ are $L$-Lipschitz in $x$, uniformly in $z$.
--
--   These are the objects of the splitting criteria the stochastic optimization forest uses to grow its trees.
--
--   **Formalization Note** The regression cost $\bar c$ is taken as the primitive: the paper's results in §2 involve $Y$ and $c(z;y)$ only through $\mathbb E[c(z;Y)\mid X\in R_j]$, which by the tower property is the $\mu$-average of $\bar c$ over $R_j$. The probability is the real number $\mu(R)$, and $1/\mu(R)$ is read as $0$ when $\mu(R)=0$, so every theorem requires positive mass. The optimal value is the real infimum, which equals the paper's minimum whenever a minimizer exists (every theorem assumes or proves one). The inverse Hessian is Lean's inverse of a continuous linear map, which is $0$ for a non-invertible map, so every statement that uses it also assumes the Hessian is positive definite at that point. The Hessian bound in $\|\cdot\|_{\mathcal F}$ uses the operator norm, while the paper uses the Frobenius norm; since the operator norm is at most the Frobenius norm, a bound in operator norm is a weaker hypothesis.
-- source:
--   Kallus & Mao, arXiv:2008.07473v6, pp. 1–10, eqs. (1), (8)–(10), (13); p. 65, eqs. (69)–(70)

import Mathlib

namespace StochOptForest.ApxRisk

open MeasureTheory

/-- The feature space `ℝ^p` with the Euclidean norm. -/
abbrev Xp (p : ℕ) : Type := EuclideanSpace ℝ (Fin p)

/-- The (unconstrained) decision space `Z = ℝ^d` with the Euclidean norm. -/
abbrev Ed (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The probability `p_R = P(X ∈ R)` of a region `R` under the law `μ` of the features. -/
noncomputable def regionProb {p : ℕ} (μ : Measure (Xp p)) (R : Set (Xp p)) : ℝ :=
  (μ R).toReal

/-- The region average `f_R(z) = E[c(z;Y) | X ∈ R] = P(X ∈ R)⁻¹ ∫_R c̄(x, z) dμ(x)` (eq. (9)),
where `cbar x z = E[c(z;Y) | X = x]` is the regression cost. -/
noncomputable def regionAvg {p d : ℕ} (μ : Measure (Xp p)) (cbar : Xp p → Ed d → ℝ)
    (R : Set (Xp p)) (z : Ed d) : ℝ :=
  (μ R).toReal⁻¹ * ∫ x in R, cbar x z ∂μ

/-- The Hessian `∇²f(z)`, as the derivative of the gradient, a linear map `ℝ^d → ℝ^d`. -/
noncomputable def hess {d : ℕ} (f : Ed d → ℝ) (z : Ed d) : Ed d →L[ℝ] Ed d :=
  fderiv ℝ (gradient f) z

/-- The Hessian of `f` at `z` is positive definite. -/
def PosDefAt {d : ℕ} (f : Ed d → ℝ) (z : Ed d) : Prop :=
  ∀ v : Ed d, v ≠ 0 → 0 < inner ℝ (hess f z v) v

/-- `z` is the unique global minimizer of `f` over `ℝ^d`. -/
def IsUniqueMin {d : ℕ} (f : Ed d → ℝ) (z : Ed d) : Prop :=
  (∀ w, f z ≤ f w) ∧ ∀ w, (∀ u, f w ≤ f u) → w = z

/-- The optimal value `v(f) = min_{z ∈ ℝ^d} f(z)` (eq. (69)), as an infimum over `ℝ^d`. -/
noncomputable def optVal {d : ℕ} (f : Ed d → ℝ) : ℝ :=
  ⨅ z, f z

/-- The second-order term `∇g(z)ᵀ (∇²f(z))⁻¹ ∇g(z)`. -/
noncomputable def newtonQuad {d : ℕ} (f g : Ed d → ℝ) (z : Ed d) : ℝ :=
  inner ℝ (gradient g z) ((hess f z).inverse (gradient g z))

/-- The oracle splitting criterion (8)/(10):
`C^oracle(R₁, R₂) = p₁ min_z f₁(z) + p₂ min_z f₂(z)`. -/
noncomputable def oracleCrit {p d : ℕ} (μ : Measure (Xp p)) (cbar : Xp p → Ed d → ℝ)
    (R1 R2 : Set (Xp p)) : ℝ :=
  regionProb μ R1 * optVal (regionAvg μ cbar R1) + regionProb μ R2 * optVal (regionAvg μ cbar R2)

/-- The approximate risk criterion (13):
`C^apx-risk(R₁, R₂) = -(1/2) Σ_{j=1,2} p_j ∇f_j(z₀)ᵀ (∇²f₀(z₀))⁻¹ ∇f_j(z₀)`. -/
noncomputable def apxRiskCrit {p d : ℕ} (μ : Measure (Xp p)) (cbar : Xp p → Ed d → ℝ)
    (R0 R1 R2 : Set (Xp p)) (z0 : Ed d) : ℝ :=
  -(1 / 2) * (regionProb μ R1 * newtonQuad (regionAvg μ cbar R0) (regionAvg μ cbar R1) z0
    + regionProb μ R2 * newtonQuad (regionAvg μ cbar R0) (regionAvg μ cbar R2) z0)

/-- `‖g‖_F ≤ N` for the norm (70): `|g|`, `‖∇g‖` and `‖∇²g‖` are bounded by `N` everywhere
(the Hessian bound is in operator norm). -/
def FNormLE {d : ℕ} (g : Ed d → ℝ) (N : ℝ) : Prop :=
  ∀ z, |g z| ≤ N ∧ ‖gradient g z‖ ≤ N ∧ ‖hess g z‖ ≤ N

/-- The regression cost and its first two `z`-derivatives are `L`-Lipschitz in `x`,
uniformly in `z`. -/
def XLipschitz {p d : ℕ} (cbar : Xp p → Ed d → ℝ) (L : ℝ) : Prop :=
  ∀ (z : Ed d) (x x' : Xp p),
    |cbar x z - cbar x' z| ≤ L * ‖x - x'‖ ∧
    ‖gradient (cbar x) z - gradient (cbar x') z‖ ≤ L * ‖x - x'‖ ∧
    ‖hess (cbar x) z - hess (cbar x') z‖ ≤ L * ‖x - x'‖

end StochOptForest.ApxRisk


