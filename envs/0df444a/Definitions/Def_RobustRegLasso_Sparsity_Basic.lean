-- Prove2me | Definitions.Def_RobustRegLasso_Sparsity_Basic
-- name    : RobustRegLasso_Sparsity_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:34.805555+00:00
-- url     : https://prove2.me/theorems/195ecf4c-8492-45f6-8abe-6fc5b863362b
-- title:
--   Robust regression objective, its solutions, and the sets $\mathcal U$, $\mathcal U^I$, $\tilde{\mathcal U}$ of §IV
-- statement:
--   Fix integers $n, m \ge 0$. The **observation matrix** $A \in \mathbb R^{n\times m}$ is given by its columns (the **features**) $a_1,\dots,a_m \in \mathbb R^n$, and $b \in \mathbb R^n$ is the response. For $x \in \mathbb R^m$ write $Ax = \sum_{i=1}^m x_i a_i$. A **disturbance** $\Delta A = (\delta_1,\dots,\delta_m)$ is a family of column perturbations $\delta_i \in \mathbb R^n$; the perturbed matrix $A + \Delta A$ has columns $a_i + \delta_i$.
--
--   1. **Robust objective.** For a set $\mathcal V$ of disturbances,
--   $$R_{A,\mathcal V}(x) = \max_{\Delta A \in \mathcal V} \|b - (A+\Delta A)x\|_2,$$
--   taken as the supremum over $\mathcal V$ in the extended reals $[-\infty,+\infty]$.
--   2. **Solution.** $x^*$ is a solution of the robust regression problem $\min_{x\in\mathbb R^m} R_{A,\mathcal V}(x)$ if $R_{A,\mathcal V}(x^*) \le R_{A,\mathcal V}(x)$ for every $x \in \mathbb R^m$. The problem **has a solution supported on** an index set $I \subseteq \{1,\dots,m\}$ if some solution $x^*$ satisfies $x^*_j = 0$ for all $j \notin I$.
--   3. **Feature-wise uncoupled uncertainty set** (2) with radii $c = (c_1,\dots,c_m)$:
--   $$\mathcal U = \{(\delta_1,\dots,\delta_m) \mid \|\delta_i\|_2 \le c_i,\ i = 1,\dots,m\}.$$
--   4. **Restriction.** For $I \subseteq \{1,\dots,m\}$ and a disturbance $\Delta A$, $\Delta A^I$ equals $\Delta A$ on the features $i \in I$ and is zero elsewhere; $\mathcal U^I = \{\Delta A^I \mid \Delta A \in \mathcal U\}$.
--   5. **Enlarged set** of Theorem 5′: for $l = (l_j)$,
--   $$\tilde{\mathcal U} = \{(\delta_1,\dots,\delta_m) \mid \|\delta_i\|_2 \le c_i,\ i \in I;\ \|\delta_j\|_2 \le c_j + l_j,\ j \notin I\}.$$
--
--   These objects carry every statement of the paper's Section IV ("Sparsity"): Theorem 5 compares the problems with data $(A, \mathcal U)$ and $(A + \Delta\tilde A^{I^c}, \mathcal U^I)$, and Theorem 5′ the problems with data $(A, \mathcal U)$ and $(\tilde A, \tilde{\mathcal U})$. The radius vector is a parameter because Theorem 5 is Theorem 5′ at different radii.
--
--   **Formalization Note** The paper writes "max" over the uncertainty set; the objective is the supremum computed in `EReal`, so no junk value of a real `sSup` can enter. When all radii are nonnegative the sets $\mathcal U$, $\mathcal U^I$, $\tilde{\mathcal U}$ (with $c_j + l_j \ge 0$) are nonempty and bounded, so the supremum is a finite real number and is attained, matching the paper's "max". Index sets are finite subsets of $\{1,\dots,m\}$ (`Finset (Fin m)`, 0-based in Lean). The paper's p. 8 writes $I \subseteq \{1,\dots,n\}$ and $I^c = \{1,\dots,n\}\setminus I$; features are indexed by $1,\dots,m$, as Theorem 5′ writes, so $m$ is used. The product $Ax$ (`matVec`) and the set (2) (`uncertaintySet`) are taken from the series' shared definition `RobustRegLasso.FeatureWise.Basic`.
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 3, Eq. (2); p. 8, notation before Theorem 5 and definition of Ũ in Theorem 5′

import Mathlib
import Definitions.Def_RobustRegLasso_FeatureWise_Basic

namespace RobustRegLasso.Sparsity

/-- The residual norm `‖b − (A + ΔA)x‖₂` under the disturbance `ΔA = (δ₁, …, δₘ)`; the perturbed
matrix `A + ΔA` has columns `aᵢ + δᵢ`. -/
noncomputable def residual {n m : ℕ} (a δ : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (x : Fin m → ℝ) : ℝ :=
  ‖b - RobustRegLasso.FeatureWise.matVec (a + δ) x‖

/-- The robust objective `R_{A,V}(x) = max_{ΔA ∈ V} ‖b − (A + ΔA)x‖₂` of the robust regression
problem with columns `a`, response `b` and a set `V` of disturbances, defined as the supremum
over `V` computed in the extended reals `EReal` (it is `⊥` if `V` is empty and `⊤` if the
residuals are unbounded on `V`; no junk value). -/
noncomputable def robustObjective {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (V : Set (Fin m → EuclideanSpace ℝ (Fin n)))
    (x : Fin m → ℝ) : EReal :=
  ⨆ δ ∈ V, ((residual a δ b x : ℝ) : EReal)

/-- `x` is a solution (an optimal solution) of the robust regression problem
`min_{x ∈ ℝᵐ} max_{ΔA ∈ V} ‖b − (A + ΔA)x‖₂`: it minimizes `R_{A,V}` over all of `ℝᵐ`. -/
def IsRobustSolution {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (V : Set (Fin m → EuclideanSpace ℝ (Fin n)))
    (x : Fin m → ℝ) : Prop :=
  ∀ y : Fin m → ℝ, robustObjective a b V x ≤ robustObjective a b V y

/-- The robust regression problem with data `(A, V)` has a solution supported on the index set
`I`: some optimal solution `x*` has `x*ⱼ = 0` for every `j ∉ I`. -/
def HasSolutionSupportedOn {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (b : EuclideanSpace ℝ (Fin n)) (V : Set (Fin m → EuclideanSpace ℝ (Fin n)))
    (I : Finset (Fin m)) : Prop :=
  ∃ x : Fin m → ℝ, IsRobustSolution a b V x ∧ ∀ j, j ∉ I → x j = 0

/-- `ΔA^I`: the disturbance that equals `ΔA` on each feature indexed by `i ∈ I` and is zero
elsewhere (p. 8). -/
def restrict {n m : ℕ} (I : Finset (Fin m)) (δ : Fin m → EuclideanSpace ℝ (Fin n)) :
    Fin m → EuclideanSpace ℝ (Fin n) :=
  fun i => if i ∈ I then δ i else 0

/-- `U^I = {ΔA^I | ΔA ∈ U}`, the restriction of the uncertainty set (2) with radii `c` to the
features in `I` (p. 8). -/
def restrictedSet {n m : ℕ} (c : Fin m → ℝ) (I : Finset (Fin m)) :
    Set (Fin m → EuclideanSpace ℝ (Fin n)) :=
  restrict I '' RobustRegLasso.FeatureWise.uncertaintySet c

/-- The enlarged set `Ũ` of Theorem 5′ (p. 8):
`Ũ = {(δ₁, …, δₘ) | ‖δᵢ‖₂ ≤ cᵢ, i ∈ I; ‖δⱼ‖₂ ≤ cⱼ + lⱼ, j ∉ I}`. -/
def enlargedSet {n m : ℕ} (c l : Fin m → ℝ) (I : Finset (Fin m)) :
    Set (Fin m → EuclideanSpace ℝ (Fin n)) :=
  {δ | (∀ i, i ∈ I → ‖δ i‖ ≤ c i) ∧ ∀ j, j ∉ I → ‖δ j‖ ≤ c j + l j}

end RobustRegLasso.Sparsity


