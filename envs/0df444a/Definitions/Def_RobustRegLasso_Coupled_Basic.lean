-- Prove2me | Definitions.Def_RobustRegLasso_Coupled_Basic
-- name    : RobustRegLasso_Coupled_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:09.081013+00:00
-- url     : https://prove2.me/theorems/5569565c-8dc7-4482-93e0-015b67dd1e35
-- title:
--   Arbitrary-norm residuals, the uncertainty sets $\mathcal U_a$, $\mathcal U'$, $\mathcal Z$ of §III, absolute norms and the dual norm
-- statement:
--   These are the objects of §III ("General uncertainty sets") of Xu, Caramanis and Mannor, *Robust Regression and Lasso*.
--
--   **Data.** Let $\|\cdot\|_a$ be an arbitrary norm on $\mathbb R^n$; we work in a real normed space $E$ standing for $(\mathbb R^n, \|\cdot\|_a)$. The observation matrix $A$ is given by its $m$ columns (features) $a_1,\dots,a_m \in E$, the response is $b \in E$, and for a coefficient vector $x \in \mathbb R^m$
--   $$Ax = \sum_{i=1}^m x_i a_i .$$
--   A disturbance $\Delta A = (\delta_1,\dots,\delta_m)$ is a family of column perturbations $\delta_i \in E$; the perturbed matrix $A + \Delta A$ has columns $a_i + \delta_i$, and its residual norm is $\|b - (A+\Delta A)x\|_a$.
--
--   **Robust objective.** For an uncertainty set $\mathcal U$ of disturbances, the robust objective is
--   $$R_{\mathcal U}(x) = \sup_{\Delta A \in \mathcal U} \|b - (A+\Delta A)x\|_a ,$$
--   taken in the extended reals $[-\infty, +\infty]$: it is $-\infty$ for an empty $\mathcal U$ and $+\infty$ when the residuals are unbounded. The set of residual values $\{\|b-(A+\Delta A)x\|_a : \Delta A \in \mathcal U\}$ is also named, so that attainment of the maximum can be stated.
--
--   **Uncertainty sets.**
--   1. For budgets $c \in \mathbb R^m$ (Theorem 3): $\mathcal U_a = \{(\delta_1,\dots,\delta_m) : \|\delta_i\|_a \le c_i,\ i = 1,\dots,m\}$.
--   2. For functions $f_1,\dots,f_k : \mathbb R^m \to \mathbb R$ (p. 6): $\mathcal U' = \{(\delta_1,\dots,\delta_m) : f_j(\|\delta_1\|_a,\dots,\|\delta_m\|_a) \le 0,\ j = 1,\dots,k\}$, and $\mathcal Z = \{z \in \mathbb R^m : f_j(z) \le 0,\ j=1,\dots,k;\ z \ge 0\}$.
--   3. For a norm $\|\cdot\|_s$ on $\mathbb R^m$ and $l \in \mathbb R$ (Corollary 1): $\{(\delta_1,\dots,\delta_m) : \|(\|\delta_1\|_a,\dots,\|\delta_m\|_a)\|_s \le l\}$.
--   4. For $T \in \mathbb R^{k\times m}$ and $s \in \mathbb R^k$ (Corollary 2): $\{(\delta_1,\dots,\delta_m) : \exists c \ge 0,\ Tc \le s,\ \|\delta_j\|_a \le c_j \ \forall j\}$, together with the feasible set $D(x) = \{\lambda \in \mathbb R^k : x \le T^\top\lambda,\ -x \le T^\top \lambda,\ \lambda \ge 0\}$ of the linear program of Corollary 2.
--
--   **Absolute norms and the dual norm.** A seminorm $\|\cdot\|_s$ on $\mathbb R^m$ is *absolute* if $\|(|z_1|,\dots,|z_m|)\|_s = \|z\|_s$ for all $z$. Its dual norm is
--   $$\|y\|_s^* = \sup\{\, y^\top z : \|z\|_s \le 1 \,\}.$$
--
--   These definitions are shared by every statement of the mission: Theorem 3, the decomposition (13), and Corollaries 1 and 2.
--
--   **Formalization Note.** $E$ is any real normed space (finite dimension is not imposed; the theorems add $E \ne 0$, i.e. $n \ge 1$). The robust objective is an `EReal` supremum, never its closed form. The norm $\|\cdot\|_s$ is a Mathlib `Seminorm` on `Fin m → ℝ` (the theorems add definiteness), because `Fin m → ℝ` already carries the sup norm. The dual norm is a real `sSup`; when $\|\cdot\|_s$ is a norm the set is nonempty and bounded above, so this is its true supremum. The paper's "symmetric norm" is read as *absolute* (see Corollary 1).
-- source:
--   Xu, Caramanis, Mannor, Robust Regression and Lasso, arXiv:0811.1790v1, p. 6, Theorem 3 (U_a), definition of U′ and Theorem 4 (Z); p. 7, Corollaries 1 and 2

import Mathlib

namespace RobustRegLasso.Coupled

/-! Objects of §III "General uncertainty sets" of Xu, Caramanis, Mannor, *Robust Regression and
Lasso*, arXiv:0811.1790v1, pp. 6–7 and Appendix B, p. 19.

`ℝⁿ` with an arbitrary norm `‖·‖ₐ` is a real normed space `E`; the observation matrix `A` is given by
its columns (features) `a : Fin m → E`; a disturbance `ΔA = (δ₁, …, δₘ)` is a family `δ : Fin m → E`
of column perturbations; coefficient vectors are `x : Fin m → ℝ`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- The product `A x = ∑ᵢ xᵢ aᵢ` of the matrix with columns `a` and a coefficient vector `x`. -/
def matVec (a : Fin m → E) (x : Fin m → ℝ) : E :=
  ∑ i, x i • a i

/-- The residual norm `‖b − (A + ΔA)x‖ₐ` under the disturbance `ΔA = δ`; the perturbed matrix
`A + ΔA` has columns `aᵢ + δᵢ`. -/
noncomputable def perturbedResidual (a δ : Fin m → E) (b : E) (x : Fin m → ℝ) : ℝ :=
  ‖b - matVec (a + δ) x‖

/-- The set `{‖b − (A + ΔA)x‖ₐ | ΔA ∈ U}` of residual norms over an uncertainty set `U`. -/
def residualValues (a : Fin m → E) (b : E) (U : Set (Fin m → E)) (x : Fin m → ℝ) : Set ℝ :=
  (fun δ => perturbedResidual a δ b x) '' U

/-- The robust objective `max_{ΔA ∈ U} ‖b − (A + ΔA)x‖ₐ`, defined as the supremum over `U`
computed in the extended reals `EReal`: it is `⊥` if `U` is empty and `⊤` if the residual norms
are unbounded over `U` (no junk value). -/
noncomputable def robustObjective (a : Fin m → E) (b : E) (U : Set (Fin m → E))
    (x : Fin m → ℝ) : EReal :=
  ⨆ δ ∈ U, ((perturbedResidual a δ b x : ℝ) : EReal)

/-- The vector `(‖δ₁‖ₐ, …, ‖δₘ‖ₐ) ∈ ℝᵐ` of the norms of the column disturbances. -/
def colNorms (δ : Fin m → E) : Fin m → ℝ :=
  fun i => ‖δ i‖

/-- The feature-wise uncertainty set of Theorem 3, p. 6:
`Uₐ = {(δ₁, …, δₘ) | ‖δᵢ‖ₐ ≤ cᵢ, i = 1, …, m}`. -/
def uncertaintySetA (c : Fin m → ℝ) : Set (Fin m → E) :=
  {δ | ∀ i, ‖δ i‖ ≤ c i}

/-- The coupled uncertainty set of p. 6:
`U′ = {(δ₁, …, δₘ) | f_j(‖δ₁‖ₐ, …, ‖δₘ‖ₐ) ≤ 0, j = 1, …, k}` for functions `f_j : ℝᵐ → ℝ`. -/
def coupledSet {k : ℕ} (f : Fin k → (Fin m → ℝ) → ℝ) : Set (Fin m → E) :=
  {δ | ∀ j, f j (colNorms δ) ≤ 0}

/-- The set of Theorem 4, p. 6: `Z = {z ∈ ℝᵐ | f_j(z) ≤ 0, j = 1, …, k; z ≥ 0}`. -/
def budgetSet {k : ℕ} (f : Fin k → (Fin m → ℝ) → ℝ) : Set (Fin m → ℝ) :=
  {z | (∀ j, f j z ≤ 0) ∧ ∀ i, 0 ≤ z i}

/-- A seminorm `N` on `ℝᵐ` is *absolute* if `N(|z₁|, …, |zₘ|) = N(z)` for every `z`. This is the
reading of the paper's "symmetric norm" (Corollary 1, p. 7). -/
def IsAbsolute (N : Seminorm ℝ (Fin m → ℝ)) : Prop :=
  ∀ z : Fin m → ℝ, N (fun i => |z i|) = N z

/-- The dual norm `‖y‖*ₛ = sup {yᵀz | ‖z‖ₛ ≤ 1}` of the norm `‖·‖ₛ = N` on `ℝᵐ`, as a real supremum.
When `N` is a norm (`N z = 0 → z = 0`) the set is nonempty (it contains `0`) and bounded above
(all norms on `ℝᵐ` are equivalent), so this is its least upper bound. -/
noncomputable def dualNorm (N : Seminorm ℝ (Fin m → ℝ)) (y : Fin m → ℝ) : ℝ :=
  sSup {t : ℝ | ∃ z : Fin m → ℝ, N z ≤ 1 ∧ t = ∑ i, y i * z i}

/-- The uncertainty set of Corollary 1, p. 7:
`U′ = {(δ₁, …, δₘ) | ‖(‖δ₁‖ₐ, …, ‖δₘ‖ₐ)‖ₛ ≤ l}`. -/
def normBudgetSet (N : Seminorm ℝ (Fin m → ℝ)) (l : ℝ) : Set (Fin m → E) :=
  {δ | N (colNorms δ) ≤ l}

/-- The polytope uncertainty set of Corollary 2, p. 7:
`U′ = {(δ₁, …, δₘ) | ∃ c ≥ 0 : Tc ≤ s; ‖δⱼ‖ₐ ≤ cⱼ}` for `T ∈ ℝ^{k×m}`, `s ∈ ℝᵏ`. -/
def polytopeSet {k : ℕ} (T : Matrix (Fin k) (Fin m) ℝ) (s : Fin k → ℝ) : Set (Fin m → E) :=
  {δ | ∃ c : Fin m → ℝ, (∀ j, 0 ≤ c j) ∧ (∀ r, Matrix.mulVec T c r ≤ s r) ∧ ∀ j, ‖δ j‖ ≤ c j}

/-- The feasible set of the linear program of Corollary 2, p. 7, for fixed `x`:
`{λ ∈ ℝᵏ | x ≤ Tᵀλ, −x ≤ Tᵀλ, λ ≥ 0}`. -/
def polytopeDualFeasible {k : ℕ} (T : Matrix (Fin k) (Fin m) ℝ) (x : Fin m → ℝ) :
    Set (Fin k → ℝ) :=
  {lam | (∀ j, x j ≤ Matrix.mulVec T.transpose lam j) ∧
    (∀ j, -x j ≤ Matrix.mulVec T.transpose lam j) ∧ ∀ r, 0 ≤ lam r}

end RobustRegLasso.Coupled


