-- Prove2me | Definitions.Def_VanderbeiLP_SelfDual_HomogeneousSelfDual
-- name    : VanderbeiLP_SelfDual_HomogeneousSelfDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T13:34:50.961414+00:00
-- url     : https://prove2.me/theorems/8107ca03-7680-4bda-b864-65c68bb2372f
-- title:
--   Homogeneous self-dual LP (22.4), infeasibility $\rho$, noncomplementarity $\mu$, neighbourhood $\mathcal N(\beta)$, step equations (22.5)–(22.6)
-- statement:
--   Fix $n \ge 1$ and a real $n \times n$ matrix $A$. The matrix is **skew symmetric** if $A = -A^T$. The **homogeneous self-dual problem** (22.4) is
--
--   $$\text{maximize } 0 \quad \text{subject to } Ax + z = 0,\quad x, z \ge 0,$$
--
--   with variables $x, z \in \mathbb{R}^n$ ($z$ is the vector of primal slacks). This file defines:
--
--   1. **feasibility** for (22.4): $Ax + z = 0$, $x \ge 0$, $z \ge 0$; and **optimality**: $(x, z)$ is feasible and its objective value $0^T x$ is at least the objective value $0^T x'$ of every feasible $(x', z')$;
--   2. the **infeasibility** $\rho(x, z) = Ax + z$ and the **noncomplementarity** $\mu(x, z) = \frac1n x^T z$;
--   3. the **Euclidean norm** $\|v\| = \big(\sum_j v_j^2\big)^{1/2}$ and the **centrality residual** $XZe - \mu(x,z)e$, the vector with components $x_j z_j - \mu(x, z)$, where $X, Z$ are the diagonal matrices with the entries of $x, z$ on the diagonal and $e$ is the vector of ones;
--   4. for a real $\beta$, the **neighbourhood**
--   $$\mathcal N(\beta) = \{(x, z) > 0 : \|XZe - \mu(x, z)e\| \le \beta\,\mu(x, z)\},$$
--   where $(x, z) > 0$ means that every component of $x$ and of $z$ is strictly positive;
--   5. the **step equations** (22.5)–(22.6) for a centering parameter $\delta$: a pair $(\Delta x, \Delta z)$ solves them at $(x, z)$ if
--   $$A\Delta x + \Delta z = -(1 - \delta)\rho(x, z), \qquad Z\Delta x + X\Delta z = \delta\mu(x, z)e - XZe;$$
--   6. the **predictor step length** (22.10), $\theta = \sup\{t \in \mathbb{R} : (x + t\Delta x, z + t\Delta z) \in \mathcal N(1/2)\}$;
--   7. the **scaled directions** (22.11) $p = X^{-1/2}Z^{1/2}\Delta x$ and $q = X^{1/2}Z^{-1/2}\Delta z$, i.e. $p_j = \sqrt{z_j}/\sqrt{x_j}\,\Delta x_j$ and $q_j = \sqrt{x_j}/\sqrt{z_j}\,\Delta z_j$.
--
--   These are the objects of the predictor–corrector algorithm of §22.2 and of its convergence analysis (Theorems 22.1–22.7).
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ` and `A : Matrix (Fin n) (Fin n) ℝ`. The book's `‖·‖` is Euclidean; Mathlib's default norm on `Fin n → ℝ` is the sup norm, so the Euclidean norm is defined explicitly. The book writes the step length (22.10) as a maximum; the set of admissible $t$ is nonempty ($t = 0$ belongs to it whenever $(x,z) \in \mathcal N(1/2)$) and, along a direction of (22.5)–(22.6) with $\delta = 0$ and skew-symmetric $A$, bounded above by $1$ (because $\mu$ of the new point is $(1-t)\mu$ and must be positive), but the maximum need not be attained, so it is defined as a supremum. The scaled directions are only used at $x > 0$, $z > 0$. The neighbourhood is defined for every real $\beta$; the book uses $0 \le \beta \le 1$.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 323 (skew symmetric, PDF p. 329); p. 325, Eq. (22.4), definitions of ρ and μ (PDF p. 331); p. 326, Eqs. (22.5)–(22.6) (PDF p. 332); p. 327, definition of N(β) (PDF p. 333); p. 328, Eqs. (22.10)–(22.11) (PDF p. 334)

import Mathlib

open Matrix

namespace VanderbeiLP.SelfDual

/-- `A` is skew symmetric: `A = -Aᵀ` (Vanderbei, p. 323). -/
def IsSkewSymmetric {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Aᵀ = -A

/-- `(x, z)` is feasible for the homogeneous self-dual problem (22.4)
`maximize 0 subject to Ax + z = 0, x, z ≥ 0` (Vanderbei, p. 325). -/
def SelfDualFeasible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x z : Fin n → ℝ) : Prop :=
  A *ᵥ x + z = 0 ∧ (∀ j, 0 ≤ x j) ∧ ∀ j, 0 ≤ z j

/-- `(x, z)` is optimal for (22.4): it is feasible and its objective value, the zero linear
functional `0ᵀx`, is at least the objective value of every feasible `(x', z')`. -/
def SelfDualOptimal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x z : Fin n → ℝ) : Prop :=
  SelfDualFeasible A x z ∧
    ∀ x' z' : Fin n → ℝ, SelfDualFeasible A x' z' →
      (0 : Fin n → ℝ) ⬝ᵥ x' ≤ (0 : Fin n → ℝ) ⬝ᵥ x

/-- The infeasibility `ρ(x, z) = Ax + z` (Vanderbei, p. 325). -/
def rho {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x z : Fin n → ℝ) : Fin n → ℝ :=
  A *ᵥ x + z

/-- The noncomplementarity `μ(x, z) = (1/n) xᵀz` (Vanderbei, p. 325). -/
noncomputable def mu {n : ℕ} (x z : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * (x ⬝ᵥ z)

/-- The Euclidean norm `‖v‖ = (∑ⱼ vⱼ²)^{1/2}` (the book's `‖·‖` without subscript). -/
noncomputable def euclidNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ j, v j ^ 2)

/-- The centrality residual `XZe - μ(x, z)e`, i.e. the vector with components
`xⱼ zⱼ - μ(x, z)`. -/
noncomputable def centralityResidual {n : ℕ} (x z : Fin n → ℝ) : Fin n → ℝ :=
  fun j => x j * z j - mu x z

/-- The neighbourhood of the central ray (Vanderbei, p. 327)
`N(β) = {(x, z) > 0 : ‖XZe - μ(x, z)e‖ ≤ β μ(x, z)}`:
every component of `x` and of `z` is strictly positive and the Euclidean norm of the
centrality residual is at most `β μ(x, z)`. -/
def Nbhd {n : ℕ} (β : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | (∀ j, 0 < p.1 j) ∧ (∀ j, 0 < p.2 j) ∧
    euclidNorm (centralityResidual p.1 p.2) ≤ β * mu p.1 p.2}

/-- `(Δx, Δz)` solves the step equations (22.5)–(22.6) at `(x, z)` with centering
parameter `δ`:
`AΔx + Δz = -(1 - δ) ρ(x, z)` and `ZΔx + XΔz = δ μ(x, z) e - XZe`
(the second written componentwise: `zⱼ Δxⱼ + xⱼ Δzⱼ = δ μ(x, z) - xⱼ zⱼ`). -/
def IsStepDirection {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ)
    (x z dx dz : Fin n → ℝ) : Prop :=
  A *ᵥ dx + dz = (-(1 - δ)) • rho A x z ∧
    ∀ j, z j * dx j + x j * dz j = δ * mu x z - x j * z j

/-- The predictor step length (22.10), `θ = max{t : (x + tΔx, z + tΔz) ∈ N(1/2)}`,
taken as the supremum of that set of step lengths (the maximum need not be attained). -/
noncomputable def predictorStepLength {n : ℕ} (x z dx dz : Fin n → ℝ) : ℝ :=
  sSup {t : ℝ | (x + t • dx, z + t • dz) ∈ Nbhd (1 / 2 : ℝ)}

/-- The scaled direction `p = X^{-1/2} Z^{1/2} Δx` of (22.11):
`pⱼ = √zⱼ / √xⱼ · Δxⱼ`. -/
noncomputable def scaledDx {n : ℕ} (x z dx : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (z j) / Real.sqrt (x j) * dx j

/-- The scaled direction `q = X^{1/2} Z^{-1/2} Δz` of (22.11):
`qⱼ = √xⱼ / √zⱼ · Δzⱼ`. -/
noncomputable def scaledDz {n : ℕ} (x z dz : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (x j) / Real.sqrt (z j) * dz j

end VanderbeiLP.SelfDual


