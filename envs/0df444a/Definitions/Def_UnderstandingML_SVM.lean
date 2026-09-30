-- Prove2me | Definitions.Def_UnderstandingML_SVM
-- name    : UnderstandingML_SVM
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T04:36:55.943882+00:00
-- url     : https://prove2.me/theorems/db88b5a5-876c-44a3-bab3-ee0b7819eade
-- title:
--   Chapter 15: linear separability, the sample margin, Hard-SVM (15.2)/(15.3), separability with a (γ, ρ)-margin (Def. 15.3), the Soft-SVM constraints and objective (15.4), the ramp loss
-- statement:
--   Chapter 15 of Shalev-Shwartz and Ben-David. A sample $(x_i, y_i)$ with $y_i \in \{\pm 1\}$ is **linearly separable** if some halfspace $(w, b)$ has $y_i(\langle w, x_i\rangle + b) > 0$ for all $i$ (`LinearlySeparable`); the **margin** of $(w, b)$ on the sample is $\min_i y_i(\langle w, x_i\rangle + b)$ (`sampleMargin`, a real infimum over $[m]$). **Hard-SVM (15.2):** $(w_0, b_0)$ minimizes $\|w\|$ subject to $y_i(\langle w, x_i\rangle + b) \ge 1$ (`IsHardSVM`); the homogenous version (15.3) with $b = 0$ (`IsHomHardSVM`). **Definition 15.3:** $D$ over $\mathbb{R}^d \times \{\pm1\}$ is separable with a $(\gamma, \rho)$-margin if some $(w^\star, b^\star)$ with $\|w^\star\| = 1$ has $y(\langle w^\star, x\rangle + b^\star) \ge \gamma$ and $\|x\| \le \rho$ with probability $1$ (`SeparableWithMargin`), and using a homogenous halfspace if $b^\star = 0$ (`HomSeparableWithMargin`). **Soft-SVM (15.4):** the constraints $y_i(\langle w, x_i\rangle + b) \ge 1 - \xi_i$, $\xi_i \ge 0$ (`SoftSVMFeasible`) and the objective $\lambda\|w\|^2 + \frac1m\sum_i \xi_i$ (`softSVMObjective`); the hinge loss of a nonhomogenous halfspace $\max\{0, 1 - y(\langle w, x\rangle + b)\}$ (`hingeLossAffine`); the homogenous Soft-SVM (15.6) is the RLM rule of Mission IX for the hinge loss. The **ramp loss** $\min\{1, \ell_{hinge}\}$ (`rampLoss`).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §15.1 pp. 202-205 (Equations (15.1)-(15.3)), Definition 15.3 p. 206, §15.2 pp. 206-207 (Equations (15.4)-(15.6)), §15.2.3 p. 210

import Definitions.Def_UnderstandingML_Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 15:
# support vector machines

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §15.1–§15.3.

**Margin and Hard-SVM (§15.1).** A sample `(xᵢ, yᵢ)` with `yᵢ ∈ {±1}` is linearly separable if
some halfspace `(w, b)` has `yᵢ(⟨w, xᵢ⟩ + b) > 0` for all `i`. Hard-SVM (15.2) returns
`(w₀, b₀) = argmin ‖w‖²` subject to `yᵢ(⟨w, xᵢ⟩ + b) ≥ 1`, normalized to `(w₀/‖w₀‖, b₀/‖w₀‖)`;
the homogenous version (15.3) has `b = 0`. **Definition 15.3:** `D` over `ℝ^d × {±1}` is
separable with a `(γ, ρ)`-margin if some `(w⋆, b⋆)` with `‖w⋆‖ = 1` has, with probability `1`,
`y(⟨w⋆, x⟩ + b⋆) ≥ γ` and `‖x‖ ≤ ρ`.

**Soft-SVM (§15.2).** The problem (15.4) with slack variables `ξᵢ ≥ 0`,
`yᵢ(⟨w, xᵢ⟩ + b) ≥ 1 − ξᵢ`, objective `λ‖w‖² + (1/m) ∑ ξᵢ`; equivalently (15.5) regularized
hinge-loss minimization; the homogenous version (15.6) is the RLM rule of Chapter 13 for the
hinge loss `max{0, 1 − y⟨w, x⟩}`. The ramp loss is `min{1, ℓ_hinge}` (§15.2.3).

**Conventions.** Labels are real numbers, with `y = ±1` as a hypothesis where the book needs it.
`sampleMargin` is `minᵢ yᵢ(⟨w, xᵢ⟩ + b)` as a real infimum over `Fin m`. Hard-SVM solutions are
minimizer relations (`IsHardSVM`, `IsHomHardSVM`); the minimizer is unique whenever the
constraints are feasible. The homogenous Soft-SVM output is `IsRLM hingeLoss λ S w` of
Mission IX.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

section SVM

variable {d m : ℕ}

/-- The sample `(xᵢ, yᵢ)` is **linearly separable** (§15.1): some halfspace `(w, b)` has
`yᵢ(⟨w, xᵢ⟩ + b) > 0` for all `i`. -/
def LinearlySeparable (x : Fin m → Vec d) (y : Fin m → ℝ) : Prop :=
  ∃ (w : Vec d) (b : ℝ), ∀ i, 0 < y i * (⟪w, x i⟫_ℝ + b)

/-- The margin `minᵢ yᵢ(⟨w, xᵢ⟩ + b)` of the halfspace `(w, b)` on the sample (15.1). -/
noncomputable def sampleMargin (x : Fin m → Vec d) (y : Fin m → ℝ) (w : Vec d) (b : ℝ) : ℝ :=
  ⨅ i, y i * (⟪w, x i⟫_ℝ + b)

/-- `(w₀, b₀)` is a solution of the **Hard-SVM** problem (15.2): `‖w₀‖` is minimal among the
halfspaces with `yᵢ(⟨w, xᵢ⟩ + b) ≥ 1` for all `i`. -/
def IsHardSVM (x : Fin m → Vec d) (y : Fin m → ℝ) (w₀ : Vec d) (b₀ : ℝ) : Prop :=
  (∀ i, 1 ≤ y i * (⟪w₀, x i⟫_ℝ + b₀)) ∧
    ∀ (w : Vec d) (b : ℝ), (∀ i, 1 ≤ y i * (⟪w, x i⟫_ℝ + b)) → ‖w₀‖ ≤ ‖w‖

/-- `w₀` is a solution of the **homogenous Hard-SVM** problem (15.3). -/
def IsHomHardSVM (x : Fin m → Vec d) (y : Fin m → ℝ) (w₀ : Vec d) : Prop :=
  (∀ i, 1 ≤ y i * ⟪w₀, x i⟫_ℝ) ∧ ∀ w : Vec d, (∀ i, 1 ≤ y i * ⟪w, x i⟫_ℝ) → ‖w₀‖ ≤ ‖w‖

/-- **Definition 15.3**: `D` is **separable with a `(γ, ρ)`-margin**: some `(w⋆, b⋆)` with
`‖w⋆‖ = 1` has `y(⟨w⋆, x⟩ + b⋆) ≥ γ` and `‖x‖ ≤ ρ` with probability `1`. -/
def SeparableWithMargin (D : Measure (Vec d × ℝ)) (γ ρ : ℝ) : Prop :=
  ∃ (w : Vec d) (b : ℝ), ‖w‖ = 1 ∧ ∀ᵐ z ∂D, γ ≤ z.2 * (⟪w, z.1⟫_ℝ + b) ∧ ‖z.1‖ ≤ ρ

/-- **Definition 15.3**, homogenous case: separable with a `(γ, ρ)`-margin using a halfspace
`(w⋆, 0)`. -/
def HomSeparableWithMargin (D : Measure (Vec d × ℝ)) (γ ρ : ℝ) : Prop :=
  ∃ w : Vec d, ‖w‖ = 1 ∧ ∀ᵐ z ∂D, γ ≤ z.2 * ⟪w, z.1⟫_ℝ ∧ ‖z.1‖ ≤ ρ

/-- The hinge loss of a nonhomogenous halfspace, `max{0, 1 − y(⟨w, x⟩ + b)}` (§15.2). -/
noncomputable def hingeLossAffine (w : Vec d) (b : ℝ) (z : Vec d × ℝ) : ℝ :=
  max 0 (1 - z.2 * (⟪w, z.1⟫_ℝ + b))

/-- The constraints of Soft-SVM (15.4): `yᵢ(⟨w, xᵢ⟩ + b) ≥ 1 − ξᵢ` and `ξᵢ ≥ 0`. -/
def SoftSVMFeasible (x : Fin m → Vec d) (y : Fin m → ℝ) (w : Vec d) (b : ℝ) (ξ : Fin m → ℝ) :
    Prop :=
  ∀ i, 1 - ξ i ≤ y i * (⟪w, x i⟫_ℝ + b) ∧ 0 ≤ ξ i

/-- The Soft-SVM objective `λ‖w‖² + (1/m) ∑ᵢ ξᵢ` (15.4). -/
noncomputable def softSVMObjective (lam : ℝ) (w : Vec d) (ξ : Fin m → ℝ) : ℝ :=
  lam * ‖w‖ ^ 2 + (∑ i, ξ i) / m

/-- The **ramp loss** `min{1, max{0, 1 − y⟨w, x⟩}}` (§15.2.3). -/
noncomputable def rampLoss (w : Vec d) (z : Vec d × ℝ) : ℝ := min 1 (hingeLoss w z)

end SVM

end UnderstandingML


