-- Prove2me | Definitions.Def_UnderstandingML_Linear
-- name    : UnderstandingML_Linear
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T03:53:06.243957+00:00
-- url     : https://prove2.me/theorems/c891988f-03bb-4d54-be52-48f37dba4c4d
-- title:
--   Chapter 9: affine functions and halfspaces, separability, the Perceptron run and the constants B and R of Theorem 9.1, squared loss and the Least Squares system (9.6), the logistic function and loss
-- statement:
--   Chapter 9 of Shalev-Shwartz and Ben-David, over $\mathbb{R}^d$ with the Euclidean inner product. The class $L_d = \{h_{w,b} : w \in \mathbb{R}^d, b \in \mathbb{R}\}$ of affine functions $h_{w,b}(x) = \langle w, x\rangle + b$ (`affine`, `affineFunctions`, the homogenous case `homLinear`); the halfspace hypotheses $x \mapsto \operatorname{sign}(\langle w, x\rangle + b)$ (`halfspace`, `true` iff $\langle w, x\rangle + b > 0$) and the classes `homHalfspaces` and `halfspaces` ($HS_d$). A training set $(x_i, y_i)$ with $y_i \in \{\pm 1\}$ is **separable** if some $w$ has $y_i\langle w, x_i\rangle > 0$ for all $i$; $B = \min\{\|w\| : \forall i,\ y_i\langle w, x_i\rangle \ge 1\}$ (`marginNorm`, an infimum) and $R = \max_i \|x_i\|$ (`radius`). A **run of the Batch Perceptron** (`IsPerceptronRun x y w T`): $w^{(0)} = 0$ and each of the $T$ updates adds $y_i x_i$ for an example with $y_i\langle w^{(t)}, x_i\rangle \le 0$. The **squared loss** $(h(x) - y)^2$ and **absolute loss** $|h(x) - y|$; the Least Squares system (9.6): $A = \sum_i x_i x_i^\top$ as the linear map $w \mapsto \sum_i \langle x_i, w\rangle x_i$ (`gram`) and $b = \sum_i y_i x_i$ (`lsTarget`). The **logistic function** $\varphi_{sig}(z) = 1/(1 + e^{-z})$ (9.9), the class $\varphi_{sig} \circ L_d$ (`logisticPredictors`) and the **logistic loss** $\log(1 + \exp(-y\langle w, x\rangle))$ (`logisticLoss`).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, Chapter 9 pp. 117-127: L_d and HS_d (pp. 117-118), §9.1.1-§9.1.2 (pp. 119-120), §9.2 and (9.6) (pp. 123-124), §9.3 and (9.9) (pp. 126-127)

import Definitions.Def_UnderstandingML_VC
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 9: linear predictors

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §9.1–§9.3.

**Affine functions and halfspaces (p. 117, §9.1).** `L_d = {h_{w,b} : w ∈ ℝ^d, b ∈ ℝ}` with
`h_{w,b}(x) = ⟨w, x⟩ + b`; the class of halfspaces is `HS_d = sign ∘ L_d`, the homogenous case
being `b = 0`. A training set `(x₁, y₁), …, (x_m, y_m)` with `yᵢ ∈ {±1}` is **separable** if
some `w` has `yᵢ⟨w, xᵢ⟩ > 0` for all `i`; in Theorem 9.1, `B = min{‖w‖ : ∀ i, yᵢ⟨w, xᵢ⟩ ≥ 1}`
and `R = maxᵢ ‖xᵢ‖`.

**Batch Perceptron (§9.1.2).** `w⁽¹⁾ = 0`; at each iteration pick an example with
`yᵢ⟨w⁽ᵗ⁾, xᵢ⟩ ≤ 0` and set `w⁽ᵗ⁺¹⁾ = w⁽ᵗ⁾ + yᵢ xᵢ`; stop when there is none.

**Linear regression (§9.2).** Squared loss `ℓ(h, (x, y)) = (h(x) − y)²`, the class `L_d`, and
Least Squares: the ERM problem for the homogenous class is `Aw = b` with `A = ∑ xᵢ xᵢᵀ`,
`b = ∑ yᵢ xᵢ` (9.6).

**Logistic regression (§9.3).** `φ_sig(z) = 1/(1 + e^{−z})` (9.9), the class
`φ_sig ∘ L_d`, and the logistic loss `ℓ(h_w, (x, y)) = log(1 + exp(−y⟨w, x⟩))`.

**Conventions.** Vectors live in `EuclideanSpace ℝ (Fin d)`. Halfspace hypotheses are
`Bool`-valued, `true` for `⟨w, x⟩ + b > 0` (so `sign(0)` is the negative label; the book leaves
`sign(0)` unspecified, and the VC computations do not depend on it). Labels of the Perceptron
and of regression are real numbers. The Perceptron's choice of a mistaken example is
nondeterministic, so a *run* is any sequence of updates obeying the rule.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- `ℝ^d` with its Euclidean inner product and norm. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

section Halfspaces

variable {d : ℕ}

/-- The affine function `h_{w,b}(x) = ⟨w, x⟩ + b` (p. 117). -/
noncomputable def affine (w : Vec d) (b : ℝ) : Vec d → ℝ := fun x ↦ ⟪w, x⟫_ℝ + b

/-- The class `L_d` of affine functions (p. 117), also the class of linear regression
predictors `H_reg` (§9.2). -/
def affineFunctions (d : ℕ) : Set (Vec d → ℝ) := {h | ∃ (w : Vec d) (b : ℝ), h = affine w b}

/-- The class of homogenous linear functions `h_w(x) = ⟨w, x⟩` (p. 118). -/
def homLinear (d : ℕ) : Set (Vec d → ℝ) := {h | ∃ w : Vec d, h = affine w 0}

/-- The halfspace hypothesis `x ↦ sign(⟨w, x⟩ + b)` (§9.1), as a `Bool`: `true` iff
`⟨w, x⟩ + b > 0`. -/
noncomputable def halfspace (w : Vec d) (b : ℝ) : Vec d → Bool :=
  fun x ↦ decide (0 < ⟪w, x⟫_ℝ + b)

/-- The class of homogenous halfspaces in `ℝ^d` (§9.1.3). -/
def homHalfspaces (d : ℕ) : Set (Vec d → Bool) := {h | ∃ w : Vec d, h = halfspace w 0}

/-- The class `HS_d` of (nonhomogenous) halfspaces in `ℝ^d` (§9.1). -/
def halfspaces (d : ℕ) : Set (Vec d → Bool) := {h | ∃ (w : Vec d) (b : ℝ), h = halfspace w b}

/-- The training set `(xᵢ, yᵢ)` is **separable** (the realizable case for homogenous
halfspaces, §9.1.1): some `w` has `yᵢ⟨w, xᵢ⟩ > 0` for all `i`. -/
def Separable {m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ) : Prop :=
  ∃ w : Vec d, ∀ i, 0 < y i * ⟪w, x i⟫_ℝ

/-- `B = min{‖w‖ : ∀ i ∈ [m], yᵢ⟨w, xᵢ⟩ ≥ 1}` of Theorem 9.1 (an infimum). -/
noncomputable def marginNorm {m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ) : ℝ :=
  sInf {r | ∃ w : Vec d, ‖w‖ = r ∧ ∀ i, 1 ≤ y i * ⟪w, x i⟫_ℝ}

/-- `R = maxᵢ ‖xᵢ‖` of Theorem 9.1. -/
noncomputable def radius {m : ℕ} (x : Fin m → Vec d) : ℝ := ⨆ i, ‖x i‖

/-- A **run of the Batch Perceptron** (§9.1.2) of `T` iterations: `w⁽⁰⁾ = 0` and each update
adds `yᵢ xᵢ` for some example with `yᵢ⟨w⁽ᵗ⁾, xᵢ⟩ ≤ 0` (the book's `w⁽¹⁾, w⁽²⁾, …` indexed
from `0`). -/
def IsPerceptronRun {m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ) (w : ℕ → Vec d) (T : ℕ) :
    Prop :=
  w 0 = 0 ∧ ∀ t < T, ∃ i, y i * ⟪w t, x i⟫_ℝ ≤ 0 ∧ w (t + 1) = w t + y i • x i

end Halfspaces

/-! ### Linear regression and Least Squares (§9.2) -/

section Regression

variable {d : ℕ}

/-- The **squared loss** `ℓ(h, (x, y)) = (h(x) − y)²` (§9.2). -/
def squaredLoss (h : Vec d → ℝ) (z : Vec d × ℝ) : ℝ := (h z.1 - z.2) ^ 2

/-- The **absolute value loss** `ℓ(h, (x, y)) = |h(x) − y|` (§9.2). -/
def absLoss (h : Vec d → ℝ) (z : Vec d × ℝ) : ℝ := |h z.1 - z.2|

/-- The matrix `A = ∑ᵢ xᵢ xᵢᵀ` of (9.6), as the linear map `w ↦ ∑ᵢ ⟨xᵢ, w⟩ xᵢ`. -/
noncomputable def gram {m : ℕ} (x : Fin m → Vec d) : Vec d →ₗ[ℝ] Vec d :=
  ∑ i, (innerₛₗ ℝ (x i)).smulRight (x i)

/-- The vector `b = ∑ᵢ yᵢ xᵢ` of (9.6). -/
noncomputable def lsTarget {m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ) : Vec d :=
  ∑ i, y i • x i

end Regression

/-! ### Logistic regression (§9.3) -/

section Logistic

variable {d : ℕ}

/-- The **logistic (sigmoid) function** `φ_sig(z) = 1/(1 + exp(−z))` (9.9). -/
noncomputable def logistic (z : ℝ) : ℝ := 1 / (1 + Real.exp (-z))

/-- The class `H_sig = φ_sig ∘ L_d` of logistic regression hypotheses (homogenous). -/
def logisticPredictors (d : ℕ) : Set (Vec d → ℝ) :=
  {h | ∃ w : Vec d, h = fun x ↦ logistic ⟪w, x⟫_ℝ}

/-- The **logistic loss** `ℓ(h_w, (x, y)) = log(1 + exp(−y⟨w, x⟩))` for `y ∈ {±1}` (§9.3). -/
noncomputable def logisticLoss (w : Vec d) (z : Vec d × ℝ) : ℝ :=
  Real.log (1 + Real.exp (-(z.2 * ⟪w, z.1⟫_ℝ)))

end Logistic

end UnderstandingML


