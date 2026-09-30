-- Prove2me | Definitions.Def_UnderstandingML_Convex
-- name    : UnderstandingML_Convex
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T04:13:21.562377+00:00
-- url     : https://prove2.me/theorems/0ad13170-8d2a-4da7-bcf0-5f99d67f4d29
-- title:
--   Chapters 12–13: convex, convex-Lipschitz-bounded and convex-smooth-bounded problems, hinge and 0–1 losses, RLM with Tikhonov regularization, on-average-replace-one stability, the ridge loss
-- statement:
--   Chapters 12–13 of Shalev-Shwartz and Ben-David, with hypotheses $w \in \mathbb{R}^d$. A learning problem $(H, Z, \ell)$ is **convex** (Definition 12.10) if $H$ is convex and every $\ell(\cdot, z)$ is convex (`ConvexLearningProblem`); every $\ell(\cdot,z)$ is **$\rho$-Lipschitz** (`IsLipschitzLoss`, Definition 12.6, over $\mathbb{R}^d$) or **$\beta$-smooth** (`IsSmoothLoss`, Definition 12.8: differentiable with $\beta$-Lipschitz gradient). **Definition 12.12:** convex-Lipschitz-bounded with parameters $\rho, B$: $H$ convex with $\|w\| \le B$ on $H$, every $\ell(\cdot,z)$ convex and $\rho$-Lipschitz (`ConvexLipschitzBounded`). **Definition 12.13:** convex-smooth-bounded with parameters $\beta, B$: additionally nonnegative and $\beta$-smooth instead of Lipschitz (`ConvexSmoothBounded`). The 0–1 loss of halfspaces $\mathbb{1}[y\langle w,x\rangle \le 0]$ (`zeroOneLoss`), the **hinge loss** $\max\{0, 1 - y\langle w,x\rangle\}$ (`hingeLoss`), and the one-dimensional squared loss $(wx - y)^2$ of Examples 12.8–12.9 (`squaredLoss1`). **RLM (13.2):** the objective $L_S(w) + \lambda\|w\|^2$ (`rlmObjective`), its minimizers over $\mathbb{R}^d$ (`IsRLM`), and learners all of whose outputs are minimizers (`IsRLMLearner`). **Definition 13.3:** $A$ is on-average-replace-one-stable with rate $\epsilon(m)$ if for every $D$ and $m \ge 1$, $\mathbb{E}_{(S,z') \sim D^{m+1}, i \sim U(m)}[\ell(A(S^{(i)}), z_i) - \ell(A(S), z_i)] \le \epsilon(m)$, where $S^{(i)}$ replaces $z_i$ by $z'$ (`OnAverageReplaceOneStable`). Strong convexity (Definition 13.4) is Mathlib's `StrongConvexOn`. The ridge loss $\frac12(\langle w,x\rangle - y)^2$ of (13.3) (`ridgeLoss`).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §12.1-§12.3 Definitions 12.6, 12.8, 12.10, 12.12, 12.13 (pp. 160-166) and the hinge loss (p. 167); §13.1-§13.3 Equations (13.2)-(13.3), Definitions 13.3 and 13.4 (pp. 172-175)

import Definitions.Def_UnderstandingML_Linear
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapters 12–13:
# convex learning problems, regularized loss minimization and stability

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §12.1–§12.3 and §13.1–§13.4.

**Convex learning problems (§12.2).** Hypotheses are vectors `w ∈ ℝ^d`. `(H, Z, ℓ)` is convex
(Definition 12.10) if `H` is convex and every `ℓ(·, z)` is convex; **convex-Lipschitz-bounded**
with parameters `ρ, B` (Definition 12.12) if moreover `‖w‖ ≤ B` on `H` and every `ℓ(·, z)` is
`ρ`-Lipschitz; **convex-smooth-bounded** with parameters `β, B` (Definition 12.13) if `‖w‖ ≤ B`
on `H` and every `ℓ(·, z)` is convex, nonnegative and `β`-smooth (its gradient is `β`-Lipschitz,
Definition 12.8). The hinge loss `max{0, 1 − y⟨w, x⟩}` is the convex surrogate of the 0–1 loss
`𝟙[y⟨w, x⟩ ≤ 0]` for halfspaces (§12.3).

**Regularized loss minimization (§13.1).** With Tikhonov regularization the rule is
`A(S) ∈ argmin_w (L_S(w) + λ‖w‖²)` (13.2), unconstrained. Ridge regression (13.3) is the case of
the loss `½(⟨w, x⟩ − y)²`.

**Stability (§13.2).** For `S = (z₁, …, z_m)` and a further example `z'`, `S⁽ⁱ⁾` replaces `zᵢ` by
`z'`. `A` is **on-average-replace-one-stable with rate `ε(m)`** (Definition 13.3) if for every
distribution `D`, `E_{(S,z') ∼ D^{m+1}, i ∼ U(m)}[ℓ(A(S⁽ⁱ⁾), zᵢ) − ℓ(A(S), zᵢ)] ≤ ε(m)`.

**Strong convexity (Definition 13.4)** is Mathlib's `StrongConvexOn Set.univ λ f`:
`f(αw + (1−α)u) ≤ αf(w) + (1−α)f(u) − (λ/2)α(1−α)‖w − u‖²`.

**Conventions.** Lipschitzness and smoothness of `ℓ(·, z)` are required on all of `ℝ^d` (the
RLM rule is unconstrained, so its outputs need not lie in `H`). The RLM rule is a relation
(`IsRLM`), and a learner implements it if every output is a minimizer; for the losses of this
chapter the minimizer exists and is unique. Expectations over the sample are Bochner integrals
against `iidLaw D m`, and over `(S, z')` against `(iidLaw D m).prod D`; the uniform choice of
`i` is the average over `Fin m`.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

section ConvexProblems

variable {d : ℕ} {Z : Type*}

/-- **Definition 12.10**: `(H, Z, ℓ)` is a **convex learning problem**. -/
def ConvexLearningProblem (H : Set (Vec d)) (loss : Vec d → Z → ℝ) : Prop :=
  Convex ℝ H ∧ ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)

/-- Every `ℓ(·, z)` is **`ρ`-Lipschitz** over `ℝ^d` (Definition 12.6). -/
def IsLipschitzLoss (ρ : ℝ) (loss : Vec d → Z → ℝ) : Prop :=
  ∀ z w₁ w₂, |loss w₁ z - loss w₂ z| ≤ ρ * ‖w₁ - w₂‖

/-- Every `ℓ(·, z)` is differentiable and **`β`-smooth** over `ℝ^d`: its gradient is
`β`-Lipschitz (Definition 12.8). -/
def IsSmoothLoss (β : ℝ) (loss : Vec d → Z → ℝ) : Prop :=
  ∀ z, Differentiable ℝ (fun w ↦ loss w z) ∧
    ∀ v w, ‖gradient (fun w ↦ loss w z) v - gradient (fun w ↦ loss w z) w‖ ≤ β * ‖v - w‖

/-- **Definition 12.12**: a **convex-Lipschitz-bounded** learning problem with parameters
`ρ, B`. -/
def ConvexLipschitzBounded (H : Set (Vec d)) (loss : Vec d → Z → ℝ) (ρ B : ℝ) : Prop :=
  Convex ℝ H ∧ (∀ w ∈ H, ‖w‖ ≤ B) ∧ (∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) ∧
    IsLipschitzLoss ρ loss

/-- **Definition 12.13**: a **convex-smooth-bounded** learning problem with parameters `β, B`
(the loss is also nonnegative). -/
def ConvexSmoothBounded (H : Set (Vec d)) (loss : Vec d → Z → ℝ) (β B : ℝ) : Prop :=
  Convex ℝ H ∧ (∀ w ∈ H, ‖w‖ ≤ B) ∧ (∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) ∧
    (∀ w z, 0 ≤ loss w z) ∧ IsSmoothLoss β loss

/-- The 0–1 loss of the halfspace `w` on `(x, y)` with `y ∈ {±1}`: `𝟙[y⟨w, x⟩ ≤ 0]` (§12.3). -/
noncomputable def zeroOneLoss (w : Vec d) (z : Vec d × ℝ) : ℝ :=
  if z.2 * ⟪w, z.1⟫_ℝ ≤ 0 then 1 else 0

/-- The **hinge loss** `max{0, 1 − y⟨w, x⟩}` (§12.3). -/
noncomputable def hingeLoss (w : Vec d) (z : Vec d × ℝ) : ℝ := max 0 (1 - z.2 * ⟪w, z.1⟫_ℝ)

/-- Homogenous linear regression on the line with the squared loss `(wx − y)²`
(Examples 12.8–12.9). -/
def squaredLoss1 (w : ℝ) (z : ℝ × ℝ) : ℝ := (w * z.1 - z.2) ^ 2

end ConvexProblems

/-! ### Regularized loss minimization and stability (Chapter 13) -/

section RLM

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

/-- The RLM objective `L_S(w) + λ‖w‖²` with Tikhonov regularization (13.2). -/
noncomputable def rlmObjective (loss : Vec d → Z → ℝ) (lam : ℝ) {m : ℕ} (S : Fin m → Z)
    (w : Vec d) : ℝ :=
  empRisk loss S w + lam * ‖w‖ ^ 2

/-- `w` is an output of the **RLM rule** (13.2): a minimizer of `L_S(w) + λ‖w‖²` over `ℝ^d`. -/
def IsRLM (loss : Vec d → Z → ℝ) (lam : ℝ) {m : ℕ} (S : Fin m → Z) (w : Vec d) : Prop :=
  ∀ w', rlmObjective loss lam S w ≤ rlmObjective loss lam S w'

/-- `A` implements the RLM rule with parameter `λ`: every output is a minimizer. -/
def IsRLMLearner (loss : Vec d → Z → ℝ) (lam : ℝ) (A : Learner Z (Vec d)) : Prop :=
  ∀ (m : ℕ) (S : Fin m → Z), IsRLM loss lam S (A m S)

/-- **Definition 13.3**: `A` is **on-average-replace-one-stable with rate `ε(m)`**: for every
distribution `D` and `m ≥ 1`,
`E_{(S,z') ∼ D^{m+1}, i ∼ U(m)}[ℓ(A(S⁽ⁱ⁾), zᵢ) − ℓ(A(S), zᵢ)] ≤ ε(m)`, where `S⁽ⁱ⁾` is `S` with
its `i`-th example replaced by `z'`. -/
def OnAverageReplaceOneStable (loss : Vec d → Z → ℝ) (A : Learner Z (Vec d)) (ε : ℕ → ℝ) :
    Prop :=
  ∀ D : Measure Z, IsProbabilityMeasure D → ∀ m : ℕ, 0 < m →
    (∑ i, ∫ p : (Fin m → Z) × Z,
        (loss (A m (Function.update p.1 i p.2)) (p.1 i) - loss (A m p.1) (p.1 i))
          ∂((iidLaw D m).prod D)) / m ≤ ε m

/-- The loss `½(⟨w, x⟩ − y)²` of ridge regression (13.3). -/
noncomputable def ridgeLoss (w : Vec d) (z : Vec d × ℝ) : ℝ := (1 / 2) * (⟪w, z.1⟫_ℝ - z.2) ^ 2

end RLM

end UnderstandingML


