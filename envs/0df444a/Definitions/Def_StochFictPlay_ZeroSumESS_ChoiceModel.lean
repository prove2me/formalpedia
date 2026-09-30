-- Prove2me | Definitions.Def_StochFictPlay_ZeroSumESS_ChoiceModel
-- name    : StochFictPlay_ZeroSumESS_ChoiceModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T08:57:07.790693+00:00
-- url     : https://prove2.me/theorems/9bbe16a3-9555-4af6-937d-284cc7c552b7
-- title:
--   Random-utility choice function, admissible perturbations and the perturbed maximum $W$
-- statement:
--   Fix a number $m$ of alternatives, indexed $0,\dots,m-1$. Write $\operatorname{int}(\Delta) = \{y \in \mathbb R^m : y_i > 0 \text{ for all } i,\ \sum_i y_i = 1\}$ for the relative interior of the probability simplex and $\mathbb R^m_0 = \{z : \sum_i z_i = 0\}$ for its tangent space.
--
--   1. **Choice function.** For a shock vector $\varepsilon$ with density $f$ on $\mathbb R^m$ and a payoff vector $\pi \in \mathbb R^m$, the additive random utility choice probabilities are
--   $$C_i(\pi) = P\big(\pi_j + \varepsilon_j < \pi_i + \varepsilon_i \text{ for all } j \neq i\big).$$
--   2. **Conditions of Theorem 2.1.** $f$ is a measurable, finite, strictly positive probability density and $C$ is continuously differentiable on $\mathbb R^m$.
--   3. **Admissible perturbation.** A function $V : \operatorname{int}(\Delta) \to \mathbb R$ is admissible if it is twice continuously differentiable, its second derivative $D^2V(y)$ is positive definite on $\mathbb R^m_0$ at every $y$, and $\|\nabla V(y)\| \to \infty$ uniformly as $y$ approaches the boundary of $\Delta$: for every $M$ there is $\delta > 0$ with $\|\nabla V(y)\| > M$ whenever some $y_i < \delta$. Here $\nabla V(y) \in \mathbb R^m_0$ is the tangent gradient.
--   4. **Perturbed best response.** A map $\tilde C : \mathbb R^m \to \mathbb R^m$ represents $V$ if for every $\pi$, $\tilde C(\pi)$ is the unique maximizer of $y \mapsto y\cdot\pi - V(y)$ over $\operatorname{int}(\Delta)$:
--   $$\tilde C(\pi) = \operatorname*{arg\,max}_{y \in \operatorname{int}(\Delta)} \big(y\cdot \pi - V(y)\big).$$
--   5. **Perturbed maximum.** $W(\pi) = \tilde C(\pi)\cdot\pi - V(\tilde C(\pi))$, which equals $\max_{y \in \operatorname{int}(\Delta)} (y\cdot\pi - V(y))$, eq. (9) of the paper.
--
--   These are the discrete-choice objects of §2 that §4 uses to rewrite the perturbed best response dynamics in deterministic form.
--
--   **Formalization Note** Indices are 0-based. Ties in the argmax have probability zero because $\varepsilon$ has a density, so strict inequalities define $C$. $V$ is a function on all of $\mathbb R^m$ of which only the values on $\operatorname{int}(\Delta)$ matter; derivatives are those of $V \circ \mathrm{proj}$, where $\mathrm{proj}(w) = w + \frac{1 - \sum_j w_j}{m}\mathbf 1$ projects onto the plane $\{\sum_j y_j = 1\}$ along $\mathbf 1$. The derivative of $V\circ\mathrm{proj}$ at $y$ is $z \mapsto \nabla V(y)\cdot z$, and its operator norm (sup norm on $\mathbb R^m$) is the $\ell^1$ norm of $\nabla V(y)$; norms are equivalent, so the blow-up condition does not depend on this choice. The argmax is supplied as a map `Ct` with the uniqueness property instead of being chosen.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, pp. 4-5 and 7: eq. (1), the definition of an admissible deterministic perturbation and the hypotheses of Theorem 2.1 (p. 5), eq. (9) and footnote 3 (p. 7)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace StochFictPlay.ZeroSumESS

/-- The relative interior `int(∆A)` of the probability simplex on `m` alternatives
(Hofbauer–Sandholm 2002, manuscript p. 4): all coordinates positive, summing to one. -/
def openSimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {y | (∀ i, 0 < y i) ∧ ∑ i, y i = 1}

/-- The additive random utility choice function, eq. (1) (manuscript p. 4):
`C_i(π) = P(argmax_j π_j + ε_j = i)` for a shock vector `ε` with density `f`. The event
"`i` is the argmax" is written with strict inequalities; ties have probability zero because
`ε` has a density. -/
noncomputable def choiceProb {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (π : Fin m → ℝ) : Fin m → ℝ :=
  fun i => ((volume.withDensity f) {e | ∀ j, j ≠ i → π j + e j < π i + e i}).toReal

/-- "The conditions of Theorem 2.1" (manuscript p. 5, used on p. 10): `f` is a strictly positive
probability density on `ℝ^m` and the induced choice function is continuously differentiable. -/
def IsRegularDensity {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) : Prop :=
  Measurable f ∧ (∀ e, 0 < f e) ∧ (∀ e, f e ≠ ⊤) ∧ (∫⁻ e, f e = 1) ∧
    ContDiff ℝ 1 (choiceProb f)

/-- The projection of `ℝ^m` onto the affine plane `{y | ∑ y = 1}` along the vector of ones.
It is the identity on the plane; `V ∘ planeProj m` is the extension of a function `V` given on
the plane that is constant along `𝟙`, used to talk about derivatives of `V` on `int(∆A)`. -/
noncomputable def planeProj (m : ℕ) (w : Fin m → ℝ) : Fin m → ℝ :=
  fun i => w i + (1 - ∑ j, w j) / m

/-- Admissible deterministic perturbation (manuscript p. 5, after Fudenberg–Levine 1998):
`V : int(∆A) → ℝ` (only its values on `openSimplex m` matter) is twice continuously
differentiable on `int(∆A)`, `D²V(y)` is positive definite on `ℝ^m_0 = {z | ∑ z = 0}`, and
`‖∇V(y)‖ → ∞` as `y` approaches the boundary of `∆A`. Derivatives are taken of the extension
`V ∘ planeProj m`, which is constant along `𝟙`, so its derivative at `y` is the tangent gradient
`∇V(y)` of footnote 3 (p. 7) acting on `ℝ^m`; its operator norm (for the sup norm) is the
`ℓ¹` norm of `∇V(y)`. -/
def IsAdmissible {m : ℕ} (V : (Fin m → ℝ) → ℝ) : Prop :=
  ContDiffOn ℝ 2 (V ∘ planeProj m) {w | ∀ i, 0 < planeProj m w i} ∧
  (∀ y ∈ openSimplex m, ∀ z : Fin m → ℝ, ∑ i, z i = 0 → z ≠ 0 →
    0 < fderiv ℝ (fderiv ℝ (V ∘ planeProj m)) y z z) ∧
  (∀ M : ℝ, ∃ δ > 0, ∀ y ∈ openSimplex m, (∃ i, y i < δ) →
    M < ‖fderiv ℝ (V ∘ planeProj m) y‖)

/-- `Ct` is the deterministically perturbed best response of `V`: for every payoff vector `π`,
`Ct π` is the **unique** maximizer of `y ↦ y · π − V(y)` over `int(∆A)` (the argmax in (2),
p. 5, and in (PV), p. 14). -/
def IsPerturbedArgmax {m : ℕ} (V : (Fin m → ℝ) → ℝ) (Ct : (Fin m → ℝ) → (Fin m → ℝ)) : Prop :=
  ∀ π : Fin m → ℝ, Ct π ∈ openSimplex m ∧
    ∀ y ∈ openSimplex m, y ≠ Ct π → y ⬝ᵥ π - V y < Ct π ⬝ᵥ π - V (Ct π)

/-- The function `W` of eq. (9) (p. 7): `W(π) = max_{y ∈ int(∆A)} (y · π − V(y))`, written as
the value at the maximizer `Ct π`. It is the maximum whenever `IsPerturbedArgmax V Ct`. -/
noncomputable def perturbedMax {m : ℕ} (V : (Fin m → ℝ) → ℝ) (Ct : (Fin m → ℝ) → (Fin m → ℝ))
    (π : Fin m → ℝ) : ℝ :=
  Ct π ⬝ᵥ π - V (Ct π)

end StochFictPlay.ZeroSumESS


