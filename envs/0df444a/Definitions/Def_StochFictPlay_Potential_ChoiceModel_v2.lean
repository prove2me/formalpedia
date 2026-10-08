-- Prove2me | Definitions.Def_StochFictPlay_Potential_ChoiceModel_v2
-- name    : StochFictPlay_Potential_ChoiceModel_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:18:20.346797+00:00
-- url     : https://prove2.me/theorems/aef13c6c-f5f7-40ef-ac98-c860d83867be
-- title:
--   Random utility choice function and the conditions of Theorem 2.1 (continuous strictly positive density)
-- statement:
--   Fix a number $m$ of alternatives, indexed $0,\dots,m-1$. Let $\varepsilon$ be a random vector in $\mathbb R^m$ with density $f$ with respect to Lebesgue measure.
--
--   1. **Choice function.** For a payoff vector $\pi \in \mathbb R^m$, the additive random utility choice probabilities are
--   $$C_i(\pi) = P\big(\pi_j + \varepsilon_j < \pi_i + \varepsilon_i \text{ for all } j \neq i\big),$$
--   the probability that alternative $i$ is the unique maximizer of the perturbed payoffs $\pi_j + \varepsilon_j$ (eq. (1), p. 4).
--   2. **Conditions of Theorem 2.1 (regular density).** The density $f$ is *continuous*, finite and strictly positive at every point of $\mathbb R^m$, integrates to $1$, and the resulting choice function $C : \mathbb R^m \to \mathbb R^m$ is continuously differentiable.
--
--   These are the conditions each player's payoff disturbances satisfy in stochastic fictitious play (p. 10); the perturbed best response of a player is $C$ applied to the player's payoff vector. The module also carries, unchanged from the retired version, the open simplex $\operatorname{int}(\Delta)$, the projection onto the affine plane $\{\sum y = 1\}$, the notion of an admissible deterministic perturbation $V$ ($C^2$ on $\operatorname{int}(\Delta)$, $D^2V$ positive definite on the tangent space, $\|\nabla V\| \to \infty$ at the boundary), the $C^N$ predicate, and the unique perturbed argmax relation $C(\pi) = \operatorname{arg\,max}_{y \in \operatorname{int}(\Delta)} (y \cdot \pi - V(y))$.
--
--   **Formalization Note.** Densities are $[0,\infty]$-valued functions on $\mathbb R^m$; continuity implies measurability, so the earlier measurability clause is dropped. The retired definition required only pointwise positivity of one measurable representative, a condition invariant under modification on null sets, so a density with a genuine zero could be patched to satisfy it while the choice function it defines has a critical point. The paper's proof of Theorem 2.1 (eq. (4), p. 6) evaluates the density on hyperplanes, i.e. it works with a fixed continuous version; requiring the representative $f$ itself to be continuous and strictly positive is the standard reading of "admits a strictly positive density" in the random-utility literature (McFadden's Williams–Daly–Zachary theorem, cited on p. 8, is stated for such densities) and is what makes the density of every payoff difference positive everywhere, hence the off-diagonal partials of $C$ strictly negative. Since $C$ depends only on the law of $\varepsilon$, requiring the chosen representative to be continuous loses no generality. The argmax event is written with strict inequalities; ties have probability zero because $\varepsilon$ has a density.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, pp. 4-6 and 10: eq. (1), the hypotheses of Theorem 2.1 (p. 5) read with the regularity its proof uses in eq. (4) (p. 6); p. 5 (admissible deterministic perturbation), p. 7 footnote 3

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace StochFictPlay.Potential

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

/-- "The conditions of Theorem 2.1" (manuscript p. 5, used on p. 10): the shock vector `ε` admits a
strictly positive density `f` on `ℝ^m`, and the induced choice function `C = choiceProb f` is
continuously differentiable. The density is taken in the regular sense in which the paper uses
it: eq. (4) (p. 6) evaluates `f` on hyperplanes `{x_j = π_i + x_i − π_j}`, which only makes sense
for a fixed **continuous** version of the density. Hence `f` is required to be a continuous,
everywhere finite, strictly positive probability density (continuity implies measurability).
Positivity is then a property of the law of `ε`, not of one representative: a density that
vanishes somewhere cannot be made to qualify by changing it on a null set, so the density of
every payoff difference is positive everywhere and the off-diagonal partials of `C` are
strictly negative, as the proof of Theorem 2.1 requires. -/
def IsRegularDensity {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) : Prop :=
  Continuous f ∧ (∀ e, 0 < f e) ∧ (∀ e, f e ≠ ⊤) ∧ (∫⁻ e, f e = 1) ∧
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
`∇V(y)` of footnote 3 (p. 7) acting on `ℝ^m`. -/
def IsAdmissible {m : ℕ} (V : (Fin m → ℝ) → ℝ) : Prop :=
  ContDiffOn ℝ 2 (V ∘ planeProj m) {w | ∀ i, 0 < planeProj m w i} ∧
  (∀ y ∈ openSimplex m, ∀ z : Fin m → ℝ, ∑ i, z i = 0 → z ≠ 0 →
    0 < fderiv ℝ (fderiv ℝ (V ∘ planeProj m)) y z z) ∧
  (∀ M : ℝ, ∃ δ > 0, ∀ y ∈ openSimplex m, (∃ i, y i < δ) →
    M < ‖fderiv ℝ (V ∘ planeProj m) y‖)

/-- `V` is `C^N` on `int(∆A)` (Proposition 4.2, manuscript p. 18), in the same sense as the
`C²` clause of `IsAdmissible`: the extension `V ∘ planeProj m`, constant along `𝟙`, is `N` times
continuously differentiable on the open set of points projecting into `int(∆A)`. -/
def IsCkOnSimplex {m : ℕ} (V : (Fin m → ℝ) → ℝ) (N : ℕ) : Prop :=
  ContDiffOn ℝ N (V ∘ planeProj m) {w | ∀ i, 0 < planeProj m w i}

/-- `Ct` is the deterministically perturbed best response of `V`: for every payoff vector `π`,
`Ct π` is the **unique** maximizer of `y ↦ y · π − V(y)` over `int(∆A)` (the argmax in (2),
p. 5, and in (PV), p. 14). -/
def IsPerturbedArgmax {m : ℕ} (V : (Fin m → ℝ) → ℝ) (Ct : (Fin m → ℝ) → (Fin m → ℝ)) : Prop :=
  ∀ π : Fin m → ℝ, Ct π ∈ openSimplex m ∧
    ∀ y ∈ openSimplex m, y ≠ Ct π → y ⬝ᵥ π - V y < Ct π ⬝ᵥ π - V (Ct π)

end StochFictPlay.Potential


