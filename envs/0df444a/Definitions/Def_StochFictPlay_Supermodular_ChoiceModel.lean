-- Prove2me | Definitions.Def_StochFictPlay_Supermodular_ChoiceModel
-- name    : StochFictPlay_Supermodular_ChoiceModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:14:37.565782+00:00
-- url     : https://prove2.me/theorems/6ddc4074-2668-42a7-83f1-7c64b6af7b75
-- title:
--   Random utility choice function and the conditions of Theorem 2.1
-- statement:
--   Fix a number $m$ of alternatives, indexed $0,\dots,m-1$. Let $\varepsilon$ be a random vector in $\mathbb R^m$ with density $f$.
--
--   1. **Choice function.** For a payoff vector $\pi \in \mathbb R^m$, the additive random utility choice probabilities are
--   $$C_i(\pi) = P\big(\pi_j + \varepsilon_j < \pi_i + \varepsilon_i \text{ for all } j \neq i\big),$$
--   the probability that alternative $i$ is the unique maximizer of the perturbed payoffs $\pi_j + \varepsilon_j$.
--   2. **Conditions of Theorem 2.1.** The density $f$ is measurable, finite, strictly positive everywhere, integrates to $1$, and the resulting choice function $C : \mathbb R^m \to \mathbb R^m$ is continuously differentiable.
--
--   These are the conditions each player's payoff disturbances satisfy in stochastic fictitious play; the perturbed best response of a player is $C$ applied to the player's payoff vector.
--
--   **Formalization Note** Densities are $[0,\infty]$-valued functions on $\mathbb R^m$ with respect to Lebesgue measure. The argmax event is written with strict inequalities; ties have probability zero because $\varepsilon$ has a density.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, pp. 4-5, eq. (1) and the hypotheses of Theorem 2.1; p. 10 (conditions imposed on each player's disturbances)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- The additive random utility choice function, eq. (1) (Hofbauer–Sandholm 2002, manuscript
p. 4): `C_i(π) = P(argmax_j π_j + ε_j = i)` for a shock vector `ε` with density `f` on `ℝ^m`.
The event "`i` is the argmax" is written with strict inequalities; ties have probability zero
because `ε` has a density. -/
noncomputable def choiceProb {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (π : Fin m → ℝ) : Fin m → ℝ :=
  fun i => ((volume.withDensity f) {e | ∀ j, j ≠ i → π j + e j < π i + e i}).toReal

/-- "The conditions of Theorem 2.1" (manuscript p. 5, required of every player's shocks on
p. 10): `f` is a strictly positive (finite, measurable) probability density on `ℝ^m`, and the
induced choice function `C = choiceProb f` is continuously differentiable. -/
def IsRegularDensity {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) : Prop :=
  Measurable f ∧ (∀ e, 0 < f e) ∧ (∀ e, f e ≠ ⊤) ∧ (∫⁻ e, f e = 1) ∧
    ContDiff ℝ 1 (choiceProb f)

end StochFictPlay.Supermodular


