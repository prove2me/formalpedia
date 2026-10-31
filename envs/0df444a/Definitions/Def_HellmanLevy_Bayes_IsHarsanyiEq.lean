-- Prove2me | Definitions.Def_HellmanLevy_Bayes_IsHarsanyiEq
-- name    : HellmanLevy_Bayes_IsHarsanyiEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:42.751201+00:00
-- url     : https://prove2.me/theorems/d7bdd8e3-b531-4cde-99c3-5fdf6666a5ac
-- title:
--   Harsányi $\varepsilon$-equilibrium of a Bayesian game
-- statement:
--   A strategy profile $\sigma$ of a Bayesian game with priors $(\mu^i)$ is a **Harsányi $\varepsilon$-equilibrium** if for every player $i$
--   $$\int_\Omega\Big[\max_{a\in A_i}r^i(a,\sigma^{-i}\mid\tau^i)-r^i(\sigma\mid\tau^i)\Big]\,d\mu^i\le\varepsilon,\qquad \tau^i=t^i_\omega .$$
--
--   This is the ex ante equilibrium notion: a player's gain from deviating is averaged over their types with respect to their own prior, so some types may gain more than $\varepsilon$ as long as the average does not. It is the notion of the paper's main theorem.
--
--   **Formalization Note** The gain is required to be $\mu^i$-integrable, which excludes nothing in the paper's setting (it is bounded and measurable) and prevents a non-integrable gain from passing with Bochner integral $0$. The phrase "for each alternative mixed action" before (4.1) binds nothing; the maximum is over pure actions.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), Definition 4.1, eq. (4.1), p.16

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_IsStrategy
import Definitions.Def_HellmanLevy_Bayes_gap

namespace HellmanLevy.Bayes

/-- `σ` is a **Harsányi ε-equilibrium** of the Bayesian game `B`: a strategy profile such that,
for each player `i`, the gain from deviating integrated against `i`'s prior is at most `ε`:
`∫_Ω [maxₐ∈Aᵢ rⁱ(a, σ⁻ⁱ | τⁱ) − rⁱ(σ | τⁱ)] dµⁱ ≤ ε` with `τⁱ = tⁱ(ω)`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), Definition 4.1, eq. (4.1), p.16.

**Formalization Note** The integrability of the gain is part of the definition, so that a
non-integrable gap (whose Bochner integral is `0` in Lean) cannot pass the test; in the paper's
setting (bounded payoffs, probability priors) the gap is bounded and measurable, so this clause
excludes nothing. The phrase "for each alternative mixed action a ∈ ∆(Ai)" preceding (4.1)
binds nothing in (4.1), whose maximum is over pure actions. -/
def IsHarsanyiEq {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (B : BayesianGame Ω I A)
    (ε : ℝ) (σ : ∀ i, Ω → PMF (A i)) : Prop :=
  IsStrategy B σ ∧ ∀ i, MeasureTheory.Integrable (gap B i σ) (B.μ i) ∧
    ∫ ω, gap B i σ ω ∂(B.μ i) ≤ ε

end HellmanLevy.Bayes


