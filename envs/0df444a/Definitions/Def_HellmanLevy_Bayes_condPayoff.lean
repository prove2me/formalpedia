-- Prove2me | Definitions.Def_HellmanLevy_Bayes_condPayoff
-- name    : HellmanLevy_Bayes_condPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:30.258558+00:00
-- url     : https://prove2.me/theorems/af19ac48-3064-49bd-8133-80b629784ddb
-- title:
--   Conditional (interim) payoff $r^i(\sigma\mid\tau^i)$
-- statement:
--   Given a strategy profile $\sigma$, a player $i$ and a state $\omega$ with type $\tau^i=t^i_\omega$, the **conditional payoff** of player $i$ is
--   $$r^i(\sigma\mid\tau^i)=\sum_{\{\omega' : t^i(\omega')=\tau^i\}} r^i(\omega',\sigma(\omega'))\,\tau^i(\omega')=\int_\Omega r^i(\omega',\sigma(\omega'))\,d\tau^i(\omega').$$
--   The payoff (3.2) of the deviation to an action $x$ is the conditional payoff of the profile in which player $i$ plays $x$ at every state and the others keep $\sigma$.
--
--   **Formalization Note** The type $\tau^i$ is concentrated on the countable class of $\omega$, so the integral is the countable sum (3.1). The integrand is bounded and measurable.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), eq. (3.1)–(3.2), p.13

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_mixedPayoff

namespace HellmanLevy.Bayes

/-- The **conditional (interim) payoff** of player `i` of type `τⁱ = tⁱ(ω)` under the profile
`σ`: `rⁱ(σ | τⁱ) = Σ_{ω' | tⁱ(ω') = τⁱ} rⁱ(ω', σ(ω')) · τⁱ(ω')`, written as the integral of
`ω' ↦ rⁱ(ω', σ(ω'))` against the type `tⁱ_ω`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), eq. (3.1), p.13. The payoff (3.2) of a deviation to an action `x` is
`condPayoff B i (Function.update σ i (fun _ => PMF.pure x)) ω`.

**Formalization Note** The type `tⁱ_ω` is concentrated on the countable class `{ω' | tⁱ(ω') =
tⁱ(ω)}` (this follows from `BayesianGame.knows`), so the integral equals the countable sum
(3.1). The integrand is bounded and measurable for every strategy profile, so the integral is
never the Bochner default. -/
noncomputable def condPayoff {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    [DecidableEq I] {A : I → Type*} [∀ i, Fintype (A i)] (B : BayesianGame Ω I A) (i : I)
    (σ : ∀ i, Ω → PMF (A i)) (ω : Ω) : ℝ :=
  ∫ ω', mixedPayoff B i σ ω' ∂(B.t i ω)

end HellmanLevy.Bayes


