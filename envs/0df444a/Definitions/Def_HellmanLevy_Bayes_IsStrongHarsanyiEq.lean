-- Prove2me | Definitions.Def_HellmanLevy_Bayes_IsStrongHarsanyiEq
-- name    : HellmanLevy_Bayes_IsStrongHarsanyiEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:35.62091+00:00
-- url     : https://prove2.me/theorems/e38b795e-51ef-4c3c-b1a9-5e26ec2ba339
-- title:
--   Strong Harsányi $\varepsilon$-equilibrium of a Bayesian game
-- statement:
--   A strategy profile $\sigma$ of a Bayesian game is a **strong Harsányi $\varepsilon$-equilibrium** if there is a set $\Omega'\subseteq\Omega$ with $\mu^i(\Omega')<\varepsilon$ for every player $i$ such that at every state $\omega\notin\Omega'$ every player optimizes exactly:
--   $$r^i(\sigma\mid\tau^i)=\max_{a\in A_i}r^i(a,\sigma^{-i}\mid\tau^i),\qquad\tau^i=t^i_\omega,\ i\in I.$$
--
--   **Formalization Note** Definition 4.2 reads "for each player $i$ there is a subset $\Omega'$ … with $\mu^i(\Omega')<\varepsilon$ such that for all $\omega\notin\Omega'$, $i\in I$"; it is read with one exceptional set for all players (the set the proof of Lemma 4.6 builds), which implies the per-player reading. The inequality is strict as printed. $\Omega'$ need not be measurable (outer measure).
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), Definition 4.2, pp.17–18

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_IsStrategy
import Definitions.Def_HellmanLevy_Bayes_gap

namespace HellmanLevy.Bayes

/-- `σ` is a **strong Harsányi ε-equilibrium** of the Bayesian game `B`: a strategy profile
together with a set `Ω' ⊆ Ω` with `µⁱ(Ω') < ε` for every player `i`, such that at every state
`ω ∉ Ω'` every player `i` optimizes exactly: `rⁱ(σ | τⁱ) = maxₐ rⁱ(a, σ⁻ⁱ | τⁱ)`, `τⁱ = tⁱ(ω)`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), Definition 4.2, pp.17–18 (strict inequality `µⁱ(Ω′) < ε` as printed).

**Formalization Note** Definition 4.2 reads "for each player i there is a subset Ω′ ⊆ Ω with
µⁱ(Ω′) < ε such that for all ω ∉ Ω′, i ∈ I"; the quantifier "i ∈ I" after the choice of `Ω'` is
read as one exceptional set serving all players, the set the proof of Lemma 4.6 constructs
(`Ω′ = ⋃ᵢ (tⁱ)⁻¹(Ω′_T)`). This reading implies the per-player one. `Ω'` need not be measurable;
`µⁱ(Ω')` is then the outer measure. -/
def IsStrongHarsanyiEq {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    [DecidableEq I] {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (B : BayesianGame Ω I A) (ε : ℝ) (σ : ∀ i, Ω → PMF (A i)) : Prop :=
  IsStrategy B σ ∧ ∃ S : Set Ω, (∀ i, B.μ i S < ENNReal.ofReal ε) ∧ ∀ ω ∉ S, ∀ i, gap B i σ ω = 0

end HellmanLevy.Bayes


