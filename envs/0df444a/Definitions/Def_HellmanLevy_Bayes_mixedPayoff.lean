-- Prove2me | Definitions.Def_HellmanLevy_Bayes_mixedPayoff
-- name    : HellmanLevy_Bayes_mixedPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:32.379998+00:00
-- url     : https://prove2.me/theorems/ae894a6e-47cc-4f62-9c54-7b37dcbc8f19
-- title:
--   Payoff at a state under a mixed profile
-- statement:
--   For a strategy profile $\sigma$ and a state $\omega$, player $i$'s payoff at $\omega$ is the multilinear extension of $r^i(\omega,\cdot)$:
--   $$r^i(\omega,\sigma(\omega))=\sum_{a\in\prod_j A_j}\Big(\prod_{j\in I}\sigma^j(\omega)(a_j)\Big)\,r^i(\omega,a).$$
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §3.1, p.12

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_BayesianGame

namespace HellmanLevy.Bayes

/-- Player `i`'s payoff at state `ω` under the mixed profile `σ(ω)`: the multilinear extension
`rⁱ(ω, σ(ω)) = Σ_a (∏ⱼ σʲ(ω)(aⱼ)) rⁱ(ω, a)`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §3.1, p.12 ("The payoff function r extends multi-linearly to mixed actions in the usual
manner"). -/
noncomputable def mixedPayoff {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    [DecidableEq I] {A : I → Type*} [∀ i, Fintype (A i)] (B : BayesianGame Ω I A) (i : I)
    (σ : ∀ i, Ω → PMF (A i)) (ω : Ω) : ℝ :=
  ∑ a : (∀ j, A j), (∏ j, (σ j ω (a j)).toReal) * B.r i ω a

end HellmanLevy.Bayes


