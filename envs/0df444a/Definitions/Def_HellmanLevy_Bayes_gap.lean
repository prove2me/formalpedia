-- Prove2me | Definitions.Def_HellmanLevy_Bayes_gap
-- name    : HellmanLevy_Bayes_gap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:32.223783+00:00
-- url     : https://prove2.me/theorems/52a620b6-cca6-4cb0-986e-7bdef8c1c2be
-- title:
--   Gain from deviating in a Bayesian game
-- statement:
--   For a strategy profile $\sigma$, a player $i$ and a state $\omega$, with $\tau^i=t^i_\omega$, the **gain from deviating** is
--   $$\max_{a\in A_i} r^i(a,\sigma^{-i}\mid\tau^i)-r^i(\sigma\mid\tau^i),$$
--   the best improvement player $i$'s type at $\omega$ can obtain by switching to a pure action while the other players keep their strategies. It is the integrand of (4.1).
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), Definition 4.1, eq. (4.1), p.16; Definition 4.2, p.18

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_condPayoff

namespace HellmanLevy.Bayes

/-- The **gain from deviating** of player `i` at state `ω`, with `τⁱ = tⁱ(ω)`:
`maxₐ∈Aᵢ rⁱ(a, σ⁻ⁱ | τⁱ) − rⁱ(σ | τⁱ)`, the integrand of (4.1).
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), Definition 4.1, eq. (4.1), p.16; Definition 4.2, p.18; with (3.1)–(3.2), p.13.

**Formalization Note** The deviation `rⁱ(a, σ⁻ⁱ | τⁱ)` replaces player `i`'s strategy by the
constant pure action `a` (`Function.update σ i (fun _ => PMF.pure a)`), the other players'
strategies unchanged. The maximum is over the finite non-empty set `Aᵢ`. -/
noncomputable def gap {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    [DecidableEq I] {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (B : BayesianGame Ω I A) (i : I) (σ : ∀ i, Ω → PMF (A i)) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
      (fun a : A i => condPayoff B i (Function.update σ i fun _ => PMF.pure a) ω) -
    condPayoff B i σ ω

end HellmanLevy.Bayes


