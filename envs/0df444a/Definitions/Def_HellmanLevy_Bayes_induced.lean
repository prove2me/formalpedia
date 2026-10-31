-- Prove2me | Definitions.Def_HellmanLevy_Bayes_induced
-- name    : HellmanLevy_Bayes_induced
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:23.646372+00:00
-- url     : https://prove2.me/theorems/0070329b-b8dc-4afb-ae02-31d5d24c7158
-- title:
--   Bayesian profile induced by a graphical profile
-- statement:
--   A strategy profile $\sigma_T:\Omega_T\to\Delta(A)$ of the associated graphical game induces the Bayesian profile in which player $i$ at state $\omega$ plays the mixed action of their type:
--   $$\sigma^i(\omega)=\sigma_T(t^i(\omega)).$$
--   It is automatically constant on player $i$'s knowledge classes.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §4.2, p.21

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_typeOf

namespace HellmanLevy.Bayes

/-- The Bayesian strategy profile **induced** by a strategy profile `σ_T` of the associated
graphical game: player `i` at state `ω` plays the mixed action of the vertex `tⁱ(ω)`,
`σⁱ(ω) = σ_T(tⁱ(ω))`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §4.2, p.21 ("Strategies in the graphical game induced by a Bayesian game naturally induce
strategies in the original Bayesian game"). -/
def induced {Ω : Type*} [MeasurableSpace Ω] {I : Type*} {A : Type*}
    (B : BayesianGame Ω I fun _ => A) (σT : TypeSpace B → PMF A) : ∀ _ : I, Ω → PMF A :=
  fun i ω => σT (typeOf B i ω)

end HellmanLevy.Bayes


