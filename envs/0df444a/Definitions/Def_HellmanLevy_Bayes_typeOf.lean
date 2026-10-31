-- Prove2me | Definitions.Def_HellmanLevy_Bayes_typeOf
-- name    : HellmanLevy_Bayes_typeOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:55.425847+00:00
-- url     : https://prove2.me/theorems/12540f9d-bd9b-439c-849d-b432f0429ead
-- title:
--   Quotient map $\omega\mapsto t^i(\omega)\in T^i\subseteq\Omega_T$
-- statement:
--   For a player $i$, the map $\iota_i:\Omega\to\Omega_T$, $\omega\mapsto t^i(\omega)\in T^i$, sends a state to player $i$'s type at that state, viewed as a vertex of the associated graphical game.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §4.2, p.20; proof of Proposition 4.5, p.21

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_TypeSpace

namespace HellmanLevy.Bayes

/-- The quotient map `ω ↦ tⁱ(ω) ∈ Tⁱ ⊆ Ω_T`: the vertex of the associated graphical game that is
player `i`'s type at state `ω`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §4.2, p.20; proof of Proposition 4.5, p.21 ("the quotient map ι(ω, i) = tⁱ(ω) ∈ Tⁱ ⊆ ΩT"). -/
def typeOf {Ω : Type*} [MeasurableSpace Ω] {I : Type*} {A : I → Type*}
    (B : BayesianGame Ω I A) (i : I) (ω : Ω) : TypeSpace B :=
  ⟨i, ⟨B.t i ω, ω, rfl⟩⟩

end HellmanLevy.Bayes


