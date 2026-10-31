-- Prove2me | Definitions.Def_HellmanLevy_Bayes_assocGraph
-- name    : HellmanLevy_Bayes_assocGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:10.048058+00:00
-- url     : https://prove2.me/theorems/9d5d0165-98dd-4177-8199-0cc2f47ea8b6
-- title:
--   Graph $G_T$ of the associated graphical game
-- statement:
--   Two distinct types $\tau\ne\tau'$ in $\Omega_T$ are adjacent in $G_T$ if and only if there is a state $\omega$ at which both are realized: $\tau=t^i(\omega)$ and $\tau'=t^j(\omega)$ for some players $i,j$.
--
--   **Formalization Note** The condition $\tau\ne\tau'$ makes $G_T$ irreflexive, as a graph must be.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §4.2, p.20

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_typeOf

namespace HellmanLevy.Bayes

/-- The **graph `G_T` of the associated graphical game**: distinct types `τ ≠ τ'` are adjacent
if and only if there is a state `ω` at which both are realized, i.e. `τ = tⁱ(ω)` and
`τ' = tʲ(ω)` for some players `i, j`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §4.2, p.20 ("there is an edge between vertices τⁱ and τʲ if and only if there is a state
ω ∈ Ω in the original Bayesian game B such that tⁱ(ω) = τⁱ and tʲ(ω) = τʲ").

**Formalization Note** The condition `τ ≠ τ'` makes the relation irreflexive, as a graph is
required to be (§2.4, p.9). -/
def assocGraph {Ω : Type*} [MeasurableSpace Ω] {I : Type*} {A : I → Type*}
    (B : BayesianGame Ω I A) (τ τ' : TypeSpace B) : Prop :=
  τ ≠ τ' ∧ ∃ ω, ∃ i j, typeOf B i ω = τ ∧ typeOf B j ω = τ'

end HellmanLevy.Bayes


