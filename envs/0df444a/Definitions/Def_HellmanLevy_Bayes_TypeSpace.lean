-- Prove2me | Definitions.Def_HellmanLevy_Bayes_TypeSpace
-- name    : HellmanLevy_Bayes_TypeSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:24.167981+00:00
-- url     : https://prove2.me/theorems/0d5d8cd9-d1ae-49fa-8900-6aa6d60f43b4
-- title:
--   Type space $\Omega_T=\bigsqcup_i T^i$ of the associated graphical game
-- statement:
--   For a Bayesian game, player $i$'s **type space** is $T^i=\Omega/t^i\cong\mathrm{Image}(t^i)\subseteq\Delta(\Omega)$, the set of player $i$'s types, and the vertex set of the associated graphical game is the disjoint union
--   $$\Omega_T=\bigsqcup_{i\in I}T^i .$$
--   Each type of each player becomes a player of the graphical game.
--
--   **Formalization Note** $T^i$ is the range of $t^i$ with the σ-algebra of $\Delta(\Omega)$, and $\Omega_T$ the disjoint union with its σ-algebra.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §4.2, p.20

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_BayesianGame

namespace HellmanLevy.Bayes

/-- The **vertex set of the associated graphical game**: the disjoint union over players `i` of
player `i`'s type space `Tⁱ = Image(tⁱ) ⊆ ∆(Ω)`, `Ω_T = ⊔ᵢ Tⁱ`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §4.2, p.20 ("For each i, set Tⁱ := Ω/tⁱ ∼ Image(tⁱ) as a quotient space"; "The set of
players of ΓB is the disjoint union ΩT := ⊔ᵢ Tⁱ").

**Formalization Note** `Tⁱ` is the range of `tⁱ` as a subtype of `Measure Ω` with the Giry
σ-algebra, and `Ω_T` the sigma type with its disjoint-union σ-algebra. -/
abbrev TypeSpace {Ω : Type*} [MeasurableSpace Ω] {I : Type*} {A : I → Type*}
    (B : BayesianGame Ω I A) : Type _ :=
  Σ i : I, Set.range (B.t i)

end HellmanLevy.Bayes


