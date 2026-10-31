-- Prove2me | Definitions.Def_HellmanLevy_Bayes_IsStrategy
-- name    : HellmanLevy_Bayes_IsStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:21.057826+00:00
-- url     : https://prove2.me/theorems/f1fcc237-44ea-441e-9188-5ae2e1e82509
-- title:
--   Strategy profile of a Bayesian game
-- statement:
--   A **strategy profile** of a Bayesian game is a family $\sigma=(\sigma^i)_{i\in I}$ of maps $\sigma^i:\Omega\to\Delta(A_i)$ such that each $\sigma^i$ is Borel and constant on the classes of player $i$'s knowledge relation: $t^i_x=t^i_y$ implies $\sigma^i(x)=\sigma^i(y)$. Equivalently, $\sigma^i$ is $\sigma(E_i)$-measurable: a player can condition only on what they know.
--
--   **Formalization Note** Mixed actions are probability mass functions on the finite set $A_i$; Borel measurability means that $\omega\mapsto\sigma^i(\omega)(a)$ is measurable for every action $a$.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §3.1, p.12; Definition 4.1, p.16

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_BayesianGame

namespace HellmanLevy.Bayes

/-- `σ` is a **strategy profile** of the Bayesian game `B`: each `σ i : Ω → ∆(Aᵢ)` is Borel
measurable and constant on player `i`'s knowledge classes (`tⁱ_x = tⁱ_y → σⁱ(x) = σⁱ(y)`),
i.e. `σ(Eᵢ)`-measurable.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §3.1, p.12 ("A strategy of a player i ∈ I is a mapping σi : Ω → ∆(Ai) which is constant
on each player's knowledge component, i.e., which is σ(Eᵢ)-measurable"); Definition 4.1, p.16
("σi : Ω → ∆(Ai) measurable with respect to Player i's knowledge").

**Formalization Note** Mixed actions are probability mass functions `PMF (A i)`; Borel
measurability of `σⁱ` is measurability of each coordinate `ω ↦ σⁱ(ω)(a)`. -/
def IsStrategy {Ω : Type*} [MeasurableSpace Ω] {I : Type*} {A : I → Type*}
    (B : BayesianGame Ω I A) (σ : ∀ i, Ω → PMF (A i)) : Prop :=
  ∀ i, (∀ a, Measurable fun ω => σ i ω a) ∧ ∀ x y, B.t i x = B.t i y → σ i x = σ i y

end HellmanLevy.Bayes


