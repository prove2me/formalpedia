-- Prove2me | Definitions.Def_HellmanLevy_Graphical_IsGraphicalGame
-- name    : HellmanLevy_Graphical_IsGraphicalGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:23.815186+00:00
-- url     : https://prove2.me/theorems/0c506a1e-f58c-47a8-a3e5-94b1498ad76c
-- title:
--   Graphical game of countable degree
-- statement:
--   Let $A$ be a finite action set. A **graphical game of countable degree** $(X,G,u)$ consists of a Borel graph of countable degree $G$ on $X$ and a payoff $u(g,a)$ for each vertex (player) $g$ and pure profile $a:X\to A$, such that
--
--   1. $u(g,\cdot)$ depends only on the actions of $g$ and of its neighbours $N(g)$;
--   2. $u(g,\cdot)$ is continuous in the Tychonoff topology (with $A$ discrete);
--   3. $u$ is bounded;
--   4. whenever $\alpha:X\times X\to A$ is Borel, $g\mapsto u(g,\alpha(g,\cdot))$ is Borel.
--
--   Graphical games are the intermediate objects of the paper: the types of a Bayesian game become the players of a graphical game.
--
--   **Formalization Note** Given item 1, continuity on $A^X$ is continuity on $A\times A^{N(g)}$. $A$ carries the discrete topology and σ-algebra.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §3.2, pp.13–14; Definition 3.3, p.14

import Mathlib
import Definitions.Def_HellmanLevy_Graphical_IsGraph
import Definitions.Def_HellmanLevy_Graphical_DependsOn

namespace HellmanLevy.Graphical

/-- `(X, G, u)` is a **graphical game of countable degree** with the finite action set `A`:
`G` is a Borel graph of countable degree, and the payoff `u : X → (X → A) → ℝ` (`u g a` is the
payoff of the player `g` under the pure profile `a`) satisfies
1. `u g a` depends only on `a g` and on `a h` for the neighbours `h` of `g`;
2. each `u g` is continuous for the product (Tychonoff) topology on `X → A`, `A` discrete;
3. `u` is bounded;
4. whenever `α : X × X → A` is Borel, `g ↦ u(g, α(g, ·))` is Borel.

Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §3.2, pp.13–14 (graphical games of countable degree, and the three bulleted assumptions
"ug is continuous in the Tychonoff topology on A × A^N(g), u is bounded, whenever α : Ω × Ω → A
is Borel, g → u(g, α(g, ·)) is Borel"); Definition 3.3, p.14.

**Formalization Note** Given (1), continuity of `u g` on the full product `A^X` is the same as
continuity of `u_g` on `A × A^N(g)`. `A` carries the discrete topology and the discrete
σ-algebra (instance arguments). The paper takes `X` Polish; the theorems of the mission take
`X` standard Borel. -/
def IsGraphicalGame {X : Type*} [MeasurableSpace X] {A : Type*} [MeasurableSpace A]
    [TopologicalSpace A] (G : X → X → Prop) (u : X → (X → A) → ℝ) : Prop :=
  IsGraph G ∧ DependsOn u G ∧ (∀ g, Continuous (u g)) ∧ (∃ M : ℝ, ∀ g a, |u g a| ≤ M) ∧
    ∀ α : X → X → A, Measurable (Function.uncurry α) → Measurable fun g => u g (α g)

end HellmanLevy.Graphical


