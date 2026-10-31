-- Prove2me | Definitions.Def_HellmanLevy_Graphical_IsNashG
-- name    : HellmanLevy_Graphical_IsNashG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:24.214058+00:00
-- url     : https://prove2.me/theorems/716a980c-bcc2-41ff-a7c5-20550f1c813a
-- title:
--   Measurable Nash equilibrium of a graphical game
-- statement:
--   A **measurable Nash equilibrium** of a graphical game is a Borel strategy profile $\sigma:X\to\Delta(A)$ such that for every vertex $g$ and every pure action $b\in A$
--   $$u(g,\sigma)\ge u(g,(b,(\sigma(h))_{h\ne g})).$$
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §3.2, p.15

import Mathlib
import Definitions.Def_HellmanLevy_Graphical_IsStrategyG
import Definitions.Def_HellmanLevy_Graphical_mixedPayoffG

namespace HellmanLevy.Graphical

/-- `σ` is a **measurable Nash equilibrium** of the graphical game `(X, G, u)`: a (Borel)
strategy profile such that no vertex `g` gains by replacing its mixed action with a pure action
`b`, the others' mixed actions fixed: `u(g, σ) ≥ u(g, (b, (σ(h))_{h≠g}))`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §3.2, p.15 ("A (measurable) Nash equilibrium of a graphical game is naturally a
(measurable) mapping σ : G → ∆(A) such that u(g, σ) ≥ u(g, (b, (σ(h))h≠g)) for each g ∈ G and each
b ∈ A"). -/
def IsNashG {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (u : X → (X → A) → ℝ)
    (σ : X → PMF A) : Prop :=
  open scoped Classical in
  IsStrategyG σ ∧ ∀ g (b : A), mixedPayoffG u (Function.update σ g (PMF.pure b)) g ≤ mixedPayoffG u σ g

end HellmanLevy.Graphical


