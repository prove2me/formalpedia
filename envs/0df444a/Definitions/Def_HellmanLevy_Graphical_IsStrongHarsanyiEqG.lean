-- Prove2me | Definitions.Def_HellmanLevy_Graphical_IsStrongHarsanyiEqG
-- name    : HellmanLevy_Graphical_IsStrongHarsanyiEqG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:35.578567+00:00
-- url     : https://prove2.me/theorems/b830a086-9055-424d-9239-bd1f4ec72cad
-- title:
--   Strong Harsányi $\varepsilon$-equilibrium of a graphical game
-- statement:
--   Let $\mu$ be a measure on the vertex set $X$. A strategy profile $\sigma$ is a **strong Harsányi $\varepsilon$-equilibrium** if there is a set $\Omega'\subseteq X$ with $\mu(\Omega')\le\varepsilon$ such that every vertex $g\notin\Omega'$ optimizes exactly:
--   $$\max_{a\in A}u(g,(a,\sigma_{-g}))=u(g,\sigma).$$
--
--   **Formalization Note** The inequality $\mu(\Omega')\le\varepsilon$ is non-strict as printed (Definition 4.2 for Bayesian games has $<$). $\Omega'$ need not be measurable (outer measure).
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), Definition 4.3, p.19

import Mathlib
import Definitions.Def_HellmanLevy_Graphical_IsStrategyG
import Definitions.Def_HellmanLevy_Graphical_gapG

namespace HellmanLevy.Graphical

/-- `σ` is a **strong Harsányi ε-equilibrium** of the graphical game `(X, G, u)` with respect to
`µ`: a strategy profile and a set `Ω' ⊆ X` with `µ(Ω') ≤ ε` such that every vertex `g ∉ Ω'`
optimizes exactly, `maxₐ u(g, (a, σ₋g)) = u(g, σ)`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), Definition 4.3, p.19 (non-strict inequality `µ(Ω′) ≤ ε` as printed; Definition 4.2 for
Bayesian games has `<`).

**Formalization Note** `Ω'` need not be measurable; `µ(Ω')` is then the outer measure. -/
def IsStrongHarsanyiEqG {X A : Type*} [MeasurableSpace X] [Fintype A] [Nonempty A]
    [MeasurableSpace A] (u : X → (X → A) → ℝ) (μ : MeasureTheory.Measure X) (ε : ℝ)
    (σ : X → PMF A) : Prop :=
  IsStrategyG σ ∧ ∃ S : Set X, μ S ≤ ENNReal.ofReal ε ∧ ∀ g ∉ S, gapG u σ g = 0

end HellmanLevy.Graphical


