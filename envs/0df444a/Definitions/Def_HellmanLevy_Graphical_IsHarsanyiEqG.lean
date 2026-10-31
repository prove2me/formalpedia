-- Prove2me | Definitions.Def_HellmanLevy_Graphical_IsHarsanyiEqG
-- name    : HellmanLevy_Graphical_IsHarsanyiEqG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:27.683142+00:00
-- url     : https://prove2.me/theorems/bfc1985c-42ee-4386-ace1-1a43ff791393
-- title:
--   Harsányi $\varepsilon$-equilibrium of a graphical game
-- statement:
--   Let $\mu$ be a measure on the vertex set $X$ of a graphical game. A strategy profile $\sigma$ is a **Harsányi $\varepsilon$-equilibrium** if
--   $$\int_X\Big[\max_{a\in A}u(g,(a,\sigma_{-g}))-u(g,\sigma)\Big]\,d\mu(g)\le\varepsilon .$$
--
--   **Formalization Note** The gain is required to be $\mu$-integrable, so a non-integrable gain cannot pass with Bochner integral $0$.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), Definition 4.3, eq. (4.4), p.18

import Mathlib
import Definitions.Def_HellmanLevy_Graphical_IsStrategyG
import Definitions.Def_HellmanLevy_Graphical_gapG

namespace HellmanLevy.Graphical

/-- `σ` is a **Harsányi ε-equilibrium** of the graphical game `(X, G, u)` with respect to the
measure `µ` on `X`: a strategy profile whose gain from deviating integrates to at most `ε`,
`∫_X [maxₐ u(g, (a, σ₋g)) − u(g, σ)] dµ(g) ≤ ε`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), Definition 4.3, eq. (4.4), p.18.

**Formalization Note** Integrability of the gain is part of the definition, so that a
non-integrable gap (Bochner integral `0` in Lean) cannot pass; for a graphical game with
bounded payoffs and a finite measure it excludes nothing. -/
def IsHarsanyiEqG {X A : Type*} [MeasurableSpace X] [Fintype A] [Nonempty A]
    [MeasurableSpace A] (u : X → (X → A) → ℝ) (μ : MeasureTheory.Measure X) (ε : ℝ)
    (σ : X → PMF A) : Prop :=
  IsStrategyG σ ∧ MeasureTheory.Integrable (gapG u σ) μ ∧ ∫ g, gapG u σ g ∂μ ≤ ε

end HellmanLevy.Graphical


