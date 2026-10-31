-- Prove2me | Definitions.Def_HellmanLevy_Graphical_IsStrategyG
-- name    : HellmanLevy_Graphical_IsStrategyG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:53:36.42079+00:00
-- url     : https://prove2.me/theorems/0c535bd4-3ba0-43b3-94bf-3c46538cd97a
-- title:
--   Strategy profile of a graphical game
-- statement:
--   A **strategy profile** of a graphical game on $X$ with action set $A$ is a Borel map $\sigma:X\to\Delta(A)$.
--
--   **Formalization Note** Mixed actions are probability mass functions on $A$; Borel means $g\mapsto\sigma(g)(b)$ is measurable for every $b\in A$.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §3.2, p.14

import Mathlib

namespace HellmanLevy.Graphical

/-- A **strategy profile** of a graphical game on `X` with action set `A`: a Borel map
`σ : X → ∆(A)`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §3.2, p.14 ("A strategy profile is then a Borel mapping σ : Ω → ∆(A)").

**Formalization Note** Mixed actions are `PMF A`; Borel measurability of `σ` is measurability of
each coordinate `g ↦ σ(g)(b)`. -/
def IsStrategyG {X A : Type*} [MeasurableSpace X] (σ : X → PMF A) : Prop :=
  ∀ b, Measurable fun g => σ g b

end HellmanLevy.Graphical


