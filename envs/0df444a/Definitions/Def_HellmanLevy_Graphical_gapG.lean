-- Prove2me | Definitions.Def_HellmanLevy_Graphical_gapG
-- name    : HellmanLevy_Graphical_gapG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:22.052906+00:00
-- url     : https://prove2.me/theorems/8f80a14d-9ed2-45f8-8759-80d22d41963b
-- title:
--   Gain from deviating in a graphical game
-- statement:
--   For a mixed profile $\sigma$ and a vertex $g$, the **gain from deviating** is
--   $$\max_{a\in A}u(g,(a,\sigma_{-g}))-u(g,\sigma),$$
--   where $(a,\sigma_{-g})$ is the profile in which $g$ plays the pure action $a$ and every other vertex keeps $\sigma$.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), Definition 4.3, eq. (4.4), pp.18–19

import Mathlib
import Definitions.Def_HellmanLevy_Graphical_mixedPayoffG

namespace HellmanLevy.Graphical

/-- The **gain from deviating** of the vertex `g`: `max_{a∈A} u(g, (a, σ₋g)) − u(g, σ)`, where
`(a, σ₋g)` is the profile in which `g` plays the pure action `a` and every other vertex keeps
`σ`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), Definition 4.3, eq. (4.4), pp.18–19. -/
noncomputable def gapG {X A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
    (u : X → (X → A) → ℝ) (σ : X → PMF A) (g : X) : ℝ :=
  open scoped Classical in
  Finset.univ.sup' Finset.univ_nonempty
      (fun a : A => mixedPayoffG u (Function.update σ g (PMF.pure a)) g) -
    mixedPayoffG u σ g

end HellmanLevy.Graphical


