-- Prove2me | Definitions.Def_HellmanLevy_Graphical_mixedPayoffG
-- name    : HellmanLevy_Graphical_mixedPayoffG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:53:38.028184+00:00
-- url     : https://prove2.me/theorems/67821e23-483a-4820-ac27-74145dd537dc
-- title:
--   Payoff of a vertex under a mixed profile
-- statement:
--   For a mixed profile $\sigma:X\to\Delta(A)$, the payoff of vertex $g$ is
--   $$u(g,\sigma)=\int_{A^X}u(g,a)\,d\Big(\bigotimes_{h\in X}\sigma(h)\Big)(a),$$
--   the expected payoff when every vertex draws its action independently from its mixed action: the multilinear extension of $u(g,\cdot)$.
--
--   **Formalization Note** For a graphical game $u(g,\cdot)$ depends on countably many coordinates and is continuous, hence measurable for the product σ-algebra, and bounded.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §3.2, p.14

import Mathlib

namespace HellmanLevy.Graphical

/-- The payoff `u(g, σ)` of the vertex `g` under the mixed profile `σ`: the expectation of
`u g a` when the actions `a h` are drawn independently from the `σ h`, i.e. the integral of
`u g` against the product measure `⊗_h σ(h)` on `A^X`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §3.2, p.14 ("Payoffs extend multi-linearly in the usual way").

**Formalization Note** The multilinear extension to infinitely many players is the expectation
under the product measure (`Measure.infinitePi`). For a graphical game, `u g` depends on the
countably many coordinates `{g} ∪ N(g)` and is continuous, hence measurable for the product
σ-algebra and bounded, so the integral is never the Bochner default. -/
noncomputable def mixedPayoffG {X A : Type*} [MeasurableSpace A] (u : X → (X → A) → ℝ)
    (σ : X → PMF A) (g : X) : ℝ :=
  ∫ a, u g a ∂(MeasureTheory.Measure.infinitePi fun h => (σ h).toMeasure)

end HellmanLevy.Graphical


