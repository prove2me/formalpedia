-- Prove2me | Definitions.Def_DROReview_PhiDiv_ball
-- name    : DROReview_PhiDiv_ball
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T21:16:59.08545+00:00
-- url     : https://prove2.me/theorems/e98707d2-58eb-4817-b96a-24991b315f06
-- title:
--   (5.9) — φ-divergence ambiguity ball
-- statement:
--   Fix a nominal probability measure $P_0$ on $(\Xi,\mathcal F)$, a divergence generator $\phi$, and a radius $\varepsilon\in[0,+\infty]$. The **$\phi$-divergence ambiguity ball** is
--
--   $$
--   \mathcal P^\phi(P_0;\varepsilon)
--     =\{P\in\mathfrak M(\Xi,\mathcal F):\mathfrak D^\phi(P,P_0)\le\varepsilon\}.
--   $$
--
--   It is the collection of probability measures within the specified divergence radius of $P_0$. Lemma 5.4 compares these balls for the four generators of Table 1.
--
--   **Formalization Note** Both the center and the members of the set are probability measures. The radius is extended nonnegative real, avoiding a junk value for infinite divergences; finite nonnegative radii are the paper's intended sizes.
-- source:
--   Rahimian, Mehrotra, Distributionally Robust Optimization: A Review, arXiv:1908.05659v1 (2019), p. 31, equation (5.9)

import Definitions.Def_DROReview_PhiDiv_phiDiv

namespace DROReview.PhiDiv

open MeasureTheory

/-- The φ-divergence ambiguity ball (5.9), p. 31, within the probability
measures on the same measurable space. -/
noncomputable def phiBall {Ξ : Type*} [MeasurableSpace Ξ]
    (φ : NNReal → ENNReal) (P₀ : ProbabilityMeasure Ξ) (ε : ENNReal) :
    Set (ProbabilityMeasure Ξ) :=
  {P | phiDiv φ P P₀ ≤ ε}

end DROReview.PhiDiv


