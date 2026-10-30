-- Prove2me | Definitions.Def_ShapleyScarf_CoreExistence_payoffCore
-- name    : ShapleyScarf_CoreExistence_payoffCore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:37:48.491006+00:00
-- url     : https://prove2.me/theorems/48f777df-2802-485d-bfc7-27eb8e42c95f
-- title:
--   Section 3 — payoff core in the ambient payoff space
-- statement:
--   Let $N$ be a finite player set and let $V$ assign to each coalition $S\subseteq N$ a set $V(S)\subseteq\mathbb R^N$ of payoff vectors. Define its payoff core by
--
--   $$C(V)=V(N)\setminus\bigcup_{\varnothing\ne S\subseteq N}\operatorname{int}_{\mathbb R^N}V(S).$$
--
--   Thus a core point is feasible for the grand coalition and belongs to no coalition's ambient interior. The union includes the grand coalition itself and excludes the empty coalition. No closedness, convexity or balance assumption is built into this definition; game hypotheses appear in the theorems that use it.
--
--   This is the general core shared by the balanced-game theorem and its housing-market application.
--
--   **Formalization Note.** The finite product $N\to\mathbb R$ carries its usual product topology, which is the finite-dimensional Euclidean topology. The source's display begins with a free $V(S)$; the next sentence explicitly specifies $V(N)$, which is the reading used here. Values assigned to $V(\varnothing)$ are ignored.
-- source:
--   Shapley and Scarf, On cores and indivisibility, Journal of Mathematical Economics 1 (1974), published, DOI 10.1016/0304-4068(74)90033-0, https://doi.org/10.1016/0304-4068(74)90033-0; Section 3, core display and the immediately following explicit V(N) verbal definition, printed p. 108 / PDF p. 5.

import Mathlib

namespace ShapleyScarf.CoreExistence

/-- Section 3, printed p. 108 / PDF p. 5: the payoff core in the ambient product topology.
The prose immediately after the displayed formula fixes its free `S` to the grand coalition
`N`. All nonempty coalitions, including `N`, occur in the union. -/
def payoffCore {N : Type*} [Fintype N]
    (V : Finset N → Set (N → ℝ)) : Set (N → ℝ) :=
  V Finset.univ \ ⋃ (S : Finset N) (_hS : S.Nonempty), interior (V S)

end ShapleyScarf.CoreExistence


