-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_decHull
-- name    : FoundationsRL_E2DStructured_decHull
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:27.630873+00:00
-- url     : https://prove2.me/theorems/b8e7d14e-ac15-4ae6-9f23-79219b39ee3a
-- title:
--   The DEC of a class, $\mathrm{dec}_\gamma(\mathcal F)$
-- statement:
--   The Decision-Estimation Coefficient of a class is
--   $$\mathrm{dec}_\gamma(\mathcal F)=\sup_{\hat f\in\mathrm{co}(\mathcal F)}\mathrm{dec}_\gamma(\mathcal F,\hat f),$$
--   where $\mathrm{co}(\mathcal F)$ is the set of all finite convex combinations of elements of $\mathcal F$.
--
--   **Formalization Note** $\mathrm{co}(\mathcal F)$ is `convexHull ℝ F` in the real vector space of functions $\Pi\to\mathbb R$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.2, (4.16), p. 65

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_dec

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The Decision-Estimation Coefficient of a class, `dec_γ(F) = sup_{f̂∈co(F)} dec_γ(F, f̂)`
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.2, p. 65, (4.16)).

**Formalization Note.** `co(F)`, "the set of all convex combinations of elements in `F`", is
`convexHull ℝ F` in the vector space `D → ℝ`, whose elements are the finite convex combinations. -/
noncomputable def decHull {D : Type*} [MeasurableSpace D] (γ : ℝ) (F : Set (D → ℝ)) : EReal :=
  ⨆ fhat ∈ convexHull ℝ F, dec γ F fhat

end FoundationsRL.E2DStructured


