-- Prove2me | Definitions.Def_FoundationsRL_DECExamples_dec
-- name    : FoundationsRL_DECExamples_dec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:22:34.059985+00:00
-- url     : https://prove2.me/theorems/8419611e-893b-4556-8650-4d0d844fed91
-- title:
--   Decision-Estimation Coefficient $\mathrm{dec}_\gamma(\mathcal F)=\sup_{\widehat f\in\mathrm{co}(\mathcal F)}\mathrm{dec}_\gamma(\mathcal F,\widehat f)$
-- statement:
--   The Decision-Estimation Coefficient of a class $\mathcal F$ at scale $\gamma$ is the worst case over reference models in the convex hull,
--
--   $$
--   \mathrm{dec}_\gamma(\mathcal F)=\sup_{\widehat f\in\mathrm{co}(\mathcal F)}\mathrm{dec}_\gamma(\mathcal F,\widehat f),
--   $$
--
--   where $\mathrm{co}(\mathcal F)$ is the set of all convex combinations of elements of $\mathcal F$. Convex combinations enter because online estimators such as exponential weights output improper predictions. The regret of the E2D algorithm is at most $\mathrm{dec}_\gamma(\mathcal F)\cdot T+\gamma\cdot\mathrm{Est}_{\mathrm{Sq}}(\mathcal F,T,\delta)$ (Proposition 13).
--
--   **Formalization Note** $\mathrm{co}(\mathcal F)$ is `convexHull ℝ F` in the function space $\Pi\to\mathbb R$; the supremum is taken in `EReal`.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.2, (4.16), p. 65

import Mathlib
import Definitions.Def_FoundationsRL_DECExamples_decAt

namespace FoundationsRL.DECExamples

/-- The Decision-Estimation Coefficient of a class, `dec_γ(F) = sup_{f̂ ∈ co(F)} dec_γ(F, f̂)`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, (4.16), p. 65.

**Formalization Note.** `co(F)`, the set of convex combinations of elements of `F`, is `convexHull ℝ F`
in the function space `D → ℝ`. -/
noncomputable def dec {D : Type*} (F : Set (D → ℝ)) (γ : ℝ) : EReal :=
  ⨆ fhat ∈ convexHull ℝ F, decAt F fhat γ

end FoundationsRL.DECExamples


