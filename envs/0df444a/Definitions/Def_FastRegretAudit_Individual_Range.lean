-- Prove2me | Definitions.Def_FastRegretAudit_Individual_Range
-- name    : FastRegretAudit_Individual_Range
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:33:34.610983+00:00
-- url     : https://prove2.me/theorems/48f3770a-e4b0-477c-8fe5-793e4e6bd258
-- title:
--   Exact extended regularizer ranges and Corollary 12 stepsize
-- statement:
--   Let $\mathcal R:\mathbb R^d\to\mathbb R$ be a regularizer and let $\Delta$ be the probability simplex. Its exact range is defined in the extended reals by
--
--   $$\operatorname{range}(\mathcal R)=\sup_{f\in\Delta}\mathcal R(f)-\inf_{f\in\Delta}\mathcal R(f).$$
--
--   For $n\ge2$ player regularizers $\mathcal R_i$, the common range and prescribed stepsize are
--
--   $$R=\max_{i<n}\operatorname{range}(\mathcal R_i),\qquad\eta(n,T)=(n-1)^{-1/2}T^{-1/4}\quad(T\ge1).$$
--
--   Nonempty simplexes ensure each range belongs to $[0,+\infty]$. These are computed quantities, not free upper bounds. No attainment or finiteness of either extremum is assumed. An unbounded range remains $+\infty$ rather than being converted to a default real value. These definitions retain the source's exact constants in the regret statements.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, main p. 5, §3.1.2 and Corollary 12, PDF p. 5; Appendix C, supplementary p. 3, PDF p. 12, Theorem 19

import Mathlib

namespace FastRegretAudit.Individual

/-- The exact extended range of a real-valued regularizer on its simplex.
On every nonempty simplex this lies in [0,+∞]; no extrema are assumed attained. -/
noncomputable def regularizerRange {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) : EReal :=
  sSup ((fun f => (𝓡 f : EReal)) '' stdSimplex ℝ (Fin d)) -
    sInf ((fun f => (𝓡 f : EReal)) '' stdSimplex ℝ (Fin d))

/-- Footnote 2, main p. 4, and §3.1.2, main p. 5: the common range is
constructed from the player regularizers, rather than supplied as a free bound. -/
noncomputable def commonRange {n d : ℕ}
    (𝓡 : Fin n → (Fin d → ℝ) → ℝ) : EReal :=
  ⨆ i, regularizerRange (𝓡 i)

/-- The fixed-horizon stepsize of Corollary 12. Its uses require n ≥ 2 and T ≥ 1. -/
noncomputable def corollaryStepsize (n T : ℕ) : ℝ :=
  Real.rpow ((n : ℝ) - 1) (-(1 / 2 : ℝ)) * Real.rpow (T : ℝ) (-(1 / 4 : ℝ))

end FastRegretAudit.Individual


