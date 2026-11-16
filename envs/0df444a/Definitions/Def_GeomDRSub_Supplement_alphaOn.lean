-- Prove2me | Definitions.Def_GeomDRSub_Supplement_alphaOn
-- name    : GeomDRSub_Supplement_alphaOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:46:08.063431+00:00
-- url     : https://prove2.me/theorems/4ba28b26-7e1c-4c4c-b184-29e405b19ed0
-- title:
--   The online coefficient $\alpha_{\mathrm{on}}(\zeta)$
-- statement:
--   $$\alpha_{\mathrm{on}}(\zeta)=\sup\{a\in[0,1]: a\text{ is attained by a uniform online algorithm with polynomial query count and regret }O(\mathrm{poly}\cdot T^{\kappa}),\ \kappa<1\}.$$
--
--   **Formalization Note** The coefficients range over $[0,1]$, where the regret (9) is defined. The set contains $0$ (play $0\in K$ without queries) and is bounded by $1$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 7.2, p.52

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_OnlineAchievable

namespace GeomDRSub.Supplement

/-- **The online coefficient `αon(ζ)` (Section 7.2).** Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, p.52: "Let `αon(ζ)` be the
supremum of coefficients `a` for which there are a uniform online algorithm, a constant `κ < 1`, and
fixed polynomials `P_Q, P_R`" satisfying (213) (see `OnlineAchievable`).

**Formalization Note.** Coefficients range over `a ∈ [0,1]`, the range for which the regret (9) is
defined (p.9). The set contains `0` (play `0 ∈ K` every round without queries) and is bounded by
`1`, so `sSup` is the supremum. -/
noncomputable def alphaOn (ζ : ℝ) : ℝ :=
  sSup {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧ OnlineAchievable ζ a}

end GeomDRSub.Supplement


