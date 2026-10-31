-- Prove2me | Definitions.Def_LearnManip_IsBDPSolution
-- name    : LearnManip_IsBDPSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:01.042754+00:00
-- url     : https://prove2.me/theorems/4b1f38d7-1966-4024-b21b-4aa0350365e6
-- title:
--   $v$ solves the BDP equation (10)
-- statement:
--   A function $v(\mu,s,c)$ solves the BDP equation when, at every state $(\mu,s,c)$ with $\mu\in\mathbb R$, $s,c\ge0$,
--   $$v(\mu,s,c)=\sup_{q\ge0}\Bigl\{-cq+\sup_{\Lambda\in\mathcal D_{\mu^q}}\bigl\{E_{\mu,s}\bigl[\Lambda\bigl(\mu^q+\alpha v(\mu^q,\tfrac{s}{1+sq},c\eta)\bigr)\bigr]-R(\Lambda)\bigr\}\Bigr\}.$$
--
--   **Formalization Note.** The double supremum is one least upper bound over pairs $(q,G)$. Distortions of infinite relative entropy have objective $-\infty$ and are excluded, which changes no supremum.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (10), p.12

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_baseLaw
import Definitions.Def_LearnManip_IsDistortion
import Definitions.Def_LearnManip_bdpObjective

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- `v` solves the BDP equation (10), p.12, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04), at every
state `(μ, s, c)`.

**Formalization Note.** The double supremum over `q` and `Λ` is one least upper bound over the pairs
`(q, G)` (`IsLUB`, so an unbounded set is not a junk value). Distortions of infinite relative entropy
have objective `−∞` and are excluded, which changes no supremum. -/
def IsBDPSolution (P : Params) (v : ℝ → ℝ≥0 → ℝ≥0 → ℝ) : Prop :=
  ∀ (μ : ℝ) (s c : ℝ≥0),
    IsLUB {x : ℝ | ∃ (q : ℝ≥0) (G : Measure ℝ), IsDistortion μ s q G ∧
        InformationTheory.klDiv G (baseLaw μ s q) ≠ ∞ ∧ x = bdpObjective P v μ s c q G}
      (v μ s c)

end LearnManip


