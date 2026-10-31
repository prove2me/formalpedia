-- Prove2me | Definitions.Def_LearnManip_hatG
-- name    : LearnManip_hatG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:49.254951+00:00
-- url     : https://prove2.me/theorems/2de9612b-dbd2-41b9-be14-546cca4389cc
-- title:
--   Finite-stage iteration $\hat G_k$
-- statement:
--   The iteration $\hat G_0=0$ and
--   $$\hat G_{k+1}(s,c)=\sup_{q\ge0}\Bigl\{-cq+\alpha\hat G_k\bigl(\tfrac{s}{1+sq},c\eta\bigr)+\frac{A_{k+1}^2\,\sigma^2_{\mu^q}}{2\gamma}\Bigr\}.$$
--
--   **Formalization Note.** The supremum is a real supremum of a set that is nonempty and bounded above; the milestone (EC.16) states that it is a least upper bound.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (EC.16), p.ec9 (PDF 48), corrected

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_hatObjective

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The finite-stage iteration `Ĝ_k` of (EC.16), p.ec9 (PDF 48), of Keppo, Kim, Zhang (SSRN 3465030,
2021-09-04), with `Ĝ_0 = 0`.

**Formalization Note.** The paper's `max` is a real `sSup`. The set is nonempty and bounded above;
`eq_EC_16` states that the value is its least upper bound, so no junk value is used. -/
noncomputable def hatG (P : Params) : ℕ → ℝ≥0 → ℝ≥0 → ℝ
  | 0, _, _ => 0
  | k + 1, s, c => sSup (Set.range (hatObjective P k (hatG P k) s c))

end LearnManip


