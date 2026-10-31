-- Prove2me | Definitions.Def_LearnManip_kappa
-- name    : LearnManip_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:30.546028+00:00
-- url     : https://prove2.me/theorems/053413d9-7848-41a3-8a87-98e86f105d87
-- title:
--   Dissemination time $\kappa(s,c)$
-- statement:
--   The dissemination time
--   $$\kappa(s,c)=\min\{\,j\in\mathbb N:\ s>s_{TH}(c\bar\eta^{\,j-1})\,\}.$$
--
--   **Formalization Note.** Footnote 9, p.19, has $\kappa=\infty$ when the set is empty. The value in Lean on the empty set is a default that is never used, because `Gclosed` tests nonemptiness first.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Theorem 1, p.15; footnote 9, p.19

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_dissemIndices

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The dissemination time `κ(s, c) = min{j ∈ ℕ : s > s_TH(c η̄^{j−1})}` of Theorem 1, p.15, of Keppo,
Kim, Zhang (SSRN 3465030, 2021-09-04).

**Formalization Note.** On an empty set `sInf` gives `0`; footnote 9, p.19, says `κ = ∞` there.
`Gclosed` tests nonemptiness first, so this value is never used. -/
noncomputable def kappa (P : Params) (s c : ℝ≥0) : ℕ := sInf (dissemIndices P s c)

end LearnManip


