-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_IsLexOpt
-- name    : MaxMinFracSched_Supplement_IsLexOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:12:46.746986+00:00
-- url     : https://prove2.me/theorems/779d73b2-dbf9-49d9-afa6-d06cae49951a
-- title:
--   Lexicographically optimal schedule
-- statement:
--   A schedule $r$ of the instance $J$ is **lexicographically optimal** when it is feasible and no feasible schedule $r'$ of $J$ has a sorted fraction vector that is lexicographically larger:
--   $$
--   \neg\bigl(f^{\uparrow}_J(r)<_{\mathrm{lex}}f^{\uparrow}_J(r')\bigr)\qquad\text{for every feasible } r'.
--   $$
--   The **lexicographic benchmark** of job $i$ is $\hat f_{J,i}=f_i(r)$ for such an $r$. It is the target of the lexicographic objective: maximize the smallest fraction, then the second smallest, and so on.
--
--   **Formalization Note** Results are stated for every lexicographically optimal schedule, with its existence asserted where it is needed; no choice function is used. All sorted vectors of $J$ have length $|J|$, so the strict lexicographic order on lists is the paper's order.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 7, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_IsSchedule
import Definitions.Def_MaxMinFracSched_Supplement_sortedFrac

namespace MaxMinFracSched

namespace Supplement

/-- **A lexicographically optimal schedule.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 7, p.33 (PDF p.35): "The offline lexicographic benchmark f̂↑J (i.e. the
lexicographic optimum) is the induced by a feasible schedule whose sorted fraction vector is
lexicographically maximum. … We will write f̂J,i for the offline benchmark fractional completion of
job i".

`IsLexOpt J r` holds when `r` is a feasible schedule of `J` and no feasible schedule `r'` of `J`
has a sorted fraction vector that is lexicographically larger than that of `r`.

**Formalization Note.** The benchmark `f̂_{J,i}` is `frac r i` for a lexicographically optimal
`r`; theorems are stated for **every** such `r` (together with existence where needed), never with
a choice function over a possibly empty set. All sorted vectors have the same length `|J|`, so the
strict lexicographic order `List.Lex (· < ·)` is the lexicographic order of the paper. -/
def IsLexOpt (J : Finset Job) (r : Job → ℝ → ℝ) : Prop :=
  IsSchedule J r ∧ ∀ r', IsSchedule J r' → ¬ List.Lex (· < ·) (sortedFrac J r) (sortedFrac J r')

end Supplement

end MaxMinFracSched


