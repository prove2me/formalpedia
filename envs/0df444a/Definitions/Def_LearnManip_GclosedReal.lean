-- Prove2me | Definitions.Def_LearnManip_GclosedReal
-- name    : LearnManip_GclosedReal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:15.364986+00:00
-- url     : https://prove2.me/theorems/fad778c4-98ab-4458-82ed-baafd9867464
-- title:
--   $G(\cdot,c)$ as a function of a real variable
-- statement:
--   The closed form $s\mapsto G(s,c)$ at fixed $c$, as a function on the real line, used only to state the derivatives of Lemma 3.
--
--   **Formalization Note.** Negative reals are sent to $0$. Only $s\ge0$ is used, with $s=0$ through a right derivative.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Lemma 3, p.33

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_Gclosed

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- `Gclosed` as a function of a real variance at fixed `c`, used only to state the derivatives of
Lemma 3, p.33, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04).

**Formalization Note.** Negative reals are sent to `0` by `Real.toNNReal`; only `s ≥ 0` is used,
with `s = 0` through a right derivative. -/
noncomputable def GclosedReal (P : Params) (c : ℝ≥0) (s : ℝ) : ℝ := Gclosed P s.toNNReal c

end LearnManip


