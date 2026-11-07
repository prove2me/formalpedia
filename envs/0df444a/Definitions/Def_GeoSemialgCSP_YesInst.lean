-- Prove2me | Definitions.Def_GeoSemialgCSP_YesInst
-- name    : GeoSemialgCSP_YesInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:46.806855+00:00
-- url     : https://prove2.me/theorems/08c43c4f-890c-4cef-969b-6d14a3eec577
-- title:
--   Completeness promise set
-- statement:
--   For a domain $X$, a predicate $P$ with accepting set $S$ and $\varepsilon\in\mathbb R$, an instance $I$ belongs to the **completeness** set if it has at least one constraint, every constraint uses distinct variables, and
--   $$\mathrm{OPT}(I_P)\ \ge\ 1-\varepsilon .$$
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 6.1, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_Inst
import Definitions.Def_GeoSemialgCSP_Inst_OPT
import Definitions.Def_GeoSemialgCSP_Inst_Distinct

namespace GeoSemialgCSP

/-- **Completeness promise set.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 6.1, printed p.19 (PDF p.20):
"CSP instances with value at least `1 − ε_comp`", with distinct variables in each constraint.

`YesInst X S ε I` holds when `I` has at least one constraint, every constraint uses distinct
variables, and `OPT(I_P) ≥ 1 − ε` over assignments into `X`. -/
def YesInst {k d : ℕ} (X : Set (E d)) (S : Set (Fin k → E d)) (ε : ℝ) (I : Inst k) : Prop :=
  I.cons ≠ [] ∧ I.Distinct ∧ 1 - ε ≤ I.OPT X S

end GeoSemialgCSP


