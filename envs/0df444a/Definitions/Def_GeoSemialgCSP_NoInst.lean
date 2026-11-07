-- Prove2me | Definitions.Def_GeoSemialgCSP_NoInst
-- name    : GeoSemialgCSP_NoInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:37.96171+00:00
-- url     : https://prove2.me/theorems/36a80f27-550e-434e-b520-8d92e749480d
-- title:
--   Soundness promise set
-- statement:
--   For a domain $X$, a predicate $P$ with accepting set $S$ and $s\in\mathbb R$, an instance $I$ belongs to the **soundness** set if it has at least one constraint, every constraint uses distinct variables, and
--   $$\mathrm{OPT}(I_P)\ \le\ s .$$
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 6.1, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_Inst
import Definitions.Def_GeoSemialgCSP_Inst_OPT
import Definitions.Def_GeoSemialgCSP_Inst_Distinct

namespace GeoSemialgCSP

/-- **Soundness promise set.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 6.1, printed p.19 (PDF p.20):
"instances with value at most `α*_P + δ`", with distinct variables in each constraint.

`NoInst X S s I` holds when `I` has at least one constraint, every constraint uses distinct
variables, and `OPT(I_P) ≤ s` over assignments into `X`. -/
def NoInst {k d : ℕ} (X : Set (E d)) (S : Set (Fin k → E d)) (s : ℝ) (I : Inst k) : Prop :=
  I.cons ≠ [] ∧ I.Distinct ∧ I.OPT X S ≤ s

end GeoSemialgCSP


