-- Prove2me | Definitions.Def_GeoSemialgCSP_Inst_Distinct
-- name    : GeoSemialgCSP_Inst_Distinct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:41.992903+00:00
-- url     : https://prove2.me/theorems/2e0ac8d5-8eb0-449c-89f4-922896867ac9
-- title:
--   Distinct variables in every constraint
-- statement:
--   An instance **uses distinct variables within each constraint** if no constraint $(i_1,\dots,i_k)$ repeats a variable: $i_a\neq i_b$ for $a\neq b$.
--
--   Theorem 6.1 states that its hardness holds even for instances with this property.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 6.1, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_GeoSemialgCSP_Inst

namespace GeoSemialgCSP

/-- **Distinct variables in each constraint.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 6.1, printed p.19
(PDF p.20): "The instances can be required to use distinct variables within each constraint."

**Formalization Note.** Each constraint, a map `Fin k → Fin n`, is injective. -/
def Inst.Distinct {k : ℕ} (I : Inst k) : Prop :=
  ∀ c ∈ I.cons, Function.Injective c

end GeoSemialgCSP


