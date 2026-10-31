-- Prove2me | Definitions.Def_SweepingDesing_calT
-- name    : SweepingDesing_calT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:51.892115+00:00
-- url     : https://prove2.me/theorems/9b663e6d-ea4d-470d-bef8-8460e53c57b3
-- title:
--   §3.2 — the set $\mathcal T$ of admissible initial times
-- statement:
--   For a set-valued map $S:\mathbb R\rightrightarrows\mathbb R^n$,
--
--   $$
--   \mathcal T=\{t\in\operatorname{dom}(S): \text{(A2) and (A3) hold at }t\}.
--   $$
--
--   Theorem A characterizes desingularization of the oriented coderivative at any $a\in\mathcal T$, typically a critical value.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §3.2, p.9

import Mathlib
import Definitions.Def_SweepingDesing_UpperRegularAt
import Definitions.Def_SweepingDesing_ContinuityAt
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §3.2, p.9: `𝒯 := {t ∈ dom(S) : (A2)–(A3) are fulfilled at t}`. -/
def calT {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) : Set ℝ :=
  {t | (S t).Nonempty ∧ UpperRegularAt S t ∧ ContinuityAt S t}

end SweepingDesing


