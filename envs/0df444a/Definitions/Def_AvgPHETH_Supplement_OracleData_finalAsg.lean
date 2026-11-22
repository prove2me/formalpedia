-- Prove2me | Definitions.Def_AvgPHETH_Supplement_OracleData_finalAsg
-- name    : AvgPHETH_Supplement_OracleData_finalAsg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:53:53.818601+00:00
-- url     : https://prove2.me/theorems/b44665c9-0fa5-42ca-991d-7144d32bd597
-- title:
--   The final assignment to the construction variables
-- statement:
--   Every variable of the group $(k,n)$ is set by the completion stage $D(k,n)$ and is not changed afterwards. This definition is the resulting total assignment; it determines every selector tree $T^k_x$ and hence the oracle $V$.
--
--   **Formalization Note** Names that are not construction variables get the empty string, which no oracle answer reads.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "The construction", p.40 (PDF 42)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_OracleData_build
import Definitions.Def_AvgPHETH_Supplement_OracleData_compStage

namespace AvgPHETH.Supplement

/-- The final assignment to the construction variables: a variable of the group `(k, n)` has the value
it holds after the completion stage `D(k, n)` of its group, "by which all variables in the group are
set" (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, p.40 (PDF 42)). It determines every selector tree `T^k_x`, hence
`V`.

**Formalization Note** A value assigned at some stage is never changed later. Names that are not
construction variables get the empty string, which no oracle answer reads. -/
noncomputable def OracleData.finalAsg (D : OracleData) (U : ℕ → CVar → ℕ → ℝ) (v : CVar) : List Bool :=
  ((D.build U (D.compStage v.k v.x.length)).1 v).getD []

end AvgPHETH.Supplement


