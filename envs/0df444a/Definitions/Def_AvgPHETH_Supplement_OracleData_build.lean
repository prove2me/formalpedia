-- Prove2me | Definitions.Def_AvgPHETH_Supplement_OracleData_build
-- name    : AvgPHETH_Supplement_OracleData_build
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:51:27.736145+00:00
-- url     : https://prove2.me/theorems/32897b38-7b91-4d28-85e3-625e922987e4
-- title:
--   The state of the construction after $i$ stages
-- statement:
--   The oracle construction proceeds in stages $i=1,2,\dots$. This definition is its state after the first $i$ stages: the partial assignment to the construction variables and the table of $A$-answers. Before stage $1$ nothing is assigned.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, pp.40–41 (PDF 42–43)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_OracleData_stage

namespace AvgPHETH.Supplement

/-- The state `(ρ, tab)` of the oracle construction after its first `i` stages: the partial assignment
to the construction variables and the table of `A`-answers
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, pp.40–41 (PDF 42–43)). Before stage `1` nothing is assigned.

**Formalization Note** `U i v c` is the seed of the variable `v`, channel `c`, in the restriction round
of stage `i` (stages are numbered from `1`). -/
noncomputable def OracleData.build (D : OracleData) (U : ℕ → CVar → ℕ → ℝ) :
    ℕ → (CVar → Option (List Bool)) × (ℕ → ℕ → List Bool → ℕ → Option Bool)
  | 0 => (fun _ => none, fun _ _ _ _ => none)
  | i + 1 => D.stage (U (i + 1)) (i + 1) (D.build U i)

end AvgPHETH.Supplement


