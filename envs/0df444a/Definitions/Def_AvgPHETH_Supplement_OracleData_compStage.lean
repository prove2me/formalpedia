-- Prove2me | Definitions.Def_AvgPHETH_Supplement_OracleData_compStage
-- name    : AvgPHETH_Supplement_OracleData_compStage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:47:05.727962+00:00
-- url     : https://prove2.me/theorems/ef652a32-86dc-44d3-9166-3711d171f321
-- title:
--   The completion stage $D(k,n)$ of a group
-- statement:
--   The pairs $(k_s,n_s)$ are reserved for diagonalization. The completion stage of a group is
--
--   $$D(k,n)=\begin{cases}J_k(n)&\text{if }(k,n)\text{ is reserved},\\ 1&\text{otherwise.}\end{cases}$$
--
--   All variables of the group $(k,n)$ are set by stage $D(k,n)$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "The construction", p.40 (PDF 42)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_OracleData
import Definitions.Def_AvgPHETH_Supplement_JPar

namespace AvgPHETH.Supplement

/-- The completion stage `D(k, n)` of the group `(k, n)`: `J_k(n)` if `(k, n)` is reserved, i.e.
`(k, n) = (k_s, n_s)` for some `s`, and `1` otherwise
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, p.40 (PDF 42)). -/
noncomputable def OracleData.compStage (D : OracleData) (k n : ℕ) : ℕ := by
  classical
  exact if ∃ s, (D.enum s).1 = k ∧ D.ns s = n then JPar D.eps k n else 1

end AvgPHETH.Supplement


