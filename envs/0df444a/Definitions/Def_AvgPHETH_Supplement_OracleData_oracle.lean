-- Prove2me | Definitions.Def_AvgPHETH_Supplement_OracleData_oracle
-- name    : AvgPHETH_Supplement_OracleData_oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:55:33.947665+00:00
-- url     : https://prove2.me/theorems/09bd00b4-09e5-4c60-8a38-3b99c91b008a
-- title:
--   The random oracle $O=A+V$ of §8.1
-- statement:
--   The oracle of Section 8, as a function of the construction data and of the seeds of the restriction rounds: $V$ is given by the final assignment to the construction variables, and the answer of $A$ to a query with time parameter $T$ is the one assigned in stage $i(T)$.
--
--   Theorems 8.5 and 8.7 state that, with probability one over the seeds, $\mathrm{DistPH}^O\subseteq\mathrm{AvgP}^O$ and $L_k^O\notin\Sigma_k\mathrm{TIME}^O[2^{o(a_k(n))}]$ for every $k\ge1$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, pp.38–41 (PDF 40–43)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_OracleData_finalAsg
import Definitions.Def_AvgPHETH_Supplement_oracleOf
import Definitions.Def_AvgPHETH_Supplement_stageOf

namespace AvgPHETH.Supplement

/-- **The oracle `O = A + V` of §8.1**, as a function of the data `D` and the seeds `U` of the
restriction rounds (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, pp.38–41 (PDF 40–43)): `V` is given by the final
assignment to the construction variables, and the answer of `A` to a query with time parameter `T` is
the one assigned in stage `i(T)`.

**Formalization Note** `oracleOf` fixes the encodings (the join, the query layouts, the two-bit answer
of `A`). An `A`-answer is not changed after the stage `i(T)` in which it is assigned. -/
noncomputable def OracleData.oracle (D : OracleData) (U : ℕ → CVar → ℕ → ℝ) : Set (List Bool) :=
  oracleOf D.eps (fun i d u T => (D.build U (stageOf T)).2 i d u T) (D.finalAsg U)

end AvgPHETH.Supplement


