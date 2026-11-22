-- Prove2me | Definitions.Def_AvgPHETH_Supplement_OracleData_tPar
-- name    : AvgPHETH_Supplement_OracleData_tPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:46:23.845783+00:00
-- url     : https://prove2.me/theorems/8d2f77ca-2a40-4bf2-a882-a0fae471885a
-- title:
--   The diagonalization clock $t_s(n)$
-- statement:
--   For the $s$-th triple $(k_s,M_s,m_s)$ of the enumeration,
--
--   $$t_s(n)=\begin{cases}\max\{n,2^{\lfloor a_{k_s}(n)/m_s\rfloor}\}&\text{if }(k_s,n)\text{ is active},\\ n&\text{otherwise.}\end{cases}$$
--
--   The running time and the witness length of $M_s$ are capped to $t_s(n)$ when diagonalizing.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "The construction", p.40 (PDF 42)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_OracleData
import Definitions.Def_AvgPHETH_Supplement_IsActive
import Definitions.Def_AvgPHETH_Supplement_aPar

namespace AvgPHETH.Supplement

/-- The clock `t_s(n) = max{n, 2^{⌊a_{k_s}(n)/m_s⌋}}` if `(k_s, n)` is active, and `t_s(n) = n` otherwise,
to which the running time and the witness length of `M_s` are capped when diagonalizing
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "The construction", p.40 (PDF 42)). -/
noncomputable def OracleData.tPar (D : OracleData) (s n : ℕ) : ℕ := by
  classical
  exact
    if IsActive D.eps (D.enum s).1 n then max n (2 ^ (aPar D.eps (D.enum s).1 n / (D.enum s).2.2))
    else n

end AvgPHETH.Supplement


