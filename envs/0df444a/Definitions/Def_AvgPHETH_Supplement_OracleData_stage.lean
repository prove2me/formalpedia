-- Prove2me | Definitions.Def_AvgPHETH_Supplement_OracleData_stage
-- name    : AvgPHETH_Supplement_OracleData_stage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:50:14.076866+00:00
-- url     : https://prove2.me/theorems/a3dced59-1838-4bb5-8c05-17e5112d1d95
-- title:
--   One stage of the oracle construction
-- statement:
--   Stage $i$ of the oracle construction consists of three steps:
--
--   1. a restriction round on every group $(k,n)$ with $D(k,n)\ge i$, after which the cumulative assignment is $\rho_i$;
--   2. the assignment of all valid $A$-queries with $i(T)=i$, in increasing order of $T$;
--   3. the completion of the groups with $D(k,n)=i$.
--
--   This definition maps the state before the stage (partial assignment and table of $A$-answers) and the seeds of the round to the state after the stage.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, pp.40–41 (PDF 42–43)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_OracleData_complete
import Definitions.Def_AvgPHETH_Supplement_restrictRound
import Definitions.Def_AvgPHETH_Supplement_aFill

namespace AvgPHETH.Supplement

/-- One stage `i` of the oracle construction, applied to the state `st = (ρ, tab)` left by the earlier
stages, where `ρ` is the partial assignment to the construction variables and `tab` the table of
`A`-answers (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "In stage `i = 1, 2, …`", pp.40–41 (PDF 42–43)):

1. a restriction round on every group `(k, n)` with `D(k, n) ≥ i`, giving `ρ_i`;
2. the `A`-queries with `i(T) = i` are assigned, in increasing order of `T`;
3. the groups with `D(k, n) = i` are completed.

**Formalization Note** `u` are the seeds of this stage's restriction round (`restrictRound`). After
step 2 the entry of the table for a query with time parameter `T` is the one written when `T` was
processed, `aFill … (T + 1)`. -/
noncomputable def OracleData.stage (D : OracleData) (u : CVar → ℕ → ℝ) (i : ℕ)
    (st : (CVar → Option (List Bool)) × (ℕ → ℕ → List Bool → ℕ → Option Bool)) :
    (CVar → Option (List Bool)) × (ℕ → ℕ → List Bool → ℕ → Option Bool) :=
  (D.complete i (restrictRound D.eps u (fun k n => i ≤ D.compStage k n) st.1)
      (fun j d w T =>
        aFill D.eps D.mach (restrictRound D.eps u (fun k n => i ≤ D.compStage k n) st.1) i st.2
          (T + 1) j d w T),
    fun j d w T =>
      aFill D.eps D.mach (restrictRound D.eps u (fun k n => i ≤ D.compStage k n) st.1) i st.2
        (T + 1) j d w T)

end AvgPHETH.Supplement


