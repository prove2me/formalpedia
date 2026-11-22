-- Prove2me | Definitions.Def_AvgPHETH_Supplement_aFill
-- name    : AvgPHETH_Supplement_aFill
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:44:47.495782+00:00
-- url     : https://prove2.me/theorems/6d9ae707-e397-445f-8bc9-1015c996e970
-- title:
--   Step 2 of a stage: assigning the $A$-queries in increasing order of $T$
-- statement:
--   In stage $i$ of the oracle construction, all valid $A$-queries $q=(\langle M,d\rangle,u,1^{T^{16}})$ with $i(T)=i$ are assigned, in increasing order of $T$, each by the rule $A(q)=1,0,\bot$ according to whether $f_q\equiv1$, $f_q\equiv0$ or neither.
--
--   This definition is the table of $A$-answers after the queries with time parameter below a given bound have been processed, starting from the table of the earlier stages.
--
--   **Formalization Note** Queries with the same $T$ are answered from the table of the smaller time parameters.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, step 2, p.41 (PDF 43)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_aAnswer
import Definitions.Def_AvgPHETH_Supplement_stageOf

namespace AvgPHETH.Supplement

open KarpLiptonOM

/-- Step 2 of stage `stage` of the oracle construction, carried out for the time parameters `T < N`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, step 2, p.41 (PDF 43)): "For all valid `A`-queries
`q = (⟨M, d⟩, u, 1^{T^16})` with `i(T) = i`, in increasing order of `T`", set `A(q)` by `aAnswer`.
`aFill ε mach ρ stage tab N` is the table of `A`-answers after the queries with `T < N` have been
processed, starting from the table `tab` of the earlier stages.

**Formalization Note** The queries with the same `T` are answered from the table of the smaller time
parameters. Valid means `d ≥ 1` and `T ≥ max{2, d|u|}`; `stageOf` is `i(T)`. -/
noncomputable def aFill (ε : ℕ → ℝ) (mach : ℕ → OracleTM) (ρ : CVar → Option (List Bool))
    (stage : ℕ) (tab : ℕ → ℕ → List Bool → ℕ → Option Bool) :
    ℕ → ℕ → ℕ → List Bool → ℕ → Option Bool
  | 0 => tab
  | N + 1 => fun i d u T =>
      if T = N ∧ stageOf N = stage ∧ 1 ≤ d ∧ max 2 (d * u.length) ≤ N then
        aAnswer ε mach (aFill ε mach ρ stage tab N) ρ i d u N
      else aFill ε mach ρ stage tab N i d u T

end AvgPHETH.Supplement


