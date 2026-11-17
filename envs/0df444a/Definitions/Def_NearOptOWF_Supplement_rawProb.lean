-- Prove2me | Definitions.Def_NearOptOWF_Supplement_rawProb
-- name    : NearOptOWF_Supplement_rawProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:04:49.2822+00:00
-- url     : https://prove2.me/theorems/efcefd47-69a9-41ec-addb-0350d32fb827
-- title:
--   Output probability of a randomized algorithm
-- statement:
--   For a randomized algorithm $A$ (a deterministic function of its input tuple and a uniform coin string) and an input tuple $\mathrm{inp}$, the probability that $A$ outputs exactly the string $o$ is
--   $$
--   \Pr[A(\mathrm{inp}) = o] = 2^{-c}\sum_{r\in\{0,1\}^c}\mathbf 1[A(\mathrm{inp}; r) = o],
--   $$
--   where $c$ is the number of coins $A$ uses on this input. The function $o\mapsto\Pr[A(\mathrm{inp})=o]$ is the output distribution of $A$, used to state that two runs are identically distributed or that an output is uniform.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 4.2, p.13 (PDF p.15); §5.1, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_NearOptOWF_Inverter
import Definitions.Def_LaconicBarrier_coinAvg
import Definitions.Def_LaconicBarrier_RunsWithin

namespace NearOptOWF.Supplement

open LaconicBarrier

/-- The probability that the randomized algorithm `A`, run on the input tuple `inp`, outputs exactly
the string `o` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 4.2, p.13 (PDF p.15):
"`A(f, y)` and `A(f′, y)` are identically distributed"; §5.1, p.24 (PDF p.26)): the average over
`A`'s uniform coins of the indicator that its output is `o`.

**Formalization Note** The output distribution of `A` on `inp` is the function `o ↦ rawProb A inp o`. -/
noncomputable def rawProb (A : Inverter) (inp : List (List Bool)) (o : List Bool) : ℝ :=
  coinAvg (A.coins (KarpLiptonOM.tupleEnc inp).length) fun r =>
    if A.run inp (bits r) = o then 1 else 0

end NearOptOWF.Supplement


