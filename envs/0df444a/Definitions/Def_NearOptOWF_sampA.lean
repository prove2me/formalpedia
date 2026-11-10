-- Prove2me | Definitions.Def_NearOptOWF_sampA
-- name    : NearOptOWF_sampA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:52:00.62719+00:00
-- url     : https://prove2.me/theorems/bc4f3e3c-42a2-4bdb-aae1-f8fb78a60005
-- title:
--   Output distribution of the pre-image sampler
-- statement:
--   The output distribution of the pre-image sampler $A(g, y)$ on $\{\perp\} \cup \{0,1\}^{10n}$: the probability of each outcome over a uniform key of $H$, uniform coins of $i\mathcal O$ and uniform coins of $A^*$. This is the distribution Claim 4.7 compares with the ideal one.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.2, p.15 (PDF p.17); Claim 4.7

import Mathlib
import Definitions.Def_NearOptOWF_sampRun
import Definitions.Def_LaconicBarrier_coinAvg

namespace NearOptOWF

open LaconicBarrier

/-- The **output distribution of the pre-image sampler** `A(g, y)` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.2, p.15 (PDF p.17);
Claim 4.7): the probability, over a uniform key `k₂` of `H`, uniform coins `ρ` of `iO` and uniform coins
of `A*`, that `A(g, y)` returns `o`, where `o = none` is `⊥` and `o = some z` is the string
`z ∈ {0,1}^{10n}`.

**Formalization Note** An output string is read as a vector `Fin (10n) → Bool` (position `i` is bit
`i`); `H` has `10n` output wires, so its outputs are exactly such strings. -/
noncomputable def sampA (O : MIOScheme) (H : PPRF) (Astar : Inverter) (lamn Sn n : ℕ)
    (g : MCircuit (10 * n)) (y : List Bool) : Option (Fin (10 * n) → Bool) → ℝ := fun o =>
  coinAvg (H.keyLen lamn n (10 * n)) fun k₂ => coinAvg (O.coins lamn n Sn) fun ρ =>
    coinAvg (Astar.coins (KarpLiptonOM.tupleEnc (sampInput O H lamn Sn n g y k₂ ρ)).length) fun r =>
      if (sampRun O H Astar lamn Sn n g y k₂ ρ (bits r)).map
          (fun z => fun i : Fin (10 * n) => z.getD (i : ℕ) false) = o then 1 else 0

end NearOptOWF


