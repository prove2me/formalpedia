-- Prove2me | Definitions.Def_NearOptOWF_sampRun
-- name    : NearOptOWF_sampRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:50:38.666447+00:00
-- url     : https://prove2.me/theorems/e88e040a-981e-4b27-a072-3ae247aa9d29
-- title:
--   One run of the pre-image sampler $A(g, y)$
-- statement:
--   The pre-image sampler $A(g, y)$ of the paper: "sample the puncturable PRF $H : \{0,1\}^n \to \{0,1\}^N$. Run $A^*(i\mathcal O(g \circ H), y) \to x$, and output $H(x)$ if $g(H(x)) = y$. Otherwise output $\perp$." With all coins fixed (the key of $H$, the coins of $i\mathcal O$ and those of $A^*$), the run returns $H(x)$ when $x \in \{0,1\}^n$ and $g(H(x)) = y$, and $\perp$ otherwise.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_NearOptOWF_sampInput
import Definitions.Def_NearOptOWF_Inverter

namespace NearOptOWF

open LaconicBarrier

/-- One run of the **pre-image sampler** `A(g, y)` on given coins (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.2, p.15 (PDF p.17):
"sample the puncturable PRF `H`. Run `A*(iO(g ∘ H), y) → x`, and output `H(x)` if `g(H(x)) = y`.
Otherwise output ⊥"): with the key `k₂` of `H`, the coins `ρ` of `iO` and the coins `r` of `A*`, run
`A*` on `sampInput` to get `x`, and return `some (H(x))` if `x ∈ {0,1}ⁿ` and `g(H(x)) = y`, else `none`
(`⊥`). -/
def sampRun (O : MIOScheme) (H : PPRF) (Astar : Inverter) (lamn Sn n : ℕ) (g : MCircuit (10 * n))
    (y : List Bool) (k₂ : Fin (H.keyLen lamn n (10 * n)) → Bool) (ρ : Fin (O.coins lamn n Sn) → Bool)
    (r : List Bool) : Option (List Bool) :=
  let x := Astar.run (sampInput O H lamn Sn n g y k₂ ρ) r
  let z := (H.circ lamn n (10 * n) k₂).eval x
  if x.length = n ∧ g.eval z = y then some z else none

end NearOptOWF


