-- Prove2me | Definitions.Def_NearOptOWF_sampInput
-- name    : NearOptOWF_sampInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:15:34.233198+00:00
-- url     : https://prove2.me/theorems/b12c862b-3adb-48dd-b19c-389120da0e8c
-- title:
--   Input of $A^*$ inside the pre-image sampler
-- statement:
--   Inside the pre-image sampler $A(g, y)$, the inverter $A^*$ is run on $(1^n,\ i\mathcal O(1^\lambda, \mathrm{pad}_S(g \circ H_{k_2}); \rho),\ y)$, for a key $k_2$ of the puncturable PRF $H : \{0,1\}^n \to \{0,1\}^{10n}$ and coins $\rho$ of $i\mathcal O$.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_NearOptOWF_obfPad
import Definitions.Def_NearOptOWF_comp
import Definitions.Def_NearOptOWF_PPRF
import Definitions.Def_LaconicBarrier_RunsWithin

namespace NearOptOWF

open LaconicBarrier

/-- The input on which the pre-image sampler `A(g, y)` runs the inverter `A*` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.2, p.15 (PDF
p.17): "sample the puncturable PRF `H : {0,1}ⁿ → {0,1}^N`. Run `A*(iO(g ∘ H), y)`"): the tuple
`(1ⁿ, iO(1^λ, padTo S (g ∘ H_{k₂}); ρ), y)` for the key `k₂` of `H` at `(λ, n, 10n)` and coins `ρ`. -/
def sampInput (O : MIOScheme) (H : PPRF) (lamn Sn n : ℕ) (g : MCircuit (10 * n)) (y : List Bool)
    (k₂ : Fin (H.keyLen lamn n (10 * n)) → Bool) (ρ : Fin (O.coins lamn n Sn) → Bool) :
    List (List Bool) :=
  [unary n, (obfPad O lamn n Sn (comp g (H.circ lamn n (10 * n) k₂)) ρ).code, y]

end NearOptOWF


