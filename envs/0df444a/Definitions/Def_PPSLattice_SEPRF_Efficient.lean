-- Prove2me | Definitions.Def_PPSLattice_SEPRF_Efficient
-- name    : PPSLattice_SEPRF_Efficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:58.912885+00:00
-- url     : https://prove2.me/theorems/a0776dcd-b165-401e-83e0-330bf64688ff
-- title:
--   The algorithms of an SEPRF scheme run in polynomial time
-- statement:
--   Setup, Sim1 and Sim2 are probabilistic polynomial-time algorithms and Eval a deterministic polynomial-time algorithm, with $\lambda$ and $\ell_{\mathrm{out}}$ in unary.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.2, p.18

import Mathlib
import Definitions.Def_PPSLattice_SEPRF
import Definitions.Def_PPSLattice_PPTSampler
import Definitions.Def_PPSLattice_PolyTimeOn
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The algorithms of an SEPRF scheme are **polynomial-time**: Setup, Sim1 and Sim2 are PPT
samplers and Eval is a deterministic polynomial-time map, with `λ` and `ℓ_out` in unary.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.2, p.18 ("consists of the following polynomial-time algorithms"). -/
def SEPRF.Efficient (F : SEPRF) : Prop :=
  PPTSampler (fun a : ℕ × ℕ => BeyondDS.tup [encNat a.1, encNat a.2]) (fun a => F.setup a.1 a.2) ∧
    PolyTimeOn (fun a : Str × Str => BeyondDS.tup [a.1, a.2]) (fun a => F.eval a.1 a.2) ∧
    PPTSampler (fun a : ℕ × ℕ × Str => BeyondDS.tup [encNat a.1, encNat a.2.1, a.2.2])
      (fun a => F.sim1 a.1 a.2.1 a.2.2) ∧
    PPTSampler (fun a : Str × Str => BeyondDS.tup [a.1, a.2]) (fun a => F.sim2 a.1 a.2)

end PPSLattice


