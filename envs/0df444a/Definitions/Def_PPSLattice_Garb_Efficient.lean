-- Prove2me | Definitions.Def_PPSLattice_Garb_Efficient
-- name    : PPSLattice_Garb_Efficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:34:09.341519+00:00
-- url     : https://prove2.me/theorems/1c60772c-b59f-4f34-bcb9-588aa47bebcf
-- title:
--   The algorithms of a garbling scheme run in polynomial time
-- statement:
--   Setup, CircGarb and Sim are probabilistic polynomial-time algorithms and InpGarb and Eval deterministic polynomial-time algorithms; $\lambda,s,\ell$ are given in unary and circuits by their descriptions.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.2, p.19

import Mathlib
import Definitions.Def_PPSLattice_Garb
import Definitions.Def_PPSLattice_PPTSampler
import Definitions.Def_PPSLattice_PolyTimeOn
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The algorithms of a garbling scheme are **polynomial-time**: Setup, CircGarb and Sim are PPT
samplers and InpGarb and Eval are deterministic polynomial-time maps; `λ`, `s`, `ℓ` are given in unary
and a circuit by its description `C.code`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.2, p.19 ("consists of the following polynomial-time algorithms"). -/
def Garb.Efficient (G : Garb) : Prop :=
  PPTSampler (fun a : ℕ × ℕ × ℕ => BeyondDS.tup [encNat a.1, encNat a.2.1, encNat a.2.2])
      (fun a => G.setup a.1 a.2.1 a.2.2) ∧
    PolyTimeOn (fun a : Str × Str => BeyondDS.tup [a.1, a.2]) (fun a => G.inpGarb a.1 a.2) ∧
    PPTSampler (fun a : Str × RestrictedDec.Circuit => BeyondDS.tup [a.1, a.2.code])
      (fun a => G.circGarb a.1 a.2) ∧
    PolyTimeOn (fun a : Str × Str => BeyondDS.tup [a.1, a.2]) (fun a => G.eval a.1 a.2) ∧
    PPTSampler (fun a : Str × Str × Str => BeyondDS.tup [a.1, a.2.1, a.2.2])
      (fun a => G.sim a.1 a.2.1 a.2.2)

end PPSLattice


