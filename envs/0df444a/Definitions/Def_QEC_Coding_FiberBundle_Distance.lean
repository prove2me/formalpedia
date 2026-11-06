-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_Distance
-- name    : QEC_Coding_FiberBundle_Distance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:16:39.353643+00:00
-- url     : https://prove2.me/theorems/3c147a36-10f1-40ac-8fb6-28587a0eee8b
-- title:
--   Distance
-- statement:
--   Definitions and structural lemmas for Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Distance.lean

import Definitions.Def_QEC_Coding_FiberBundle_Core
set_option autoImplicit false
namespace QEC.Coding.FiberBundle
universe u
def CohomologyDistanceAtLeast
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (d : Nat) : Prop :=
  ∀ x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne),
    x ∈ (chainComplex D).middleCocycleCode.carrier →
    x ∉ (chainComplex D).firstCoboundaryCheckCode.carrier →
    d ≤ HammingWeight x
def HomologyDistanceAtLeast
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (d : Nat) : Prop :=
  ∀ z : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne),
    z ∈ (chainComplex D).middleCycleCode.carrier →
    z ∉ (chainComplex D).middleBoundaryCode.carrier →
    d ≤ HammingWeight z
end QEC.Coding.FiberBundle


