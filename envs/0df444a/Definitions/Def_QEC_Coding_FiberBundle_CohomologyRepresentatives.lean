-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
-- name    : QEC_Coding_FiberBundle_CohomologyRepresentatives
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:05:29.465013+00:00
-- url     : https://prove2.me/theorems/196a3793-85d9-4bbd-a1ad-f9a8a8edde57
-- title:
--   Cohomology Representatives
-- statement:
--   Definitions and structural lemmas for Cohomology Representatives, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
namespace QEC.Coding.FiberBundle
universe u
def cycleFiberPrimitive
    (n : Nat) [NeZero n]
    (g : Word (ZMod 2) (ZMod n)) :
    Word (ZMod 2) (ZMod n) :=
  fun j => ∑ k ∈ Finset.range j.val, g (k : ZMod n)
noncomputable def bundleCocoboundary
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    Word (ZMod 2) (C2Index baseOne fiberOne) :=
  wordLinearMapTranspose (boundary2 D) z
def verticalFiberPrimitiveWord
    {r ell : Nat} [NeZero ell]
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell)))) :
    Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))) :=
  fun ai => cycleFiberPrimitive (ell * ell) (verticalFiber z ai.1) ai.2
def constantFiberWord
    {baseZero fiberZero : Type u}
    (t : Word (ZMod 2) baseZero) :
    Word (ZMod 2) (C0Index baseZero fiberZero) :=
  fun ai => t ai.1
end QEC.Coding.FiberBundle


