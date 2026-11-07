-- Prove2me | Definitions.Def_QEC_Coding_CSS_Distance
-- name    : QEC_Coding_CSS_Distance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:19:36.371198+00:00
-- url     : https://prove2.me/theorems/81c380a8-281d-441e-beed-f5b77a2b05f7
-- title:
--   Distance
-- statement:
--   Definitions and structural lemmas for Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/Distance.lean

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_Distance
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
open Classical
universe u v
namespace PauliSymplectic
variable {ι κP κQ : Type v} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ]
def CSSXLogicalMinimumDistance
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (d : Nat) : Prop :=
  RelativeMinimumDistance (parityCheckKernelCode P) (parityCheckRowCode Q) d
def CSSZLogicalMinimumDistance
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (d : Nat) : Prop :=
  RelativeMinimumDistance (parityCheckKernelCode Q) (parityCheckRowCode P) d
def StrictGeneratedGroupPurity
    (C : StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι))
    (threshold : Nat) : Prop :=
  ∀ E : Binary ι,
    C.InGeneratedGroupUpToSign E →
    ¬ BinaryUpToSign E binaryOne →
    threshold < weight E
end PauliSymplectic
namespace StabilizerCode
open PauliSymplectic
variable {ι κP κQ : Type v} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ]
end StabilizerCode
end Coding
end QEC


