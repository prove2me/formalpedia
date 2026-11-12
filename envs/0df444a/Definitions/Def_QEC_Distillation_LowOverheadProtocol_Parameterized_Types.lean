-- Prove2me | Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
-- name    : QEC_Distillation_LowOverheadProtocol_Parameterized_Types
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:30:52.424113+00:00
-- url     : https://prove2.me/theorems/bd3087bd-c9ab-4564-9371-fb809fa05cf8
-- title:
--   Types
-- statement:
--   Definitions and structural lemmas for Types, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Types.lean

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
attribute [local instance 100] Fintype.ofFinite
abbrev PhysicalSite (m w : Nat) :=
  HH18PuncturedReedMuller.PhysicalSite m w
abbrev LogicalSite (m w : Nat) :=
  HH18PuncturedReedMuller.LogicalSite m w
abbrev PhysicalRegister (m w : Nat) := QubitRegister (PhysicalSite m w)
abbrev LogicalRegister (m w : Nat) := QubitRegister (LogicalSite m w)
abbrev PhysicalErrorWord (m w : Nat) :=
  HH18NoisyInput.PhysicalErrorWord m w
def physicalInputCount (m w : Nat) : Nat := Fintype.card (PhysicalSite m w)
def logicalOutputCount (m w : Nat) : Nat := Fintype.card (LogicalSite m w)
def codeDistance (r w : Nat) : Nat := binomialTail (r + 1) w
noncomputable def logicalPlus (m w : Nat) : LogicalRegister m w :=
  Triorthogonal.BinaryRowFamily.logicalPlusState (LogicalSite m w)
noncomputable def encodedLogicalPlus {w r m : Nat} (h : Admissible w r m) :
    PhysicalRegister m w :=
  (HH18PuncturedReedMuller.encodedCode h).encode (logicalPlus m w)
noncomputable def physicalTInvBranch {w r m : Nat}
    (h : Admissible w r m) (_hdegree : 3 * r < m) : PhysicalRegister m w :=
  HH18PuncturedReedMuller.physicalTInv w m (encodedLogicalPlus h)
end HH18Parameterized
end Distillation
end QEC


