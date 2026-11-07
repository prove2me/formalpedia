-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_Register
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:16:34.053661+00:00
-- url     : https://prove2.me/theorems/89befb53-a22b-48c6-9e3c-e28b0d4b7459
-- title:
--   Register
-- statement:
--   Definitions and structural lemmas for Register, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Register.lean

import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Distillation
universe u
abbrev ComputationalBasisQudit (F : Type u) [Fintype F] : Type u :=
  EuclideanSpace Complex F
abbrev ComputationalBasisRegisterLabel (F ι : Type u) : Type u :=
  ι → F
abbrev ComputationalBasisRegister (F ι : Type u) : Type u :=
  EuclideanSpace Complex (ComputationalBasisRegisterLabel F ι)
variable {F ι : Type u} [Field F] [Fintype F]
def quditBasisKet (label : F) : ComputationalBasisQudit F :=
  EuclideanSpace.basisFun F Complex label
def registerBasisKet [Fintype ι] [DecidableEq ι]
    (label : ComputationalBasisRegisterLabel F ι) :
    ComputationalBasisRegister F ι :=
  EuclideanSpace.basisFun (ComputationalBasisRegisterLabel F ι) Complex label
inductive ThreeCopyTag
  | first
  | second
  | third
  deriving DecidableEq
instance : Fintype ThreeCopyTag where
  elems := {.first, .second, .third}
  complete := by intro tag; cases tag <;> simp
abbrev TaggedThreeCopyCoordinate (ι : Type u) : Type u :=
  ThreeCopyTag × ι
abbrev TaggedThreeCopyRegisterLabel (F ι : Type u) : Type u :=
  TaggedThreeCopyCoordinate ι → F
abbrev TaggedThreeCopyRegister (F ι : Type u) : Type u :=
  EuclideanSpace Complex (TaggedThreeCopyRegisterLabel F ι)
def assembleTagged (blocks : ThreeCopyTag → ComputationalBasisRegisterLabel F ι) :
    TaggedThreeCopyRegisterLabel F ι :=
  fun coordinate => blocks coordinate.1 coordinate.2
def extractBlock (label : TaggedThreeCopyRegisterLabel F ι) (tag : ThreeCopyTag) :
    ComputationalBasisRegisterLabel F ι :=
  fun site => label (tag, site)
def coordinateSupport [Fintype ι] [DecidableEq ι] (site : ι) :
    Finset (TaggedThreeCopyCoordinate ι) :=
  Finset.univ.filter (fun coordinate => coordinate.2 = site)
end QEC.Distillation


