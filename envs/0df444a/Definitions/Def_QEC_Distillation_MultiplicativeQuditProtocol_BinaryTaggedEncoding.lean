-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:47:31.734003+00:00
-- url     : https://prove2.me/theorems/b6236b3b-9bf4-4319-9595-f489fc54766f
-- title:
--   Binary Tagged Encoding
-- statement:
--   Definitions and structural lemmas for Binary Tagged Encoding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTaggedEncoding.lean

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Theorems.Thm_QEC_Coding_f256MFESigma_injective

set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable (J : Type)
def taggedPhysicalWordEmbedding : TaggedThreeCopyRegisterLabel F256 J →ₗ[ZMod 2]
    TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512) where
  toFun u x := f256MFESigma (u (x.1, x.2.1)) x.2.2
  map_add' u v := by ext x; exact congrFun (map_add f256MFESigma _ _) x.2.2
  map_smul' c u := by ext x; exact congrFun (f256MFESigma.map_smul c _) x.2.2
theorem taggedPhysicalWordEmbedding_injective : Function.Injective (taggedPhysicalWordEmbedding J) := by
  intro u v h
  funext x
  apply f256MFESigma_injective
  funext q
  exact congrFun h (x.1, (x.2, q))
variable [Fintype J] [DecidableEq J]
def taggedLogicalIsometry : TaggedThreeCopyRegister (ZMod 2) J →ₗᵢ[Complex]
    TaggedThreeCopyRegister F256 J :=
  ComputationalEmbedding.isometry
    ⟨logicalWordEmbedding (ThreeCopyTag × J), logicalWordEmbedding_injective _⟩
def taggedPhysicalIsometry : TaggedThreeCopyRegister F256 J →ₗᵢ[Complex]
    TaggedThreeCopyRegister (ZMod 2) (J × Fin 512) :=
  ComputationalEmbedding.isometry
    ⟨taggedPhysicalWordEmbedding J, taggedPhysicalWordEmbedding_injective J⟩
local instance (priority := 2000) binaryTaggedFinDecidableEq {n : Nat} :
    DecidableEq (Fin n) := instDecidableEqFin n
section SourceEncoding
variable {I Logical : Type} [Fintype I] [Fintype Logical]
local instance binaryTaggedLogicalDecidableEq : DecidableEq Logical := Classical.decEq _
def sourceBinaryTaggedEncodingIsometry (data : SourceInput F256 I Logical) :
    TaggedThreeCopyRegister (ZMod 2) Logical →ₗᵢ[Complex]
      TaggedThreeCopyRegister (ZMod 2) (data.PivotComplement × Fin 512) :=
  (taggedPhysicalIsometry data.PivotComplement).comp
    ((taggedEncodingIsometry data).comp (taggedLogicalIsometry Logical))
def sourceBinaryTaggedEncodingLinearMap (data : SourceInput F256 I Logical) :
    TaggedThreeCopyRegister (ZMod 2) Logical →ₗ[Complex]
      TaggedThreeCopyRegister (ZMod 2) (data.PivotComplement × Fin 512) :=
  (sourceBinaryTaggedEncodingIsometry data).toLinearMap
end SourceEncoding
def binaryTaggedEncodingIsometry (i : Nat) :=
  sourceBinaryTaggedEncodingIsometry (f256SourceInput i)
def binaryTaggedEncodingLinearMap (i : Nat) :
    TaggedThreeCopyRegister (ZMod 2) (Fin (f256MultiplicationLogicalCount i)) →ₗ[Complex]
      TaggedThreeCopyRegister (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512) :=
  sourceBinaryTaggedEncodingLinearMap (f256SourceInput i)
def binaryTaggedCosetLabel (i : Nat)
    (u : TaggedThreeCopyRegisterLabel (ZMod 2) (Fin (f256MultiplicationLogicalCount i)))
    (h : ThreeCopyTag → (f256SourceInput i).H0) :
    TaggedThreeCopyRegisterLabel (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512) :=
  assembleTagged fun tag => binaryCosetWordMap i (extractBlock u tag, h tag)
end QEC.Distillation.Ngu24Binary


