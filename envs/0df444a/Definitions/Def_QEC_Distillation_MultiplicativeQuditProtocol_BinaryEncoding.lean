-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:37:33.362774+00:00
-- url     : https://prove2.me/theorems/0dc9fcaf-8095-46a3-bd92-d5929cb419d0
-- title:
--   Binary Encoding
-- statement:
--   Definitions and structural lemmas for Binary Encoding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryEncoding.lean

import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Theorems.Thm_QEC_Coding_f256MFESigma_injective
import Theorems.Thm_QEC_Coding_f256RMFEphi_injective

set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable (J : Type)
def logicalWordEmbedding : (J → ZMod 2) →ₗ[ZMod 2] (J → F256) where
  toFun u j := f256RMFEphi (u j)
  map_add' u v := by ext j; exact map_add f256RMFEphi _ _
  map_smul' c u := by ext j; exact f256RMFEphi.map_smul c (u j)
theorem logicalWordEmbedding_injective : Function.Injective (logicalWordEmbedding J) := by
  intro u v h
  funext j
  exact f256RMFEphi_injective (congrFun h j)
def physicalWordEmbedding : (J → F256) →ₗ[ZMod 2] ((J × Fin 512) → ZMod 2) where
  toFun u x := f256MFESigma (u x.1) x.2
  map_add' u v := by ext x; exact congrFun (map_add f256MFESigma _ _) x.2
  map_smul' c u := by ext x; exact congrFun (f256MFESigma.map_smul c (u x.1)) x.2
theorem physicalWordEmbedding_injective : Function.Injective (physicalWordEmbedding J) := by
  intro u v h
  funext j
  apply f256MFESigma_injective
  funext q
  exact congrFun h (j, q)
section Native
variable [Fintype J] [DecidableEq J]
local instance _p2m_local_instance_3142684436_53 {A : Type} [Fintype A] : Fintype (Word F256 A) := Fintype.ofFinite _
def logicalIsometry : Qubit.QubitRegister J →ₗᵢ[Complex] ComputationalBasisRegister F256 J :=
  ComputationalEmbedding.isometry ⟨logicalWordEmbedding J, logicalWordEmbedding_injective J⟩
def physicalIsometry : ComputationalBasisRegister F256 J →ₗᵢ[Complex]
    Qubit.QubitRegister (J × Fin 512) :=
  ComputationalEmbedding.isometry ⟨physicalWordEmbedding J, physicalWordEmbedding_injective J⟩
def binaryEncodingIsometry (i : Nat) :
    Qubit.QubitRegister (Fin (f256MultiplicationLogicalCount i)) →ₗᵢ[Complex]
      Qubit.QubitRegister ((f256SourceInput i).PivotComplement × Fin 512) :=
  (physicalIsometry (f256SourceInput i).PivotComplement).comp
    ((f256SourceInput i).encodingIsometry.comp
      (logicalIsometry (Fin (f256MultiplicationLogicalCount i))))
def binaryEncodedCode (i : Nat) :
    EncodedCode (Qubit.QubitRegister (Fin (f256MultiplicationLogicalCount i)))
      (Qubit.QubitRegister ((f256SourceInput i).PivotComplement × Fin 512)) where
  code := ⟨(binaryEncodingIsometry i).toLinearMap.range⟩
  encoding := LinearIsometry.equivRange (binaryEncodingIsometry i)
end Native
end QEC.Distillation.Ngu24Binary


