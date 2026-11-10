-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T12:30:45.981416+00:00
-- url     : https://prove2.me/theorems/61dc0237-eba8-4cf5-b91b-497856ad1841
-- title:
--   Binary Self Dual
-- statement:
--   Definitions and structural lemmas for Binary Self Dual, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinarySelfDual.lean

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Theorems.Thm_QEC_Coding_f256MFEFromSelfDual_injective
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable (J : Type)
def selfDualWordEquiv : (J → F256) ≃ₗ[ZMod 2] ((J × Fin 8) → ZMod 2) where
  toFun u x := f256SelfDualBasis.equivFun (u x.1) x.2
  invFun v j := f256SelfDualBasis.equivFun.symm (fun b => v (j, b))
  left_inv u := by
    funext j
    exact f256SelfDualBasis.equivFun.symm_apply_apply (u j)
  right_inv v := by
    funext x
    exact congrFun (f256SelfDualBasis.equivFun.apply_symm_apply (fun b => v (x.1, b))) x.2
  map_add' u v := by
    ext x
    exact congrFun (map_add f256SelfDualBasis.equivFun (u x.1) (v x.1)) x.2
  map_smul' c u := by
    ext x
    exact congrFun (f256SelfDualBasis.equivFun.map_smul c (u x.1)) x.2
def mfeFromSelfDualWordMap : ((J × Fin 8) → ZMod 2) →ₗ[ZMod 2]
    ((J × Fin 512) → ZMod 2) where
  toFun v x := f256MFEFromSelfDual (fun b => v (x.1, b)) x.2
  map_add' u v := by
    ext x
    exact congrFun (map_add f256MFEFromSelfDual _ _) x.2
  map_smul' c u := by
    ext x
    exact congrFun (f256MFEFromSelfDual.map_smul c _) x.2
theorem mfeFromSelfDualWordMap_injective : Function.Injective (mfeFromSelfDualWordMap J) := by
  intro u v h
  funext x
  have hb : (fun b => u (x.1, b)) = (fun b => v (x.1, b)) := by
    apply f256MFEFromSelfDual_injective
    funext q
    exact congrFun h (x.1, q)
  exact congrFun hb x.2
section Native
variable [Fintype J] [DecidableEq J]
local instance binarySelfDualFieldWordFintype {A : Type} [Fintype A] :
    Fintype (Word F256 A) := Fintype.ofFinite _
def selfDualIsometry : ComputationalBasisRegister F256 J →ₗᵢ[Complex]
    Qubit.QubitRegister (J × Fin 8) :=
  ComputationalEmbedding.isometry (selfDualWordEquiv J).toEquiv.toEmbedding
def mfeFromSelfDualIsometry : Qubit.QubitRegister (J × Fin 8) →ₗᵢ[Complex]
    Qubit.QubitRegister (J × Fin 512) :=
  ComputationalEmbedding.isometry
    ⟨mfeFromSelfDualWordMap J, mfeFromSelfDualWordMap_injective J⟩
end Native
end QEC.Distillation.Ngu24Binary


