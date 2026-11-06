-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InvolutionResidueTransport
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Rational_InvolutionResidueTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:36:42.262591+00:00
-- url     : https://prove2.me/theorems/747205bf-914b-42d1-99ca-81372ce04487
-- title:
--   Involution Residue Transport
-- statement:
--   Definitions and structural lemmas for Involution Residue Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/InvolutionResidueTransport.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_RationalInfinityTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueCoordinate
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_xAdic_order_rationalInvolution_eq_rationalInfinity_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
open scoped Polynomial RatFunc WithZero
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
structure RationalInvolutionTarget (k : Type*) [Field k] where
  down : RatFunc k
def rationalInvolutionTargetEquiv :
    RationalInvolutionTarget k ≃ RatFunc k where
  toFun := RationalInvolutionTarget.down
  invFun f := ⟨f⟩
  left_inv f := by cases f; rfl
  right_inv _ := rfl
noncomputable instance rationalInvolutionTargetField :
    Field (RationalInvolutionTarget k) :=
  (rationalInvolutionTargetEquiv (k := k)).field
noncomputable def rationalInvolutionTargetRingEquiv :
    RationalInvolutionTarget k ≃+* RatFunc k :=
  (rationalInvolutionTargetEquiv (k := k)).ringEquiv
noncomputable instance rationalInvolutionTargetConstantAlgebra :
    Algebra k (RationalInvolutionTarget k) :=
  ((rationalInvolutionTargetRingEquiv (k := k)).symm.toRingHom.comp
    (algebraMap k (RatFunc k))).toAlgebra
noncomputable def rationalInvolutionTargetAlgEquiv :
    RationalInvolutionTarget k ≃ₐ[k] RatFunc k where
  __ := rationalInvolutionTargetRingEquiv (k := k)
  commutes' _ := rfl
noncomputable instance rationalInvolutionToTargetAlgebra :
    Algebra (RatFunc k) (RationalInvolutionTarget k) :=
  ((InverseAffinePlace.rationalInvolution k).trans
    (rationalInvolutionTargetAlgEquiv (k := k)).symm).toRingHom.toAlgebra
noncomputable instance rationalInvolutionToTargetTower :
    IsScalarTower k (RatFunc k) (RationalInvolutionTarget k) :=
  IsScalarTower.of_algebraMap_eq fun c =>
    (((InverseAffinePlace.rationalInvolution k).trans
      (rationalInvolutionTargetAlgEquiv (k := k)).symm).commutes c).symm
noncomputable instance rationalInvolutionFromTargetAlgebra :
    Algebra (RationalInvolutionTarget k) (RatFunc k) :=
  (rationalInvolutionTargetAlgEquiv (k := k)).toRingHom.toAlgebra
noncomputable instance rationalInvolutionFromTargetTower :
    IsScalarTower k (RationalInvolutionTarget k) (RatFunc k) :=
  IsScalarTower.of_algebraMap_eq fun c =>
    ((rationalInvolutionTargetAlgEquiv (k := k)).commutes c).symm
noncomputable def rationalDifferentialToTarget :
    Differential k (RatFunc k) →ₗ[RatFunc k]
      Differential k (RationalInvolutionTarget k) :=
  KaehlerDifferential.map k k (RatFunc k) (RationalInvolutionTarget k)
noncomputable def rationalDifferentialFromTarget :
    Differential k (RationalInvolutionTarget k) →ₗ[RationalInvolutionTarget k]
      Differential k (RatFunc k) :=
  KaehlerDifferential.map k k (RationalInvolutionTarget k) (RatFunc k)
noncomputable def rationalDifferentialInvolution
    (omega : Differential k (RatFunc k)) : Differential k (RatFunc k) :=
  rationalDifferentialFromTarget (k := k)
    (rationalDifferentialToTarget (k := k) omega)
theorem xAdic_valuation_rationalInvolution_eq_rationalInfinity_valuation
    (f : RatFunc k) :
    (xAdicPlace k).valuation (InverseAffinePlace.rationalInvolution k f) =
      (GlobalPlace.rationalInfinity k).valuation f := by
  by_cases hf : f = 0
  · subst f
    simp
  have hef : InverseAffinePlace.rationalInvolution k f ≠ 0 :=
    (map_ne_zero_iff _ (InverseAffinePlace.rationalInvolution k).injective).mpr hf
  have horder := xAdic_order_rationalInvolution_eq_rationalInfinity_order k f
  have hlog :
      WithZero.log ((xAdicPlace k).valuation
          (InverseAffinePlace.rationalInvolution k f)) =
        WithZero.log ((GlobalPlace.rationalInfinity k).valuation f) := by
    unfold GlobalPlace.order at horder
    omega
  calc
    (xAdicPlace k).valuation (InverseAffinePlace.rationalInvolution k f) =
        WithZero.exp (WithZero.log ((xAdicPlace k).valuation
          (InverseAffinePlace.rationalInvolution k f))) :=
      (WithZero.exp_log ((xAdicPlace k).valuation.ne_zero_iff.mpr hef)).symm
    _ = WithZero.exp
        (WithZero.log ((GlobalPlace.rationalInfinity k).valuation f)) := by
      rw [hlog]
    _ = (GlobalPlace.rationalInfinity k).valuation f :=
      WithZero.exp_log
        ((GlobalPlace.rationalInfinity k).valuation.ne_zero_iff.mpr hf)
noncomputable def rationalInfinityValuationRingEquivXAdic :
    (GlobalPlace.rationalInfinity k).valuationRing ≃+* (xAdicPlace k).valuationRing where
  toFun z := ⟨InverseAffinePlace.rationalInvolution k (z : RatFunc k), by
    rw [GlobalPlace.mem_valuationRing_iff,
      xAdic_valuation_rationalInvolution_eq_rationalInfinity_valuation]
    exact z.property⟩
  invFun z := ⟨(InverseAffinePlace.rationalInvolution k).symm (z : RatFunc k), by
    rw [GlobalPlace.mem_valuationRing_iff]
    have h := xAdic_valuation_rationalInvolution_eq_rationalInfinity_valuation
      (k := k) ((InverseAffinePlace.rationalInvolution k).symm (z : RatFunc k))
    rw [(InverseAffinePlace.rationalInvolution k).apply_symm_apply] at h
    rw [← h]
    exact z.property⟩
  left_inv z := by
    apply Subtype.ext
    exact (InverseAffinePlace.rationalInvolution k).symm_apply_apply (z : RatFunc k)
  right_inv z := by
    apply Subtype.ext
    exact (InverseAffinePlace.rationalInvolution k).apply_symm_apply (z : RatFunc k)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul _ _ _
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
instance rationalInfinityValuationRingEquivXAdic_isLocalHom :
    IsLocalHom
      (rationalInfinityValuationRingEquivXAdic (k := k)).toRingHom :=
  ⟨fun x hx => by
    simpa using hx.map
      (rationalInfinityValuationRingEquivXAdic (k := k)).symm.toRingHom⟩
noncomputable def rationalInfinityResidueEquivXAdic :
    (GlobalPlace.rationalInfinity k).residueField ≃+* (xAdicPlace k).residueField :=
  IsLocalRing.ResidueField.mapEquiv
    (rationalInfinityValuationRingEquivXAdic (k := k))
end QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport


