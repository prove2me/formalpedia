-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorTraceResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorTraceResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:40:56.657631+00:00
-- url     : https://prove2.me/theorems/8882895a-46c4-4c8d-88c0-bf7fb5295a78
-- title:
--   Factor Trace Residue
-- statement:
--   Definitions and structural lemmas for Factor Trace Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorTraceResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorResidueTransport
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
noncomputable local instance directFactorTraceResidue_constantAlgebra : Algebra k F := AffinePlace.constantAlgebra k F
attribute [local instance] directFactorTraceResidue_constantAlgebra
noncomputable local instance _p2m_local_instance_49470eb06b_39 : IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))
abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F
local instance _p2m_local_instance_49470eb06b_49 : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
open DirectIntegralDifferentialResidue DirectFactorResidueTransport
noncomputable def directFactorBaseResidueMap
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    p.asIdeal.ResidueField →+*
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residueField := by
  letI : (P : Ideal (B k F)).IsMaximal :=
    (Ideal.Factors.isPrime p.asIdeal P).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal P)
  letI : Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime (P : Ideal (B k F))) :=
    Localization.AtPrime.algebraOfLiesOver p.asIdeal (P : Ideal (B k F))
  exact (directFactorResidueEquiv k F p P).toRingHom.comp
    (algebraMap p.asIdeal.ResidueField (P : Ideal (B k F)).ResidueField)
noncomputable def directFactorPlaceTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (x : (AffinePlace.globalPlace k F
      (directFactorPlace k F p P)).residueField) :
    p.asIdeal.ResidueField := by
  letI : Algebra p.asIdeal.ResidueField
      (AffinePlace.globalPlace k F
        (directFactorPlace k F p P)).residueField :=
    (directFactorBaseResidueMap k F p P).toAlgebra
  exact Algebra.trace p.asIdeal.ResidueField
    (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residueField x
end QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue


