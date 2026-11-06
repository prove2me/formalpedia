-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:42:01.493201+00:00
-- url     : https://prove2.me/theorems/b4fdc834-1236-4524-99c0-1de713a1ee8e
-- title:
--   Factor Semilocal Logarithmic Residue
-- statement:
--   Definitions and structural lemmas for Factor Semilocal Logarithmic Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalLogarithmicResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalMultiplier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorTraceResidue
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
namespace QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
noncomputable local instance _p2m_local_instance_af27c6fddd_36 : Algebra k F := AffinePlace.constantAlgebra k F
noncomputable local instance _p2m_local_instance_af27c6fddd_38 : IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))
abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F
local instance _p2m_local_instance_af27c6fddd_48 : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
open DirectIntegralDifferentialResidue DirectFactorTraceResidue
noncomputable def directFactorSemilocalLogarithmicDifferentialAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (t : B k F) (ht : t ≠ 0) (b : B k F) :
    Differential.simplePoleDifferentialLattice
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)) :=
  directIntegralToValuationRing k F p P b •
    Differential.logarithmicDifferentialAtSimplePole
      (k := k) (F := F)
      (AffinePlace.globalPlace k F (directFactorPlace k F p P))
      (algebraMap (B k F) F t)
      ((map_ne_zero_iff _ (IsFractionRing.injective (B k F) F)).mpr ht)
end QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue


