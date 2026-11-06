-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:35:57.511808+00:00
-- url     : https://prove2.me/theorems/72240f8e-7daa-4cc6-b151-a0905d06be12
-- title:
--   Integral Differential Residue
-- statement:
--   Definitions and structural lemmas for Integral Differential Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralDifferentialResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_valuation_algebraMap_of_integral
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue
open scoped Polynomial RatFunc nonZeroDivisors
open Submodule.IsPrincipal UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
noncomputable local instance _p2m_local_instance_3e6bb6d2a4_37 : Algebra k F := AffinePlace.constantAlgebra k F
noncomputable local instance _p2m_local_instance_3e6bb6d2a4_39 : IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))
abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F
local instance _p2m_local_instance_3e6bb6d2a4_49 : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
noncomputable def directFactorPlace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    AffinePlace.carrier k F :=
  { asIdeal := (P : Ideal (B k F))
    isPrime := Ideal.Factors.isPrime p.asIdeal P
    ne_bot := Ideal.Factors.ne_bot p.asIdeal P }
omit [Finite k] in
@[simp]
theorem directFactorPlace_asIdeal
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    (directFactorPlace k F p P).asIdeal = (P : Ideal (B k F)) :=
  rfl
noncomputable def directIntegralToValuationRing
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    B k F →+*
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).valuationRing :=
  (algebraMap (B k F) F).codRestrict
    (AffinePlace.globalPlace k F (directFactorPlace k F p P)).valuationRing
    fun b => by
      change AffinePlace.valuation k F (directFactorPlace k F p P)
        (algebraMap (B k F) F b) ≤ 1
      rw [AffinePlace.valuation_algebraMap_of_integral k F
        (directFactorPlace k F p P) b]
      exact (directFactorPlace k F p P).intValuation_le_one b
@[simp]
theorem coe_directIntegralToValuationRing
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    ((directIntegralToValuationRing k F p P b :
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).valuationRing) : F) =
      algebraMap (B k F) F b :=
  rfl
theorem directBaseGenerator_ne_zero
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) :
    algebraMap (R k) F (generator p.asIdeal) ≠ 0 := by
  have hq : generator p.asIdeal ≠ 0 := by
    intro hzero
    apply p.ne_bot
    exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p.asIdeal).mpr hzero
  simpa only [map_zero] using
    (_root_.FunctionField.algebraMap_injective k F).ne hq
noncomputable def directIntegralLogarithmicDifferentialAtSimplePole
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    Differential.simplePoleDifferentialLattice
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)) :=
  directIntegralToValuationRing k F p P b •
    Differential.logarithmicDifferentialAtSimplePole
      (k := k) (F := F)
      (AffinePlace.globalPlace k F (directFactorPlace k F p P))
      (algebraMap (R k) F (generator p.asIdeal))
      (directBaseGenerator_ne_zero k F p)
end QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue


