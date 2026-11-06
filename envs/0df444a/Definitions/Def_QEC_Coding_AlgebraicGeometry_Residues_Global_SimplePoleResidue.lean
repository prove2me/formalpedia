-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:34:26.137143+00:00
-- url     : https://prove2.me/theorems/e8f5482a-f60e-4150-ab32-6f64365d2bf2
-- title:
--   Simple Pole Residue
-- statement:
--   Definitions and structural lemmas for Simple Pole Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Global/SimplePoleResidue.lean

import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_localDifferentialLattice_iff_differentialOrder_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
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
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
namespace Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
omit [IsScalarTower k (RatFunc k) F] in
theorem residueField_finiteDimensional (P : GlobalPlace k F) :
    letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
    FiniteDimensional k P.residueField := by
  letI : Algebra (Polynomial k) F :=
    ((algebraMap (RatFunc k) F).comp
      (algebraMap (Polynomial k) (RatFunc k))).toAlgebra
  letI : IsScalarTower (Polynomial k) (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
  letI : Finite P.residueField := GlobalPlace.finite_residueField P
  exact (Module.finite_iff_finite).mpr inferInstance
noncomputable def simplePoleTraceResidue (P : GlobalPlace k F)
    (omega : Differential k F)
    (homega : omega ∈ simplePoleDifferentialLattice P) : k := by
  letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    residueField_finiteDimensional (k := k) (F := F) P
  exact Algebra.trace k P.residueField
    (simplePoleResidue (k := k) (F := F) P ⟨omega, homega⟩)
theorem simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
    (P : GlobalPlace k F) (omega : Differential k F)
    (homegaSimple : omega ∈ simplePoleDifferentialLattice P)
    (homegaRegular : omega ∈ localDifferentialLattice P) :
    simplePoleTraceResidue (k := k) (F := F) P omega homegaSimple = 0 := by
  letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    residueField_finiteDimensional (k := k) (F := F) P
  change Algebra.trace k P.residueField
      (simplePoleResidue (k := k) (F := F) P ⟨omega, homegaSimple⟩) = 0
  rw [simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
    (k := k) (F := F) P ⟨omega, homegaSimple⟩ homegaRegular, map_zero]
def IsGlobalSimplePole (omega : Differential k F) : Prop :=
  ∀ P : GlobalPlace k F, omega ∈ simplePoleDifferentialLattice P
noncomputable def globalSimplePoleResidueCoefficient
    (omega : Differential k F) (homega : IsGlobalSimplePole omega)
    (P : GlobalPlace k F) : k :=
  simplePoleTraceResidue (k := k) (F := F) P omega (homega P)
theorem globalSimplePoleResidueCoefficient_support_finite
    (omega : Differential k F) (homega : IsGlobalSimplePole omega) :
    (Function.support fun P : GlobalPlace k F =>
      globalSimplePoleResidueCoefficient (k := k) (F := F) omega homega P).Finite := by
  by_cases homegaZero : omega = 0
  · subst omega
    have hzero : (fun P : GlobalPlace k F =>
        globalSimplePoleResidueCoefficient (k := k) (F := F) 0 homega P) = 0 := by
      funext P
      exact simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
        (k := k) (F := F) P 0 (homega P) (localDifferentialLattice P).zero_mem
    rw [hzero]
    simp [Function.support]
  · refine (differentialOrder_support_finite (k := k) (F := F)
      omega homegaZero).subset ?_
    intro P hP
    simp only [Function.mem_support, ne_eq] at hP ⊢
    intro horder
    apply hP
    apply simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := F) P omega (homega P)
    apply (mem_localDifferentialLattice_iff_differentialOrder_nonnegative
      (k := k) (F := F) P omega homegaZero).mpr
    rw [horder]
noncomputable def globalSimplePoleResidue
    (omega : Differential k F) (homega : IsGlobalSimplePole omega) :
    GlobalPlace k F →₀ k :=
  Finsupp.ofSupportFinite
    (fun P => globalSimplePoleResidueCoefficient (k := k) (F := F) omega homega P)
    (globalSimplePoleResidueCoefficient_support_finite
      (k := k) (F := F) omega homega)
noncomputable def globalSimplePoleResidueSum
    (omega : Differential k F) (homega : IsGlobalSimplePole omega) : k :=
  (globalSimplePoleResidue (k := k) (F := F) omega homega).sum
    (fun _ residue => residue)
end Differential
end QEC.Coding.AlgebraicGeometry


