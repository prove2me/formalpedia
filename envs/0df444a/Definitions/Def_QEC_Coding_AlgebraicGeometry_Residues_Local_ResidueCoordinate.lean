-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueCoordinate
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueCoordinate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:32:49.39042+00:00
-- url     : https://prove2.me/theorems/a392ca86-a7c2-41e1-847e-04dcba3b636f
-- title:
--   Residue Coordinate
-- statement:
--   Definitions and structural lemmas for Residue Coordinate, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/ResidueCoordinate.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
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
noncomputable def simplePoleResidueCoordinate (P : GlobalPlace k F) :
    simplePoleDifferentialLattice P →ₗ[P.valuationRing] P.valuationRing := by
  classical
  let pi : P.valuationRing := P.uniformizerInValuationRing
  let a : F := functionFieldDerivation (k := k) (F := F) (pi : F)
  let C : Differential k F →ₗ[F] F :=
    functionFieldDifferentialCoordinate (k := k) (F := F)
  have ha := uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
    (k := k) (F := F) P
  refine
    { toFun := fun omega => ?_
      map_add' := ?_
      map_smul' := ?_ }
  · have homega := omega.property
    change pi • (omega : Differential k F) ∈ localDifferentialLattice P at homega
    have hcoordinate :
        (pi : F) * C (omega : Differential k F) ∈
          localDerivativeLattice (k := k) (F := F) P := by
      have h := (mem_localDifferentialLattice_iff_coordinate_mem_localDerivativeLattice
        (k := k) (F := F) P (pi • (omega : Differential k F))).mp homega
      rw [LinearMap.map_smul_of_tower] at h
      exact h
    rw [ha.2.1] at hcoordinate
    let r : P.valuationRing :=
      Classical.choose (Submodule.mem_span_singleton.mp hcoordinate)
    have hr : r • a = (pi : F) * C (omega : Differential k F) :=
      Classical.choose_spec (Submodule.mem_span_singleton.mp hcoordinate)
    change (r : F) * a = (pi : F) * C (omega : Differential k F) at hr
    refine ⟨(pi : F) * C (omega : Differential k F) * a⁻¹, ?_⟩
    have hvalue :
        (pi : F) * C (omega : Differential k F) * a⁻¹ = (r : F) := by
      have ha_ne : a ≠ 0 := ha.1
      calc
        (pi : F) * C (omega : Differential k F) * a⁻¹ =
            ((r : F) * a) * a⁻¹ := by rw [← hr]
        _ = (r : F) := by
          rw [mul_assoc, mul_inv_cancel₀ ha_ne, mul_one]
    rw [hvalue]
    exact r.property
  · intro omega eta
    apply Subtype.ext
    change (pi : F) * C ((omega : Differential k F) + (eta : Differential k F)) *
        a⁻¹ =
      (pi : F) * C (omega : Differential k F) * a⁻¹ +
        (pi : F) * C (eta : Differential k F) * a⁻¹
    rw [map_add]
    ring
  · intro r omega
    apply Subtype.ext
    change (pi : F) * C ((r : F) • (omega : Differential k F)) * a⁻¹ =
      (r : F) * ((pi : F) * C (omega : Differential k F) * a⁻¹)
    rw [map_smul]
    simp only [smul_eq_mul]
    ring
end Differential
end QEC.Coding.AlgebraicGeometry


