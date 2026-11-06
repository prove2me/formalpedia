-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:31:30.520202+00:00
-- url     : https://prove2.me/theorems/91e3338d-be62-45e9-8a88-9b0c05f3e52c
-- title:
--   Residue
-- statement:
--   Definitions and structural lemmas for Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/Residue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_uniformizerLogDifferentialClass_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
namespace Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
noncomputable def uniformizerDerivativeResidueEquiv
    (P : GlobalPlace k F) :
    localResidueLine P ≃ₗ[P.valuationRing] GlobalPlace.residueField P :=
  localResidueLineEquivResidueField_ofPrincipalCutoff (k := k) (F := F) P
    (functionFieldDerivation (k := k) (F := F)
      (P.uniformizerInValuationRing : F))
    (uniformizerDerivative_isLocalDerivativeLatticePrincipalCutoff
      (k := k) (F := F) P)
noncomputable def uniformizerResidueNormalizationUnit
    (P : GlobalPlace k F) : (GlobalPlace.residueField P)ˣ :=
  Units.mk0
    (uniformizerDerivativeResidueEquiv (k := k) (F := F) P
      (uniformizerLogDifferentialClass (k := k) (F := F) P))
    ((uniformizerDerivativeResidueEquiv (k := k) (F := F) P).map_ne_zero_iff.mpr
      (uniformizerLogDifferentialClass_ne_zero (k := k) (F := F) P))
noncomputable def simplePoleResidueEquiv (P : GlobalPlace k F) :
    localResidueLine P ≃ₗ[P.valuationRing] GlobalPlace.residueField P :=
  (uniformizerDerivativeResidueEquiv (k := k) (F := F) P).trans
    (Units.mulLeftLinearEquiv P.valuationRing (GlobalPlace.residueField P)
      ((uniformizerResidueNormalizationUnit (k := k) (F := F) P)⁻¹))
noncomputable def simplePoleResidue (P : GlobalPlace k F) :
    simplePoleDifferentialLattice P →ₗ[P.valuationRing]
      GlobalPlace.residueField P :=
  (simplePoleResidueEquiv (k := k) (F := F) P).toLinearMap.comp
    (regularDifferentialSubmoduleOfSimplePole P).mkQ
end Differential
end QEC.Coding.AlgebraicGeometry


