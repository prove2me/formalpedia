-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalLogarithmicDifferential
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_LocalLogarithmicDifferential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:16:14.312195+00:00
-- url     : https://prove2.me/theorems/91c4e612-90c2-42e1-9481-6f6ac9fce198
-- title:
--   Local Logarithmic Differential
-- statement:
--   Definitions and structural lemmas for Local Logarithmic Differential, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalLogarithmicDifferential.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differential_mem_localDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_localDifferentialLattice_le_simplePoleDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_differential_mul
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
namespace Differential
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
noncomputable def logarithmicDifferential (f : F) : Differential k F :=
  f⁻¹ • differential k F f
theorem logarithmicDifferential_mul (f g : F) (hf : f ≠ 0) (hg : g ≠ 0) :
    logarithmicDifferential (k := k) (F := F) (f * g) =
      logarithmicDifferential (k := k) (F := F) f +
        logarithmicDifferential (k := k) (F := F) g := by
  rw [logarithmicDifferential, logarithmicDifferential,
    logarithmicDifferential, differential_mul, smul_add, smul_smul,
    smul_smul, add_comm]
  congr 1 <;> field_simp
theorem logarithmicDifferential_mem_localDifferentialLattice_of_unit
    (P : GlobalPlace k F) (u : P.valuationRingˣ) :
    logarithmicDifferential (k := k) (F := F) (u : F) ∈
      localDifferentialLattice P := by
  have hdifferential := differential_mem_localDifferentialLattice
    (k := k) (F := F) P (u : P.valuationRing)
  have hsmul := (localDifferentialLattice P).smul_mem
    (↑(u⁻¹) : P.valuationRing) hdifferential
  rw [logarithmicDifferential]
  have hinv :
      P.valuationRing.subtype (↑(u⁻¹) : P.valuationRing) = (u : F)⁻¹ :=
    map_units_inv P.valuationRing.subtype u
  rw [← hinv]
  change (↑(u⁻¹) : P.valuationRing) • differential k F (u : F) ∈
    localDifferentialLattice P
  exact hsmul
noncomputable def uniformizerLogDifferential (P : GlobalPlace k F) :
    simplePoleDifferentialLattice P := by
  refine ⟨logarithmicDifferential (k := k) (F := F)
    (P.uniformizerInValuationRing : F), ?_⟩
  change P.uniformizerInValuationRing •
      logarithmicDifferential (k := k) (F := F)
        (P.uniformizerInValuationRing : F) ∈ localDifferentialLattice P
  rw [logarithmicDifferential, ← smul_assoc]
  change ((P.uniformizerInValuationRing : F) *
      (P.uniformizerInValuationRing : F)⁻¹) •
        differential k F (P.uniformizerInValuationRing : F) ∈
          localDifferentialLattice P
  rw [mul_inv_cancel₀, one_smul]
  · exact differential_mem_localDifferentialLattice
      (k := k) (F := F) P P.uniformizerInValuationRing
  · simpa [GlobalPlace.uniformizerInValuationRing, localParameter] using
      localParameter_ne_zero (k := k) (F := F) P
noncomputable def unitMulUniformizerLogDifferential
    (P : GlobalPlace k F) (u : P.valuationRingˣ) :
    simplePoleDifferentialLattice P := by
  have hu : (u : F) ≠ 0 := by
    intro hzero
    apply Units.ne_zero u
    apply Subtype.ext
    exact hzero
  have hpi : (P.uniformizerInValuationRing : F) ≠ 0 := by
    simpa [GlobalPlace.uniformizerInValuationRing, localParameter] using
      localParameter_ne_zero (k := k) (F := F) P
  refine ⟨logarithmicDifferential (k := k) (F := F)
    ((u : F) * (P.uniformizerInValuationRing : F)), ?_⟩
  rw [logarithmicDifferential_mul (k := k) (F := F) _ _ hu hpi]
  exact (simplePoleDifferentialLattice P).add_mem
    (localDifferentialLattice_le_simplePoleDifferentialLattice
      (k := k) (F := F) P
      (logarithmicDifferential_mem_localDifferentialLattice_of_unit
        (k := k) (F := F) P u))
    (uniformizerLogDifferential (k := k) (F := F) P).property
noncomputable def uniformizerLogDifferentialClass (P : GlobalPlace k F) :
    localResidueLine P :=
  Submodule.Quotient.mk (uniformizerLogDifferential (k := k) (F := F) P)
end Differential
end QEC.Coding.AlgebraicGeometry


