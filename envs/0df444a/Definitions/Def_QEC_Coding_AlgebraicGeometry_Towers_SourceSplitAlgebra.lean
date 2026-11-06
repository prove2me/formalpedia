-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:54:49.902755+00:00
-- url     : https://prove2.me/theorems/6f4a4f87-6226-427b-9d89-af04327c95a6
-- title:
--   Source Split Algebra
-- statement:
--   Definitions and structural lemmas for Source Split Algebra, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitAlgebra.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_f256_card
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
theorem sourceAlgebraMap_trace_eq_f256ArtinSchreier (x : F256) :
    algebraMap F16 F256 (Algebra.trace F16 F256 x) =
      f256ArtinSchreier x := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow]
  simp only [f256_finrank_over_f16, Nat.card_eq_fintype_card, f16_card]
  norm_num [Finset.sum_range_succ, f256ArtinSchreier_apply, add_comm]
theorem sourceSplitPoint_denominator_ne_zero
    (a : GaloisBaseSplitPoint) :
    (a : F256) ^ 15 + 1 ≠ 0 := by
  intro hzero
  apply a.property
  rw [galoisBaseWValue_eq]
  calc
    (a : F256) ^ 16 + a = a * (a ^ 15 + 1) := by ring
    _ = 0 := by rw [hzero, mul_zero]
noncomputable def sourceSplitScalar
    (a : GaloisBaseSplitPoint) : F16 :=
  Algebra.norm F16 (a : F256) / Algebra.trace F16 F256 (a : F256)
theorem algebraMap_sourceSplitScalar
    (a : GaloisBaseSplitPoint) :
    algebraMap F16 F256 (sourceSplitScalar a) =
      sourceStepRhs (a : F256) := by
  have hnorm : algebraMap F16 F256 (Algebra.norm F16 (a : F256)) =
      (a : F256) ^ 17 := by
    rw [FiniteField.algebraMap_norm_eq_pow]
    norm_num [Nat.card_eq_fintype_card, f16_card, f256_card]
  have htrace := sourceAlgebraMap_trace_eq_f256ArtinSchreier (a : F256)
  have hw : (a : F256) ^ 16 + a ≠ 0 := by
    simpa only [galoisBaseWValue_eq] using a.property
  have hden := sourceSplitPoint_denominator_ne_zero a
  rw [sourceSplitScalar, map_div₀, hnorm, htrace,
    f256ArtinSchreier_apply, sourceStepRhs]
  field_simp [hw, hden]
noncomputable def sourceStepArtinSchreierRoot
    (a : GaloisBaseSplitPoint) : F256 :=
  Classical.choose
    (Algebra.trace_surjective F16 F256 (sourceSplitScalar a))
theorem sourceStepArtinSchreierRoot_trace
    (a : GaloisBaseSplitPoint) :
    Algebra.trace F16 F256 (sourceStepArtinSchreierRoot a) =
      sourceSplitScalar a :=
  Classical.choose_spec
    (Algebra.trace_surjective F16 F256 (sourceSplitScalar a))
theorem sourceStepArtinSchreierRoot_spec (a : GaloisBaseSplitPoint) :
    f256ArtinSchreier (sourceStepArtinSchreierRoot a) =
      sourceStepRhs (a : F256) := by
  calc
    f256ArtinSchreier (sourceStepArtinSchreierRoot a) =
        algebraMap F16 F256
          (Algebra.trace F16 F256 (sourceStepArtinSchreierRoot a)) :=
      (sourceAlgebraMap_trace_eq_f256ArtinSchreier _).symm
    _ = algebraMap F16 F256 (sourceSplitScalar a) := by
      rw [sourceStepArtinSchreierRoot_trace]
    _ = sourceStepRhs (a : F256) := algebraMap_sourceSplitScalar a
noncomputable def sourceStepArtinSchreierRoots
    (a : GaloisBaseSplitPoint) : Finset F256 :=
  Finset.univ.filter fun y =>
    f256ArtinSchreier y = sourceStepRhs (a : F256)
noncomputable def sourceStepArtinSchreierKernelEquivRoots
    (a : GaloisBaseSplitPoint) :
    LinearMap.ker f256ArtinSchreier ≃
      ↥(sourceStepArtinSchreierRoots a) where
  toFun y := ⟨sourceStepArtinSchreierRoot a + y, by
    simp only [sourceStepArtinSchreierRoots, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [map_add, sourceStepArtinSchreierRoot_spec, y.property, add_zero]⟩
  invFun y := ⟨y - sourceStepArtinSchreierRoot a, by
    change f256ArtinSchreier (y - sourceStepArtinSchreierRoot a) = 0
    rw [map_sub, sourceStepArtinSchreierRoot_spec]
    have hy : f256ArtinSchreier (y : F256) =
        sourceStepRhs (a : F256) := by
      simpa only [sourceStepArtinSchreierRoots, Finset.mem_filter,
        Finset.mem_univ, true_and] using y.property
    rw [hy, sub_self]⟩
  left_inv y := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
noncomputable def sourceStepResidualPolynomial
    (a : GaloisBaseSplitPoint) : F256[X] :=
  X ^ 16 + (X - C (sourceStepRhs (a : F256)))
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


