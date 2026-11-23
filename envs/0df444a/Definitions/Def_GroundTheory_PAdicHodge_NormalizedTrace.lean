-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
-- name    : GroundTheory_PAdicHodge_NormalizedTrace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:20.015771+00:00
-- url     : https://prove2.me/theorems/f327a571-0353-4bfc-97d7-0dd6064a650a
-- title:
--   Normalized Trace
-- statement:
--   Definitions and structural lemmas for Normalized Trace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
section General
variable (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
def normTraceF (y : Ω) : F := -(minpoly F y).nextCoeff / ((minpoly F y).natDegree : F)
def normTrace (y : Ω) : Ω := algebraMap F Ω (normTraceF F y)
@[simp]
theorem normTraceF_algebraMap (a : F) : normTraceF F (algebraMap F Ω a) = a := by
  rw [normTraceF, minpoly.eq_X_sub_C, nextCoeff_X_sub_C, natDegree_X_sub_C]
  simp
@[simp]
theorem normTrace_algebraMap (a : F) : normTrace F (algebraMap F Ω a) = algebraMap F Ω a := by
  rw [normTrace, normTraceF_algebraMap]
theorem normTraceF_eq_trace_div [CharZero F] (L : Type*) [Field L] [Algebra F L] [Algebra L Ω]
    [IsScalarTower F L Ω] [FiniteDimensional F L] (y : L) :
    normTraceF F (algebraMap L Ω y) = Algebra.trace F L y / (finrank F L : F) := by
  have hy : IsIntegral F y := IsIntegral.of_finite F y
  haveI : FiniteDimensional F⟮y⟯ L := FiniteDimensional.right F F⟮y⟯ L
  rw [normTraceF, minpoly.algebraMap_eq (algebraMap L Ω).injective,
    trace_eq_finrank_mul_minpoly_nextCoeff, ← Module.finrank_mul_finrank F F⟮y⟯ L,
    IntermediateField.adjoin.finrank hy]
  have h1 : ((minpoly F y).natDegree : F) ≠ 0 :=
    Nat.cast_ne_zero.2 (minpoly.natDegree_pos hy).ne'
  have h2 : (finrank F⟮y⟯ L : F) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  push_cast
  field_simp
variable [CharZero F] [Algebra.IsIntegral F Ω]
theorem normTraceF_add (y z : Ω) : normTraceF F (y + z) = normTraceF F y + normTraceF F z := by
  haveI := IntermediateField.finiteDimensional_adjoin_pair
    (Algebra.IsIntegral.isIntegral (R := F) y) (Algebra.IsIntegral.isIntegral (R := F) z)
  have hy : y ∈ F⟮y, z⟯ := subset_adjoin F _ (by simp)
  have hz : z ∈ F⟮y, z⟯ := subset_adjoin F _ (by simp)
  have e := normTraceF_eq_trace_div F (Ω := Ω) F⟮y, z⟯
  have h1 := e ⟨y, hy⟩
  have h2 := e ⟨z, hz⟩
  have h3 := e (⟨y, hy⟩ + ⟨z, hz⟩)
  rw [LinearMap.map_add, add_div, ← h1, ← h2] at h3
  exact h3
theorem normTraceF_smul (a : F) (y : Ω) : normTraceF F (a • y) = a * normTraceF F y := by
  haveI := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) y)
  have e := normTraceF_eq_trace_div F (Ω := Ω) F⟮y⟯
  have h1 := e (AdjoinSimple.gen F y)
  have h2 := e (a • AdjoinSimple.gen F y)
  rw [LinearMap.map_smul, smul_eq_mul, mul_div_assoc, ← h1] at h2
  exact h2
def normTraceFₗ : Ω →ₗ[F] F where
  toFun := normTraceF F
  map_add' := normTraceF_add F
  map_smul' := normTraceF_smul F
def normTraceₗ : Ω →ₗ[F] Ω := (Algebra.linearMap F Ω).comp (normTraceFₗ F)
end General
section Transport
variable {Ω : Type*} [Field Ω]
end Transport
section Degree
variable {B₀ Ω : Type*} [Field B₀] [Field Ω] [Algebra B₀ Ω]
end Degree
section Norm
variable {p : ℕ} [Fact p.Prime]
end Norm
end
end GroundTheory.PAdicHodge


