-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
-- name    : GroundTheory_AutomorphicForms_QuadraticConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:44.736695+00:00
-- url     : https://prove2.me/theorems/2fb66f90-e87e-4da4-843c-4fe62ecf834c
-- title:
--   Quadratic Conj
-- statement:
--   Definitions and structural lemmas for Quadratic Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/QuadraticConj.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open Module
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E]
noncomputable def conjLinear : E →ₗ[F] E :=
  (Algebra.linearMap F E).comp (Algebra.trace F E) - LinearMap.id
variable {F E}
theorem conjLinear_apply (x : E) :
    conjLinear F E x = algebraMap F E (Algebra.trace F E x) - x := rfl
variable [Algebra.IsQuadraticExtension F E]
theorem trace_algebraMap_quadratic (c : F) : Algebra.trace F E (algebraMap F E c) = 2 * c := by
  rw [Algebra.trace_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two, nsmul_eq_mul]
  norm_num
theorem conjLinear_algebraMap (c : F) : conjLinear F E (algebraMap F E c) = algebraMap F E c := by
  rw [conjLinear_apply, trace_algebraMap_quadratic, map_mul, map_ofNat]
  ring
theorem conjLinear_one : conjLinear F E 1 = 1 := by
  simpa using conjLinear_algebraMap (F := F) (E := E) 1
omit [Algebra.IsQuadraticExtension F E] in

theorem linearIndependent_one_of_not_mem [Nontrivial E] {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : LinearIndependent F ![1, x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    refine ⟨?_, rfl⟩
    by_contra hs
    exact one_ne_zero ((smul_eq_zero.mp hst).resolve_left hs)
  · exfalso
    apply hx
    refine ⟨-(s / t), ?_⟩
    have : t • x = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
    rw [Algebra.algebraMap_eq_smul_one]
    have h2 : x = t⁻¹ • (t • x) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
theorem nontrivial_quadratic (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Algebra.IsQuadraticExtension K A] : Nontrivial A :=
  Module.nontrivial_of_finrank_pos (R := K) (by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two]; norm_num)
noncomputable def basisOneOf {x : E} (hx : x ∉ Set.range (algebraMap F E)) : Basis (Fin 2) F E :=
  haveI := nontrivial_quadratic F E
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_of_not_mem hx)
    (by rw [Algebra.IsQuadraticExtension.finrank_eq_two, Fintype.card_fin])
theorem basisOneOf_zero {x : E} (hx : x ∉ Set.range (algebraMap F E)) : basisOneOf hx 0 = 1 := by
  simp [basisOneOf]
theorem basisOneOf_one {x : E} (hx : x ∉ Set.range (algebraMap F E)) : basisOneOf hx 1 = x := by
  simp [basisOneOf]
theorem sq_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    x * x = algebraMap F E ((basisOneOf hx).repr (x * x) 0) +
      algebraMap F E ((basisOneOf hx).repr (x * x) 1) * x := by
  conv_lhs => rw [← (basisOneOf hx).sum_repr (x * x)]
  rw [Fin.sum_univ_two, basisOneOf_zero, basisOneOf_one, Algebra.smul_def, Algebra.smul_def,
    mul_one]
theorem repr_self_zero {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    (basisOneOf hx).repr x 0 = 0 := by
  have h := (basisOneOf hx).repr_self 1
  rw [basisOneOf_one] at h
  rw [h]; simp
theorem trace_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    Algebra.trace F E x = (basisOneOf hx).repr (x * x) 1 := by
  rw [Algebra.trace_eq_matrix_trace (basisOneOf hx), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisOneOf_zero,
    basisOneOf_one, mul_one, repr_self_zero, zero_add]
theorem conjLinear_mul_self (x : E) :
    conjLinear F E (x * x) = conjLinear F E x * conjLinear F E x := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [← map_mul, conjLinear_algebraMap, conjLinear_algebraMap, map_mul]
  · have hsq := sq_eq_of_not_mem hx
    have htr : Algebra.trace F E x = (basisOneOf hx).repr (x * x) 1 := trace_eq_of_not_mem hx
    have htr2 : Algebra.trace F E (x * x) = 2 * (basisOneOf hx).repr (x * x) 0 +
        (basisOneOf hx).repr (x * x) 1 * (basisOneOf hx).repr (x * x) 1 := by
      conv_lhs => rw [hsq]
      rw [map_add, trace_algebraMap_quadratic, ← Algebra.smul_def, map_smul, htr, smul_eq_mul]
    rw [conjLinear_apply, conjLinear_apply, htr2, htr]
    simp only [map_add, map_mul, map_ofNat]
    linear_combination (-2 : E) * hsq
theorem conjLinear_mul (x y : E) :
    conjLinear F E (x * y) = conjLinear F E x * conjLinear F E y := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [conjLinear_algebraMap, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
  · have key : (conjLinear F E).comp (LinearMap.mulLeft F x) =
        (LinearMap.mulLeft F (conjLinear F E x)).comp (conjLinear F E) := by
      refine (basisOneOf hx).ext fun i => ?_
      fin_cases i
      · simp [basisOneOf_zero, conjLinear_one]
      · simp only [Fin.mk_one, basisOneOf_one, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.mulLeft_apply]
        exact conjLinear_mul_self x
    exact LinearMap.congr_fun key y
theorem conjLinear_conjLinear (x : E) : conjLinear F E (conjLinear F E x) = x := by
  rw [conjLinear_apply, conjLinear_apply x, map_sub, trace_algebraMap_quadratic, map_sub,
    map_mul, map_ofNat]
  ring
variable (F E) in

noncomputable def conj : E ≃ₐ[F] E :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofInvolutive (conjLinear F E) (fun x => conjLinear_conjLinear x))
    conjLinear_one conjLinear_mul
end GroundTheory.Automorphic


