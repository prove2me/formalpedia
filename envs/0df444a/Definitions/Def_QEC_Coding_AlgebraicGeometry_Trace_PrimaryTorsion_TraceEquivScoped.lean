-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceEquivScoped
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:41:46.376315+00:00
-- url     : https://prove2.me/theorems/0299d56b-2dd8-4fb5-8498-25859155bc1c
-- title:
--   Trace Equiv
-- statement:
--   Definitions and structural lemmas for Trace Equiv, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceEquiv.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
theorem traceEquiv_primaryTorsionLayer_map_equiv (p : Ideal R)
    (e : M ≃ₗ[R] N) (i : ℕ) :
    (primaryTorsionLayer p M i).map (e : M →ₗ[R] N) =
      primaryTorsionLayer p N i := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ primaryTorsionLayer p M i := hx
    rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff] at hx'
    have hy' : e x ∈
        Submodule.torsionBySet R N (p ^ i : Ideal R) := by
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      rw [← e.map_smul, hx' a, map_zero]
    exact hy'
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff] at hy
    have hx' : e.symm y ∈
        Submodule.torsionBySet R M (p ^ i : Ideal R) := by
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      apply e.injective
      rw [e.map_smul, e.apply_symm_apply, map_zero]
      exact hy a
    exact hx'
noncomputable def primaryTorsionLayerEquiv (p : Ideal R)
    (e : M ≃ₗ[R] N) (i : ℕ) :
    primaryTorsionLayer p M i ≃ₗ[R] primaryTorsionLayer p N i :=
  e.ofSubmodules _ _ (traceEquiv_primaryTorsionLayer_map_equiv p e i)
def traceEquiv_primaryTorsionPreviousLayerAt (p : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] (i : ℕ) :
    Submodule R (primaryTorsionLayer p M (i + 1)) :=
  (primaryTorsionLayer p M i).comap
    (primaryTorsionLayer p M (i + 1)).subtype
theorem traceEquiv_primaryTorsionPreviousLayerAt_map_equiv (p : Ideal R)
    (e : M ≃ₗ[R] N) (i : ℕ) :
    (traceEquiv_primaryTorsionPreviousLayerAt p M i).map
        (primaryTorsionLayerEquiv p e (i + 1) :
          primaryTorsionLayer p M (i + 1) →ₗ[R]
            primaryTorsionLayer p N (i + 1)) =
      traceEquiv_primaryTorsionPreviousLayerAt p N i := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e (x : M) ∈ primaryTorsionLayer p N i
    rw [← traceEquiv_primaryTorsionLayer_map_equiv p e i]
    exact Submodule.mem_map_of_mem hx
  · intro hy
    refine ⟨(primaryTorsionLayerEquiv p e (i + 1)).symm y, ?_,
      (primaryTorsionLayerEquiv p e (i + 1)).apply_symm_apply y⟩
    change e.symm (y : N) ∈ primaryTorsionLayer p M i
    rw [← traceEquiv_primaryTorsionLayer_map_equiv p e.symm i]
    exact Submodule.mem_map_of_mem hy
noncomputable def traceEquiv_primaryTorsionGradeEquivR (p : Ideal R)
    (e : M ≃ₗ[R] N) (i : ℕ) :
    primaryTorsionGrade p M i ≃ₗ[R] primaryTorsionGrade p N i := by
  change
    (primaryTorsionLayer p M (i + 1) ⧸
        traceEquiv_primaryTorsionPreviousLayerAt p M i) ≃ₗ[R]
      (primaryTorsionLayer p N (i + 1) ⧸
        traceEquiv_primaryTorsionPreviousLayerAt p N i)
  exact Submodule.Quotient.equiv
    (traceEquiv_primaryTorsionPreviousLayerAt p M i)
    (traceEquiv_primaryTorsionPreviousLayerAt p N i)
    (primaryTorsionLayerEquiv p e (i + 1))
    (traceEquiv_primaryTorsionPreviousLayerAt_map_equiv p e i)
noncomputable def primaryTorsionGradeEquiv (p : Ideal R)
    (e : M ≃ₗ[R] N) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    primaryTorsionGrade p M i ≃ₗ[R ⧸ p]
      primaryTorsionGrade p N i := by
  let hM := primaryTorsionGrade_annihilated (M := M) p i
  let hN := primaryTorsionGrade_annihilated (M := N) p i
  letI : Module (R ⧸ p) (primaryTorsionGrade p M i) := hM.module
  letI : Module (R ⧸ p) (primaryTorsionGrade p N i) := hN.module
  let eR := traceEquiv_primaryTorsionGradeEquivR p e i
  exact
    { toEquiv := eR.toEquiv
      map_add' := eR.map_add
      map_smul' := by
        intro c x
        induction c using Quotient.inductionOn' with
        | _ r =>
            change eR (Ideal.Quotient.mk p r • x) =
              Ideal.Quotient.mk p r • eR x
            rw [Module.IsTorsionBySet.mk_smul hM,
              Module.IsTorsionBySet.mk_smul hN]
            exact eR.map_smul r x }
end QEC.Coding.AlgebraicGeometry


