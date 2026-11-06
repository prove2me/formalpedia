-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_TraceFunctorial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:33:27.229656+00:00
-- url     : https://prove2.me/theorems/d72a5b25-e219-4af5-8d71-dd0f7dd54464
-- title:
--   Trace Functorial
-- statement:
--   Definitions and structural lemmas for Trace Functorial, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/TraceFunctorial.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Trace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
theorem primaryTorsionLayer_map_le (p : Ideal R)
    (f : M →ₗ[R] N) (i : ℕ) :
    primaryTorsionLayer p M i ≤
      (primaryTorsionLayer p N i).comap f := by
  intro x hx
  rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff] at hx
  change f x ∈ primaryTorsionLayer p N i
  rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff]
  intro a
  rw [← f.map_smul, hx a, map_zero]
def primaryTorsionLayerMap (p : Ideal R) (f : M →ₗ[R] N) (i : ℕ) :
    primaryTorsionLayer p M i →ₗ[R] primaryTorsionLayer p N i :=
  (f.domRestrict (primaryTorsionLayer p M i)).codRestrict
    (primaryTorsionLayer p N i)
      (fun x => primaryTorsionLayer_map_le p f i x.property)
def primaryTorsionPreviousLayerAt (p : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (i : ℕ) :
    Submodule R (primaryTorsionLayer p M (i + 1)) :=
  (primaryTorsionLayer p M i).comap
    (primaryTorsionLayer p M (i + 1)).subtype
theorem primaryTorsionPreviousLayer_map_le (p : Ideal R)
    (f : M →ₗ[R] N) (i : ℕ) :
    primaryTorsionPreviousLayerAt p M i ≤
      (primaryTorsionPreviousLayerAt p N i).comap
        (primaryTorsionLayerMap p f (i + 1)) := by
  intro x hx
  change f (x : M) ∈ primaryTorsionLayer p N i
  exact primaryTorsionLayer_map_le p f i hx
def primaryTorsionGradeMapR (p : Ideal R)
    (f : M →ₗ[R] N) (i : ℕ) :
    primaryTorsionGrade p M i →ₗ[R] primaryTorsionGrade p N i := by
  change
    (primaryTorsionLayer p M (i + 1) ⧸
        primaryTorsionPreviousLayerAt p M i) →ₗ[R]
      (primaryTorsionLayer p N (i + 1) ⧸
        primaryTorsionPreviousLayerAt p N i)
  exact (primaryTorsionPreviousLayerAt p M i).mapQ
    (primaryTorsionPreviousLayerAt p N i)
    (primaryTorsionLayerMap p f (i + 1))
    (primaryTorsionPreviousLayer_map_le p f i)
noncomputable def primaryTorsionGradeMap (p : Ideal R)
    (f : M →ₗ[R] N) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    letI := primaryTorsionGradeModule (M := N) p i
    primaryTorsionGrade p M i →ₗ[R ⧸ p] primaryTorsionGrade p N i := by
  let hM := primaryTorsionGrade_annihilated (M := M) p i
  let hN := primaryTorsionGrade_annihilated (M := N) p i
  letI : Module (R ⧸ p) (primaryTorsionGrade p M i) := hM.module
  letI : Module (R ⧸ p) (primaryTorsionGrade p N i) := hN.module
  let fR := primaryTorsionGradeMapR p f i
  exact
    { toFun := fR
      map_add' := fR.map_add
      map_smul' := by
        intro c x
        induction c using Quotient.inductionOn' with
        | _ r =>
            change fR (Ideal.Quotient.mk p r • x) =
              Ideal.Quotient.mk p r • fR x
            rw [Module.IsTorsionBySet.mk_smul hM,
              Module.IsTorsionBySet.mk_smul hN]
            exact fR.map_smul r x }
end QEC.Coding.AlgebraicGeometry


