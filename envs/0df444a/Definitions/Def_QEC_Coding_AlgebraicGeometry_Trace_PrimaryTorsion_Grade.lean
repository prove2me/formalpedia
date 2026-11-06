-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Grade
-- name    : QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_Grade
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:24:46.564648+00:00
-- url     : https://prove2.me/theorems/98abdc79-b99f-48a5-8cfb-2c5dd9c34389
-- title:
--   Grade
-- statement:
--   Definitions and structural lemmas for Grade, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PrimaryTorsion/Grade.lean

import Mathlib.Algebra.Module.Torsion.Basic
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
def primaryTorsionLayer (p : Ideal R) (M : Type*) [AddCommGroup M]
    [Module R M] (i : ℕ) : Submodule R M :=
  Submodule.torsionBySet R M (p ^ i : Ideal R)
def primaryTorsionPreviousLayer (p : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] (i : ℕ) :
    Submodule R (primaryTorsionLayer p M (i + 1)) :=
  (primaryTorsionLayer p M i).comap
    (primaryTorsionLayer p M (i + 1)).subtype
abbrev primaryTorsionGrade (p : Ideal R) (M : Type*) [AddCommGroup M]
    [Module R M] (i : ℕ) :=
  primaryTorsionLayer p M (i + 1) ⧸
    primaryTorsionPreviousLayer p M i
theorem primaryTorsionGrade_annihilated (p : Ideal R) (i : ℕ) :
    Module.IsTorsionBySet R (primaryTorsionGrade p M i) p := by
  rw [Module.isTorsionBySet_quotient_iff]
  intro x r hr
  change (r : R) • (x : M) ∈ primaryTorsionLayer p M i
  rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff]
  intro a
  have har : (a : R) * (r : R) ∈ p ^ (i + 1) := by
    rw [pow_succ]
    exact Ideal.mul_mem_mul a.property hr
  have hx : ((a : R) * (r : R)) • (x : M) = 0 :=
    (Submodule.mem_torsionBySet_iff (R := R)
      (s := (p ^ (i + 1) : Ideal R)) (x : M)).mp x.property ⟨_, har⟩
  simpa only [smul_smul] using hx
@[implicit_reducible]
noncomputable def primaryTorsionGradeModule (p : Ideal R) (i : ℕ) :
    Module (R ⧸ p) (primaryTorsionGrade p M i) :=
  (primaryTorsionGrade_annihilated (M := M) p i).module
theorem primaryTorsionLayer_invariant (p : Ideal R)
    (f : M →ₗ[R] M) (i : ℕ) :
    primaryTorsionLayer p M i ≤
      (primaryTorsionLayer p M i).comap f := by
  intro x hx
  rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff] at hx
  change f x ∈ primaryTorsionLayer p M i
  rw [primaryTorsionLayer, Submodule.mem_torsionBySet_iff]
  intro a
  rw [← f.map_smul, hx a, map_zero]
def primaryTorsionLayerEndomorphism (p : Ideal R) (f : M →ₗ[R] M)
    (i : ℕ) :
    primaryTorsionLayer p M i →ₗ[R] primaryTorsionLayer p M i :=
  (f.domRestrict (primaryTorsionLayer p M i)).codRestrict
    (primaryTorsionLayer p M i)
      (fun x => primaryTorsionLayer_invariant p f i x.property)
theorem primaryTorsionPreviousLayer_invariant (p : Ideal R)
    (f : M →ₗ[R] M) (i : ℕ) :
    primaryTorsionPreviousLayer p M i ≤
      (primaryTorsionPreviousLayer p M i).comap
        (primaryTorsionLayerEndomorphism p f (i + 1)) := by
  intro x hx
  change f (x : M) ∈ primaryTorsionLayer p M i
  exact primaryTorsionLayer_invariant p f i hx
def primaryTorsionGradeEndomorphismR (p : Ideal R)
    (f : M →ₗ[R] M) (i : ℕ) :
    primaryTorsionGrade p M i →ₗ[R] primaryTorsionGrade p M i :=
  (primaryTorsionPreviousLayer p M i).mapQ
    (primaryTorsionPreviousLayer p M i)
    (primaryTorsionLayerEndomorphism p f (i + 1))
    (primaryTorsionPreviousLayer_invariant p f i)
noncomputable def primaryTorsionGradeEndomorphism (p : Ideal R)
    (f : M →ₗ[R] M) (i : ℕ) :
    letI := primaryTorsionGradeModule (M := M) p i
    primaryTorsionGrade p M i →ₗ[R ⧸ p] primaryTorsionGrade p M i := by
  let h := primaryTorsionGrade_annihilated (M := M) p i
  letI : Module (R ⧸ p) (primaryTorsionGrade p M i) := h.module
  let fR := primaryTorsionGradeEndomorphismR p f i
  exact
    { toFun := fR
      map_add' := fR.map_add
      map_smul' := by
        intro c x
        induction c using Quotient.inductionOn' with
        | _ r =>
            change fR (Ideal.Quotient.mk p r • x) =
              Ideal.Quotient.mk p r • fR x
            rw [Module.IsTorsionBySet.mk_smul h,
              Module.IsTorsionBySet.mk_smul h]
            exact fR.map_smul r x }
end QEC.Coding.AlgebraicGeometry


