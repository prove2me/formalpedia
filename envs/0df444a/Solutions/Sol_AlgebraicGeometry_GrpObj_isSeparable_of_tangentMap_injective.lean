-- Prove2me | solution 1 for AlgebraicGeometry.GrpObj.isSeparable_of_tangentMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T09:39:45.487431+00:00
-- url     : https://prove2.me/submissions/1129af2f-1bac-40a5-95e4-08162524b9b7

import Mathlib
import Definitions.Def_RPLib_F2_018

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsProper A.hom] [IsIntegral A.left]
    (ι₀ : 𝟙_ (Over (Spec (.of k))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))))
    (hι₀ : ι₀.left = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom))
    (φ : A ⟶ A) [IsMonHom φ]
    (hφ : ∀ t s : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) ⟶ A,
      ι₀ ≫ t = 1 → ι₀ ≫ s = 1 → t ≫ φ = s ≫ φ → t = s) :
    IsDominant φ.left ∧ Finite {c : 𝟙_ (Over (Spec (.of k))) ⟶ A // c ≫ φ = 1} ∧
      ∃ h : φ.left (genericPoint A.left) = genericPoint A.left,
        @Algebra.IsSeparable A.left.functionField A.left.functionField _ _
          (A.left.presheaf.stalkSpecializes (specializes_of_eq h) ≫
            φ.left.stalkMap (genericPoint A.left)).hom.toAlgebra ∧
        @Module.finrank A.left.functionField A.left.functionField _ _
          (A.left.presheaf.stalkSpecializes (specializes_of_eq h) ≫
            φ.left.stalkMap (genericPoint A.left)).hom.toAlgebra.toModule =
          Nat.card {c : 𝟙_ (Over (Spec (.of k))) ⟶ A // c ≫ φ = 1} := by
  have hι : ι₀ = RamanujanPetersson.IsogDegB.ι0 k := by
    ext1
    exact hι₀
  subst hι
  have hinj : Function.Injective (RamanujanPetersson.IsogDegB.dφ (A := A) φ) := by
    intro t s hts
    exact Subtype.ext (hφ t.1 s.1 (RamanujanPetersson.IsogDegB.tan_spec t)
      (RamanujanPetersson.IsogDegB.tan_spec s) (congrArg Subtype.val hts))
  obtain ⟨hdom, hsep, hdeg⟩ := RamanujanPetersson.IsogDegB.separable_of_injective φ hinj
  refine ⟨hdom, (RamanujanPetersson.IsogDegB.isDominant_iff_finite_ker φ).1 hdom,
    RamanujanPetersson.IsogDegA.map_genericPoint φ.left, hsep, ?_⟩
  rw [RamanujanPetersson.IsogDegA.degree_of_isDominant] at hdeg
  exact hdeg
