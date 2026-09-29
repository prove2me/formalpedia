-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.irreducibleSpace_and_topologicalKrullDim_pullback_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/716210b7-7d13-570c-a838-65eeb0ce7045

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_irreducibleSpace_and_topologicalKrullDim_pullback_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem solution
    {K₁ : Type} [Field K₁] [IsAlgClosed K₁] {F : Type} [Field F] [Algebra K₁ F]
    (𝔐 : AlgebraicCurve.CurveModel K₁ F)
    {B : Type} [CommRing B] (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B))
    (sbar : Spec (CommRingCat.of K₁) ⟶ Spec (CommRingCat.of B))
    (e𝔐 : 𝔐.C ⟶ Limits.pullback πX sbar) [IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ Limits.pullback.snd πX sbar = 𝔐.toBase)
    (k : Type) [Field k] (j : K₁ →+* k) :
    IrreducibleSpace ↑(Limits.pullback πX (Spec.map (CommRingCat.ofHom j) ≫ sbar)) ∧
    topologicalKrullDim ↑(Limits.pullback πX (Spec.map (CommRingCat.ofHom j) ≫ sbar)) = 1 ∧
    LocallyOfFiniteType (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom j) ≫ sbar)) ∧
    QuasiCompact (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom j) ≫ sbar)) := by
  classical
  set y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K₁) := Spec.map (CommRingCat.ofHom j) with hy

  have heq : 𝔐.toBase ≫ 𝟙 _ = e𝔐 ≫ pullback.snd πX sbar := by rw [Category.comp_id, he𝔐]
  let m : pullback 𝔐.toBase y ⟶ pullback (pullback.snd πX sbar) y :=
    pullback.map 𝔐.toBase y (pullback.snd πX sbar) y e𝔐 (𝟙 _) (𝟙 _) heq (by simp)
  haveI : IsIso m := inferInstance
  let e : pullback 𝔐.toBase y ≅ pullback πX (y ≫ sbar) := asIso m ≪≫ pullbackLeftPullbackSndIso πX sbar y
  have hm : m ≫ pullback.snd (pullback.snd πX sbar) y = pullback.snd 𝔐.toBase y := by
    show pullback.lift _ _ _ ≫ _ = _
    rw [pullback.lift_snd, Category.comp_id]
  have hsnd : e.hom ≫ pullback.snd πX (y ≫ sbar) = pullback.snd 𝔐.toBase y := by
    simp only [e, Iso.trans_hom, asIso_hom, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, hm]
  have hsnd' : pullback.snd πX (y ≫ sbar) = e.inv ≫ pullback.snd 𝔐.toBase y := by
    rw [← hsnd, Iso.inv_hom_id_assoc]

  haveI hGI : GeometricallyIrreducible 𝔐.toBase :=
    AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed 𝔐.toBase
  haveI : IrreducibleSpace ↑(pullback 𝔐.toBase y) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := pullback.snd 𝔐.toBase y)
  haveI hsm : SmoothOfRelativeDimension 1 (pullback.snd 𝔐.toBase y) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : Smooth 𝔐.toBase := SmoothOfRelativeDimension.smooth (n := 1) (f := 𝔐.toBase)

  have h1 : IrreducibleSpace ↑(pullback πX (y ≫ sbar)) :=
    e.hom.homeomorph.surjective.irreducibleSpace e.hom.homeomorph.continuous

  have h2 : topologicalKrullDim ↑(pullback πX (y ≫ sbar)) = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph]
    have hpre : ((pullback.snd 𝔐.toBase y).base ⁻¹' {(default : ↥(Spec (CommRingCat.of k)))}) = Set.univ := by
      ext x; simp [Subsingleton.elim ((pullback.snd 𝔐.toBase y).base x) default]
    have hne : ((pullback.snd 𝔐.toBase y).base ⁻¹' {(default : ↥(Spec (CommRingCat.of k)))}).Nonempty := by
      rw [hpre]; exact Set.univ_nonempty
    have h := AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq
      (pullback.snd 𝔐.toBase y) 1 default hne
    rw [hpre] at h
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ ↑(pullback 𝔐.toBase y)).isHomeomorph]
    exact_mod_cast h

  have h3 : LocallyOfFiniteType (pullback.snd πX (y ≫ sbar)) := by rw [hsnd']; infer_instance
  have h4 : QuasiCompact (pullback.snd πX (y ≫ sbar)) := by rw [hsnd']; infer_instance
  exact ⟨h1, h2, h3, h4⟩

end S_AlgebraicCurve_CurveModel_irreducibleSpace_and_topologicalKrullDim_pullback_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_irreducibleSpace_and_topologicalKrullDim_pullback_eq_one (solution)
