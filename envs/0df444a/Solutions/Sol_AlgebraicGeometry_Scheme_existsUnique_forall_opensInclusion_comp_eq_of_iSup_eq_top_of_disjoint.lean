-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.existsUnique_forall_opensInclusion_comp_eq_of_iSup_eq_top_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/22dd0e23-ba24-52ad-80e4-b7a9482267a5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_existsUnique_forall_opensInclusion_comp_eq_of_iSup_eq_top_of_disjoint

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace SectionGlue

variable {X : Scheme.{u}}

theorem isEmpty_pullback_ι (A B : X.Opens) (hd : A ⊓ B = ⊥) : IsEmpty ↑(pullback A.ι B.ι) := by
  refine ⟨fun p => ?_⟩
  have h1 : (pullback.fst A.ι B.ι ≫ A.ι).base p = (pullback.snd A.ι B.ι ≫ B.ι).base p := by
    rw [pullback.condition]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, Scheme.Opens.ι_apply] at h1
  have hA : ((pullback.fst A.ι B.ι).base p).1 ∈ A := ((pullback.fst A.ι B.ι).base p).2
  have hB : ((pullback.snd A.ι B.ι).base p).1 ∈ B := ((pullback.snd A.ι B.ι).base p).2
  rw [← h1] at hB
  have hmem : ((pullback.fst A.ι B.ι).base p).1 ∈ A ⊓ B := ⟨hA, hB⟩
  rw [hd] at hmem
  exact hmem

theorem main {X Y : Scheme.{u}} {ι : Type v} (W : ι → X.Opens) (hW : ⨆ i, W i = ⊤)
    (hdisj : ∀ i j, i ≠ j → W i ⊓ W j = ⊥) (f : ∀ i, (W i : Scheme.{u}) ⟶ Y) :
    ∃! g : X ⟶ Y, ∀ i, (W i).ι ≫ g = f i := by
  classical
  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover W hW
  have hcompat : ∀ i j : ι, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ f j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      show pullback.fst (W i).ι (W i).ι ≫ f i = pullback.snd (W i).ι (W i).ι ≫ f i
      rw [fst_eq_snd_of_mono_eq]
    · haveI := isEmpty_pullback_ι (W i) (W j) (hdisj i j hij)
      exact (isInitialOfIsEmpty (X := pullback (W i).ι (W j).ι)).hom_ext _ _
  refine ⟨𝒰.glueMorphisms f hcompat, fun i => Scheme.Cover.ι_glueMorphisms 𝒰 f hcompat i, ?_⟩
  intro g hg
  exact Scheme.Cover.hom_ext 𝒰 _ _ (fun i => by
    show (W i).ι ≫ g = (W i).ι ≫ Scheme.Cover.glueMorphisms 𝒰 f hcompat
    rw [hg i]
    exact (Scheme.Cover.ι_glueMorphisms 𝒰 f hcompat i).symm)

end SectionGlue

theorem solution
    {X Y : Scheme.{u}} {ι : Type v} (W : ι → X.Opens) (hW : ⨆ i, W i = ⊤)
    (hdisj : ∀ i j, i ≠ j → W i ⊓ W j = ⊥) (f : ∀ i, (W i : Scheme.{u}) ⟶ Y) :
    ∃! g : X ⟶ Y, ∀ i, (W i).ι ≫ g = f i :=
  SectionGlue.main W hW hdisj f

end S_AlgebraicGeometry_Scheme_existsUnique_forall_opensInclusion_comp_eq_of_iSup_eq_top_of_disjoint
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_existsUnique_forall_opensInclusion_comp_eq_of_iSup_eq_top_of_disjoint (solution)
