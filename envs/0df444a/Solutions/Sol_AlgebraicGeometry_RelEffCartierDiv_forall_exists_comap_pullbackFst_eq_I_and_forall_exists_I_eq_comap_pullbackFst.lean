-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.forall_exists_comap_pullbackFst_eq_I_and_forall_exists_I_eq_comap_pullbackFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2014a197-dc1b-55ec-8eda-23a8234d5896

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_forall_exists_comap_pullbackFst_eq_I_and_forall_exists_I_eq_comap_pullbackFst

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace RecbDiv

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem isPullback_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData) (m : X ⟶ Y) :
    IsPullback ((I.comapIso m).hom ≫ pullback.snd m I.subschemeι) (I.comap m).subschemeι I.subschemeι m := by
  refine (IsPullback.of_iso_pullback ⟨?_⟩ (I.comapIso m) ?_ ?_).flip
  · simp [pullback.condition]
  · simp
  · simp

theorem main {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) (g : T ⟶ S) (r : ℕ) :
    (∀ D' : RelEffCartierDiv (pullback.snd f g) r (𝟙 T),
        ∃ D : RelEffCartierDiv f r g, D.I.comap (pullback.fst (pullback.snd f g) (𝟙 T)) = D'.I) ∧
    (∀ D : RelEffCartierDiv f r g,
        ∃ D' : RelEffCartierDiv (pullback.snd f g) r (𝟙 T), D'.I = D.I.comap (pullback.fst (pullback.snd f g) (𝟙 T))) := by
  set p := pullback.snd f g with hp
  set e : pullback p (𝟙 T) ⟶ pullback f g := pullback.fst p (𝟙 T) with he

  have sqe : IsPullback e (pullback.snd p (𝟙 T)) p (𝟙 T) := IsPullback.of_hasPullback p (𝟙 T)
  refine ⟨fun D' => ?_, fun D => ?_⟩
  ·
    let e' : pullback f g ⟶ pullback p (𝟙 T) := inv e

    have hcomm : e' ≫ pullback.snd p (𝟙 T) = p ≫ 𝟙 T := by
      rw [Category.comp_id]
      have : e ≫ p = pullback.snd p (𝟙 T) ≫ 𝟙 T := pullback.condition
      rw [Category.comp_id] at this
      rw [← this, IsIso.inv_hom_id_assoc]
    have sqe' : IsPullback e' p (pullback.snd p (𝟙 T)) (𝟙 T) :=
      IsPullback.of_horiz_isIso ⟨hcomm⟩
    have sq := (isPullback_comap D'.I e').paste_vert sqe'
    haveI := D'.isFinite
    haveI := D'.flat
    haveI := D'.locallyOfFinitePresentation
    refine ⟨{ I := D'.I.comap e'
              isFinite := MorphismProperty.of_isPullback sq ‹_›
              flat := MorphismProperty.of_isPullback sq ‹_›
              locallyOfFinitePresentation := MorphismProperty.of_isPullback sq ‹_›
              finrank_eq := fun t => by
                rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq t]
                exact D'.finrank_eq _ }, ?_⟩
    change (D'.I.comap e').comap e = D'.I
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.hom_inv_id, Scheme.IdealSheafData.comap_id]
  ·
    have sq := (isPullback_comap D.I e).paste_vert sqe
    haveI := D.isFinite
    haveI := D.flat
    haveI := D.locallyOfFinitePresentation
    exact ⟨{ I := D.I.comap e
             isFinite := MorphismProperty.of_isPullback sq ‹_›
             flat := MorphismProperty.of_isPullback sq ‹_›
             locallyOfFinitePresentation := MorphismProperty.of_isPullback sq ‹_›
             finrank_eq := fun t => by
               rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq t]
               exact D.finrank_eq _ }, rfl⟩

end RecbDiv

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem solution
    {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) (g : T ⟶ S) (r : ℕ) :
    (∀ D' : RelEffCartierDiv (pullback.snd f g) r (𝟙 T),
        ∃ D : RelEffCartierDiv f r g, D.I.comap (pullback.fst (pullback.snd f g) (𝟙 T)) = D'.I) ∧
    (∀ D : RelEffCartierDiv f r g,
        ∃ D' : RelEffCartierDiv (pullback.snd f g) r (𝟙 T), D'.I = D.I.comap (pullback.fst (pullback.snd f g) (𝟙 T))) :=
  RecbDiv.main f g r

end S_AlgebraicGeometry_RelEffCartierDiv_forall_exists_comap_pullbackFst_eq_I_and_forall_exists_I_eq_comap_pullbackFst
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_forall_exists_comap_pullbackFst_eq_I_and_forall_exists_I_eq_comap_pullbackFst (solution)
