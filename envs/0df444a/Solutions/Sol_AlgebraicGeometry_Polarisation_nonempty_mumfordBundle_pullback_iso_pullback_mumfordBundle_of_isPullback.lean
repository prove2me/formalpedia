-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/284a0908-9401-5ccb-9979-0d7a9f7138c7

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace MumfordBC17

theorem mul_coe_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (x y : SchemeHomOver t₁ f) :
    (L.mul t₁ x y).1 = (L.mul t₂ ⟨x.1, by rw [← h]; exact x.2⟩ ⟨y.1, by rw [← h]; exact y.2⟩).1 := by
  subst h; rfl

theorem mul_coe_congr_pts {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)}
    (x y x' y' : SchemeHomOver t f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t x' y').1 := by
  rw [Subtype.ext hx, Subtype.ext hy]

end MumfordBC17

open MumfordBC17 in
theorem solution
    (k k' : Type) [CommRing k] [CommRing k'] (φ : k →+* k')
    {A A' : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (f' : A' ⟶ Spec (CommRingCat.of k')) (L' : RelativeGroupLaw k' f')
    (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    Nonempty (mumfordBundle f' L' ((Scheme.Modules.pullback g).obj 𝓛) ≅
      (Scheme.Modules.pullback
        (pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
          (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))).obj
        (mumfordBundle f L 𝓛)) := by

  have hG1 : pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
      (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]) ≫ pullback.fst f f =
      pullback.fst f' f' ≫ g := pullback.lift_fst _ _ _
  have hG2 : pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
      (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]) ≫ pullback.snd f f =
      pullback.snd f' f' ≫ g := pullback.lift_snd _ _ _
  have hGμ : addMor f' L' ≫ g =
      pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]) ≫ addMor f L := by
    have nat := congrArg Subtype.val (L.mul_natural (pullback.fst f f ≫ f)
      (pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]) ≫ pullback.fst f f ≫ f)
      (pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc])) rfl
      ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at nat
    have hbase : pullback.lift (pullback.fst f' f' ≫ g) (pullback.snd f' f' ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]) ≫ pullback.fst f f ≫ f =
        (pullback.fst f' f' ≫ f') ≫ Spec.map (CommRingCat.ofHom φ) := by
      rw [← Category.assoc, hG1, Category.assoc, hg.w, Category.assoc]
    rw [addMor, addMor, hg_mul, nat, mul_coe_congr L hbase]
    apply mul_coe_congr_pts
    · show pullback.fst f' f' ≫ g = _ ≫ pullback.fst f f
      rw [hG1]
    · show pullback.snd f' f' ≫ g = _ ≫ pullback.snd f f
      rw [hG2]

  obtain ⟨d⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 g h𝓛
  refine ⟨?_⟩
  refine (?_ ⊗ᵢ (?_ ⊗ᵢ ?_)) ≪≫ (whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso _ _ _).symm) ≪≫
    (Scheme.Modules.pullbackTensorObjIso _ _ _).symm
  · exact ((Scheme.Modules.pullbackComp (addMor f' L') g).app 𝓛) ≪≫ (Scheme.Modules.pullbackCongr hGμ).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp _ (addMor f L)).app 𝓛).symm
  · exact (Scheme.Modules.pullback (pullback.fst f' f')).mapIso d.symm ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst f' f') g).app _) ≪≫ (Scheme.Modules.pullbackCongr hG1.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ (pullback.fst f f)).app _).symm
  · exact (Scheme.Modules.pullback (pullback.snd f' f')).mapIso d.symm ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd f' f') g).app _) ≪≫ (Scheme.Modules.pullbackCongr hG2.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ (pullback.snd f f)).app _).symm

end S_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback (solution)
