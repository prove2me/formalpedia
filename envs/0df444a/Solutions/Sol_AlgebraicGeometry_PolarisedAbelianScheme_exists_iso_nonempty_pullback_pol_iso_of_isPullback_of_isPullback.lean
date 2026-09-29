-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_iso_nonempty_pullback_pol_iso_of_isPullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5a840545-7811-57e4-8474-023fe836460e

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_iso_nonempty_pullback_pol_iso_of_isPullback_of_isPullback

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_iso_nonempty_pullback_pol_iso_of_isPullback_of_isPullback.AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Spec.map Scheme Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp PolarisedAbelianScheme PolarisedAbelianScheme.IsPullback"
namespace PolarisedAbelianScheme
p2m_export "AlgebraicGeometry.PolarisedAbelianScheme" "Iso IsPullback L A P f pol"
namespace H2Aux
p2m_open "AlgebraicGeometry.PolarisedAbelianScheme AlgebraicGeometry"

theorem exists_iso {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A B B' : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (fB : B ⟶ Spec (CommRingCat.of S'))
    (fB' : B' ⟶ Spec (CommRingCat.of S')) (gA : B ⟶ A) (gA' : B' ⟶ A)
    (hg : CategoryTheory.IsPullback gA fB f (Spec.map (CommRingCat.ofHom φ)))
    (hg' : CategoryTheory.IsPullback gA' fB' f (Spec.map (CommRingCat.ofHom φ))) :
    ∃ e : B ≅ B', e.hom ≫ gA' = gA ∧ e.hom ≫ fB' = fB :=
  ⟨hg.isoIsPullback _ _ hg', CategoryTheory.IsPullback.isoIsPullback_hom_fst _ _ hg hg',
    CategoryTheory.IsPullback.isoIsPullback_hom_snd _ _ hg hg'⟩

end AlgebraicGeometry.PolarisedAbelianScheme.H2Aux

theorem solution
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (v v' : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.IsPullback φ u v) (h' : PolarisedAbelianScheme.IsPullback φ u v') :
    ∃ (e : v.A ≅ v'.A) (he : e.hom ≫ v'.f = v.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t v.f),
        (v.L.mul t x y).1 ≫ e.hom =
          (v'.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
            ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1) ∧
      (∀ i, (v.P i).1 ≫ e.hom = (v'.P i).1) ∧
      Nonempty ((Scheme.Modules.pullback e.hom).obj v'.pol ≅ v.pol) := by
  obtain ⟨gA, hg, hmul, hP, ⟨ι⟩⟩ := h
  obtain ⟨gA', hg', hmul', hP', ⟨ι'⟩⟩ := h'
  obtain ⟨e, hegA, hef⟩ := PolarisedAbelianScheme.H2Aux.exists_iso φ u.f v.f v'.f gA gA' hg hg'
  refine ⟨e, hef, ?_, ?_, ⟨?_⟩⟩
  · intro T t x y
    apply hg'.hom_ext
    · rw [Category.assoc, hegA, hmul, hmul']
      congr 2
      · exact Subtype.ext (by change x.1 ≫ gA = (x.1 ≫ e.hom) ≫ gA'; rw [Category.assoc, hegA])
      · exact Subtype.ext (by change y.1 ≫ gA = (y.1 ≫ e.hom) ≫ gA'; rw [Category.assoc, hegA])
    · conv_lhs => rw [Category.assoc, hef, (v.L.mul t x y).2]
      exact ((v'.L.mul t _ _).2).symm
  · intro i
    apply hg'.hom_ext
    · rw [Category.assoc, hegA, hP, hP']
    · conv_lhs => rw [Category.assoc, hef, (v.P i).2]
      exact ((v'.P i).2).symm
  · exact (Scheme.Modules.pullback e.hom).mapIso ι'.symm ≪≫ (Scheme.Modules.pullbackComp e.hom gA').app u.pol ≪≫
      (Scheme.Modules.pullbackCongr hegA).app u.pol ≪≫ ι

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_iso_nonempty_pullback_pol_iso_of_isPullback_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_iso_nonempty_pullback_pol_iso_of_isPullback_of_isPullback (solution)
