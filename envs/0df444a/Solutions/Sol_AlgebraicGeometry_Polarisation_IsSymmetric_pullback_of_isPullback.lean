-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.IsSymmetric.pullback_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/889ea7d4-4577-5a67-8138-ffadd54841a1

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_IsSymmetric_pullback_of_isPullback

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

namespace SYMBC

theorem inv_coe_congr {S : Type u} [CommRing S] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {P₁ : SchemeHomOver t₁ f} {P₂ : SchemeHomOver t₂ f} (hP : P₁.1 = P₂.1) :
    (L.inv t₁ P₁).1 = (L.inv t₂ P₂).1 := by
  subst ht
  rw [Subtype.ext hP]

theorem inv_natural {S : Type u} [CommRing S] {A T T' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t
  letI := L.pointGroup t'
  let F : SchemeHomOver t f →* SchemeHomOver t' f :=
    MonoidHom.mk' (GoodReductionJacobian.schemeHomOverComp ψ hψ) (fun a b => L.mul_natural t t' ψ hψ a b)
  exact map_inv F x

end SYMBC

open SYMBC

theorem solution
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')} {g : A' ⟶ A}
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (𝓛 : A.Modules) (h : IsSymmetric f L 𝓛) :
    IsSymmetric f' L' ((Scheme.Modules.pullback g).obj 𝓛) := by

  have hinv : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' f'),
      (L'.inv t' P).1 ≫ g =
        (L.inv (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩).1 := by
    intro T t' P
    letI := L'.pointGroup t'
    letI := L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom φ))
    let F : SchemeHomOver t' f' →* SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f :=
      MonoidHom.mk' (fun P => ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩)
        (fun a b => Subtype.ext (hmul t' a b))
    exact congrArg Subtype.val (map_inv F P)

  have hneg : negMor f' L' ≫ g = g ≫ negMor f L := by
    have lhs := hinv f' (idPt f')
    have rhs := congrArg Subtype.val (inv_natural L f (g ≫ f) g rfl (idPt f))
    simp only [GoodReductionJacobian.schemeHomOverComp_coe] at rhs
    change (L'.inv f' (idPt f')).1 ≫ g = g ≫ (L.inv f (idPt f)).1
    rw [lhs, rhs]
    apply inv_coe_congr L hg.w.symm
    simp only [idPt, GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp, Category.comp_id]

  have h1 : LocIsoOnBase f' ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback (negMor f L)).obj 𝓛))
      ((Scheme.Modules.pullback g).obj 𝓛) :=
    AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_isPullback φ hg h
  have e : (Scheme.Modules.pullback (negMor f' L')).obj ((Scheme.Modules.pullback g).obj 𝓛) ≅
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) :=
    (Scheme.Modules.pullbackComp (negMor f' L') g).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hneg).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp g (negMor f L)).app 𝓛).symm
  intro s
  obtain ⟨U, hs, ⟨e'⟩⟩ := h1 s
  exact ⟨U, hs, ⟨(Scheme.Modules.pullback _).mapIso e ≪≫ e'⟩⟩

end S_AlgebraicGeometry_Polarisation_IsSymmetric_pullback_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_IsSymmetric_pullback_of_isPullback (solution)
