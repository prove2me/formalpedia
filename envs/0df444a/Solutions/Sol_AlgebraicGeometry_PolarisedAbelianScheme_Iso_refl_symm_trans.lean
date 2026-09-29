-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.Iso.refl_symm_trans
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a7f5561f-4d53-50a5-9458-f18f0eb018c2

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_Iso_refl_symm_trans

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

namespace BenchR_EDa

universe u

open _root_.AlgebraicGeometry.Scheme.Modules in

noncomputable def transportIso {X Y Z : Scheme.{u}} (a : X ⟶ Z) (b : Y ⟶ Z) (ε : X ⟶ Y) (h : ε ≫ b = a)
    {M N : Z.Modules} (φ : (Scheme.Modules.pullback b).obj M ≅ (Scheme.Modules.pullback b).obj N) :
    (Scheme.Modules.pullback a).obj M ≅ (Scheme.Modules.pullback a).obj N :=
  (pullbackCongr h.symm).app M ≪≫ ((pullbackComp ε b).symm).app M ≪≫ (Scheme.Modules.pullback ε).mapIso φ ≪≫
    (pullbackComp ε b).app N ≪≫ (pullbackCongr h).app N

open _root_.AlgebraicGeometry.Scheme.Modules in

noncomputable def pbCompObj {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ≅ (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) :=
  ((pullbackComp f g).symm).app M

theorem mul_fst_congr {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    {x x' y y' : SchemeHomOver t f} (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t x' y').1 := by
  rw [Subtype.ext hx, Subtype.ext hy]

end BenchR_EDa

open BenchR_EDa _root_.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {g d n : ℕ} {S : Type} [CommRing S] :
    (∀ u : PolarisedAbelianScheme g d n S, PolarisedAbelianScheme.Iso u u) ∧
    (∀ u v : PolarisedAbelianScheme g d n S, PolarisedAbelianScheme.Iso u v → PolarisedAbelianScheme.Iso v u) ∧
    (∀ u v w : PolarisedAbelianScheme g d n S,
      PolarisedAbelianScheme.Iso u v → PolarisedAbelianScheme.Iso v w → PolarisedAbelianScheme.Iso u w) := by
  refine ⟨?_, ?_, ?_⟩
  ·
    intro u
    refine ⟨Iso.refl u.A, by simp, ?_, ?_, ?_⟩
    · intro T t x y
      have hx : (⟨x.1 ≫ (Iso.refl u.A).hom, by rw [Category.assoc]; simp [x.2]⟩ : SchemeHomOver t u.f) = x :=
        Subtype.ext (by simp)
      have hy : (⟨y.1 ≫ (Iso.refl u.A).hom, by rw [Category.assoc]; simp [y.2]⟩ : SchemeHomOver t u.f) = y :=
        Subtype.ext (by simp)
      rw [hx, hy]; simp
    · intro i; simp
    · intro s
      refine ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (u.f ⁻¹ᵁ ⊤).ι).mapIso ((pullbackId u.A).app u.pol)⟩⟩
  ·
    rintro u v ⟨e, he, hmul, hP, hpol⟩
    have he' : e.inv ≫ u.f = v.f := by rw [Iso.inv_comp_eq, he]
    refine ⟨e.symm, he', ?_, ?_, ?_⟩
    · intro T t x y

      let x' : SchemeHomOver t u.f := ⟨x.1 ≫ e.inv, by rw [Category.assoc, he']; exact x.2⟩
      let y' : SchemeHomOver t u.f := ⟨y.1 ≫ e.inv, by rw [Category.assoc, he']; exact y.2⟩
      have key := hmul t x' y'
      have hx : (⟨x'.1 ≫ e.hom, by rw [Category.assoc, he]; exact x'.2⟩ : SchemeHomOver t v.f) = x :=
        Subtype.ext (by simp [x'])
      have hy : (⟨y'.1 ≫ e.hom, by rw [Category.assoc, he]; exact y'.2⟩ : SchemeHomOver t v.f) = y :=
        Subtype.ext (by simp [y'])
      rw [hx, hy] at key
      show (v.L.mul t x y).1 ≫ e.inv = (u.L.mul t x' y').1
      rw [← key]; simp
    · intro i
      show (v.P i).1 ≫ e.inv = (u.P i).1
      rw [← hP i]; simp
    · intro s
      obtain ⟨U, hsU, ⟨φ⟩⟩ := hpol s
      refine ⟨U, hsU, ?_⟩

      have hle : v.f ⁻¹ᵁ U ≤ e.inv ⁻¹ᵁ (u.f ⁻¹ᵁ U) := by
        rw [← Scheme.Hom.comp_preimage, he']
      let ε := e.inv.resLE (u.f ⁻¹ᵁ U) (v.f ⁻¹ᵁ U) hle
      have hε : ε ≫ (u.f ⁻¹ᵁ U).ι = (v.f ⁻¹ᵁ U).ι ≫ e.inv := Scheme.Hom.resLE_comp_ι _ _

      have ψ : (Scheme.Modules.pullback ((v.f ⁻¹ᵁ U).ι ≫ e.inv)).obj u.pol ≅
          (Scheme.Modules.pullback ((v.f ⁻¹ᵁ U).ι ≫ e.inv)).obj ((Scheme.Modules.pullback e.hom).obj v.pol) :=
        transportIso _ _ ε hε φ.symm
      exact ⟨(pbCompObj _ _ _).symm ≪≫ ψ ≪≫ (pbCompObj ((v.f ⁻¹ᵁ U).ι ≫ e.inv) e.hom v.pol).symm ≪≫
        (Scheme.Modules.pullbackCongr (by simp)).app v.pol⟩
  ·
    rintro u v w ⟨e₁, he₁, hmul₁, hP₁, hpol₁⟩ ⟨e₂, he₂, hmul₂, hP₂, hpol₂⟩
    have he : (e₁ ≪≫ e₂).hom ≫ w.f = u.f := by simp [he₁, he₂]
    refine ⟨e₁ ≪≫ e₂, he, ?_, ?_, ?_⟩
    · intro T t x y
      simp only [Iso.trans_hom]
      rw [← Category.assoc, hmul₁, hmul₂]
      exact mul_fst_congr _ _ (by simp) (by simp)
    · intro i
      simp only [Iso.trans_hom]
      rw [← Category.assoc, hP₁, hP₂]
    · intro s
      obtain ⟨U₁, hs₁, ⟨φ₁⟩⟩ := hpol₁ s
      obtain ⟨U₂, hs₂, ⟨φ₂⟩⟩ := hpol₂ s
      refine ⟨U₁ ⊓ U₂, ⟨hs₁, hs₂⟩, ?_⟩
      set V := u.f ⁻¹ᵁ (U₁ ⊓ U₂) with hV

      have hV₁ : V ≤ u.f ⁻¹ᵁ U₁ := fun x hx => hx.1
      let ιa := u.A.homOfLE hV₁
      have hιa : ιa ≫ (u.f ⁻¹ᵁ U₁).ι = V.ι := Scheme.homOfLE_ι _ _

      have hle : V ≤ e₁.hom ⁻¹ᵁ (v.f ⁻¹ᵁ U₂) := by
        rw [← Scheme.Hom.comp_preimage, he₁]; exact fun x hx => hx.2
      let ε := e₁.hom.resLE (v.f ⁻¹ᵁ U₂) V hle
      have hε : ε ≫ (v.f ⁻¹ᵁ U₂).ι = V.ι ≫ e₁.hom := Scheme.Hom.resLE_comp_ι _ _
      exact ⟨(Scheme.Modules.pullback V.ι).mapIso (pbCompObj e₁.hom e₂.hom w.pol) ≪≫
        (pbCompObj V.ι e₁.hom _).symm ≪≫ transportIso _ _ ε hε φ₂ ≪≫ pbCompObj V.ι e₁.hom _ ≪≫
        transportIso _ _ ιa hιa φ₁⟩

end S_AlgebraicGeometry_PolarisedAbelianScheme_Iso_refl_symm_trans
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_Iso_refl_symm_trans (solution)
