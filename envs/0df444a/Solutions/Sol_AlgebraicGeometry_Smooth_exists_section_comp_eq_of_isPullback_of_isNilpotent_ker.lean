-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.exists_section_comp_eq_of_isPullback_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/80766a7c-b1fb-5e2c-a422-105a6403c742

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isNilpotent_of_isAffine
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_section_comp_eq_of_isPullback_of_isNilpotent_ker

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

namespace E160K1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem isLocalRing_of_surjective_of_isNilpotent_ker {T' T : Type u} [CommRing T'] [IsLocalRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π)) : IsLocalRing T := by
  have hnt : Nontrivial T := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    have h1 : (1 : T') ∈ RingHom.ker π := by
      rw [RingHom.mem_ker]; exact Subsingleton.elim _ _
    obtain ⟨n, hn⟩ := hker
    have hmem : (1 : T') ^ n ∈ (RingHom.ker π) ^ n := Ideal.pow_mem_pow h1 n
    rw [hn, one_pow] at hmem
    exact one_ne_zero ((Submodule.mem_bot T').mp hmem)
  exact IsLocalRing.of_surjective' π hπ

theorem exists_affineOpens_range_subset {T : Type u} [CommRing T] [IsLocalRing T] {A : Scheme.{u}}
    (h : Spec (CommRingCat.of T) ⟶ A) :
    ∃ U : A.Opens, U ∈ A.affineOpens ∧ Set.range h ⊆ (U : Set A) := by
  have ha : h (closedPoint T) ∈ (⊤ : A.Opens) := TopologicalSpace.Opens.mem_top _
  obtain ⟨U, hU, haU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.isBasis_affineOpens) ha
  refine ⟨U, hU, ?_⟩
  have htop : h ⁻¹ᵁ U = ⊤ := (IsLocalRing.closedPoint_mem_iff (h ⁻¹ᵁ U)).mp haU
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ h ⁻¹ᵁ U := by rw [htop]; exact TopologicalSpace.Opens.mem_top _
  exact hx

theorem exists_lift_of_local {T' T : Type u} [CommRing T'] [IsLocalRing T'] [CommRing T]
    (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) [Smooth f]
    (x₀' : Spec (CommRingCat.of T) ⟶ A)
    (hx₀' : x₀' ≫ f = Spec.map (CommRingCat.ofHom π)) :
    ∃ x : Spec (CommRingCat.of T') ⟶ A,
      x ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom π) ≫ x = x₀' := by
  haveI : IsLocalRing T := isLocalRing_of_surjective_of_isNilpotent_ker π hπ hker
  obtain ⟨U, hU, hrange⟩ := exists_affineOpens_range_subset x₀'
  haveI : IsAffine U := hU

  have hrange' : Set.range x₀' ⊆ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  set y₀ : Spec (CommRingCat.of T) ⟶ U := IsOpenImmersion.lift U.ι x₀' hrange' with hy₀def
  have hy₀ : y₀ ≫ U.ι = x₀' := IsOpenImmersion.lift_fac _ _ _

  set J : Ideal T' := RingHom.ker π with hJ
  let ε : (T' ⧸ J) ≃+* T := RingHom.quotientKerEquivOfSurjective hπ
  let eIso : CommRingCat.of (T' ⧸ J) ≅ CommRingCat.of T := ε.toCommRingCatIso
  have hεmk : CommRingCat.ofHom π ≫ eIso.inv = CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    change CommRingCat.ofHom π ≫ CommRingCat.ofHom ε.symm.toRingHom = _
    rw [← CommRingCat.ofHom_comp, RingHom.quotientKerEquivOfSurjective_symm_comp]
  set x₀ : Spec (CommRingCat.of (T' ⧸ J)) ⟶ U := Spec.map eIso.inv ≫ y₀ with hx₀def
  have hx₀ : x₀ ≫ (U.ι ≫ f) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ 𝟙 (Spec (CommRingCat.of T')) := by
    rw [Category.comp_id, hx₀def, Category.assoc, reassoc_of% hy₀, hx₀', ← Spec.map_comp, hεmk]
  have hlift := AlgebraicGeometry.Smooth.exists_lift_comp_eq_of_isNilpotent_of_isAffine
    (U.ι ≫ f) J hker (𝟙 _) x₀ hx₀
  obtain ⟨y, hy1, hy2⟩ := hlift
  refine ⟨y ≫ U.ι, by rw [Category.assoc, hy1], ?_⟩
  have hπ' : CommRingCat.ofHom π = CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ eIso.hom := by
    rw [← hεmk, Category.assoc, eIso.inv_hom_id, Category.comp_id]
  rw [hπ', Spec.map_comp, Category.assoc, reassoc_of% hy2, hx₀def, Category.assoc, hy₀,
    ← Spec.map_comp_assoc, eIso.inv_hom_id, Spec.map_id, Category.id_comp]

end E160K1

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T))
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (e₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) f₀) :
    ∃ e : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f,
      Spec.map (CommRingCat.ofHom π) ≫ e.1 = e₀.1 ≫ g := by
  haveI := hs
  have hx₀' : (e₀.1 ≫ g) ≫ f = Spec.map (CommRingCat.ofHom π) := by
    rw [Category.assoc, hg.w, ← Category.assoc, e₀.2, Category.id_comp]
  have h := E160K1.exists_lift_of_local π hπ hker f (e₀.1 ≫ g) hx₀'
  obtain ⟨x, hx1, hx2⟩ := h
  exact ⟨⟨x, hx1⟩, hx2⟩

end S_AlgebraicGeometry_Smooth_exists_section_comp_eq_of_isPullback_of_isNilpotent_ker
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_exists_section_comp_eq_of_isPullback_of_isNilpotent_ker (solution)
