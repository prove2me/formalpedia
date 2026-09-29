-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.exists_overlap_isos_local_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/195fc15a-3080-541e-82b5-5f67f15b8487

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_iso_hom_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_isPullback_opens_local_lift
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_preimage_opens_local_lift_eq_of_iso_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_overlap_isos_restrict_inter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_overlap_isos_local_lifts

set_option autoImplicit false
set_option linter.unusedVariables false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

theorem solution
    (T' T : Type u) [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) [IsSeparated f₀]
    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π)))

    (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W'))
    (hOaff : ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W)) :
    ∃ (φ : ∀ (a b : 𝒰.ι), a < b → ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b))))
      (hφq : ∀ (a b : 𝒰.ι) (h : a < b),
        (φ a b h).hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a)
      (hφg : ∀ (a b : 𝒰.ι) (h : a < b),
        ∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
          (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
          γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
          γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
          γ ≫ (φ a b h).hom = γ')
      (hφO : ∀ (a b : 𝒰.ι) (h : a < b) (W : A₀.Opens),
        (φ a b h).hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W)

      (ρab : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 1) (𝒰.inter r))))
      (ρbc : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 1) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
      (ρac : ∀ r : 𝒰.Idx 2, ((↑(O (r.1 0) (𝒰.inter r)) : Scheme.{u}) ≅ ↑(O (r.1 2) (𝒰.inter r))))
      (hρab : ∀ r : 𝒰.Idx 2,
        (ρab r).hom ≫ (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) =
          (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 1))) ≫
            (φ (r.1 0) (r.1 1) (r.2 (by decide))).hom)
      (hρbc : ∀ r : 𝒰.Idx 2,
        (ρbc r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) =
          (Y (r.1 1)).homOfLE (hOm (r.1 1) (le_inf (𝒰.inter_le r 1) (𝒰.inter_le r 2))) ≫
            (φ (r.1 1) (r.1 2) (r.2 (by decide))).hom)
      (hρac : ∀ r : 𝒰.Idx 2,
        (ρac r).hom ≫ (Y (r.1 2)).homOfLE (hOm (r.1 2) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) =
          (Y (r.1 0)).homOfLE (hOm (r.1 0) (le_inf (𝒰.inter_le r 0) (𝒰.inter_le r 2))) ≫
            (φ (r.1 0) (r.1 2) (r.2 (by decide))).hom),
        (∀ r : 𝒰.Idx 2,
        letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
        ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
            (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) ≫ q (r.1 2) =
          Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))) ∧
        ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
            (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) ≫ q (r.1 2) =
          Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r))))) ∧
        (∀ r : 𝒰.Idx 2,
        letI := algebraOfHom (q (r.1 0)) (O (r.1 0) (𝒰.inter r))
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))))) ≫
            ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρac r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι) =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(Y (r.1 0), O (r.1 0) (𝒰.inter r)))))) ≫
            ((hOaff (r.1 0) (𝒰.inter r) (Scheme.OrderedAffineCover.isAffineOpen_inter f₀ 𝒰 r) (𝒰.inter_le r 0)).isoSpec.inv ≫
              (ρab r).hom ≫ (ρbc r).hom ≫ (O (r.1 2) (𝒰.inter r)).ι)) := by

  have key : ∀ (a b : 𝒰.ι), a < b →
      ∃ (φ : ((↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) ≅ ↑(O b (𝒰.U a ⊓ 𝒰.U b)))),
        (φ.hom ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a) ∧
        (∃ (γ : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O a (𝒰.U a ⊓ 𝒰.U b)))
            (γ' : (↑(𝒰.U a ⊓ 𝒰.U b) : Scheme.{u}) ⟶ ↑(O b (𝒰.U a ⊓ 𝒰.U b))),
            γ ≫ (O a (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_left ≫ g a ∧
            γ' ≫ (O b (𝒰.U a ⊓ 𝒰.U b)).ι = A₀.homOfLE inf_le_right ≫ g b ∧
            γ ≫ φ.hom = γ') ∧
        (∀ W : A₀.Opens,
            φ.hom ⁻¹ᵁ ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O b W) = (O a (𝒰.U a ⊓ 𝒰.U b)).ι ⁻¹ᵁ O a W) := by
    intro a b hab
    have hWaff : IsAffineOpen (𝒰.U a ⊓ 𝒰.U b) :=
      Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated f₀ (𝒰.isAffineOpen a) (𝒰.isAffineOpen b)
    obtain ⟨hsa, γ, hγ, hγc⟩ :=
      AlgebraicGeometry.Scheme.OrderedAffineCover.exists_isPullback_opens_local_lift
        T' T π hπ hker f₀ 𝒰 Y q hq g hg O hO hOm hOtop hOinf hOaff a (𝒰.U a ⊓ 𝒰.U b) hWaff inf_le_left
    obtain ⟨hsb, γ', hγ', hγ'c⟩ :=
      AlgebraicGeometry.Scheme.OrderedAffineCover.exists_isPullback_opens_local_lift
        T' T π hπ hker f₀ 𝒰 Y q hq g hg O hO hOm hOtop hOinf hOaff b (𝒰.U a ⊓ 𝒰.U b) hWaff inf_le_right
    haveI : IsAffine (↑(O a (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) := hOaff a _ hWaff inf_le_left
    haveI : IsAffine (↑(O b (𝒰.U a ⊓ 𝒰.U b)) : Scheme.{u}) := hOaff b _ hWaff inf_le_right
    obtain ⟨φ, hφq, hφγ⟩ :=
      AlgebraicGeometry.Smooth.exists_iso_hom_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
        π hπ hker ((𝒰.U a ⊓ 𝒰.U b).ι ≫ f₀)
        ((O a (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q a) hsa ((O b (𝒰.U a ⊓ 𝒰.U b)).ι ≫ q b) hsb γ hγc γ' hγ'c
    refine ⟨φ, ?_, ⟨γ, γ', hγ, hγ', hφγ⟩, ?_⟩
    · exact hφq
    · intro W
      exact AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_opens_local_lift_eq_of_iso_comp_eq
        T' T π hπ hker f₀ 𝒰 Y q hq g hg O hO hOm hOtop hOinf hOaff a b φ γ γ' hγ hγ' hφγ W
  choose φ hφq hφg hφO using key
  obtain ⟨ρab, ρbc, ρac, hρab, hρbc, hρac, hρT, hρI⟩ :=
    AlgebraicGeometry.Scheme.OrderedAffineCover.exists_overlap_isos_restrict_inter
      T' T π hπ hker f₀ 𝒰 Y q hq g hg O hO hOm hOtop hOinf hOaff φ hφq hφg hφO
  exact ⟨φ, hφq, hφg, hφO, ρab, ρbc, ρac, hρab, hρbc, hρac, hρT, hρI⟩

end S_AlgebraicGeometry_Smooth_exists_overlap_isos_local_lifts
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_exists_overlap_isos_local_lifts (solution)
