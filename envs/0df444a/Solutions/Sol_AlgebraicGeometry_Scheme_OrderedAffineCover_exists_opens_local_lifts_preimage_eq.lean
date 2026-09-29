-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCover.exists_opens_local_lifts_preimage_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4d5afb69-ba7b-53dc-9dcb-7ba5544a52a5

import Mathlib
import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations
import Theorems.Thm_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
import Theorems.Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_opens_local_lifts_preimage_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover TopologicalSpace"

universe u

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥) (hI : RingHom.ker π ≤ maximalIdeal T')
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T))
    (𝒰 : A₀.OrderedAffineCover)
    (Y : 𝒰.ι → Scheme.{u}) (q : ∀ a, Y a ⟶ Spec (CommRingCat.of T')) (hq : ∀ a, Smooth (q a))
    (g : ∀ a, (↑(𝒰.U a) : Scheme.{u}) ⟶ Y a)
    (hg : ∀ a, IsPullback (g a) ((𝒰.U a).ι ≫ f₀) (q a) (Spec.map (CommRingCat.ofHom π))) :
    ∃ (O : ∀ a, A₀.Opens → (Y a).Opens)
    (hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W)
    (hOm : ∀ a, Monotone (O a))
    (hOtop : ∀ a, O a (𝒰.U a) = ⊤)
    (hOinf : ∀ (a : 𝒰.ι) (W W' : A₀.Opens), O a W ⊓ O a W' ≤ O a (W ⊓ W')),
      ∀ (a : 𝒰.ι) (W : A₀.Opens), IsAffineOpen W → W ≤ 𝒰.U a → IsAffineOpen (O a W) := by
  classical

  have H : ∀ a, IsClosedImmersion (g a) ∧ Surjective (g a) ∧ IsHomeomorph (g a).base := fun a =>
    AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker π hπ hker (q a)
      ((𝒰.U a).ι ≫ f₀) (g a) (hg a)

  let O : ∀ a, A₀.Opens → (Y a).Opens := fun a W =>
    ⟨(g a).base '' ((𝒰.U a).ι ⁻¹ᵁ W : Set _), (H a).2.2.isOpenMap _ ((𝒰.U a).ι ⁻¹ᵁ W).2⟩
  have hOcoe : ∀ a W, ((O a W : (Y a).Opens) : Set _) = (g a).base '' ((𝒰.U a).ι ⁻¹ᵁ W : Set _) := fun a W => rfl
  have hO : ∀ (a : 𝒰.ι) (W : A₀.Opens), g a ⁻¹ᵁ O a W = (𝒰.U a).ι ⁻¹ᵁ W := by
    intro a W
    ext x
    show (g a).base x ∈ (g a).base '' _ ↔ x ∈ ((𝒰.U a).ι ⁻¹ᵁ W : Set _)
    exact ⟨fun ⟨y, hy, hyx⟩ => (H a).2.2.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  refine ⟨O, hO, ?_, ?_, ?_, ?_⟩
  · intro a W W' hWW'
    show (g a).base '' _ ⊆ (g a).base '' _
    exact Set.image_mono (fun x hx => hWW' hx)
  · intro a
    ext y
    simp only [Opens.coe_top, Set.mem_univ, iff_true]
    show y ∈ (g a).base '' _
    obtain ⟨x, rfl⟩ := (H a).2.2.surjective y
    exact ⟨x, by rw [Scheme.Opens.ι_preimage_self]; trivial, rfl⟩
  · intro a W W'
    rintro y ⟨⟨x, hx, rfl⟩, ⟨x', hx', hxx'⟩⟩
    have hx'x : x' = x := (H a).2.2.injective hxx'
    exact ⟨x, ⟨hx, hx'x ▸ hx'⟩, rfl⟩
  · intro a W hW hWU

    haveI := (H a).1
    haveI := (H a).2.1
    haveI : Surjective (g a ∣_ O a W) := MorphismProperty.of_isPullback (isPullback_morphismRestrict ..).flip (H a).2.1
    have haff : IsAffineOpen (g a ⁻¹ᵁ O a W) := by
      rw [hO]
      exact hW.preimage_of_isOpenImmersion (𝒰.U a).ι (by rw [Scheme.Opens.opensRange_ι]; exact hWU)
    haveI : IsAffine ↑(g a ⁻¹ᵁ O a W) := haff
    exact AlgebraicGeometry.isAffine_of_isClosedImmersion_of_surjective (g a ∣_ O a W)

end S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_opens_local_lifts_preimage_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_opens_local_lifts_preimage_eq (solution)
