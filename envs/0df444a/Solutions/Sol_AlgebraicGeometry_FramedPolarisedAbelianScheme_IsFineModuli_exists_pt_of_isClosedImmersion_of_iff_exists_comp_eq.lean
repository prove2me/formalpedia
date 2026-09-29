-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.IsFineModuli.exists_pt_of_isClosedImmersion_of_iff_exists_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/e85bcb31-783f-56b1-8253-52798b38b1b8

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_IsFineModuli_exists_pt_of_isClosedImmersion_of_iff_exists_comp_eq

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (g N n : ℕ) (B : Type) [CommRing B]
    (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of B))
    (ptH : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FramedPolarisedAbelianScheme g N n S → SchemeHomOver s πH)
    (hH : FramedPolarisedAbelianScheme.IsFineModuli g N n H πH ptH)
    (hsep : IsSeparated πH) (hqc : QuasiCompact πH) (hfp : LocallyOfFinitePresentation πH)
    (hAF : ∀ F : Finset H, ∃ U : H.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (hQP : (∃ (qpm : ℕ) (qpι : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpm + 1)) B)), IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpm = πH))
    (Θ : ∀ (S : Type) [CommRing S], FramedPolarisedAbelianScheme g N n S → Prop)
    (HΘ : Scheme.{0}) (ι : HΘ ⟶ H) (hι : IsClosedImmersion ι) (hιfp : LocallyOfFinitePresentation ι)
    (hΘ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (X : FramedPolarisedAbelianScheme g N n S),
      Θ S X ↔ ∃ y : Spec (CommRingCat.of S) ⟶ HΘ, y ≫ ι = (ptH S s X).1) :
    ∃ (ptΘ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (X : FramedPolarisedAbelianScheme g N n S), Θ S X → SchemeHomOver s (ι ≫ πH)),
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (X : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X), (ptΘ S s X hX).1 ≫ ι = (ptH S s X).1) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (X X' : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X) (hX' : Θ S X'),
        FramedPolarisedAbelianScheme.Iso X X' → ptΘ S s X hX = ptΘ S s X' hX') ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S') (hX : Θ S X) (hX' : Θ S' X'),
        FramedPolarisedAbelianScheme.IsPullback φ X X' →
        (ptΘ S' s' X' hX').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptΘ S s X hX).1) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s (ι ≫ πH)),
        ∃ (X : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X), ptΘ S s X hX = x) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (X X' : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X) (hX' : Θ S X'), ptΘ S s X hX = ptΘ S s X' hX' →
        FramedPolarisedAbelianScheme.Iso X X') ∧
      IsSeparated (ι ≫ πH) ∧ QuasiCompact (ι ≫ πH) ∧ LocallyOfFinitePresentation (ι ≫ πH) ∧
      (∀ F : Finset HΘ, ∃ U : HΘ.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
      (∃ (qpn : ℕ) (qpι : HΘ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) B)),
        IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpn = ι ≫ πH) := by
  classical
  haveI := hι
  haveI := hιfp
  haveI := hsep
  haveI := hqc
  haveI := hfp

  let ptΘ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (X : FramedPolarisedAbelianScheme g N n S), Θ S X → SchemeHomOver s (ι ≫ πH) :=
    fun S _ s X hX => ⟨((hΘ S s X).mp hX).choose, by
      rw [← Category.assoc, ((hΘ S s X).mp hX).choose_spec]; exact (ptH S s X).2⟩
  have hfac : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (X : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X), (ptΘ S s X hX).1 ≫ ι = (ptH S s X).1 :=
    fun S _ s X hX => ((hΘ S s X).mp hX).choose_spec
  refine ⟨ptΘ, hfac, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro S _ s X X' hX hX' e
    apply Subtype.ext
    rw [← cancel_mono ι, hfac S s X hX, hfac S s X' hX', hH.pt_iso S s X X' e]
  ·
    intro S S' _ _ φ s s' hss' X X' hX hX' hP
    rw [← cancel_mono ι, Category.assoc, hfac S' s' X' hX', hfac S s X hX]
    exact hH.pt_pullback S S' φ s s' hss' X X' hP
  ·
    intro S _ s x
    obtain ⟨X, hX⟩ := hH.pt_surjective S s ⟨x.1 ≫ ι, by rw [Category.assoc]; exact x.2⟩
    have hΘX : Θ S X := (hΘ S s X).mpr ⟨x.1, by rw [hX]⟩
    refine ⟨X, hΘX, Subtype.ext ?_⟩
    rw [← cancel_mono ι, hfac S s X hΘX, hX]
  ·
    intro S _ s X X' hX hX' h
    apply hH.pt_injective S s X X'
    apply Subtype.ext
    rw [← hfac S s X hX, ← hfac S s X' hX', h]
  · infer_instance
  · infer_instance
  · infer_instance
  ·
    intro F
    obtain ⟨U, hU, hFU⟩ := hAF (F.image ι.base)
    refine ⟨ι ⁻¹ᵁ U, hU.preimage ι, fun x hx => ?_⟩
    exact hFU _ (Finset.mem_image_of_mem _ hx)
  ·
    obtain ⟨qpm, qpι, hqpι, hq⟩ := hQP
    haveI := hqpι
    exact ⟨qpm, ι ≫ qpι, inferInstance, by rw [Category.assoc, hq]⟩

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_IsFineModuli_exists_pt_of_isClosedImmersion_of_iff_exists_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_IsFineModuli_exists_pt_of_isClosedImmersion_of_iff_exists_comp_eq (solution)
