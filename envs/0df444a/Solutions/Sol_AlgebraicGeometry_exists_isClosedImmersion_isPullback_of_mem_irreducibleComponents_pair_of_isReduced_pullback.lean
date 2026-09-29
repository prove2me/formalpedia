-- Prove2me | solution 1 for AlgebraicGeometry.exists_isClosedImmersion_isPullback_of_mem_irreducibleComponents_pair_of_isReduced_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/eb5e806e-ccb0-557a-b684-c16d4e884b81

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal
import Theorems.Thm_AlgebraicGeometry_isReduced_of_flat_of_isReduced_pullback_of_isFractionRing
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_isPullback_of_mem_irreducibleComponents_pair_of_isReduced_pullback

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_isPullback_of_mem_irreducibleComponents_pair_of_isReduced_pullback.AlgebraicGeometry TopologicalSpace Topology"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.fromSpecStalk_closedPoint isAffineOpen_opensRange morphismRestrict_base_coe Scheme.IdealSheafData.coe_support_vanishingIdeal Scheme.Hom Flat.SpecMap_iff stalkwise Scheme.range_fromSpecStalk Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme IsAffineOpen.fromSpecStalk Scheme.IdealSheafData.vanishingIdeal isReduced_of_isReduced_stalk IsPreimmersion.of_isLocalization Scheme.Pullback.range_snd Flat.stalkMap Flat IsClosedImmersion IsReduced IsPreimmersion Scheme.SpecMap_stalkMap_fromSpecStalk flat_and_surjective_SpecMap_iff IsAffineOpen isIso_of_isClosedImmersion_of_surjective isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.isIntegral_subscheme_vanishingIdeal isReduced_of_flat_of_isReduced_pullback_of_isFractionRing IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced"
p2m_open "AlgebraicGeometry"

private theorem surjective_specMap_of_fields {K Ω : Type u} [Field K] [Field Ω] (φ : K →+* Ω) :
    Surjective (Spec.map (CommRingCat.ofHom φ)) :=
  ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩

private theorem flat_specMap_of_moduleFlat {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom]
  exact (RingHom.flat_algebraMap_iff (R := R) (S := S)).mpr inferInstance

private theorem isReduced_stalk_of_flat {G Y : Scheme.{u}} (q : G ⟶ Y) [Flat q] [IsReduced G] (w : G) :
    _root_.IsReduced (Y.presheaf.stalk (q.base w)) := by
  let ψ := (q.stalkMap w).hom
  letI := ψ.toAlgebra
  haveI : Module.Flat (Y.presheaf.stalk (q.base w)) (G.presheaf.stalk w) := Flat.stalkMap q w
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (q.base w)) (G.presheaf.stalk w)) :=
    inferInstanceAs (IsLocalHom ψ)
  haveI : Module.FaithfullyFlat (Y.presheaf.stalk (q.base w)) (G.presheaf.stalk w) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact isReduced_of_injective (algebraMap (Y.presheaf.stalk (q.base w)) (G.presheaf.stalk w))
    (FaithfulSMul.algebraMap_injective _ _)

private theorem isReduced_of_flat_of_isPreimmersion {G Y : Scheme.{u}} (q : G ⟶ Y) [Flat q] [IsPreimmersion q]
    (h : ∀ w : G, _root_.IsReduced (Y.presheaf.stalk (q.base w))) : IsReduced G := by
  have : ∀ w : G, _root_.IsReduced (G.presheaf.stalk w) := by
    intro w
    let ψ := (q.stalkMap w).hom
    letI := ψ.toAlgebra
    haveI : Module.Flat (Y.presheaf.stalk (q.base w)) (G.presheaf.stalk w) := Flat.stalkMap q w
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (q.base w)) (G.presheaf.stalk w)) :=
      inferInstanceAs (IsLocalHom ψ)
    haveI : Module.FaithfullyFlat (Y.presheaf.stalk (q.base w)) (G.presheaf.stalk w) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    have hinj : Function.Injective ψ := FaithfulSMul.algebraMap_injective _ _
    have hsurj : Function.Surjective ψ := q.stalkMap_surjective w
    haveI := h w
    exact isReduced_of_injective (RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm
      (RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm.injective
  exact isReduced_of_isReduced_stalk G

private theorem flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hxU : x ∈ U := X.affineCover.covers x
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  dsimp [IsAffineOpen.fromSpecStalk]
  haveI : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
    haveI := hU.isLocalization_stalk ⟨x, hxU⟩
    haveI : Module.Flat Γ(X, U) (X.presheaf.stalk x) :=
      IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    have : Spec.map (X.presheaf.germ U x hxU) =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (X.presheaf.stalk x))) := rfl
    rw [this]; exact flat_specMap_of_moduleFlat
  infer_instance

private theorem exists_specializes_of_flat {P C : Scheme.{u}} (p : P ⟶ C) [Flat p] (w : P) (c : C)
    (hc : c ⤳ p.base w) : ∃ w' : P, w' ⤳ w ∧ p.base w' = c := by

  have hc' : c ∈ Set.range (C.fromSpecStalk (p.base w)).base := by
    rw [Scheme.range_fromSpecStalk]; exact hc
  obtain ⟨t, ht⟩ := hc'

  have hff : (p.stalkMap w).hom.FaithfullyFlat := by
    letI := (p.stalkMap w).hom.toAlgebra
    haveI : Module.Flat (C.presheaf.stalk (p.base w)) (P.presheaf.stalk w) := Flat.stalkMap p w
    haveI : IsLocalHom (algebraMap (C.presheaf.stalk (p.base w)) (P.presheaf.stalk w)) :=
      inferInstanceAs (IsLocalHom (p.stalkMap w).hom)
    exact (RingHom.faithfullyFlat_algebraMap_iff).mpr Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hs : Surjective (Spec.map (p.stalkMap w)) := ((flat_and_surjective_SpecMap_iff _).mpr hff).2
  obtain ⟨t', rfl⟩ := hs.surj t
  refine ⟨(P.fromSpecStalk w).base t', ?_, ?_⟩
  · have : (P.fromSpecStalk w).base t' ∈ Set.range (P.fromSpecStalk w).base := ⟨t', rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  · rw [← ht, ← Scheme.Hom.comp_apply, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.Hom.comp_apply]

private theorem fromSpecStalk_fractionRing_eq_genericPoint {X : Scheme.{u}} [IsIntegral X] (x : X)
    (t : Spec (CommRingCat.of (FractionRing (X.presheaf.stalk x)))) :
    (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)))) ≫
      X.fromSpecStalk x).base t = genericPoint X := by
  let K := FractionRing (X.presheaf.stalk x)
  set s : Spec (X.presheaf.stalk x) := (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) K))).base t
    with hs

  have hsgen : ∀ s' : Spec (X.presheaf.stalk x), s ⤳ s' := by
    intro s'
    have : s.asIdeal = ⊥ := by
      rw [hs]
      change Ideal.comap _ t.asIdeal = ⊥
      have ht : t.asIdeal = ⊥ := Ideal.eq_bot_of_prime (K := K) t.asIdeal
      rw [CommRingCat.hom_ofHom, ht, Ideal.comap_bot_of_injective _ (IsFractionRing.injective (X.presheaf.stalk x) K)]
    exact (PrimeSpectrum.le_iff_specializes s s').mp
      ((PrimeSpectrum.asIdeal_le_asIdeal s s').mp (by rw [this]; exact bot_le))
  rw [Scheme.Hom.comp_apply, ← hs]
  set y := (X.fromSpecStalk x).base s
  have h1 : genericPoint X ⤳ y := genericPoint_specializes y
  have h2 : y ⤳ genericPoint X := by
    have : genericPoint X ∈ Set.range (X.fromSpecStalk x).base := by
      rw [Scheme.range_fromSpecStalk]; exact genericPoint_specializes x
    obtain ⟨s', hs'⟩ := this
    rw [← hs']
    exact (hsgen s').map (X.fromSpecStalk x).continuous
  exact (h2.antisymm h1).eq

private theorem exists_pair_of_image_subset {α β : Type u} [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (hf : Continuous f) (hfs : Function.Surjective f)
    (Z₀ Z₁ : Set β) (hZ₀ : Z₀ ∈ irreducibleComponents β) (hZ₁ : Z₁ ∈ irreducibleComponents β)
    (hne : Z₀ ≠ Z₁) (hall : ∀ Z ∈ irreducibleComponents β, Z = Z₀ ∨ Z = Z₁)
    (W F : Set α) (hW : IsIrreducible W) (hF : IsIrreducible F) (hcov : ∀ a, a ∈ W ∨ a ∈ F) :
    ∃ Z Z' : Set β, Z ∈ irreducibleComponents β ∧ Z' ∈ irreducibleComponents β ∧ ¬ Z ⊆ Z' ∧
      f '' W ⊆ Z ∧ f '' F ⊆ Z' := by
  have cl : ∀ Z ∈ irreducibleComponents β, IsClosed Z := fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ
  have cover : ∀ b : β, b ∈ Z₀ ∪ Z₁ := fun b => by
    rcases hall _ (irreducibleComponent_mem_irreducibleComponents b) with h | h
    · exact Or.inl (h ▸ mem_irreducibleComponent)
    · exact Or.inr (h ▸ mem_irreducibleComponent)
  have sub : ∀ S : Set β, IsIrreducible S → S ⊆ Z₀ ∨ S ⊆ Z₁ := fun S hS =>
    (isPreirreducible_iff_isClosed_union_isClosed.mp hS.2) Z₀ Z₁ (cl _ hZ₀) (cl _ hZ₁) (fun b _ => cover b)
  have n01 : ¬ Z₀ ⊆ Z₁ := fun h => hne (Set.Subset.antisymm h (hZ₀.2 hZ₁.1 h))
  have n10 : ¬ Z₁ ⊆ Z₀ := fun h => hne (Set.Subset.antisymm (hZ₁.2 hZ₀.1 h) h)
  have hWi : IsIrreducible (f '' W) := hW.image f hf.continuousOn
  have hFi : IsIrreducible (f '' F) := hF.image f hf.continuousOn
  have all_in : ∀ Z : Set β, f '' W ⊆ Z → f '' F ⊆ Z → ∀ b, b ∈ Z := by
    intro Z h1 h2 b
    obtain ⟨a, rfl⟩ := hfs b
    rcases hcov a with ha | ha
    · exact h1 ⟨a, ha, rfl⟩
    · exact h2 ⟨a, ha, rfl⟩
  rcases sub _ hWi with hW0 | hW1 <;> rcases sub _ hFi with hF0 | hF1
  · exact absurd (fun b _ => all_in Z₀ hW0 hF0 b) n10
  · exact ⟨Z₀, Z₁, hZ₀, hZ₁, n01, hW0, hF1⟩
  · exact ⟨Z₁, Z₀, hZ₁, hZ₀, n10, hW1, hF0⟩
  · exact absurd (fun b _ => all_in Z₁ hW1 hF1 b) n01

end AlgebraicGeometry

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_isPullback_of_mem_irreducibleComponents_pair_of_isReduced_pullback.AlgebraicGeometry"

theorem solution
    {κ k : Type u} [Field κ] [Field k] [Algebra κ k]
    {X S : Scheme.{u}} (f : X ⟶ S) (a : Spec (CommRingCat.of κ) ⟶ S) (b : Spec (CommRingCat.of k) ⟶ S)
    (hb : b = Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ a)

    (Z₀ Z₁ : Set ↥(pullback f a))
    (hZ₀ : Z₀ ∈ irreducibleComponents ↥(pullback f a)) (hZ₁ : Z₁ ∈ irreducibleComponents ↥(pullback f a))
    (hne : Z₀ ≠ Z₁) (hall : ∀ Z ∈ irreducibleComponents ↥(pullback f a), Z = Z₀ ∨ Z = Z₁)

    [IsReduced (pullback f b)]
    {C : Scheme.{u}} [IsIntegral C] (i : C ⟶ pullback f b) [IsClosedImmersion i]
    (F : Set ↥(pullback f b)) (hF : IsIrreducible F) (hFc : IsClosed F)
    (hcover : ∀ z : ↥(pullback f b), z ∈ Set.range i.base ∨ z ∈ F) :
    ∃ (Cₚ : Scheme.{u}) (iₚ : Cₚ ⟶ pullback f a) (g : C ⟶ Cₚ),
      IsClosedImmersion iₚ ∧ IsIntegral Cₚ ∧
      Set.range iₚ.base ∈ irreducibleComponents ↥(pullback f a) ∧
      IsPullback g (i ≫ pullback.snd f b) (iₚ ≫ pullback.snd f a) (Spec.map (CommRingCat.ofHom (algebraMap κ k))) ∧
      g ≫ iₚ ≫ pullback.fst f a = i ≫ pullback.fst f b := by

  set φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of κ) := Spec.map (CommRingCat.ofHom (algebraMap κ k)) with hφ
  let π : pullback f b ⟶ pullback f a :=
    pullback.lift (pullback.fst f b) (pullback.snd f b ≫ φ) (by rw [pullback.condition, hb, Category.assoc])
  have hπfst : π ≫ pullback.fst f a = pullback.fst f b := pullback.lift_fst _ _ _
  have hπsnd : π ≫ pullback.snd f a = pullback.snd f b ≫ φ := pullback.lift_snd _ _ _
  have sqπ : IsPullback π (pullback.snd f b) (pullback.snd f a) φ := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f a) (v₁₃ := f) (h₂₂ := a) ?_ hπsnd (IsPullback.of_hasPullback f a)
    rw [hπfst, ← hb]; exact IsPullback.of_hasPullback f b
  haveI : Surjective π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sqπ.flip (surjective_specMap_of_fields (algebraMap κ k))
  haveI : Flat π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sqπ.flip flat_specMap_of_moduleFlat

  set W : Set ↥(pullback f b) := Set.range i.base with hW
  have hWirr : IsIrreducible W := by
    simpa [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ (↥C)).image _ i.continuous.continuousOn
  have hWc : IsClosed W := i.isClosedEmbedding.isClosed_range
  obtain ⟨Z, Z', hZ, hZ', hnZZ', hWZ, hFZ'⟩ :=
    exists_pair_of_image_subset π.base π.continuous π.surjective Z₀ Z₁ hZ₀ hZ₁ hne hall W F hWirr hF hcover
  clear hZ₀ hZ₁ hne hall Z₀ Z₁
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hZ'c : IsClosed Z' := isClosed_of_mem_irreducibleComponents Z' hZ'

  let ZC : Closeds ↥(pullback f a) := ⟨Z, hZc⟩
  let Cₚ : Scheme.{u} := (Scheme.IdealSheafData.vanishingIdeal ZC).subscheme
  let iₚ : Cₚ ⟶ pullback f a := (Scheme.IdealSheafData.vanishingIdeal ZC).subschemeι
  have hrange : Set.range iₚ.base = Z := by
    show Set.range (Scheme.IdealSheafData.vanishingIdeal ZC).subschemeι.base = Z
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  haveI : IsIntegral Cₚ := Scheme.isIntegral_subscheme_vanishingIdeal ZC hZ.1

  let p₁ := pullback.fst iₚ π
  let jP := pullback.snd iₚ π
  have sqPφ : IsPullback p₁ (jP ≫ pullback.snd f b) (iₚ ≫ pullback.snd f a) φ :=
    (IsPullback.of_hasPullback iₚ π).paste_vert sqπ

  let ξ : ↥Cₚ := genericPoint Cₚ
  have hθ : IsGenericPoint (iₚ.base ξ) Z := by
    have := (genericPoint_spec (↥Cₚ)).image iₚ.continuous
    rwa [Set.image_univ, hrange, hZc.closure_eq] at this
  have KF : ∀ y : ↥(pullback f b), π.base y = iₚ.base ξ → y ∉ F := fun y hy hyF =>
    hnZZ' ((hθ.mem_closed_set_iff hZ'c).mp (hFZ' ⟨y, hyF, hy⟩))
  have hgen : ∀ w : ↥(pullback iₚ π), p₁.base w = ξ → jP.base w ∉ F := by
    intro w hw
    apply KF
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact congrArg _ hw

  have hjPW : ∀ w : ↥(pullback iₚ π), jP.base w ∈ W := by
    intro w
    obtain ⟨w', hw'w, hw'⟩ := exists_specializes_of_flat p₁ w ξ (genericPoint_specializes _)
    have h1 : jP.base w' ∈ W := (hcover _).resolve_right (hgen w' hw')
    exact (hw'w.map jP.continuous).mem_closed hWc h1

  have hstalkU : ∀ y : ↥(pullback iₚ π), jP.base y ∉ F → _root_.IsReduced ((pullback iₚ π).presheaf.stalk y) := by
    intro y hy
    let U : (pullback f b).Opens := ⟨Fᶜ, hFc.isOpen_compl⟩
    haveI : IsReduced (↑U : Scheme.{u}) := isReduced_of_isOpenImmersion U.ι
    haveI : Surjective (jP ∣_ U) := by
      refine ⟨fun u => ?_⟩
      have hu : u.1 ∈ Set.range jP.base := by
        rw [Scheme.Pullback.range_snd]
        show π.base u.1 ∈ Set.range iₚ.base
        rw [hrange]
        exact hWZ ⟨u.1, (hcover u.1).resolve_right u.2, rfl⟩
      obtain ⟨w, hw⟩ := hu
      refine ⟨⟨w, show jP.base w ∈ U by rw [hw]; exact u.2⟩, Subtype.ext ?_⟩
      rw [morphismRestrict_base_coe]; exact hw
    haveI : IsIso (jP ∣_ U) := isIso_of_isClosedImmersion_of_surjective _
    haveI : IsReduced (↑(jP ⁻¹ᵁ U) : Scheme.{u}) := isReduced_of_isOpenImmersion (jP ∣_ U)

    let y' : ↥(jP ⁻¹ᵁ U) := ⟨y, hy⟩
    let e := ((jP ⁻¹ᵁ U).ι).stalkMap y'
    haveI : IsIso e := inferInstance
    have : ((jP ⁻¹ᵁ U).ι).base y' = y := rfl
    rw [← this]
    exact isReduced_of_injective e.hom (ConcreteCategory.injective_of_mono_of_preservesPullback e)
  haveI hPred : IsReduced (pullback iₚ π) := by
    have : ∀ z : ↥(pullback iₚ π), _root_.IsReduced ((pullback iₚ π).presheaf.stalk z) := by
      intro z
      let c := p₁.base z
      let O : Type u := ↥(Cₚ.presheaf.stalk c)
      haveI : IsDomain O := inferInstanceAs (IsDomain (Cₚ.presheaf.stalk c))
      let K := FractionRing O
      let fs : Spec (CommRingCat.of O) ⟶ Cₚ := Cₚ.fromSpecStalk c
      haveI : Flat fs := flat_fromSpecStalk Cₚ c
      let fX : pullback p₁ fs ⟶ Spec (CommRingCat.of O) := pullback.snd p₁ fs
      let sK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom (algebraMap O K))
      haveI : Flat sK := flat_specMap_of_moduleFlat
      haveI : IsPreimmersion sK := IsPreimmersion.of_isLocalization (R := O) (S := K) (nonZeroDivisors O)

      let q : pullback fX sK ⟶ pullback iₚ π := pullback.fst fX sK ≫ pullback.fst p₁ fs
      haveI : Flat q := inferInstance
      haveI : IsPreimmersion q := inferInstance
      haveI : IsReduced (pullback fX sK) := by
        refine isReduced_of_flat_of_isPreimmersion q fun w => hstalkU _ (hgen _ ?_)
        show (q ≫ p₁).base w = ξ
        have : q ≫ p₁ = pullback.snd fX sK ≫ sK ≫ fs := by
          simp only [q, Category.assoc, pullback.condition]
          rw [← Category.assoc, pullback.condition, Category.assoc]
        rw [this, Scheme.Hom.comp_apply]
        exact fromSpecStalk_fractionRing_eq_genericPoint c _
      haveI : IsReduced (pullback p₁ fs) := isReduced_of_flat_of_isReduced_pullback_of_isFractionRing (R := O) K fX

      obtain ⟨x₀, hx₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p₁) (g := fs) z
        (IsLocalRing.closedPoint O) (Scheme.fromSpecStalk_closedPoint (x := c)).symm
      rw [← hx₀]
      exact isReduced_stalk_of_flat (pullback.fst p₁ fs) x₀
    exact isReduced_of_isReduced_stalk _

  obtain ⟨g₀, hg₀, -⟩ := IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced iₚ (i ≫ π) (by
    rw [hrange]; rintro _ ⟨c0, rfl⟩; exact hWZ ⟨i.base c0, ⟨c0, rfl⟩, rfl⟩)
  let g : C ⟶ pullback iₚ π := pullback.lift g₀ i hg₀
  have hgp₁ : g ≫ p₁ = g₀ := pullback.lift_fst _ _ _
  have hgj : g ≫ jP = i := pullback.lift_snd _ _ _
  obtain ⟨h, hh, -⟩ := IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced i jP (by
    rintro _ ⟨w, rfl⟩; exact hjPW w)
  have hgh : g ≫ h = 𝟙 C := by
    rw [← cancel_mono i, Category.assoc, hh, hgj, Category.id_comp]
  have hhg : h ≫ g = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hgp₁, Category.id_comp, ← cancel_mono iₚ, Category.assoc, hg₀, ← Category.assoc, hh,
        pullback.condition]
    · rw [Category.assoc, hgj, hh, Category.id_comp]
  haveI : IsIso g := ⟨⟨h, hgh, hhg⟩⟩
  have sqC : IsPullback g (i ≫ pullback.snd f b) (jP ≫ pullback.snd f b) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, ← Category.assoc, hgj]⟩
  have sq := sqC.paste_horiz sqPφ
  rw [Category.id_comp, hgp₁] at sq
  refine ⟨Cₚ, iₚ, g₀, inferInstance, inferInstance, hrange ▸ hZ, sq, ?_⟩
  rw [← Category.assoc, hg₀, Category.assoc, hπfst]

#print axioms solution

end S_AlgebraicGeometry_exists_isClosedImmersion_isPullback_of_mem_irreducibleComponents_pair_of_isReduced_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_isPullback_of_mem_irreducibleComponents_pair_of_isReduced_pullback (solution)
