-- Prove2me | solution 1 for AlgebraicGeometry.isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/cb8af3df-0844-5eb0-a900-ef795ede1624

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace GammaTransfer

theorem surjective_specMap_of_surjective_of_isNilpotent_ker
    {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B')
    (hπs : Function.Surjective π) (hπn : IsNilpotent (RingHom.ker π)) :
    Surjective (Spec.map (CommRingCat.ofHom π)) := by
  have hhom : IsHomeomorph (PrimeSpectrum.comap π) := by
    refine PrimeSpectrum.isHomeomorph_comap π (fun x => ⟨1, Nat.one_pos, ?_⟩) ?_
    · obtain ⟨y, hy⟩ := hπs x
      exact ⟨y, by rw [pow_one]; exact hy⟩
    · intro x hx
      rw [mem_nilradical]
      obtain ⟨n, hn⟩ := hπn
      refine ⟨n, ?_⟩
      have : x ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at this
      simpa using this
  exact ⟨hhom.surjective⟩

theorem gamma0 {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B')
    (hπs : Function.Surjective π) (hπn : IsNilpotent (RingHom.ker π))
    {X X' : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of P)) (f' : X' ⟶ Spec (CommRingCat.of B'))
    (k' : X' ⟶ X) (hk : IsPullback k' f' f (Spec.map (CommRingCat.ofHom π))) :
    IsClosedImmersion k' ∧ Function.Bijective k'.base := by
  have hci : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) :=
    IsClosedImmersion.spec_of_surjective _ hπs
  have hsj : Surjective (Spec.map (CommRingCat.ofHom π)) :=
    surjective_specMap_of_surjective_of_isNilpotent_ker π hπs hπn
  have h1 : IsClosedImmersion k' := MorphismProperty.of_isPullback hk.flip hci
  have h2 : Surjective k' := MorphismProperty.of_isPullback hk.flip hsj
  exact ⟨h1, h1.isClosedEmbedding.injective, h2.1⟩

theorem finiteType_of_finiteType_baseChange_of_surjective_of_isNilpotent_ker
    {P B' A : Type*} [CommRing P] [CommRing B'] [CommRing A] [Algebra P B'] [Algebra P A]
    (hπs : Function.Surjective (algebraMap P B')) (hπn : IsNilpotent (RingHom.ker (algebraMap P B')))
    (h : (Algebra.TensorProduct.includeRight (R := P) (A := A) (B := B')).toRingHom.FiniteType) :
    Algebra.FiniteType P A := by
  classical
  set J : Ideal P := RingHom.ker (algebraMap P B') with hJdef
  let ι : A →ₐ[P] A ⊗[P] B' := Algebra.TensorProduct.includeLeft

  have hιs : Function.Surjective ι := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a b =>
        obtain ⟨p, rfl⟩ := hπs b
        refine ⟨p • a, ?_⟩
        change (p • a) ⊗ₜ[P] (1 : B') = a ⊗ₜ[P] algebraMap P B' p
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    | add x y hx hy =>
        obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by rw [map_add, ha, hb]⟩

  let JA : Ideal A := J.map (algebraMap P A)
  have hker : ∀ a : A, ι a = 0 → a ∈ JA := by
    let e : (P ⧸ J) ≃ₐ[P] B' := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId P B') hπs
    let g : (P ⧸ J) →ₐ[P] A ⧸ JA := Ideal.quotientMapₐ JA (Algebra.ofId P A) Ideal.le_comap_map
    let fB : B' →ₐ[P] A ⧸ JA := g.comp e.symm.toAlgHom
    let β : A ⊗[P] B' →ₐ[P] A ⧸ JA :=
      Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ P JA) fB (fun _ _ => mul_comm _ _)
    intro a ha
    have hβ : β (ι a) = Ideal.Quotient.mk JA a := by
      change β (a ⊗ₜ[P] (1 : B')) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rfl
    rw [ha, map_zero] at hβ
    exact Ideal.Quotient.eq_zero_iff_mem.mp hβ.symm

  letI instB : Algebra B' (A ⊗[P] B') :=
    (Algebra.TensorProduct.includeRight (R := P) (A := A) (B := B')).toRingHom.toAlgebra
  have hFT : Algebra.FiniteType B' (A ⊗[P] B') := h
  obtain ⟨T, hT⟩ := hFT.out
  choose s hs using fun t : A ⊗[P] B' => hιs t
  let S : Subalgebra P A := Algebra.adjoin P (s '' (T : Set (A ⊗[P] B')))

  have hS' : ∀ x : A ⊗[P] B', ∃ a ∈ S, ι a = x := by
    let S' : Subalgebra B' (A ⊗[P] B') :=
      { carrier := {x | ∃ a ∈ S, ι a = x}
        mul_mem' := by
          rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
          exact ⟨a * b, S.mul_mem ha hb, map_mul _ _ _⟩
        add_mem' := by
          rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
          exact ⟨a + b, S.add_mem ha hb, map_add _ _ _⟩
        algebraMap_mem' := by
          intro b
          obtain ⟨p, rfl⟩ := hπs b
          refine ⟨p • 1, S.smul_mem S.one_mem p, ?_⟩
          change (p • (1 : A)) ⊗ₜ[P] (1 : B') = (1 : A) ⊗ₜ[P] algebraMap P B' p
          rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul] }
    have hle : Algebra.adjoin B' (T : Set (A ⊗[P] B')) ≤ S' := by
      refine Algebra.adjoin_le ?_
      intro t ht
      exact ⟨s t, Algebra.subset_adjoin ⟨t, ht, rfl⟩, hs t⟩
    intro x
    have hx : x ∈ S' := hle (by rw [hT]; exact Algebra.mem_top)
    exact hx

  have h1 : (⊤ : Submodule P A) ≤ S.toSubmodule ⊔ J • (⊤ : Submodule P A) := by
    intro a _
    obtain ⟨b, hb, hba⟩ := hS' (ι a)
    have hmem : a - b ∈ JA := hker (a - b) (by rw [map_sub, hba, sub_self])
    have hmem' : a - b ∈ J • (⊤ : Submodule P A) := by
      rw [Ideal.smul_top_eq_map]; exact hmem
    have : a = b + (a - b) := by ring
    rw [this]
    exact Submodule.add_mem_sup hb hmem'

  have h2 : ∀ n : ℕ, (⊤ : Submodule P A) ≤ S.toSubmodule ⊔ J ^ n • (⊤ : Submodule P A) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
    | succ n ih =>
        calc (⊤ : Submodule P A) ≤ S.toSubmodule ⊔ J ^ n • (⊤ : Submodule P A) := ih
          _ ≤ S.toSubmodule ⊔ J ^ n • (S.toSubmodule ⊔ J • (⊤ : Submodule P A)) :=
              sup_le_sup_left (Submodule.smul_mono le_rfl h1) _
          _ = S.toSubmodule ⊔ (J ^ n • S.toSubmodule ⊔ J ^ (n + 1) • (⊤ : Submodule P A)) := by
              rw [Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ]
          _ ≤ S.toSubmodule ⊔ J ^ (n + 1) • (⊤ : Submodule P A) :=
              sup_le le_sup_left (sup_le (le_sup_left.trans' Submodule.smul_le_right) le_sup_right)
  obtain ⟨N, hN⟩ := hπn
  have hN' : J ^ N = ⊥ := hN
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro a _
    have := h2 N (Submodule.mem_top : a ∈ (⊤ : Submodule P A))
    rw [hN', Submodule.bot_smul, sup_bot_eq] at this
    exact this
  exact ⟨⟨(T.image s), by rw [Finset.coe_image]; exact htop⟩⟩

theorem locallyOfFiniteType_specMap_of_pullback_snd {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B')
    (hπs : Function.Surjective π) (hπn : IsNilpotent (RingHom.ker π))
    {R : CommRingCat.{0}} (ψ : CommRingCat.of P ⟶ R)
    (h : LocallyOfFiniteType (pullback.snd (Spec.map ψ) (Spec.map (CommRingCat.ofHom π)))) :
    LocallyOfFiniteType (Spec.map ψ) := by
  letI algR : Algebra P R := ψ.hom.toAlgebra
  letI algB : Algebra P B' := π.toAlgebra
  have h' : LocallyOfFiniteType (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap P R)))
      (Spec.map (CommRingCat.ofHom (algebraMap P B')))) := h
  rw [← pullbackSpecIso_hom_snd P R B',
    MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType),
    HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h'
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  have hπs' : Function.Surjective (algebraMap P B') := hπs
  have hπn' : IsNilpotent (RingHom.ker (algebraMap P B')) := hπn
  exact finiteType_of_finiteType_baseChange_of_surjective_of_isNilpotent_ker hπs' hπn' h'

theorem gamma1 {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B')
    (hπs : Function.Surjective π) (hπn : IsNilpotent (RingHom.ker π))
    {X X' : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of P)) (f' : X' ⟶ Spec (CommRingCat.of B'))
    (k' : X' ⟶ X) (hk : IsPullback k' f' f (Spec.map (CommRingCat.ofHom π)))
    (hft : LocallyOfFiniteType f') : LocallyOfFiniteType f := by
  have hsnd : LocallyOfFiniteType (pullback.snd f (Spec.map (CommRingCat.ofHom π))) := by
    rw [← hk.isoPullback_inv_snd]; infer_instance
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) X.affineCover]
  intro i
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.affineCover.f i ≫ f)
  have h2 : LocallyOfFiniteType (pullback.snd (X.affineCover.f i)
      (pullback.fst f (Spec.map (CommRingCat.ofHom π))) ≫ pullback.snd f (Spec.map (CommRingCat.ofHom π))) :=
    inferInstance
  have h3 : LocallyOfFiniteType (pullback.snd (Spec.map ψ) (Spec.map (CommRingCat.ofHom π))) := by
    rw [hψ, ← pullbackRightPullbackFstIso_inv_snd_snd,
      MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType)]
    exact h2
  have key := locallyOfFiniteType_specMap_of_pullback_snd π hπs hπn ψ h3
  rw [hψ] at key
  exact key

theorem isSeparated_of_isSeparated_comp_of_surjective {X X' S : Scheme.{0}} (k : X' ⟶ X) (f : X ⟶ S)
    [IsClosedImmersion k] [Surjective k] [IsSeparated (k ≫ f)] : IsSeparated f := by

  let μ := pullback.map (k ≫ f) (k ≫ f) f f k k (𝟙 S) ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)
  have hμc : IsClosedImmersion μ := MorphismProperty.pullbackMap (P := @IsClosedImmersion) ‹_› ‹_› rfl rfl
  have hμs : Surjective μ := MorphismProperty.pullbackMap (P := @Surjective) ‹_› ‹_› rfl rfl
  have hcomm : k ≫ pullback.diagonal f = pullback.diagonal (k ≫ f) ≫ μ := by
    apply pullback.hom_ext <;>
      simp only [μ, pullback.diagonal, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
  have hrange : Set.range (pullback.diagonal f).base = μ.base '' Set.range (pullback.diagonal (k ≫ f)).base := by
    have h1 : Set.range (pullback.diagonal f).base = Set.range (k ≫ pullback.diagonal f).base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr (Surjective.surj (f := k)), Set.image_univ]
    rw [h1, hcomm, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hclosed : IsClosed (Set.range (pullback.diagonal f).base) := by
    rw [hrange]
    exact hμc.isClosedEmbedding.isClosedMap _ (pullback.diagonal (k ≫ f)).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩

theorem gamma2 {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B')
    (hπs : Function.Surjective π)
    {X X' : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of P)) (f' : X' ⟶ Spec (CommRingCat.of B'))
    (k' : X' ⟶ X) (hk : IsPullback k' f' f (Spec.map (CommRingCat.ofHom π)))
    [IsClosedImmersion k'] [Surjective k'] [LocallyOfFiniteType f]
    (hp : IsProper f') : IsProper f := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) := IsClosedImmersion.spec_of_surjective _ hπs
  haveI : IsProper (k' ≫ f) := by rw [hk.w]; infer_instance
  haveI : UniversallyClosed f := UniversallyClosed.of_comp_surjective k' f
  haveI : IsSeparated f := isSeparated_of_isSeparated_comp_of_surjective k' f
  constructor

theorem isIso_residueFieldMap_of_surjectiveOnStalks {X Y : Scheme.{0}} (g : X ⟶ Y) [SurjectiveOnStalks g]
    (x : X) : IsIso (g.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(g.residueFieldMap x).hom.injective, ?_⟩
  have hs : Function.Surjective ((g.stalkMap x ≫ X.residue x).hom) := by
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (X.residue_surjective x).comp (g.stalkMap_surjective x)
  rw [← Scheme.residue_residueFieldMap, CommRingCat.hom_comp, RingHom.coe_comp] at hs
  exact Function.Surjective.of_comp hs

theorem smooth_of_isPullback_of_isIso {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {u : B ⟶ D} {v : C ⟶ D}
    (sq : IsPullback fst snd u v) (hv : IsIso v) (hs : Smooth snd) : Smooth u := by
  haveI : IsIso (pullback.fst u v) := inferInstance
  haveI : IsIso fst := by
    rw [← sq.isoPullback_hom_fst]; infer_instance
  have hu : u = inv fst ≫ snd ≫ v := by
    rw [← sq.w, IsIso.inv_hom_id_assoc]
  rw [hu]
  infer_instance

theorem gamma3 {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B')
    (hπs : Function.Surjective π)
    {X X' : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of P)) (f' : X' ⟶ Spec (CommRingCat.of B'))
    (k' : X' ⟶ X) (hk : IsPullback k' f' f (Spec.map (CommRingCat.ofHom π)))
    (hsurj : Surjective (Spec.map (CommRingCat.ofHom π)))
    (hfl : Flat f) (hfp : LocallyOfFinitePresentation f) (hsm : Smooth f') : Smooth f := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) := IsClosedImmersion.spec_of_surjective _ hπs
  refine Smooth.of_smooth_fiberToSpecResidueField f fun y => ?_
  obtain ⟨y', rfl⟩ := hsurj.1 y
  have sq := isPullback_fiberToSpecResidueField_of_isPullback hk y'
  have hres : IsIso ((Spec.map (CommRingCat.ofHom π)).residueFieldMap y') :=
    isIso_residueFieldMap_of_surjectiveOnStalks _ y'
  have hres' : IsIso (Spec.map ((Spec.map (CommRingCat.ofHom π)).residueFieldMap y')) := inferInstance
  have hsm' : Smooth (f'.fiberToSpecResidueField y') :=
    MorphismProperty.pullback_snd (P := @Smooth) _ _ hsm
  exact smooth_of_isPullback_of_isIso sq hres' hsm'

end GammaTransfer

open GammaTransfer in
theorem solution
    {P B' : Type} [CommRing P] [CommRing B'] (π : P →+* B')
    (hπs : Function.Surjective π) (hπn : IsNilpotent (RingHom.ker π))
    {X X' : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of P)) (f' : X' ⟶ Spec (CommRingCat.of B'))
    (k' : X' ⟶ X) (hk : IsPullback k' f' f (Spec.map (CommRingCat.ofHom π))) :
    (IsClosedImmersion k' ∧ Function.Bijective k'.base) ∧
    (LocallyOfFiniteType f' → LocallyOfFiniteType f) ∧
    (IsProper f' → IsProper f) ∧
    (Flat f → LocallyOfFinitePresentation f → Smooth f' → Smooth f) := by
  obtain ⟨hci, hbij⟩ := gamma0 π hπs hπn f f' k' hk
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom π)) :=
    surjective_specMap_of_surjective_of_isNilpotent_ker π hπs hπn
  refine ⟨⟨hci, hbij⟩, fun h => gamma1 π hπs hπn f f' k' hk h, fun hp => ?_, fun hfl hfp hsm => ?_⟩
  · haveI := hci
    haveI : Surjective k' := ⟨hbij.2⟩
    haveI : LocallyOfFiniteType f := gamma1 π hπs hπn f f' k' hk inferInstance
    exact gamma2 π hπs f f' k' hk hp
  · exact gamma3 π hπs f f' k' hk hsurj hfl hfp hsm

end S_AlgebraicGeometry_isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker
end P2MW
export P2MW.S_AlgebraicGeometry_isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker (solution)
