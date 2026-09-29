-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8a823a93-0127-5580-bd5c-2176cbbc9c29

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

namespace SpecialPrime

theorem exists_preconnected_nhd {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ _root_.IsPreconnected (U : Set X) := by
  let B : Set X := ⋃ Z ∈ {Z ∈ irreducibleComponents X | x ∉ Z}, Z
  have hB : IsClosed B := by
    apply Set.Finite.isClosed_biUnion
    · exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (fun Z hZ => hZ.1)
    · intro Z hZ; exact isClosed_of_mem_irreducibleComponents _ hZ.1
  refine ⟨⟨Bᶜ, hB.isOpen_compl⟩, fun h => ?_, ?_⟩
  · obtain ⟨Z, hZ, hxZ⟩ := Set.mem_iUnion₂.mp h
    exact hZ.2 hxZ
  · have hcover : (Bᶜ : Set X) = ⋃₀ {S | ∃ Z ∈ irreducibleComponents X, x ∈ Z ∧ S = Z ∩ Bᶜ} := by
      ext z
      constructor
      · intro hz
        refine ⟨irreducibleComponent z ∩ Bᶜ, ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z, ?_, rfl⟩,
          mem_irreducibleComponent, hz⟩
        by_contra hxZ
        exact hz (Set.mem_iUnion₂.mpr ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z, hxZ⟩,
          mem_irreducibleComponent⟩)
      · rintro ⟨S, ⟨Z, -, -, rfl⟩, hzS⟩
        exact hzS.2
    change _root_.IsPreconnected (Bᶜ : Set X)
    rw [hcover]
    apply isPreconnected_sUnion x
    · rintro S ⟨Z, hZ, hxZ, rfl⟩
      exact ⟨hxZ, fun h => (Set.mem_iUnion₂.mp h).elim fun Z' hZ' => hZ'.1.2 hZ'.2⟩
    · rintro S ⟨Z, hZ, hxZ, rfl⟩
      have hZirr : IsPreirreducible Z := hZ.1.isPreirreducible
      have : IsPreirreducible (Z ∩ Bᶜ) := by
        intro u v hu hv ⟨a, ⟨haZ, haB⟩, hau⟩ ⟨b, ⟨hbZ, hbB⟩, hbv⟩
        obtain ⟨c, hcZ, ⟨hcu, hcB⟩, hcv, -⟩ := hZirr (u ∩ Bᶜ) (v ∩ Bᶜ) (hu.inter hB.isOpen_compl)
          (hv.inter hB.isOpen_compl) ⟨a, haZ, hau, haB⟩ ⟨b, hbZ, hbv, hbB⟩
        exact ⟨c, ⟨hcZ, hcB⟩, hcu, hcv⟩
      exact this.isPreconnected

theorem isDomain_stalk_of_smooth {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k))
    [Smooth g] [LocallyOfFiniteType g] [CompactSpace X] (x : X) : IsDomain (X.presheaf.stalk x) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : IsNoetherian X := {}
  obtain ⟨U, hxU, hU⟩ := exists_preconnected_nhd x
  haveI : PreconnectedSpace (U : Scheme.{u}) := isPreconnected_iff_preconnectedSpace.mp hU
  haveI : Nonempty (U : Scheme.{u}) := ⟨⟨x, hxU⟩⟩
  have hint : IsIntegral (U : Scheme.{u}) :=
    AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace (U.ι ≫ g)
  haveI : IsDomain ((U : Scheme.{u}).presheaf.stalk ⟨x, hxU⟩) := inferInstance
  exact Function.Injective.isDomain (U.ι.stalkMap ⟨x, hxU⟩).hom
    (ConcreteCategory.injective_of_mono_of_preservesPullback (U.ι.stalkMap ⟨x, hxU⟩))

theorem isDomain_localization_atPrime_of_smooth {k : Type u} [Field k] {C : Type u} [CommRing C] [Algebra k C]
    [Algebra.Smooth k C] (q : Ideal C) [q.IsPrime] : IsDomain (Localization.AtPrime q) := by
  let g : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k C))
  haveI : Smooth g := HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr ‹Algebra.Smooth k C›)
  have h := isDomain_stalk_of_smooth g ⟨q, inferInstance⟩
  haveI : IsDomain ((AlgebraicGeometry.structurePresheafInCommRingCat C).stalk ⟨q, inferInstance⟩) := h
  exact MulEquiv.isDomain _ (StructureSheaf.stalkIso C ⟨q, inferInstance⟩).toMulEquiv

theorem isDomain_quot_of_smooth
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    {B : Type u} [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (𝔓 : Ideal B) [𝔓.IsPrime] (hϖ𝔓 : algebraMap R B ϖ ∈ 𝔓)
    (O : Type u) [CommRing O] [Algebra B O] [IsLocalization.AtPrime O 𝔓] :
    IsDomain (O ⧸ Ideal.map (algebraMap B O) (Ideal.span {algebraMap R B ϖ})) := by
  classical
  let I₀ : Ideal R := Ideal.span {ϖ}
  haveI hmax : I₀.IsMaximal := by
    rw [show I₀ = IsLocalRing.maximalIdeal R from hϖ.symm]; exact IsLocalRing.maximalIdeal.isMaximal R
  let k := R ⧸ I₀
  letI : Field k := Ideal.Quotient.field I₀
  let I : Ideal B := Ideal.span {algebraMap R B ϖ}
  have hI : I = I₀.map (algebraMap R B) := by
    change Ideal.span {algebraMap R B ϖ} = Ideal.map (algebraMap R B) (Ideal.span {ϖ})
    rw [Ideal.map_span, Set.image_singleton]
  have hIle : I ≤ 𝔓 := by
    change Ideal.span {algebraMap R B ϖ} ≤ 𝔓
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hϖ𝔓
  let C := B ⧸ I

  letI algkC : Algebra k C := Ideal.Quotient.algebraQuotientOfLEComap (by rw [hI]; exact Ideal.le_comap_map)
  have hsmooth : Algebra.Smooth k C := by
    let e₁ : C ≃ₐ[B] B ⊗[R] k :=
      (Ideal.quotientEquivAlgOfEq B hI).trans (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀)
    let e₂ : B ⊗[R] k ≃ₐ[R] k ⊗[R] B := Algebra.TensorProduct.comm R B k
    have he₁ : ∀ b : B, e₁ (Ideal.Quotient.mk I b) = b ⊗ₜ[R] (1 : k) := by
      intro b
      change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀)
        (Ideal.quotientEquivAlgOfEq B hI (Ideal.Quotient.mk I b)) = _
      rw [Ideal.quotientEquivAlgOfEq_mk]
      exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk B I₀ b
    let e : C ≃ₐ[k] k ⊗[R] B :=
      AlgEquiv.ofRingEquiv (f := (e₁.toRingEquiv.trans e₂.toRingEquiv)) (by
        intro c
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        change e₂ (e₁ (Ideal.Quotient.mk I (algebraMap R B r))) = algebraMap k (k ⊗[R] B) (Ideal.Quotient.mk I₀ r)
        rw [he₁, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one r,
          ← TensorProduct.smul_tmul', map_smul]
        change r • (Algebra.TensorProduct.comm R B k) ((1 : B) ⊗ₜ[R] (1 : k)) = _
        rw [Algebra.TensorProduct.comm_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
        rfl)
    exact Algebra.Smooth.of_equiv e.symm

  let q : Ideal C := 𝔓.map (Ideal.Quotient.mk I)
  have hqcomap : q.comap (Ideal.Quotient.mk I) = 𝔓 := by
    change Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) 𝔓) = 𝔓
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hIle]
  haveI hq : q.IsPrime := by
    refine Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker]; exact hIle
  let O' := O ⧸ Ideal.map (algebraMap B O) I
  letI algCO' : Algebra C O' := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  haveI : IsLocalization (𝔓.primeCompl.map (Ideal.Quotient.mk I)) O' :=
    IsLocalization.of_surjective (M := 𝔓.primeCompl) (S := O) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk (Ideal.map (algebraMap B O) I)) Ideal.Quotient.mk_surjective (by rfl)
      (by rw [Ideal.mk_ker, Ideal.mk_ker])
  have hM : 𝔓.primeCompl.map (Ideal.Quotient.mk I) = q.primeCompl := by
    ext c
    constructor
    · rintro ⟨b, hb, rfl⟩
      change Ideal.Quotient.mk I b ∉ q
      intro hc
      apply hb
      change b ∈ 𝔓
      rw [← hqcomap]; exact hc
    · intro hc
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨b, ?_, rfl⟩
      intro hb
      exact hc (Ideal.mem_map_of_mem _ hb)
  haveI : IsLocalization.AtPrime O' q := by
    change IsLocalization q.primeCompl O'
    rw [← hM]; infer_instance
  haveI : IsDomain (Localization.AtPrime q) := isDomain_localization_atPrime_of_smooth (k := k) q
  exact MulEquiv.isDomain (Localization.AtPrime q) (IsLocalization.algEquiv q.primeCompl O' (Localization.AtPrime q)).toMulEquiv

set_option maxHeartbeats 3200000 in
theorem main
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (p : Y) (hp : f.base p = IsLocalRing.closedPoint R)
    [Algebra R (Y.presheaf.stalk p)]
    (halg : Y.fromSpecStalk p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk p)))) :
    algebraMap R (Y.presheaf.stalk p) ϖ ≠ 0 ∧
      (Ideal.span {algebraMap R (Y.presheaf.stalk p) ϖ}).IsPrime := by
  classical
  let O := Y.presheaf.stalk p

  have hmor : CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk p)) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base p) trivial) ≫
        f.stalkMap p := by
    apply Spec.map_injective
    rw [← halg, Spec.map_comp, ← Spec.fromSpecStalk_eq, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hc : ∀ r : R, algebraMap R O r =
      (f.stalkMap p).hom (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base p) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
    intro r
    exact congrArg (fun φ : CommRingCat.of R ⟶ Y.presheaf.stalk p => φ.hom r) hmor
  have hϖ0 : ϖ ≠ 0 := by
    intro h; apply IsDiscreteValuationRing.not_a_field R; rw [hϖ, Ideal.span_singleton_eq_bot]; exact h

  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  let A := Γ(Spec (CommRingCat.of R), ⊤)
  let B := Γ(Y, V)
  letI algAB : Algebra A B := (f.appLE ⊤ V le_top).hom.toAlgebra
  have hsAB : (f.appLE ⊤ V le_top).hom.Smooth :=
    HasRingHomProperty.appLE (P := @Smooth) f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  haveI : Algebra.Smooth A B := hsAB
  letI algRA : Algebra R A := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toAlgebra
  letI algRB : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.Smooth R A := by
    haveI : Algebra.Smooth R R := {}
    refine Algebra.Smooth.of_equiv (A := R) ?_
    exact AlgEquiv.ofBijective (Algebra.ofId R A)
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.bijective
  haveI : Algebra.Smooth R B := Algebra.Smooth.comp R A B

  let 𝔓 := hV.primeIdealOf ⟨p, hpV⟩
  letI algBO : Algebra B O := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨p, hpV⟩ : V)
  haveI hloc : IsLocalization.AtPrime O 𝔓.asIdeal := hV.isLocalization_stalk ⟨p, hpV⟩
  have htow : ∀ r : R, algebraMap B O (algebraMap R B r) = algebraMap R O r := by
    intro r
    rw [hc r]
    change (Y.presheaf.germ V p hpV).hom ((f.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      (f.stalkMap p).hom (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base p) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply _ (f.stalkMap p),
      Scheme.Hom.germ_stalkMap f ⊤ p trivial, Scheme.Hom.appLE, Category.assoc]
    erw [TopCat.Presheaf.germ_res]
  haveI : IsScalarTower R B O := IsScalarTower.of_algebraMap_eq fun r => (htow r).symm

  haveI : Module.Flat B O := IsLocalization.flat O 𝔓.asIdeal.primeCompl
  haveI : Module.Flat R O := Module.Flat.trans R B O
  have hne : algebraMap R O ϖ ≠ 0 := by
    intro h
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := O) (mem_nonZeroDivisors_of_ne_zero hϖ0)
    have h1 : ϖ • (1 : O) = ϖ • (0 : O) := by rw [Algebra.smul_def, mul_one, smul_zero]; exact h
    exact one_ne_zero (hreg h1)

  have hmem : algebraMap R B ϖ ∈ 𝔓.asIdeal := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff O 𝔓.asIdeal, htow, hc, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, isUnit_map_iff (f.stalkMap p).hom,
      ← Scheme.mem_basicOpen (Spec (CommRingCat.of R)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ) (f.base p) trivial,
      AlgebraicGeometry.basicOpen_eq_of_affine]
    have : ϖ ∈ (f.base p).asIdeal := by
      rw [hp]; change ϖ ∈ IsLocalRing.maximalIdeal R; rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
    intro hmem
    simp only [PrimeSpectrum.mem_basicOpen, SetLike.mem_coe] at hmem
    exact hmem this
  have hdom := isDomain_quot_of_smooth ϖ hϖ 𝔓.asIdeal hmem O
  have hmap : Ideal.map (algebraMap B O) (Ideal.span {algebraMap R B ϖ}) = Ideal.span {algebraMap R O ϖ} := by
    rw [Ideal.map_span, Set.image_singleton, htow]
  refine ⟨hne, ?_⟩
  change (Ideal.span {algebraMap R O ϖ}).IsPrime
  rw [← hmap]
  exact (Ideal.Quotient.isDomain_iff_prime _).mp hdom

end SpecialPrime

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (p : Y) (hp : f.base p = IsLocalRing.closedPoint R)
    [Algebra R (Y.presheaf.stalk p)]
    (halg : Y.fromSpecStalk p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk p)))) :
    algebraMap R (Y.presheaf.stalk p) ϖ ≠ 0 ∧
      (Ideal.span {algebraMap R (Y.presheaf.stalk p) ϖ}).IsPrime :=
  SpecialPrime.main ϖ hϖ f p hp halg

end S_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint (solution)
