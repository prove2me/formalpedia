-- Prove2me | solution 1 for AlgebraicGeometry.exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5c99d92e-d1e1-5187-b345-afa96303f731

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_algHom_retraction_stalk_and_ker_le_span_sup_sq_of_section_of_smoothOfRelativeDimension_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace SecParam

theorem eq_of_retraction_of_ker_le {A S : Type*} [CommRing A] [CommRing S] (ι : A →+* S) (π π' : S →+* A)
    (hπ : ∀ a, π (ι a) = a) (hπ' : ∀ a, π' (ι a) = a) (h : RingHom.ker π' ≤ RingHom.ker π) : π = π' := by
  ext z
  have hz : z - ι (π' z) ∈ RingHom.ker π' := by
    rw [RingHom.mem_ker, map_sub, hπ', sub_self]
  have hz' := h hz
  rw [RingHom.mem_ker, map_sub, hπ] at hz'
  exact sub_eq_zero.mp hz'

theorem eq_span_of_le_span_sup_sq {S : Type*} [CommRing S] [IsLocalRing S] {I : Ideal S} (hfg : I.FG)
    (hI : I ≤ maximalIdeal S) {t : S} (ht : t ∈ I) (hle : I ≤ Ideal.span {t} ⊔ I ^ 2) : I = Ideal.span {t} := by
  apply le_antisymm _ ((Ideal.span_singleton_le_iff_mem _).mpr ht)
  have hjac : I ≤ (⊥ : Ideal S).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact hI
  exact Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac (by rwa [Ideal.smul_eq_mul, ← pow_two])

theorem maximalIdeal_eq_ker_sup_map {A S : Type*} [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S]
    (ι : A →+* S) (π : S →+* A) (hπ : ∀ a, π (ι a) = a) :
    maximalIdeal S = RingHom.ker π ⊔ (maximalIdeal A).map ι := by
  have hkle : RingHom.ker π ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)
  apply le_antisymm
  · intro z hz
    have hk : z - ι (π z) ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, map_sub, hπ, sub_self]
    by_cases hu : IsUnit (π z)
    · exfalso
      have h1 : ι (π z) ∈ maximalIdeal S := by
        have e : ι (π z) = z - (z - ι (π z)) := by ring
        rw [e]
        exact sub_mem hz (hkle hk)
      exact (IsLocalRing.mem_maximalIdeal _).mp h1 (hu.map ι)
    · have hm : π z ∈ maximalIdeal A := hu
      have e : z = (z - ι (π z)) + ι (π z) := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mem_sup_left hk) (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hm))
  · refine sup_le hkle ?_
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun h =>
      (IsLocalRing.mem_maximalIdeal _).mp ha (by simpa [hπ] using h.map π)

theorem bijective_toStalk_closedPoint (A : Type u) [CommRing A] [IsLocalRing A] :
    Function.Bijective (StructureSheaf.toStalk A (closedPoint A)).hom := by
  letI : Algebra A ((Spec.structureSheaf A).presheaf.stalk (closedPoint A)) := StructureSheaf.stalkAlgebra A (closedPoint A)
  haveI : IsLocalization.AtPrime ((Spec.structureSheaf A).presheaf.stalk (closedPoint A)) (closedPoint A).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A (closedPoint A)
  have hM : (closedPoint A).asIdeal.primeCompl ≤ nonZeroDivisors A := fun u hu =>
    (show IsUnit u from not_not.mp hu).mem_nonZeroDivisors
  change Function.Bijective (algebraMap A ((Spec.structureSheaf A).presheaf.stalk (closedPoint A)))
  refine ⟨IsLocalization.injective _ hM, fun z => ?_⟩
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (closedPoint A).asIdeal.primeCompl z
  have hu : IsUnit (u : A) := not_not.mp u.2
  refine ⟨a * ↑hu.unit⁻¹, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]

end SecParam

open SecParam in

theorem solution
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
    [SmoothOfRelativeDimension 1 c]
    (σ : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ c = 𝟙 _) :
    ∃ t : X.presheaf.stalk (σ.base (closedPoint A)),
      RingHom.ker (Scheme.Hom.stalkMap σ (closedPoint A)).hom = Ideal.span {t} ∧
      maximalIdeal (X.presheaf.stalk (σ.base (closedPoint A))) =
        Ideal.span {t} ⊔ (maximalIdeal A).map ((X.presheaf.germ ⊤ (σ.base (closedPoint A)) trivial).hom.comp
          (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) := by
  classical
  let s := closedPoint A
  let S := X.presheaf.stalk (σ.base (closedPoint A))
  let algA : A →+* S := (X.presheaf.germ ⊤ (σ.base (closedPoint A)) trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)

  obtain ⟨π, t, hkerle, hπt, hle, -⟩ :=
    AlgebraicGeometry.exists_algHom_retraction_stalk_and_ker_le_span_sup_sq_of_section_of_smoothOfRelativeDimension_one
      c σ hσ (closedPoint A) (isClosed_singleton_closedPoint A)
  letI : Algebra A S := algA.toAlgebra
  have hret : ∀ a, π (algA a) = a := fun a => π.commutes a
  have hπt' : t ∈ RingHom.ker π.toRingHom := hπt

  let ι₀ : A →+* (Spec (CommRingCat.of A)).presheaf.stalk s :=
    ((Spec (CommRingCat.of A)).presheaf.germ ⊤ s trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hι₀ : Function.Bijective ι₀ := by
    have h := SecParam.bijective_toStalk_closedPoint A
    convert h using 1
    rfl
    rfl
  have key1 : ∀ a, (σ.stalkMap s).hom (algA a) = ι₀ a := by
    intro a
    show (σ.stalkMap s).hom ((X.presheaf.germ ⊤ (σ.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
      ((Spec (CommRingCat.of A)).presheaf.germ ⊤ s trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
    rw [Scheme.Hom.germ_stalkMap_apply]
    change ((Spec (CommRingCat.of A)).presheaf.germ ⊤ s trivial).hom ((c.appTop ≫ σ.appTop).hom _) = _
    rw [← AlgebraicGeometry.Scheme.Hom.comp_appTop, hσ]
    simp
  let e₀ : A ≃+* (Spec (CommRingCat.of A)).presheaf.stalk s := RingEquiv.ofBijective ι₀ hι₀
  let π' : S →+* A := e₀.symm.toRingHom.comp (σ.stalkMap s).hom
  have hret' : ∀ a, π' (algA a) = a := by
    intro a
    show e₀.symm ((σ.stalkMap s).hom (algA a)) = a
    rw [key1]
    exact e₀.symm_apply_apply a
  have hkerσ : RingHom.ker (σ.stalkMap s).hom = RingHom.ker π' := by
    ext z
    simp only [RingHom.mem_ker, π', RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      map_eq_zero_iff _ e₀.symm.injective]
  have hππ' : (π : S →+* A) = π' :=
    SecParam.eq_of_retraction_of_ker_le algA π π' hret hret' (hkerσ ▸ hkerle)
  have hker : RingHom.ker (σ.stalkMap s).hom = RingHom.ker π.toRingHom := by
    rw [hkerσ, ← hππ']
    rfl

  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have hfg : (RingHom.ker π.toRingHom).FG := by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := σ.base s) (U := ⊤) trivial
    have hVle : V ≤ c ⁻¹ᵁ ⊤ := le_top
    have hfp : (c.appLE ⊤ V hVle).hom.FinitePresentation :=
      HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) c inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ hVle
    let algB : A →+* Γ(X, V) := (c.appLE ⊤ V hVle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    have hfpB : algB.FinitePresentation :=
      hfp.comp (RingHom.FinitePresentation.of_bijective (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.bijective)
    letI : Algebra Γ(X, V) S := (X.presheaf.germ V (σ.base s) hxV).hom.toAlgebra
    haveI : IsLocalization.AtPrime S (hV.primeIdealOf ⟨σ.base s, hxV⟩).asIdeal := hV.isLocalization_stalk ⟨σ.base s, hxV⟩
    have hcompat : ∀ a, algebraMap Γ(X, V) S (algB a) = algA a := by
      intro a
      show (X.presheaf.germ V (σ.base s) hxV).hom ((c.appLE ⊤ V hVle).hom _) =
        (X.presheaf.germ ⊤ (σ.base s) trivial).hom (c.appTop.hom _)
      rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
      rfl
    letI : Algebra A Γ(X, V) := algB.toAlgebra
    haveI : Algebra.FinitePresentation A Γ(X, V) := hfpB
    let ψ : Γ(X, V) →ₐ[A] A :=
      { π.toRingHom.comp (algebraMap Γ(X, V) S) with
        commutes' := fun a => by
          show π (algebraMap Γ(X, V) S (algB a)) = a
          rw [hcompat]
          exact hret a }
    have hψsurj : Function.Surjective ψ := fun a => ⟨algB a, by
      show π (algebraMap Γ(X, V) S (algB a)) = a
      rw [hcompat]
      exact hret a⟩
    have hJ : (RingHom.ker ψ.toRingHom).FG := Algebra.FinitePresentation.ker_fG_of_surjective ψ hψsurj
    have hmap : RingHom.ker π.toRingHom = (RingHom.ker ψ.toRingHom).map (algebraMap Γ(X, V) S) := by
      apply le_antisymm
      · intro z hz
        obtain ⟨b, u, rfl⟩ := IsLocalization.exists_mk'_eq (hV.primeIdealOf ⟨σ.base s, hxV⟩).asIdeal.primeCompl z
        have hb : b ∈ RingHom.ker ψ.toRingHom := by
          have e := IsLocalization.mk'_spec S b u
          have e' := congrArg π e
          rw [map_mul] at e'
          rw [RingHom.mem_ker] at hz
          have hz' : π (IsLocalization.mk' S b u) = 0 := hz
          rw [hz', zero_mul] at e'
          exact e'.symm
        rw [IsLocalization.mk'_eq_mul_mk'_one]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb)
      · rw [Ideal.map_le_iff_le_comap]
        intro b hb
        exact hb
    rw [hmap]
    exact hJ.map _

  have hI : RingHom.ker π.toRingHom = Ideal.span {t} :=
    SecParam.eq_span_of_le_span_sup_sq hfg (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)) hπt' hle
  refine ⟨t, hker.trans hI, ?_⟩

  rw [← hI]
  exact SecParam.maximalIdeal_eq_ker_sup_map algA π.toRingHom hret

end S_AlgebraicGeometry_exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one (solution)
