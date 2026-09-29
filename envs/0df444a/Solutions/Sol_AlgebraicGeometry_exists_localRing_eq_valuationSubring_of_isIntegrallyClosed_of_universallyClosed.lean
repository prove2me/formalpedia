-- Prove2me | solution 1 for AlgebraicGeometry.exists_localRing_eq_valuationSubring_of_isIntegrallyClosed_of_universallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e8fa2a1f-6d68-50be-bc88-c0ec7fe3341c

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_Subalgebra_isMaximal_of_isPrime_of_ne_bot_of_isAlgebraic_adjoin_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_localRing_eq_valuationSubring_of_isIntegrallyClosed_of_universallyClosed

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_localRing_eq_valuationSubring_of_isIntegrallyClosed_of_universallyClosed.AlgebraicGeometry IsLocalRing AlgebraicCurve"

universe u v

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian Scheme.SpecMap_stalkSpecializes_fromSpecStalk UniversallyClosed ValuativeCommSq Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.stalkClosedPointTo Spec.map_injective UniversallyClosed.eq_valuativeCriterion Scheme.Spec_stalkClosedPointTo_fromSpecStalk SpecMap_ΓSpecIso_hom Spec.map_id ValuativeCriterion.Existence Scheme.fromSpecStalk_toSpecΓ_assoc ValuativeCriterion toSpecΓ Scheme.ΓSpecIso"
namespace NormalModelPointsAux
p2m_open "AlgebraicGeometry"

noncomputable def germConst {A₀ : Type u} [CommRing A₀] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A₀)) (x : X) (a : A₀) : X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a))

theorem algebraMap_germConst {A₀ : Type u} [CommRing A₀] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of A₀)) (x : X) (a : A₀) :
    algebraMap (X.presheaf.stalk x) X.functionField (germConst f x a) =
      SemistableModel.baseToFunctionField f a := by
  change (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom
      ((X.presheaf.germ ⊤ x trivial).hom _) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rfl

theorem fromSpecStalk_genericPoint_comp {A₀ : Type u} [CommRing A₀] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of A₀)) :
    X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map (CommRingCat.ofHom (SemistableModel.baseToFunctionField f)) := by
  have h1 : X.fromSpecStalk (genericPoint X) ≫ f ≫ (Spec (CommRingCat.of A₀)).toSpecΓ =
      Spec.map (f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial) := by
    rw [Scheme.toSpecΓ_naturality, Scheme.fromSpecStalk_toSpecΓ_assoc, ← Spec.map_comp]
  have h2 : X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map (f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial) ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv := by
    rw [← h1, Category.assoc, Category.assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  rw [h2, ← Spec.map_comp]
  rfl

theorem exists_centre {A₀ : Type u} [CommRing A₀] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of A₀)) [UniversallyClosed f] (V : ValuationSubring X.functionField)
    (hV : ∀ a : A₀, SemistableModel.baseToFunctionField f a ∈ V) :
    ∃ (c : X) (ψ : X.presheaf.stalk c →+* ↥V), IsLocalHom ψ ∧
      ∀ r : X.presheaf.stalk c, ((ψ r : ↥V) : X.functionField) =
        algebraMap (X.presheaf.stalk c) X.functionField r := by

  let ι₀ : A₀ →+* ↥V := (SemistableModel.baseToFunctionField f).codRestrict V hV
  let ι : CommRingCat.of A₀ ⟶ CommRingCat.of ↥V := CommRingCat.ofHom ι₀
  have hι : ι ≫ CommRingCat.ofHom (algebraMap ↥V X.functionField) =
      CommRingCat.ofHom (SemistableModel.baseToFunctionField f) := by
    ext a; rfl

  let S : ValuativeCommSq f :=
    { R := ↥V
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map ι
      commSq := ⟨by
        rw [← Spec.map_comp, hι]
        exact fromSpecStalk_genericPoint_comp f⟩ }
  have hE : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨l, hl₁, hl₂⟩ := (hE S).exists_lift

  refine ⟨l.base (closedPoint ↥V), (Scheme.stalkClosedPointTo l).hom, inferInstance, ?_⟩

  have hgen : genericPoint X ⤳ l.base (closedPoint ↥V) := genericPoint_specializes _
  have key : Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap ↥V X.functionField) =
      X.presheaf.stalkSpecializes hgen := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (l.base (closedPoint ↥V)))]
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact hl₁
  intro r
  have := congrArg (fun φ => φ.hom r) key
  exact this

end AlgebraicGeometry.NormalModelPointsAux

open AlgebraicGeometry.NormalModelPointsAux in
theorem solution
    {A₀ : Type u} [CommRing A₀]
    {X₀ : Scheme.{u}} (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsLocallyNoetherian X₀] [UniversallyClosed toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))
    {F₀ : Type v} [Field F₀] [Algebra A₀ F₀]
    (φ₀ : F₀ ≃+* X₀.functionField)
    (hφ₀ : ∀ a : A₀, φ₀ (algebraMap A₀ F₀ a) = SemistableModel.baseToFunctionField toBase₀ a)
    (t : F₀) [Algebra.IsAlgebraic ↥(Algebra.adjoin A₀ ({t} : Set F₀)) F₀]
    (O : ValuationSubring F₀)
    (hAO : ∀ a : A₀, algebraMap A₀ F₀ a ∈ O)
    (hAO' : ∀ a : A₀, algebraMap A₀ F₀ a ≠ 0 → (algebraMap A₀ F₀ a)⁻¹ ∈ O) :
    ∃ x : X₀, SemistableModel.localRing X₀ φ₀ x = O.toSubring := by
  classical

  let V : ValuationSubring X₀.functionField := O.comap φ₀.symm.toRingHom
  have hVmem : ∀ g : X₀.functionField, g ∈ V ↔ φ₀.symm g ∈ O := fun g => ValuationSubring.mem_comap
  have hV : ∀ a : A₀, SemistableModel.baseToFunctionField toBase₀ a ∈ V := by
    intro a
    rw [hVmem, ← hφ₀, RingEquiv.symm_apply_apply]
    exact hAO a

  obtain ⟨c, ψ, hψ, hψK⟩ := exists_centre toBase₀ V hV
  haveI := hψ
  refine ⟨c, ?_⟩

  let g : (X₀.presheaf.stalk c) →+* F₀ := (φ₀.symm : X₀.functionField ≃+* F₀).toRingHom.comp (algebraMap (X₀.presheaf.stalk c) X₀.functionField)
  have hg_apply : ∀ r : (X₀.presheaf.stalk c), g r = φ₀.symm (algebraMap (X₀.presheaf.stalk c) X₀.functionField r) := fun _ => rfl
  have hg_inj : Function.Injective g :=
    φ₀.symm.injective.comp (IsFractionRing.injective (X₀.presheaf.stalk c) X₀.functionField)
  have hloc : SemistableModel.localRing X₀ φ₀ c = g.range := rfl
  have halg_ne : ∀ r : (X₀.presheaf.stalk c), r ≠ 0 → algebraMap (X₀.presheaf.stalk c) X₀.functionField r ≠ 0 := fun r hr h =>
    hr (IsFractionRing.injective (X₀.presheaf.stalk c) X₀.functionField (h.trans (map_zero _).symm))

  have hsub : ∀ r : (X₀.presheaf.stalk c), g r ∈ O := by
    intro r
    rw [hg_apply, ← hVmem, ← hψK r]
    exact (ψ r).2

  have hgconst : ∀ a : A₀, g (germConst toBase₀ c a) = algebraMap A₀ F₀ a := by
    intro a
    rw [hg_apply, algebraMap_germConst, ← hφ₀, RingEquiv.symm_apply_apply]
  have hunit : ∀ a : A₀, algebraMap A₀ F₀ a ≠ 0 → IsUnit (germConst toBase₀ c a) := by
    intro a ha
    apply IsUnit.of_map ψ
    have hval : ((ψ (germConst toBase₀ c a) : ↥V) : X₀.functionField) = φ₀ (algebraMap A₀ F₀ a) := by
      rw [hψK, algebraMap_germConst, hφ₀]
    have hne : φ₀ (algebraMap A₀ F₀ a) ≠ 0 := (map_ne_zero φ₀).mpr ha
    have hinvV : (φ₀ (algebraMap A₀ F₀ a))⁻¹ ∈ V := by
      rw [hVmem, map_inv₀, RingEquiv.symm_apply_apply]
      exact hAO' a ha
    refine IsUnit.of_mul_eq_one (⟨(φ₀ (algebraMap A₀ F₀ a))⁻¹, hinvV⟩ : ↥V) ?_
    apply Subtype.ext
    change ((ψ (germConst toBase₀ c a) : ↥V) : X₀.functionField) * (φ₀ (algebraMap A₀ F₀ a))⁻¹ = 1
    rw [hval, mul_inv_cancel₀ hne]
  have hinvmem : ∀ a : A₀, algebraMap A₀ F₀ a ≠ 0 → (algebraMap A₀ F₀ a)⁻¹ ∈ g.range := by
    intro a ha
    obtain ⟨u, hu⟩ := hunit a ha
    refine ⟨((u⁻¹ : (X₀.presheaf.stalk c)ˣ) : (X₀.presheaf.stalk c)), ?_⟩
    rw [map_units_inv, hu, hgconst]

  let Sc : Subalgebra A₀ F₀ :=
    { carrier := Set.range g
      mul_mem' := fun ha hb => g.range.mul_mem ha hb
      one_mem' := g.range.one_mem
      add_mem' := fun ha hb => g.range.add_mem ha hb
      zero_mem' := g.range.zero_mem
      algebraMap_mem' := fun a => ⟨germConst toBase₀ c a, hgconst a⟩ }
  have hScS : ∀ a : A₀, algebraMap A₀ F₀ a ≠ 0 → (algebraMap A₀ F₀ a)⁻¹ ∈ Sc := hinvmem
  let gS : (X₀.presheaf.stalk c) →+* ↥Sc := g.codRestrict Sc (fun r => ⟨r, rfl⟩)
  have gS_bij : Function.Bijective gS := by
    refine ⟨fun x y h => hg_inj ?_, fun y => ?_⟩
    · exact congrArg Subtype.val h
    · obtain ⟨r, hr⟩ := y.2
      exact ⟨r, Subtype.ext hr⟩
  let e : (X₀.presheaf.stalk c) ≃+* ↥Sc := RingEquiv.ofBijective gS gS_bij

  have hprime : ∀ P : Ideal (X₀.presheaf.stalk c), P ≠ ⊥ → P.IsPrime → P = maximalIdeal (X₀.presheaf.stalk c) := by
    intro P hP hPp
    let P' : Ideal ↥Sc := Ideal.comap e.symm.toRingHom P
    haveI hP'p : P'.IsPrime := Ideal.comap_isPrime e.symm.toRingHom P
    have hmemP' : ∀ p : (X₀.presheaf.stalk c), e p ∈ P' ↔ p ∈ P := by
      intro p
      change e.symm.toRingHom (e p) ∈ P ↔ p ∈ P
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
    have hP' : P' ≠ ⊥ := by
      intro h
      apply hP
      refine le_bot_iff.mp fun p hp => ?_
      have hp' : e p ∈ P' := (hmemP' p).mpr hp
      rw [h, Ideal.mem_bot] at hp'
      rw [Ideal.mem_bot]
      exact e.injective (hp'.trans (map_zero e).symm)
    have hmax : P'.IsMaximal :=
      Subalgebra.isMaximal_of_isPrime_of_ne_bot_of_isAlgebraic_adjoin_singleton t Sc hScS P' hP'
    have hPeq : P = Ideal.comap e.toRingHom P' := by
      ext p
      rw [Ideal.mem_comap]
      exact (hmemP' p).symm
    have hPmax : P.IsMaximal := by
      rw [hPeq]
      exact Ideal.comap_isMaximal_of_surjective e.toRingHom e.surjective
    exact IsLocalRing.eq_maximalIdeal hPmax

  have htf := (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X₀.presheaf.stalk c)).out 3 1
  have hVR : ValuationRing (X₀.presheaf.stalk c) := htf.mp ⟨hn₀ c, hprime⟩

  rw [hloc]
  apply le_antisymm
  · rintro y ⟨r, rfl⟩
    exact hsub r
  · intro f hf
    have hf' : f ∈ O := hf
    by_contra hfn
    have hfV : φ₀ f ∈ V := by
      rw [hVmem, RingEquiv.symm_apply_apply]; exact hf'

    obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := (X₀.presheaf.stalk c)) (φ₀ f)
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    rcases ValuationRing.dvd_total r s with ⟨q, hq⟩ | ⟨q, hq⟩
    ·
      have hr0 : r ≠ 0 := by rintro rfl; rw [zero_mul] at hq; exact hs0 hq
      have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hs0 hq
      have hφf : φ₀ f = (algebraMap (X₀.presheaf.stalk c) X₀.functionField q)⁻¹ := by
        rw [← hrs, hq, map_mul, div_mul_eq_div_div, div_self (halg_ne r hr0), one_div]
      have hqu : ¬ IsUnit q := by
        rintro ⟨u, hu⟩
        apply hfn
        refine ⟨((u⁻¹ : (X₀.presheaf.stalk c)ˣ) : (X₀.presheaf.stalk c)), ?_⟩
        rw [hg_apply, map_units_inv, hu, ← hφf, RingEquiv.symm_apply_apply]
      apply hqu
      apply IsUnit.of_map ψ
      refine IsUnit.of_mul_eq_one (⟨φ₀ f, hfV⟩ : ↥V) ?_
      apply Subtype.ext
      change ((ψ q : ↥V) : X₀.functionField) * φ₀ f = 1
      rw [hψK, hφf, mul_inv_cancel₀ (halg_ne q hq0)]
    ·
      apply hfn
      refine ⟨q, ?_⟩
      have : φ₀ f = algebraMap (X₀.presheaf.stalk c) X₀.functionField q := by
        rw [← hrs, hq, map_mul, mul_div_cancel_left₀ _ (halg_ne s hs0)]
      rw [hg_apply, ← this, RingEquiv.symm_apply_apply]

end S_AlgebraicGeometry_exists_localRing_eq_valuationSubring_of_isIntegrallyClosed_of_universallyClosed
end P2MW
export P2MW.S_AlgebraicGeometry_exists_localRing_eq_valuationSubring_of_isIntegrallyClosed_of_universallyClosed (solution)
