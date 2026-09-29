-- Prove2me | solution 1 for AlgebraicCurve.exists_closedPoint_range_stalk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/93d43637-3802-586d-8b78-23ba79164c59

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_closedPoint_range_stalk_eq

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place baseToFunctionField isClosed_singleton_of_ne_genericPoint"
p2m_open "AlgebraicCurve"

theorem exists_lift_of_valuationSubring
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c]
    (R : ValuationSubring C.functionField) (hK : ∀ a : K, baseToFunctionField c a ∈ R) :
    ∃ ℓ : Spec (CommRingCat.of R) ⟶ C,
      Spec.map (CommRingCat.ofHom (algebraMap R C.functionField)) ≫ ℓ =
        C.fromSpecStalk (genericPoint C) ∧
      ℓ ≫ c = Spec.map (CommRingCat.ofHom ((baseToFunctionField c).codRestrict R hK)) := by
  classical
  set η := genericPoint C with hη
  let A : CommRingCat.of R ⟶ C.presheaf.stalk η :=
    CommRingCat.ofHom (algebraMap R C.functionField)
  let B : CommRingCat.of K ⟶ CommRingCat.of R :=
    CommRingCat.ofHom ((baseToFunctionField c).codRestrict R hK)
  have hBA : B ≫ A = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫
      C.presheaf.germ ⊤ η trivial := by
    ext a
    rfl

  have w : C.fromSpecStalk η ≫ c = Spec.map A ≫ Spec.map B := by
    apply ext_of_isAffine
    rw [← Spec.map_comp, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
    have h1 : (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk η)).Opens) ≤ ⊤)).op = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [h1, CategoryTheory.Functor.map_id, Category.comp_id]

    have h2 : (Spec.map (B ≫ A)).appTop =
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ (B ≫ A) ≫
          (Scheme.ΓSpecIso (C.presheaf.stalk η)).inv := by
      rw [← Iso.inv_comp_eq]
      exact (Scheme.ΓSpecIso_inv_naturality (B ≫ A)).symm
    rw [h2, hBA]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

  have hvc : ValuativeCriterion c := by
    have h : IsProper c := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  obtain ⟨ℓ, hl₁, hl₂⟩ := (hvc.existence ⟨R, C.functionField, C.fromSpecStalk η, Spec.map B, ⟨w⟩⟩).exists_lift
  dsimp only at hl₁ hl₂
  exact ⟨ℓ, hl₁, hl₂⟩

private theorem _root_.ValuationSubring.eq_of_le_of_isUnit_imp {F : Type*} [Field F]
    {S R : ValuationSubring F} (hle : S ≤ R)
    (hunit : ∀ s : S, IsUnit (⟨(s : F), hle s.2⟩ : R) → IsUnit s) : S = R := by
  refine le_antisymm hle fun r hr => ?_
  by_contra hrS
  have hr0 : r ≠ 0 := by rintro rfl; exact hrS S.zero_mem
  have hinv : r⁻¹ ∈ S := (S.mem_or_inv_mem r).resolve_left hrS
  have hu : IsUnit (⟨r⁻¹, hle hinv⟩ : R) :=
    isUnit_iff_exists_inv.mpr ⟨⟨r, hr⟩, Subtype.ext (inv_mul_cancel₀ hr0)⟩
  obtain ⟨w, hw⟩ := hunit ⟨r⁻¹, hinv⟩ hu

  have : ((w⁻¹ : Sˣ) : S).1 = r := by
    have h1 : ((w⁻¹ : Sˣ) : S).1 * r⁻¹ = 1 := by
      have := congrArg (fun t : S => t.1) (w.inv_mul)
      simpa [hw] using this
    field_simp at h1
    linear_combination h1
  exact hrS (this ▸ ((w⁻¹ : Sˣ) : S).2)

p2m_alias "P2MW.S_AlgebraicCurve_exists_closedPoint_range_stalk_eq.ValuationSubring.eq_of_le_of_isUnit_imp" "ValuationSubring.eq_of_le_of_isUnit_imp"
end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_exists_closedPoint_range_stalk_eq.AlgebraicCurve in

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ v : AlgebraicCurve.Place K C.functionField, ∃ x : C, IsClosed ({x} : Set C) ∧
      (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring := by
  letI := (baseToFunctionField c).toAlgebra
  intro v
  classical
  set R := v.toValuationSubring with hRdef
  have hK : ∀ a : K, baseToFunctionField c a ∈ R := v.algebraMap_mem'
  obtain ⟨ℓ, hl₁, -⟩ := exists_lift_of_valuationSubring c R hK
  set x := ℓ.base (closedPoint R) with hxdef
  have hgen : genericPoint C ⤳ x := (genericPoint_spec C).specializes trivial

  set φ := Scheme.stalkClosedPointTo ℓ with hφdef
  have hφ : φ ≫ CommRingCat.ofHom (algebraMap R C.functionField) =
      C.presheaf.stalkSpecializes hgen := by
    apply Spec.map_injective
    rw [← cancel_mono (C.fromSpecStalk x), Spec.map_comp, Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hφ' : ∀ s, algebraMap R C.functionField (φ.hom s) =
      algebraMap (C.presheaf.stalk x) C.functionField s := by
    intro s
    have := congrArg (fun g => g.hom s) hφ
    simp at this
    exact this

  haveI : ValuationRing (C.presheaf.stalk x) :=
    AlgebraicGeometry.valuationRing_stalk_of_smoothOfRelativeDimension_one c x
  let S : ValuationSubring C.functionField :=
    (ValuationRing.valuation (C.presheaf.stalk x) C.functionField).valuationSubring
  have hS : ∀ f, f ∈ S ↔ ∃ a, algebraMap (C.presheaf.stalk x) C.functionField a = f := fun f =>
    ValuationRing.mem_integer_iff (C.presheaf.stalk x) C.functionField f
  have hSR : S ≤ R := by
    intro f hf
    obtain ⟨a, rfl⟩ := (hS f).mp hf
    rw [← hφ' a]
    exact (φ.hom a).2
  let ψ : C.presheaf.stalk x →+* S :=
    (algebraMap (C.presheaf.stalk x) C.functionField).codRestrict S fun a => (hS _).mpr ⟨a, rfl⟩
  have hunit : ∀ s : S, IsUnit (⟨(s : C.functionField), hSR s.2⟩ : R) → IsUnit s := by
    rintro ⟨f, hf⟩ hu
    obtain ⟨a, rfl⟩ := (hS f).mp hf
    have hu' : IsUnit (φ.hom a) := by
      have heq : φ.hom a = ⟨algebraMap (C.presheaf.stalk x) C.functionField a, hSR hf⟩ :=
        Subtype.ext (hφ' a)
      rwa [heq]
    have ha : IsUnit a := isUnit_of_map_unit φ.hom a hu'
    exact ha.map ψ
  have hSReq : S = R := ValuationSubring.eq_of_le_of_isUnit_imp hSR hunit
  have hrange : (algebraMap (C.presheaf.stalk x) C.functionField).range = R.toSubring := by
    rw [← hSReq]
    ext f
    rw [RingHom.mem_range]
    exact (hS f).symm

  have key : ∀ y : C, y = genericPoint C →
      (algebraMap (C.presheaf.stalk y) C.functionField).range = ⊤ := by
    rintro y rfl
    refine eq_top_iff.mpr fun f _ => ⟨f, ?_⟩
    change (C.presheaf.stalkSpecializes (specializes_refl _)).hom f = f
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hxη : x ≠ genericPoint C := by
    intro hx
    apply v.ne_top'
    apply ValuationSubring.toSubring_injective
    change R.toSubring = _
    rw [← hrange, key x hx]
    rfl
  exact ⟨x, isClosed_singleton_of_ne_genericPoint c x hxη, hrange⟩

end S_AlgebraicCurve_exists_closedPoint_range_stalk_eq
end P2MW
export P2MW.S_AlgebraicCurve_exists_closedPoint_range_stalk_eq (solution)
