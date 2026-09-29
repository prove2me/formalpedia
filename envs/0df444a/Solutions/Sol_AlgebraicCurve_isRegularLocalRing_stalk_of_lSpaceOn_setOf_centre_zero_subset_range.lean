-- Prove2me | solution 1 for AlgebraicCurve.isRegularLocalRing_stalk_of_lSpaceOn_setOf_centre_zero_subset_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5806f520-453b-519a-916c-5ebad6bb84b9

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_isRegularLocalRing_stalk_of_lSpaceOn_setOf_centre_zero_subset_range

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace LocRegL6

open WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_iff_adicValuation_le_one (v : Place K F) (x : F) :
    x ∈ v.toValuationSubring ↔ v.adicValuation x ≤ 1 := by
  refine ⟨fun h => v.adicValuation_le_one_of_mem h, fun h => ?_⟩
  by_contra hx
  have hx0 : x ≠ 0 := fun e => hx (e ▸ v.toValuationSubring.zero_mem)
  have hxi : x⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem x).resolve_left hx
  have hnu : ¬ IsUnit (⟨x⁻¹, hxi⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨w, hw⟩ := hu
    apply hx
    have : x = ((w⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) := by
      have h1 : ((w : v.toValuationSubring) : F) * ((w⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) = 1 := by
        rw [← MulMemClass.coe_mul, w.mul_inv]
        rfl
      rw [hw] at h1
      rw [eq_inv_of_mul_eq_one_right h1, inv_inv]
    rw [this]
    exact SetLike.coe_mem _
  have hlt : v.adicValuation x⁻¹ < 1 :=
    lt_of_le_of_ne (v.adicValuation_le_one_of_mem hxi)
      (fun e => hnu ((v.adicValuation_coe_eq_one_iff ⟨x⁻¹, hxi⟩).mp e))
  rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.mpr (v.adicValuation_ne_zero hx0))] at hlt
  exact not_le.mpr hlt h

theorem adicValuation_lt_one_iff_of_mem (v : Place K F) {x : F} (hx : x ∈ v.toValuationSubring) :
    v.adicValuation x < 1 ↔ ¬ IsUnit (⟨x, hx⟩ : v.toValuationSubring) := by
  rw [← v.adicValuation_coe_eq_one_iff, lt_iff_le_and_ne]
  simp [v.adicValuation_le_one_of_mem hx]

theorem adicValuation_algebraMap_eq_one (v : Place K F) {c : K} (hc : c ≠ 0) :
    v.adicValuation (algebraMap K F c) = 1 := by
  rw [show algebraMap K F c = ((⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) : F)
    from rfl, v.adicValuation_coe_eq_one_iff]
  refine ⟨⟨⟨_, v.algebraMap_mem' c⟩, ⟨_, v.algebraMap_mem' c⁻¹⟩, ?_, ?_⟩, rfl⟩ <;>
    ext <;> simp [hc]

end LocRegL6

open LocRegL6 in

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] (z : C)
    (hSfin : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra;
      {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))}.Finite)
    (hδ : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra;
      ((lSpaceOn {v : Place k C.functionField |
        (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField) : Set C.functionField) ⊆
        Set.range (algebraMap (C.presheaf.stalk z) C.functionField))) :
    IsRegularLocalRing (C.presheaf.stalk z) := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra

  set S : Set (Place k C.functionField) := {v : Place k C.functionField |
        (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} with hSdef
  set φ := algebraMap (C.presheaf.stalk z) C.functionField with hφdef
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hsub : ∀ v ∈ S, ∀ s : C.presheaf.stalk z, φ s ∈ v.toValuationSubring := fun v hv s =>
    (mem_iff_adicValuation_le_one v _).mpr (hv s).1
  have hdom : ∀ v ∈ S, ∀ s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z),
      v.adicValuation (φ s) < 1 := fun v hv s hs => (hv s).2 hs
  have hrange : ∀ b : C.functionField, (∀ v ∈ S, v.adicValuation b ≤ 1) → b ∈ Set.range φ := by
    intro b hb
    apply hδ
    show b ∈ lSpaceOn S 0
    rw [mem_lSpaceOn_iff]
    simpa using hb

  have key : ∀ v₁ ∈ S, ∀ v₂ ∈ S, ∀ a : C.functionField,
      a ∈ v₁.toValuationSubring → a ∉ v₂.toValuationSubring → False := by
    intro v₁ hv₁ v₂ hv₂ a ha₁ ha₂
    let ι := algebraMap k C.functionField

    let bad : Place k C.functionField → Set k := fun v =>
      {t : k | v.adicValuation (a + ι t) < 1}
    have hbad1 : ∀ v, (bad v).Subsingleton := by
      intro v t ht t' ht'
      by_contra hne
      have h1 : v.adicValuation (ι (t - t')) = 1 :=
        adicValuation_algebraMap_eq_one v (sub_ne_zero.mpr hne)
      have h2 : v.adicValuation ((a + ι t) - (a + ι t')) < 1 :=
        lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ht ht')
      rw [show (a + ι t) - (a + ι t') = ι (t - t') by simp [ι, map_sub]] at h2
      exact (lt_irrefl _) (h1 ▸ h2)
    have hfin : (⋃ v ∈ S, bad v).Finite :=
      hSfin.biUnion fun v _ => (hbad1 v).finite
    obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists, exists_prop, not_and] at ht

    set a' := a + ι t with ha'
    have hge : ∀ v ∈ S, 1 ≤ v.adicValuation a' := by
      intro v hv
      by_cases hav : a ∈ v.toValuationSubring
      · exact not_lt.mp (ht v hv)
      · have hgt : 1 < v.adicValuation a := not_le.mp fun h => hav ((mem_iff_adicValuation_le_one v a).mpr h)
        have hιt : v.adicValuation (ι t) < v.adicValuation a :=
          lt_of_le_of_lt (v.adicValuation_algebraMap_le_one t) hgt
        rw [ha', Valuation.map_add_eq_of_lt_left _ hιt]
        exact hgt.le
    have ha'0 : a' ≠ 0 := by
      intro e
      have := hge v₁ hv₁
      rw [e, map_zero] at this
      exact not_lt.mpr this zero_lt_one

    have hb : ∀ v ∈ S, v.adicValuation a'⁻¹ ≤ 1 := fun v hv => by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (hge v hv)
    obtain ⟨s, hs⟩ := hrange _ hb

    have ha'1 : a' ∈ v₁.toValuationSubring := add_mem ha₁ (v₁.algebraMap_mem' t)
    have hv1 : v₁.adicValuation a'⁻¹ = 1 := by
      rw [map_inv₀, le_antisymm (v₁.adicValuation_le_one_of_mem ha'1) (hge v₁ hv₁), inv_one]
    have hsunit : IsUnit s := by
      by_contra hns
      have := hdom v₁ hv₁ s ((IsLocalRing.mem_maximalIdeal s).mpr hns)
      rw [hs, hv1] at this
      exact lt_irrefl _ this

    obtain ⟨u, rfl⟩ := hsunit
    have ha'φ : a' = φ ((u⁻¹ : (C.presheaf.stalk z)ˣ) : C.presheaf.stalk z) := by
      rw [← inv_inv a', ← hs, ← map_units_inv]
    apply ha₂
    have : a = a' - ι t := by rw [ha']; ring
    rw [this]
    exact sub_mem (ha'φ ▸ hsub v₂ hv₂ _) (v₂.algebraMap_mem' t)
  have hSS : S.Subsingleton := by
    intro v₁ hv₁ v₂ hv₂
    by_contra hne
    have hne' : v₁.toValuationSubring ≠ v₂.toValuationSubring := fun e => hne (Place.ext e)
    rcases not_and_or.mp (fun h => hne' (le_antisymm h.1 h.2)) with h | h
    · obtain ⟨a, ha₁, ha₂⟩ := SetLike.not_le_iff_exists.mp h
      exact key v₁ hv₁ v₂ hv₂ a ha₁ ha₂
    · obtain ⟨a, ha₂, ha₁⟩ := SetLike.not_le_iff_exists.mp h
      exact key v₂ hv₂ v₁ hv₁ a ha₂ ha₁

  rcases S.eq_empty_or_nonempty with hempty | ⟨v, hv⟩
  · have hsurj : Function.Surjective φ := fun b => hrange b (by simp [hempty])
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.ofBijective φ ⟨hφ, hsurj⟩).symm
  · have hsurj : Function.Surjective (φ.codRestrict v.toValuationSubring (hsub v hv)) := by
      rintro ⟨x, hx⟩
      obtain ⟨s, hs⟩ := hrange x (fun w hw => by
        rw [hSS hw hv]; exact v.adicValuation_le_one_of_mem hx)
      exact ⟨s, Subtype.ext hs⟩
    have hinj : Function.Injective (φ.codRestrict v.toValuationSubring (hsub v hv)) :=
      fun s s' e => hφ (congrArg Subtype.val e)
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm

#print axioms solution

end S_AlgebraicCurve_isRegularLocalRing_stalk_of_lSpaceOn_setOf_centre_zero_subset_range
end P2MW
export P2MW.S_AlgebraicCurve_isRegularLocalRing_stalk_of_lSpaceOn_setOf_centre_zero_subset_range (solution)
