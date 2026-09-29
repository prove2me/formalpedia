-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_place_comap_algebraMap_eq_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/d11a2e71-40b2-5270-858e-8e39b05bc785

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_place_comap_algebraMap_eq_of_finite
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    (κ : Type) [Field κ] [IsAlgClosed κ]
    (Ω : Type) [Field Ω] [Algebra κ Ω] (V : Place κ Ω)
    (res : IsLocalRing.ResidueField ↥V.toValuationSubring →+* κ)
    (hr : ∀ c : κ, res (algebraMap κ (IsLocalRing.ResidueField ↥V.toValuationSubring) c) = c)
    (x : Ω) (hx : Transcendental κ x) [FiniteDimensional ↥(IntermediateField.adjoin κ ({x} : Set Ω)) Ω]
    (Ω₁ : Type) [Field Ω₁] [Algebra κ Ω₁] [Algebra Ω Ω₁] [IsScalarTower κ Ω Ω₁] [Module.Finite Ω Ω₁] :
    ∃ (V₁ : Place κ Ω₁) (res₁ : IsLocalRing.ResidueField ↥V₁.toValuationSubring →+* κ)
      (ιO : ↥V.toValuationSubring →+* ↥V₁.toValuationSubring),
      V₁.toValuationSubring.comap (algebraMap Ω Ω₁) = V.toValuationSubring ∧
      (∀ a : ↥V.toValuationSubring, ((ιO a : ↥V₁.toValuationSubring) : Ω₁) = algebraMap Ω Ω₁ (a : Ω)) ∧
      (∀ c : κ, res₁ (algebraMap κ (IsLocalRing.ResidueField ↥V₁.toValuationSubring) c) = c) ∧
      (∀ a : ↥V.toValuationSubring,
        res₁ (IsLocalRing.residue ↥V₁.toValuationSubring (ιO a)) = res (IsLocalRing.residue ↥V.toValuationSubring a)) := by
  classical

  set x₁ : Ω₁ := algebraMap Ω Ω₁ x with hx₁def
  have hx₁ : Transcendental κ x₁ := by
    rw [hx₁def]; exact (transcendental_algebraMap_iff (algebraMap Ω Ω₁).injective).mpr hx
  haveI hfd₁ : FiniteDimensional ↥(IntermediateField.adjoin κ ({x₁} : Set Ω₁)) Ω₁ := by
    set L₀ := IntermediateField.adjoin κ ({x} : Set Ω) with hL₀
    set L₁ := IntermediateField.adjoin κ ({x₁} : Set Ω₁) with hL₁
    let φ : Ω →ₐ[κ] Ω₁ := IsScalarTower.toAlgHom κ Ω Ω₁
    have hmap : L₀.map φ = L₁ := by
      rw [hL₀, hL₁, IntermediateField.adjoin_map, Set.image_singleton, hx₁def]; rfl

    let ψ : ↥L₀ →+* ↥L₁ :=
      { toFun := fun y => ⟨φ y, hmap ▸ (IntermediateField.mem_map (S := L₀) (f := φ)).mpr ⟨y, y.2, rfl⟩⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp
        map_zero' := by ext; simp
        map_add' := fun a b => by ext; simp }
    haveI : Module.Finite ↥L₀ Ω₁ := Module.Finite.trans Ω Ω₁
    letI : Algebra ↥L₀ ↥L₁ := ψ.toAlgebra
    haveI : IsScalarTower ↥L₀ ↥L₁ Ω₁ := IsScalarTower.of_algebraMap_eq (fun a => rfl)
    exact Module.Finite.of_restrictScalars_finite ↥L₀ ↥L₁ Ω₁
  set A := V.toValuationSubring with hA

  let f : ↥A →+* Ω₁ := (algebraMap Ω Ω₁).comp A.subtype
  obtain ⟨A₁, hA₁, hloc⟩ := IsLocalRing.exists_factor_valuationRing f

  have hf : ∀ a : ↥A, f a = algebraMap Ω Ω₁ (a : Ω) := fun a => rfl

  have hover : A₁.comap (algebraMap Ω Ω₁) = A := by
    ext x
    rw [ValuationSubring.mem_comap]
    refine ⟨fun hx => ?_, fun hx => hA₁ ⟨x, hx⟩⟩
    by_contra hxA
    have hx0 : x ≠ 0 := fun h => hxA (h ▸ A.zero_mem)
    have hinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hxA

    have hnu : ¬ IsUnit (⟨x⁻¹, hinv⟩ : ↥A) := by
      intro hu
      apply hxA
      obtain ⟨u, hu⟩ := hu
      have : ((u⁻¹ : (↥A)ˣ) : ↥A).1 = x := by
        have h1 : ((u⁻¹ : (↥A)ˣ) : ↥A).1 * x⁻¹ = 1 := by
          have := congrArg (fun z : ↥A => (z : Ω)) (u.inv_mul)
          rw [hu] at this
          simpa using this
        field_simp at h1
        linear_combination h1
      rw [← this]; exact ((u⁻¹ : (↥A)ˣ) : ↥A).2

    apply hnu
    apply (hloc.map_nonunit _)
    refine ⟨⟨⟨algebraMap Ω Ω₁ x⁻¹, hA₁ ⟨x⁻¹, hinv⟩⟩, ⟨algebraMap Ω Ω₁ x, hx⟩, ?_, ?_⟩, rfl⟩
    · ext; simp [hx0]
    · ext; simp [hx0]
  have hne : A₁ ≠ ⊤ := by
    intro h
    apply V.ne_top'
    rw [← hA, ← hover, h]
    ext x; simp [ValuationSubring.mem_comap, ValuationSubring.mem_top]
  have hκ : ∀ c : κ, algebraMap κ Ω₁ c ∈ A₁ := by
    intro c
    rw [IsScalarTower.algebraMap_apply κ Ω Ω₁]
    exact hA₁ ⟨algebraMap κ Ω c, V.algebraMap_mem' c⟩
  obtain ⟨V₁, hV₁⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional x₁ A₁ hκ hne

  have hdeg : V₁.deg = 1 := AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed V₁
    (AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin x₁ hx₁ V₁)
  have hsurj : Function.Surjective (algebraMap κ V₁.ResidueField) :=
    (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField V₁).mp hdeg
  have hbij : Function.Bijective (algebraMap κ V₁.ResidueField) := ⟨(algebraMap κ V₁.ResidueField).injective, hsurj⟩
  let e₁ : κ ≃+* V₁.ResidueField := RingEquiv.ofBijective (algebraMap κ V₁.ResidueField) hbij
  let res₁ : IsLocalRing.ResidueField ↥V₁.toValuationSubring →+* κ := e₁.symm.toRingHom
  have hres₁ : ∀ c : κ, res₁ (algebraMap κ _ c) = c := fun c => e₁.symm_apply_apply c

  have hA₁' : ∀ a : ↥A, algebraMap Ω Ω₁ (a : Ω) ∈ V₁.toValuationSubring := fun a => by rw [hV₁]; exact hA₁ a
  let ιO : ↥V.toValuationSubring →+* ↥V₁.toValuationSubring :=
    { toFun := fun a => ⟨algebraMap Ω Ω₁ (a : Ω), hA₁' a⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  have hιO : ∀ a : ↥V.toValuationSubring, ((ιO a : ↥V₁.toValuationSubring) : Ω₁) = algebraMap Ω Ω₁ (a : Ω) := fun a => rfl

  have hιloc : ∀ a : ↥V.toValuationSubring, IsUnit (ιO a) → IsUnit a := by
    intro a hu
    apply hloc.map_nonunit a

    obtain ⟨u, hu⟩ := hu
    have hmem : ∀ y : ↥V₁.toValuationSubring, (y : Ω₁) ∈ A₁.toSubring := fun y => by
      show (y : Ω₁) ∈ A₁; rw [← hV₁]; exact y.2
    refine ⟨⟨⟨(u : ↥V₁.toValuationSubring), hmem _⟩, ⟨((u⁻¹ : (↥V₁.toValuationSubring)ˣ) : ↥V₁.toValuationSubring), hmem _⟩, ?_, ?_⟩, ?_⟩
    · ext; exact congrArg (fun z : ↥V₁.toValuationSubring => (z : Ω₁)) u.mul_inv
    · ext; exact congrArg (fun z : ↥V₁.toValuationSubring => (z : Ω₁)) u.inv_mul
    · ext; exact congrArg (fun z : ↥V₁.toValuationSubring => (z : Ω₁)) hu
  refine ⟨V₁, res₁, ιO, by rw [hV₁]; exact hover, hιO, hres₁, ?_⟩
  intro a

  set c₁ := res₁ (IsLocalRing.residue ↥V₁.toValuationSubring (ιO a)) with hc₁
  have h1 : IsLocalRing.residue ↥V₁.toValuationSubring (ιO a) = algebraMap κ _ c₁ := by
    rw [hc₁]; exact (e₁.apply_symm_apply _).symm

  have hιOalg : ∀ c : κ, ιO (algebraMap κ ↥V.toValuationSubring c) = algebraMap κ ↥V₁.toValuationSubring c := by
    intro c; ext
    show algebraMap Ω Ω₁ ((algebraMap κ ↥V.toValuationSubring c : ↥V.toValuationSubring) : Ω) =
      ((algebraMap κ ↥V₁.toValuationSubring c : ↥V₁.toValuationSubring) : Ω₁)
    rw [AlgebraicCurve.Place.coe_algebraMap, AlgebraicCurve.Place.coe_algebraMap,
      ← IsScalarTower.algebraMap_apply κ Ω Ω₁]
  have hres_alg : ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra κ W] (c : κ),
      IsLocalRing.residue W (algebraMap κ W c) = algebraMap κ (IsLocalRing.ResidueField W) c := fun W _ _ _ c => rfl
  have h2 : IsLocalRing.residue ↥V.toValuationSubring a = algebraMap κ _ c₁ := by
    rw [← hres_alg, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    intro hu
    have hu1 : IsUnit (ιO (a - algebraMap κ ↥V.toValuationSubring c₁)) := hu.map ιO
    rw [map_sub, hιOalg] at hu1
    have hm : ιO a - algebraMap κ ↥V₁.toValuationSubring c₁ ∈ IsLocalRing.maximalIdeal ↥V₁.toValuationSubring := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h1, hres_alg, sub_self]
    exact (IsLocalRing.mem_maximalIdeal _).mp hm |> mem_nonunits_iff.mp <| hu1
  rw [h2, hr]

end S_AlgebraicCurve_Place_exists_place_comap_algebraMap_eq_of_finite
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_place_comap_algebraMap_eq_of_finite (solution)
