-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/138da9c9-aeb9-529f-ab88-c5b122f5f691

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {κ : Type*} [Field κ] {k : Type*} [Field k] {E : Type*} [Field E]
    [Algebra κ k] [Algebra k E] [Algebra κ E] [IsScalarTower κ k E] [Algebra.IsAlgebraic k E]
    (x : E) [FiniteDimensional ↥(IntermediateField.adjoin κ ({x} : Set E)) E]
    (W : ValuationSubring k) (hW : W ≠ ⊤) (hκ : ∀ a : κ, algebraMap κ k a ∈ W) :
    ∃ w : AlgebraicCurve.Place κ E, w.toValuationSubring.comap (algebraMap k E) = W := by
  classical
  set f : k →+* E := algebraMap k E with hf_def
  have hf : Function.Injective f := (algebraMap k E).injective

  let A : LocalSubring E := (W.toLocalSubring).map f
  obtain ⟨V, hAV⟩ := A.exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hAV
  have hAdef : A.toSubring = W.toSubring.map f := rfl
  have hmemV : ∀ y : k, y ∈ W → f y ∈ V := fun y hy => hle ⟨y, hy, rfl⟩

  have hcomap : V.comap f = W := by
    ext y
    rw [ValuationSubring.mem_comap]
    refine ⟨fun hy => ?_, hmemV y⟩
    by_contra hyW
    have hy0 : y ≠ 0 := fun h => hyW (h ▸ W.zero_mem)
    have hyinv : y⁻¹ ∈ W := (W.mem_or_inv_mem y).resolve_left hyW

    have hnu : ¬ IsUnit (⟨y⁻¹, hyinv⟩ : W) := by
      rintro ⟨u, hu⟩
      have h0 : ((u⁻¹ : Wˣ) : W) * ⟨y⁻¹, hyinv⟩ = 1 := by rw [← hu]; exact u.inv_mul
      have h1 : (((u⁻¹ : Wˣ) : W) : k) * y⁻¹ = 1 := by
        have := congrArg Subtype.val h0
        simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using this
      have h2 : (((u⁻¹ : Wˣ) : W) : k) = y := (mul_inv_eq_one₀ hy0).mp h1
      exact hyW (h2 ▸ ((u⁻¹ : Wˣ) : W).2)

    have hunitV : IsUnit (Subring.inclusion hle ⟨f y⁻¹, ⟨y⁻¹, hyinv, rfl⟩⟩) := by
      refine ⟨⟨⟨f y⁻¹, hmemV _ hyinv⟩, ⟨f y, hy⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext; show f y⁻¹ * f y = 1; rw [← map_mul, inv_mul_cancel₀ hy0, map_one]
      · apply Subtype.ext; show f y * f y⁻¹ = 1; rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
    have hunitA : IsUnit (⟨f y⁻¹, ⟨y⁻¹, hyinv, rfl⟩⟩ : A.toSubring) := hloc.map_nonunit _ hunitV
    let e : W.toSubring ≃+* W.toSubring.map f := W.toSubring.equivMapOfInjective f hf
    have he : e ⟨y⁻¹, hyinv⟩ = (⟨f y⁻¹, ⟨y⁻¹, hyinv, rfl⟩⟩ : W.toSubring.map f) := Subtype.ext rfl
    have hunitW : IsUnit (⟨y⁻¹, hyinv⟩ : W) := by
      have h3 : IsUnit (e ⟨y⁻¹, hyinv⟩) := by rw [he]; exact hunitA
      have h4 := h3.map e.symm.toRingHom
      simpa using h4
    exact hnu hunitW

  have hVtop : V ≠ ⊤ := by
    intro hV
    apply hW
    rw [← hcomap, hV]
    ext y; simp [ValuationSubring.mem_comap, ValuationSubring.mem_top]
  have hVκ : ∀ a : κ, algebraMap κ E a ∈ V := fun a => by
    rw [IsScalarTower.algebraMap_apply κ k E]; exact hmemV _ (hκ a)
  obtain ⟨w, hw⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional x V hVκ hVtop
  exact ⟨w, by rw [hw, hcomap]⟩

end S_AlgebraicCurve_Place_exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic (solution)
