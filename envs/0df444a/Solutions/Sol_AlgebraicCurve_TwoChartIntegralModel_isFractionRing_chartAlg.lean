-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/29dd4b2c-e993-5294-a847-7076e3ffb6df

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
set_option autoImplicit false
universe u
open AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

theorem solution
    (R : Type u) [CommRing R] [IsDomain R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (S : Set F) [Algebra.IsAlgebraic ↥(IntermediateField.adjoin K₀ S) F] :
    IsFractionRing ↥(chartAlg R F S) F := by
  classical

  have hinj : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K₀ F]
    exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)
  have hne : ∀ {d : R}, d ≠ 0 → algebraMap R F d ≠ 0 := fun hd => (map_ne_zero_iff _ hinj).mpr hd

  have hK₀ : ∀ c : K₀, ∃ r d : R, d ≠ 0 ∧ algebraMap R F d * algebraMap K₀ F c = algebraMap R F r := by
    intro c
    obtain ⟨r, d, hd, hc⟩ := IsFractionRing.div_surjective (A := R) c
    refine ⟨r, d, nonZeroDivisors.ne_zero hd, ?_⟩
    rw [← hc, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_eq_mul_inv,
      mul_comm (algebraMap R F r), ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd)), one_mul]

  have hL2 : ∀ w ∈ Algebra.adjoin K₀ S, ∃ d : R, d ≠ 0 ∧ algebraMap R F d * w ∈ Algebra.adjoin R S := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by rw [map_one, one_mul]; exact Algebra.subset_adjoin hx⟩
    | algebraMap c =>
      obtain ⟨r, d, hd, h⟩ := hK₀ c
      exact ⟨d, hd, by rw [h]; exact Subalgebra.algebraMap_mem _ r⟩
    | add x y _ _ hx hy =>
      obtain ⟨d₁, hd₁, h₁⟩ := hx
      obtain ⟨d₂, hd₂, h₂⟩ := hy
      refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
      have e : algebraMap R F (d₁ * d₂) * (x + y) =
          algebraMap R F d₂ * (algebraMap R F d₁ * x) + algebraMap R F d₁ * (algebraMap R F d₂ * y) := by
        rw [map_mul]; ring
      rw [e]
      exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) h₁) (mul_mem (Subalgebra.algebraMap_mem _ _) h₂)
    | mul x y _ _ hx hy =>
      obtain ⟨d₁, hd₁, h₁⟩ := hx
      obtain ⟨d₂, hd₂, h₂⟩ := hy
      refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
      have e : algebraMap R F (d₁ * d₂) * (x * y) = (algebraMap R F d₁ * x) * (algebraMap R F d₂ * y) := by
        rw [map_mul]; ring
      rw [e]
      exact mul_mem h₁ h₂

  have hle : ∀ x ∈ Algebra.adjoin R S, x ∈ IntermediateField.adjoin K₀ S := by
    intro x hx
    exact Algebra.adjoin_le (S := (IntermediateField.adjoin K₀ S).toSubalgebra.restrictScalars R)
      (IntermediateField.subset_adjoin K₀ S) hx
  let φ : ↥(Algebra.adjoin R S) →+* ↥(IntermediateField.adjoin K₀ S) :=
    (Algebra.adjoin R S).val.toRingHom.codRestrict (IntermediateField.adjoin K₀ S) (fun a => hle a a.2)
  letI : Algebra ↥(Algebra.adjoin R S) ↥(IntermediateField.adjoin K₀ S) := φ.toAlgebra
  haveI : IsScalarTower ↥(Algebra.adjoin R S) ↥(IntermediateField.adjoin K₀ S) F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul ↥(Algebra.adjoin R S) ↥(IntermediateField.adjoin K₀ S) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (fun a b h =>
      Subtype.ext (congrArg (fun z : ↥(IntermediateField.adjoin K₀ S) => (z : F)) h))
  haveI : IsDomain ↥(Algebra.adjoin R S) := Subalgebra.isDomain _

  haveI : IsFractionRing ↥(Algebra.adjoin R S) ↥(IntermediateField.adjoin K₀ S) := by
    refine IsFractionRing.of_field _ _ (fun c => ?_)
    obtain ⟨r, hr, s, hs, hc⟩ := IntermediateField.mem_adjoin_iff_div.mp c.2
    obtain ⟨d₁, hd₁, h₁⟩ := hL2 r hr
    obtain ⟨d₂, hd₂, h₂⟩ := hL2 s hs
    refine ⟨⟨algebraMap R F d₂ * (algebraMap R F d₁ * r), mul_mem (Subalgebra.algebraMap_mem _ _) h₁⟩,
      ⟨algebraMap R F d₁ * (algebraMap R F d₂ * s), mul_mem (Subalgebra.algebraMap_mem _ _) h₂⟩, ?_⟩
    apply (algebraMap (↥(IntermediateField.adjoin K₀ S)) F).injective
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    show (c : F) = (algebraMap R F d₂ * (algebraMap R F d₁ * r)) / (algebraMap R F d₁ * (algebraMap R F d₂ * s))
    rw [hc, ← mul_assoc, ← mul_assoc, mul_comm (algebraMap R F d₁) (algebraMap R F d₂),
      mul_div_mul_left r s (mul_ne_zero (hne hd₂) (hne hd₁))]

  haveI : Algebra.IsAlgebraic ↥(Algebra.adjoin R S) F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ↥(Algebra.adjoin R S))
      (K := ↥(IntermediateField.adjoin K₀ S)) (C := F)).mpr inferInstance

  letI : Algebra ↥(Algebra.adjoin R S) ↥(chartAlg R F S) :=
    (Subalgebra.inclusion (adjoin_le_chartAlg R F S)).toRingHom.toAlgebra
  haveI : IsScalarTower ↥(Algebra.adjoin R S) ↥(chartAlg R F S) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsIntegralClosure ↥(chartAlg R F S) ↥(Algebra.adjoin R S) F :=
    ⟨fun a b h => Subtype.ext h, fun {x} => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩⟩
  haveI : IsDomain ↥(chartAlg R F S) := Subalgebra.isDomain _

  exact IsIntegralClosure.isFractionRing_of_algebraic ↥(Algebra.adjoin R S) ↥(chartAlg R F S)
    (fun x hx => Subtype.ext hx)

end S_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg (solution)
