-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/d19bb71b-8e90-5fc7-b1ff-18309cc03ef0

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Subring F) [IsLocalRing D] (hK : ∀ a : K, algebraMap K F a ∈ D)
    (hD : ∃ d : D, d ≠ 0 ∧ ¬ IsUnit d) :
    ∃ Q : AlgebraicCurve.Place K F, (∀ d : F, d ∈ D → d ∈ Q.toValuationSubring) ∧
      ∀ d : D, ((d : F) ∈ Q.toValuationSubring.nonunits ↔ ¬ IsUnit d) := by
  classical
  obtain ⟨d₀, hd₀0, hd₀u⟩ := hD

  have hmax : IsLocalRing.maximalIdeal D ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  obtain ⟨O, hDO, hdom⟩ := Ideal.image_subset_nonunits_valuationSubring (IsLocalRing.maximalIdeal D) hmax

  have hd₀O : (d₀ : F) ∈ O.nonunits :=
    hdom ⟨d₀, (IsLocalRing.mem_maximalIdeal _).mpr hd₀u, rfl⟩
  have hO : O ≠ ⊤ := by
    intro htop
    rw [ValuationSubring.mem_nonunits_iff] at hd₀O
    have : O.valuation (d₀ : F) = 1 := by
      subst htop
      have hne : ((d₀ : D) : F) ≠ 0 := fun h => hd₀0 (Subtype.ext h)

      have hu : IsUnit (⟨(d₀ : F), ValuationSubring.mem_top _⟩ : (⊤ : ValuationSubring F)) := by
        refine IsUnit.of_mul_eq_one ⟨(d₀ : F)⁻¹, ValuationSubring.mem_top _⟩ ?_
        exact Subtype.ext (mul_inv_cancel₀ hne)
      exact ((⊤ : ValuationSubring F).valuation_eq_one_iff _).mp hu
    exact absurd this (ne_of_lt hd₀O)

  obtain ⟨Q, hQ⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional x O
    (fun a => hDO (hK a)) hO
  refine ⟨Q, fun d hd => hQ ▸ hDO hd, fun d => ⟨fun hn hu => ?_, fun hnu => ?_⟩⟩
  ·
    obtain ⟨u, hu'⟩ := hu
    have hmem : (d : F) ∈ O := hDO d.2
    have hinv : ((u⁻¹ : Dˣ) : D).1 ∈ O := hDO ((u⁻¹ : Dˣ) : D).2
    have hunitO : IsUnit (⟨(d : F), hmem⟩ : O) := by
      refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
      change (d : F) * (((u⁻¹ : Dˣ) : D) : F) = 1
      rw [← hu', ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    rw [hQ, ValuationSubring.mem_nonunits_iff] at hn
    exact absurd ((O.valuation_eq_one_iff _).mp hunitO) (ne_of_lt hn)
  · rw [hQ]
    exact hdom ⟨d, (IsLocalRing.mem_maximalIdeal _).mpr hnu, rfl⟩

end S_AlgebraicCurve_Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing (solution)
