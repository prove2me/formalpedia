-- Prove2me | solution 1 for AlgebraicCurve.Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a9d89b3f-74af-5123-b58a-6621e6934d2d

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos

set_option autoImplicit false

open AlgebraicCurve

namespace EvalAtAux

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  have h1 : v.adicValuation f ≤ 1 := by
    rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · have hne := v.adicValuation_ne_zero hf0
    have : WithZero.log (v.adicValuation f) ≤ WithZero.log 1 := (WithZero.log_le_log hne one_ne_zero).mpr h1
    rw [WithZero.log_one] at this
    show 0 ≤ -(WithZero.log (v.adicValuation f))
    omega

theorem ord_pos_of_mem_of_not_isUnit {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0)
    (hu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring)) : 0 < v.ord f := by
  have hmem : (⟨f, hf⟩ : v.toValuationSubring) ∈ v.heightOneSpectrum.asIdeal := by
    rw [v.heightOneSpectrum_asIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hu
  have h1 : v.adicValuation f < 1 := by
    rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
    exact (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).mpr hmem
  have hne := v.adicValuation_ne_zero hf0
  have : WithZero.log (v.adicValuation f) < WithZero.log 1 := (WithZero.log_lt_log hne one_ne_zero).mpr h1
  rw [WithZero.log_one] at this
  show 0 < -(WithZero.log (v.adicValuation f))
  omega

theorem ord_eq_zero_of_isUnit {f : F} (hf : f ∈ v.toValuationSubring) (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) :
    v.ord f = 0 := by
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rwa [hu] at this

theorem mem_of_ord_nonneg {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  by_contra hf
  have hf0 : f ≠ 0 := by rintro rfl; exact hf (zero_mem _)
  have hinv : f⁻¹ ∈ v.toValuationSubring := (ValuationSubring.mem_or_inv_mem _ f).resolve_left hf
  have hu : ¬ IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    rintro ⟨u, hu⟩
    apply hf
    have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) * ⟨f⁻¹, hinv⟩ = 1 := by rw [← hu, Units.inv_mul]
    have h2 : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) * f⁻¹ = 1 := by
      have := congrArg (fun z : v.toValuationSubring => (z : F)) h1
      simpa using this
    have h3 : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = f := by
      have := congrArg (· * f) h2
      simpa [mul_assoc, inv_mul_cancel₀ hf0] using this
    rw [← h3]
    exact SetLike.coe_mem _
  have hpos := ord_pos_of_mem_of_not_isUnit v hinv (inv_ne_zero hf0) hu
  rw [v.ord_inv] at hpos
  omega

end EvalAtAux

open EvalAtAux

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) (hv : v.IsRational) (f : F) (a : K) (hfa : f ≠ algebraMap K F a) :
    (f ∈ v.toValuationSubring ∧ v.evalAt f = a) ↔ 0 < v.ord (f - algebraMap K F a) := by
  classical
  have hfa' : f - algebraMap K F a ≠ 0 := sub_ne_zero.mpr hfa
  have hamem : algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem' a
  constructor
  · rintro ⟨hf, hev⟩
    have hmem : f - algebraMap K F a ∈ v.toValuationSubring := sub_mem hf hamem
    apply ord_pos_of_mem_of_not_isUnit v hmem hfa'
    intro hu

    have hres : IsLocalRing.residue v.toValuationSubring ⟨f - algebraMap K F a, hmem⟩ = 0 := by
      have h1 : (⟨f - algebraMap K F a, hmem⟩ : v.toValuationSubring) = ⟨f, hf⟩ - ⟨algebraMap K F a, hamem⟩ := rfl
      rw [h1, map_sub, ← v.algebraMap_evalAt hv hf, hev]
      have h2 : (⟨algebraMap K F a, hamem⟩ : v.toValuationSubring) = algebraMap K v.toValuationSubring a := rfl
      rw [h2, sub_eq_zero]
      exact (IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField a).symm
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hres
    exact hres hu
  · intro hpos
    have hmem : f - algebraMap K F a ∈ v.toValuationSubring := mem_of_ord_nonneg v hpos.le
    have hf : f ∈ v.toValuationSubring := by
      have : f = (f - algebraMap K F a) + algebraMap K F a := by ring
      rw [this]; exact add_mem hmem hamem
    refine ⟨hf, ?_⟩

    have hnu : ¬ IsUnit (⟨f - algebraMap K F a, hmem⟩ : v.toValuationSubring) := fun hu => by
      have := ord_eq_zero_of_isUnit v hmem hu; omega
    have hres : IsLocalRing.residue v.toValuationSubring ⟨f - algebraMap K F a, hmem⟩ = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hnu
    have h1 : (⟨f - algebraMap K F a, hmem⟩ : v.toValuationSubring) = ⟨f, hf⟩ - ⟨algebraMap K F a, hamem⟩ := rfl
    rw [h1, map_sub, sub_eq_zero] at hres
    rw [v.evalAt_of_mem hf, hres]
    have h2 : (⟨algebraMap K F a, hamem⟩ : v.toValuationSubring) = algebraMap K v.toValuationSubring a := rfl
    rw [h2]
    have h3 : IsLocalRing.residue v.toValuationSubring (algebraMap K v.toValuationSubring a) = algebraMap K v.ResidueField a :=
      (IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField a).symm
    rw [h3, v.residueInv_algebraMap]

end S_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
end P2MW
export P2MW.S_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos (solution)
