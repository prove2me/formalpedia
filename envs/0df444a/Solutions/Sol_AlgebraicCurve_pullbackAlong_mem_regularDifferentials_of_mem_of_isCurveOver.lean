-- Prove2me | solution 1 for AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1c9eba14-ee54-51c3-b605-535c7af3d76c

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

open AlgebraicCurve
open scoped Pointwise

namespace RegPull

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_inv_smul_iff (w : F ≃ₐ[K] F) (v : Place K F) (f : F) :
    f ∈ (w⁻¹ • v).toValuationSubring ↔ w f ∈ v.toValuationSubring := by
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv,
    AlgEquiv.smul_def]

theorem exists_mem_D_eq_smul_dCoord [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [∀ w : Place K F, w.DCoordGenerates] (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring) :
    ∃ c ∈ v.toValuationSubring, KaehlerDifferential.D K F g = c • v.dCoord := by

  have key : ∀ u : F, u ≠ 0 → v.ord u = 0 →
      ∃ c ∈ v.toValuationSubring, KaehlerDifferential.D K F u = c • v.dCoord := by
    intro u hu0 hu
    refine ⟨v.differentialCoeff (KaehlerDifferential.D K F u), ?_, (v.differentialCoeff_smul_dCoord _).symm⟩
    rcases localUnitDerivativeRegular_of_isCurveOver v u hu0 hu with h | h
    · rw [h]; exact zero_mem _
    · exact v.mem_toValuationSubring_of_ord_nonneg h
  set a : v.toValuationSubring := ⟨g, hg⟩ with ha
  by_cases hunit : IsUnit a
  ·
    have hord : v.ord g = 0 := by
      have := v.ord_coe_unit hunit.unit
      rwa [IsUnit.unit_spec] at this
    have hg0 : g ≠ 0 := by
      intro h0
      apply hunit.ne_zero
      exact Subtype.ext h0
    exact key g hg0 hord
  ·
    have h1 : IsUnit (1 + a) := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (-a) with h | h
      · exact absurd (IsUnit.neg_iff _ |>.mp h) hunit
      · simpa using h
    have hord : v.ord (1 + g) = 0 := by
      have := v.ord_coe_unit h1.unit
      rwa [IsUnit.unit_spec] at this
    have hne : (1 + g) ≠ 0 := by
      intro h0
      apply h1.ne_zero
      exact Subtype.ext h0
    obtain ⟨c, hc, hcD⟩ := key (1 + g) hne hord
    refine ⟨c, hc, ?_⟩
    rw [← hcD, map_add, Derivation.map_one_eq_zero, zero_add]

theorem main [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [∀ v : Place K F, v.DCoordGenerates]
    (w : F ≃ₐ[K] F) {ω : Ω[F⁄K]} (hω : ω ∈ regularDifferentials K F) :
    Differential.pullbackAlong (w : F →ₐ[K] F) ω ∈ regularDifferentials K F := by
  rw [mem_regularDifferentials_iff] at hω ⊢
  intro v
  obtain ⟨f, hf, hωf⟩ := hω (w⁻¹ • v)
  obtain ⟨π, hπ1, hπd⟩ := (w⁻¹ • v).exists_ord_eq_one_and_dCoord_eq
  have hwf : w f ∈ v.toValuationSubring := (mem_inv_smul_iff w v f).mp hf
  have hπmem : π ∈ (w⁻¹ • v).toValuationSubring :=
    (w⁻¹ • v).mem_toValuationSubring_of_ord_nonneg (by rw [hπ1]; exact zero_le_one)
  have hwπ : w π ∈ v.toValuationSubring := (mem_inv_smul_iff w v π).mp hπmem
  obtain ⟨c, hc, hcD⟩ := exists_mem_D_eq_smul_dCoord v hwπ
  refine ⟨w f * c, mul_mem hwf hc, ?_⟩
  rw [hωf, hπd, Differential.pullbackAlong_smul, Differential.pullbackAlong_D, AlgEquiv.coe_algHom, hcD,
    mul_smul]

end RegPull

open AlgebraicCurve in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (w : F ≃ₐ[K] F) {ω : Ω[F⁄K]} (hω : ω ∈ AlgebraicCurve.regularDifferentials K F) :
    AlgebraicCurve.Differential.pullbackAlong (w : F →ₐ[K] F) ω ∈ AlgebraicCurve.regularDifferentials K F :=
  RegPull.main w hω

#print axioms solution

end S_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver
end P2MW
export P2MW.S_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver (solution)
