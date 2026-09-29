-- Prove2me | solution 1 for AlgebraicCurve.dlog_mem_regularDifferentials_of_forall_dvd_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/6286a039-ee1c-5703-97d0-65e5f089e922

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_KwNo6HspecCartierDlogCampaignFrame
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_dlog_mem_regularDifferentials_of_forall_dvd_ord
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve KaehlerDifferential

namespace P2mWs11R5

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem dlog_inv {g : F} (hg : g ≠ 0) : kw_hwcd_dlog K g⁻¹ = - kw_hwcd_dlog K g := by
  have h := kw_hwcd_dlog_mul (K := K) hg (inv_ne_zero hg)
  rw [mul_inv_cancel₀ hg, kw_hwcd_dlog_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem dlog_zpow (n : ℤ) {g : F} (hg : g ≠ 0) : kw_hwcd_dlog K (g ^ n) = n • kw_hwcd_dlog K g := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, kw_hwcd_dlog_pow m hg, natCast_zsmul]
  · rw [zpow_neg, zpow_natCast, dlog_inv (pow_ne_zero _ hg), kw_hwcd_dlog_pow m hg, neg_smul,
      natCast_zsmul]

theorem charP_zsmul_eq_zero (p : ℕ) [CharP F p] (ω : Ω[F⁄K]) : (p : ℤ) • ω = 0 := by
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F p, zero_smul]

theorem main [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [∀ w : Place K F, w.DCoordGenerates] (p : ℕ) [Fact p.Prime] [CharP F p]
    {f : F} (hf : f ≠ 0) (h : ∀ v : Place K F, (p : ℤ) ∣ v.ord f) :
    f⁻¹ • KaehlerDifferential.D K F f ∈ AlgebraicCurve.regularDifferentials K F := by
  rw [AlgebraicCurve.mem_regularDifferentials_iff]
  intro v
  obtain ⟨π, hπ1, hπd⟩ := Place.exists_ord_eq_one_and_dCoord_eq v
  have hπ0 : π ≠ 0 := by intro h0; rw [h0, v.ord_zero] at hπ1; exact zero_ne_one hπ1
  obtain ⟨m, hm⟩ := h v

  set n : ℤ := v.ord f with hn
  let u : F := f * π ^ (-n)
  have hu0 : u ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ hπ0)
  have hordu : v.ord u = 0 := by
    simp only [u]
    rw [v.ord_mul hf (zpow_ne_zero _ hπ0), v.ord_zpow, hπ1, mul_one, ← hn, add_neg_cancel]
  have hfu : f = u * π ^ n := by
    simp only [u]
    rw [mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]

  have hdlog : f⁻¹ • D K F f = kw_hwcd_dlog K u := by
    rw [show f⁻¹ • D K F f = kw_hwcd_dlog K f from rfl, hfu,
      kw_hwcd_dlog_mul hu0 (zpow_ne_zero _ hπ0), dlog_zpow n hπ0, hm, mul_comm, mul_zsmul,
      charP_zsmul_eq_zero p, zsmul_zero, add_zero]
  rw [hdlog, kw_hwcd_dlog]

  set c : F := v.differentialCoeff (D K F u) with hc
  have hDu : D K F u = c • v.dCoord := (v.differentialCoeff_smul_dCoord _).symm
  have hcmem : c ∈ v.toValuationSubring := by
    rcases localUnitDerivativeRegular_of_isCurveOver v u hu0 hordu with h0 | hnn
    · rw [hc, h0]; exact zero_mem _
    · exact v.kw_hwcd_mem_of_ord_nonneg hnn
  have humem : u⁻¹ ∈ v.toValuationSubring :=
    v.kw_hwcd_mem_of_ord_nonneg (by rw [v.ord_inv, hordu, neg_zero])
  refine ⟨u⁻¹ * c, v.toValuationSubring.mul_mem _ _ humem hcmem, ?_⟩
  rw [hDu, smul_smul]

end P2mWs11R5

theorem solution
    (K F : Type*) [Field K] [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {f : F} (hf : f ≠ 0) (h : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) ∣ v.ord f) :
    f⁻¹ • KaehlerDifferential.D K F f ∈ AlgebraicCurve.regularDifferentials K F :=
  P2mWs11R5.main p hf h

end S_AlgebraicCurve_dlog_mem_regularDifferentials_of_forall_dvd_ord
end P2MW
export P2MW.S_AlgebraicCurve_dlog_mem_regularDifferentials_of_forall_dvd_ord (solution)
