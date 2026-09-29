-- Prove2me | solution 1 for AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cdbb3b03-e570-5423-8a05-ba11f362911a

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Theorems.Thm_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place IsCurveOver IsCurveOver.kaehler_free_rank_one exists_mem_D_eq_smul_D_of_isCurveOver"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ord ord_unit_smul_zpow exists_unit_mul_zpow toValuationSubring DCoordGenerates differentialCoeff differentialCoeff_unique uniformizer ord_uniformizer"
p2m_open "AlgebraicCurve.Place"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n
p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem"
private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)
p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg"
theorem mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩
end Place
end AlgebraicCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place IsCurveOver IsCurveOver.kaehler_free_rank_one exists_mem_D_eq_smul_D_of_isCurveOver"
p2m_open "AlgebraicCurve"

theorem localUnitDerivativeRegular_of_isCurveOver_port {K : Type*} {F' : Type*} [Field K] [Field F'] [Algebra K F']
    [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates] :
    ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)) := by
  intro w u hu h0
  haveI : Nontrivial Ω[F'⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (IsCurveOver.kaehler_free_rank_one (K := K) (F := F')).2
  have hu_mem : u ∈ w.toValuationSubring := w.mem_of_ord_nonneg hu (by rw [h0])
  obtain ⟨c, hc, hcu⟩ :=
    exists_mem_D_eq_smul_D_of_isCurveOver (K := K) w (π := w.uniformizer) w.ord_uniformizer hu_mem
  have hcoeff : w.differentialCoeff (KaehlerDifferential.D K F' u) = c :=
    w.differentialCoeff_unique (by rw [hcu]; rfl)
  rw [hcoeff]
  rcases eq_or_ne c 0 with rfl | hc0
  · exact Or.inl rfl
  · exact Or.inr (w.ord_nonneg_of_mem hc)
end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver.AlgebraicCurve in
theorem solution {K : Type*} {F' : Type*} [Field K] [Field F'] [Algebra K F']
    [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates] :
    ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)) :=
  AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver_port

end S_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
end P2MW
export P2MW.S_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver (solution)
