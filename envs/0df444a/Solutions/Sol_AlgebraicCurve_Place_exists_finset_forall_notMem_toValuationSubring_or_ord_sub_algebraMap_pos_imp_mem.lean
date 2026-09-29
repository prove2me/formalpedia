-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0f29e67e-9c03-5dd3-9e52-23ea7d945298

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ExistsBadset.ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    {w : Place K F} {f : F} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp [Place.ord_zero]
  · by_contra hneg
    push Not at hneg
    haveI : IsDiscreteValuationRing w.toValuationSubring := by
      refine ⟨?_⟩
      intro hbot
      exact ValuationSubring.not_isField_of_ne_top (F := F) (A := w.toValuationSubring) w.ne_top'
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf0 hπ
    have hπF : (π : F) ≠ 0 := by
      simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
    set m : ℕ := (-(w.ord f)).toNat with hm_def
    have hmZ : (m : ℤ) = -(w.ord f) := by
      rw [hm_def]
      exact Int.toNat_of_nonneg (by omega)
    have hm1 : m ≠ 0 := by omega

    have hfm : (π : F) ^ m * f = ((u : w.toValuationSubring) : F) := by
      rw [hu, mul_comm ((u : w.toValuationSubring) : F) _, ← mul_assoc,
        ← zpow_natCast ((π : F)) m, ← zpow_add₀ hπF, hmZ]
      simp

    have hO : (π ^ m) * (⟨f, hf⟩ : w.toValuationSubring) = (u : w.toValuationSubring) := by
      ext
      push_cast
      exact hfm
    have hdvd : π ∣ (u : w.toValuationSubring) := by
      refine dvd_trans (dvd_pow_self π hm1) ⟨⟨f, hf⟩, hO.symm⟩
    exact hπ.not_isUnit (isUnit_of_dvd_unit hdvd u.isUnit)

theorem ExistsBadset.ord_neg_of_notMem {K F : Type*} [Field K] [Field F] [Algebra K F]
    {w : Place K F} {f : F} (hf : f ∉ w.toValuationSubring) : w.ord f < 0 := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ zero_mem _)
  have hinv : f⁻¹ ∈ w.toValuationSubring :=
    (w.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have h1 : 0 ≤ w.ord f⁻¹ := ExistsBadset.ord_nonneg_of_mem hinv
  rw [Place.ord_inv] at h1
  rcases (show w.ord f ≤ 0 by omega).lt_or_eq with h | h
  · exact h
  · exfalso
    haveI : IsDiscreteValuationRing w.toValuationSubring := by
      refine ⟨?_⟩
      intro hbot
      exact ValuationSubring.not_isField_of_ne_top (F := F) (A := w.toValuationSubring) w.ne_top'
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow (inv_ne_zero hf0) hπ
    have hordinv : w.ord f⁻¹ = 0 := by
      rw [Place.ord_inv, h, neg_zero]
    rw [hordinv, zpow_zero, mul_one] at hu
    have h2F : (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F)
        * (((u : w.toValuationSubringˣ) : w.toValuationSubring) : F) = 1 := by
      have h2 := u.inv_mul
      have h3 := congrArg (fun z : w.toValuationSubring => (z : F)) h2
      push_cast at h3
      exact h3
    have hfval : f = (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F) := by
      have h4 := congrArg Inv.inv hu
      rw [inv_inv] at h4
      rw [h4, eq_comm]
      exact eq_inv_of_mul_eq_one_left h2F
    rw [hfval] at hf
    exact hf (SetLike.coe_mem _)

theorem ExistsBadset.ne_algebraMap_of_coeff_neg_one_eq_one {L : Type*} [Field L]
    {S : IntermediateField L (LaurentSeries L)} {x : ↥S}
    (hx : (x : LaurentSeries L).coeff (-1 : ℤ) = 1) (c : L) : x ≠ algebraMap L ↥S c := by
  intro h
  have hamb : (x : LaurentSeries L) = algebraMap L (LaurentSeries L) c := by
    rw [h]
    rfl
  have h5 : (algebraMap L (LaurentSeries L)) c = HahnSeries.single (0 : ℤ) c := by
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, HahnSeries.ofPowerSeries_C]
    rfl
  rw [hamb, h5, HahnSeries.coeff_single_of_ne (by norm_num : (-1 : ℤ) ≠ 0)] at hx
  exact zero_ne_one hx

theorem ExistsBadset.exists_finset_forall_notMem_or_ord_sub_pos_imp_mem
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (jel : F) (hnc : ∀ c : K, jel ≠ algebraMap K F c) (S : Finset K) :
    ∃ T : Finset (Place K F), ∀ t : Place K F,
      (jel ∉ t.toValuationSubring ∨ ∃ s ∈ S, 0 < t.ord (jel - algebraMap K F s)) → t ∈ T := by
  classical
  have hjne : jel ≠ 0 := by
    intro h0
    exact hnc 0 (by rw [h0, map_zero])
  obtain ⟨Dinf, hDinf, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) jel hjne
  set Ds : K → Divisor K F :=
    fun s => if h : jel - algebraMap K F s ≠ 0 then
        (HasPrincipalDivisors.exists_divisor (K := K) (F := F) _ h).choose
      else 0 with hDs_def
  have hDs_spec : ∀ s (v : Place K F) (h : jel - algebraMap K F s ≠ 0),
      (Ds s) v = v.ord (jel - algebraMap K F s) := by
    intro s v h
    rw [hDs_def]
    simp only [dif_pos h]
    exact ((HasPrincipalDivisors.exists_divisor (K := K) (F := F) _ h).choose_spec).1 v
  refine ⟨Dinf.support ∪ S.biUnion (fun s => (Ds s).support), ?_⟩
  intro t ht
  rcases ht with hpole | ⟨s, hs, hzero⟩
  · refine Finset.mem_union_left _ ?_
    rw [Finsupp.mem_support_iff, hDinf t]
    have hneg := ExistsBadset.ord_neg_of_notMem hpole
    omega
  · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s, hs, ?_⟩)
    have hne : jel - algebraMap K F s ≠ 0 := by
      intro h0
      rw [h0, Place.ord_zero] at hzero
      omega
    rw [Finsupp.mem_support_iff, hDs_spec s t hne]
    omega

theorem ExistsBadset.fbar
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (xjb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
    (hxjb : ((xjb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (S : Finset (ResidueField ↥A)) :
    ∃ T : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
      ∀ t, (xjb ∉ t.toValuationSubring ∨
        ∃ s ∈ S, 0 < t.ord (xjb - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) s)) → t ∈ T := by
  haveI := (ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
    p M H hpM hpM2 (ResidueField ↥A)).1
  refine ExistsBadset.exists_finset_forall_notMem_or_ord_sub_pos_imp_mem xjb (fun c => ?_) S
  have hc : ((xjb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)).coeff (-1 : ℤ) = 1 := by
    rw [hxjb]; exact coeff_jqModC_neg_one (ResidueField ↥A)
  exact ExistsBadset.ne_algebraMap_of_coeff_neg_one_eq_one hc c

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (x : F) (hx : ∀ c : K, x ≠ algebraMap K F c) (S : Finset K) :
    ∃ T : Finset (Place K F), ∀ t : Place K F,
      (x ∉ t.toValuationSubring ∨ ∃ s ∈ S, 0 < t.ord (x - algebraMap K F s)) → t ∈ T :=
  ExistsBadset.exists_finset_forall_notMem_or_ord_sub_pos_imp_mem x hx S

end S_AlgebraicCurve_Place_exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem (solution)
