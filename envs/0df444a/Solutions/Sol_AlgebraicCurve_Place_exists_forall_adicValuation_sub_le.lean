-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_forall_adicValuation_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/048a7289-bd7f-5b91-bd19-0ac64bf905b3

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_forall_adicValuation_sub_le
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.adicValuation_le_exp_iff Place.exists_forall_ord_eq_finset"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "adicValuation ord ord_zero ord_one ord_mul ord_inv ord_zpow adicValuation_le_exp_iff exists_forall_ord_eq_finset ord_add_eq_of_lt min_ord_le_ord_add ord_neg"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.wa_add_ne_zero_of_ord_lt {f g : F} (hlt : v.ord f < v.ord g) : f + g ≠ 0 := by
  intro h0
  rw [eq_neg_of_add_eq_zero_right h0, v.ord_neg] at hlt
  exact lt_irrefl _ hlt

p2m_export "AlgebraicCurve.Place" "wa_add_ne_zero_of_ord_lt"

private theorem _root_.AlgebraicCurve.Place.wa_min_ord_le_ord_add {f g : F} (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [zero_add]; exact min_le_right _ _
  rcases eq_or_ne g 0 with rfl | hg
  · rw [add_zero]; exact min_le_left _ _
  exact v.min_ord_le_ord_add hf hg hfg

p2m_export "AlgebraicCurve.Place" "wa_min_ord_le_ord_add"

theorem wa_exists_separating_finset [DecidableEq (Place K F)] (T : Finset (Place K F)) :
    ∃ t : F, t ≠ 0 ∧ v.ord t = 1 ∧ ∀ w ∈ T, w ≠ v → w.ord t = -1 := by
  obtain ⟨t, ht0, ht⟩ :=
    Place.exists_forall_ord_eq_finset (insert v T) (fun w => if w = v then 1 else -1)
  refine ⟨t, ht0, ?_, fun w hw hwv => ?_⟩
  · simpa using ht v (Finset.mem_insert_self v T)
  · simpa [hwv] using ht w (Finset.mem_insert_of_mem hw)

private theorem _root_.AlgebraicCurve.Place.wa_ord_finsetSum_ge {ι : Type*} (s : Finset ι)
    (g : ι → F) (m : ℤ) (hbound : ∀ i ∈ s, g i = 0 ∨ m ≤ v.ord (g i)) :
    s.sum g = 0 ∨ m ≤ v.ord (s.sum g) := by
  classical
  induction s using Finset.cons_induction with
  | empty => exact Or.inl Finset.sum_empty
  | cons i s hi ih =>
      rw [Finset.sum_cons]
      have ih' := ih fun j hj => hbound j (Finset.mem_cons.mpr (Or.inr hj))
      rcases eq_or_ne (g i) 0 with h0 | hgi0
      · rw [h0, zero_add]; exact ih'
      · have hgi : m ≤ v.ord (g i) :=
          (hbound i (Finset.mem_cons_self i s)).resolve_left hgi0
        rcases ih' with hs0 | hlt
        · rw [hs0, add_zero]; exact Or.inr hgi
        · rcases eq_or_ne (g i + s.sum g) 0 with hz' | hz'
          · exact Or.inl hz'
          · exact Or.inr (le_trans (le_min hgi hlt) (v.wa_min_ord_le_ord_add hz'))

p2m_export "AlgebraicCurve.Place" "wa_ord_finsetSum_ge"
end Place

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_exists_forall_adicValuation_sub_le.AlgebraicCurve in

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    (T : Finset (AlgebraicCurve.Place K F)) (β : AlgebraicCurve.Place K F → F)
    (n : AlgebraicCurve.Place K F → ℤ) :
    ∃ f : F, ∀ v ∈ T, v.adicValuation (f - β v) ≤ WithZero.exp (n v) := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | -
  · exact ⟨0, fun w hw => absurd hw (Finset.notMem_empty w)⟩

  have key : ∀ (w : Place K F) (x : F), (x = 0 ∨ -n w ≤ w.ord x) →
      w.adicValuation x ≤ WithZero.exp (n w) := fun w x hx =>
    (Place.adicValuation_le_exp_iff w).mpr hx

  choose t ht0 htv htT using fun v => Place.wa_exists_separating_finset (K := K) (F := F) v T

  set P : ℕ := 1 + (T.sup fun w => T.sup fun w' =>
    (1 - n w - w.ord (β w')).toNat) with hP
  have hP1 : 1 ≤ (P : ℤ) := by rw [hP]; push_cast; omega
  have hPbd : ∀ w ∈ T, ∀ w' ∈ T, -n w - w.ord (β w') < (P : ℤ) := by
    intro w hw w' hw'
    have h1 : (1 - n w - w.ord (β w')).toNat
        ≤ T.sup fun w'' => (1 - n w - w.ord (β w'')).toNat :=
      Finset.le_sup (f := fun w'' => (1 - n w - w.ord (β w'')).toNat) hw'
    have h2 : (T.sup fun w'' => (1 - n w - w.ord (β w'')).toNat)
        ≤ T.sup fun v => T.sup fun w'' => (1 - n v - v.ord (β w'')).toNat :=
      Finset.le_sup (f := fun v => T.sup fun w'' => (1 - n v - v.ord (β w'')).toNat) hw
    have h3 : ((1 - n w - w.ord (β w')).toNat : ℤ)
        ≤ ((T.sup fun v => T.sup fun w'' => (1 - n v - v.ord (β w'')).toNat : ℕ) : ℤ) := by
      exact_mod_cast le_trans h1 h2
    rw [hP]; push_cast; omega

  have hden0 : ∀ v, (1 : F) + t v ^ (P : ℤ) ≠ 0 := fun v =>
    v.wa_add_ne_zero_of_ord_lt (f := 1) (g := t v ^ (P : ℤ))
      (by rw [v.ord_one, v.ord_zpow, htv v]; omega)
  set e : Place K F → F := fun v => ((1 : F) + t v ^ (P : ℤ))⁻¹ with he
  have he0 : ∀ v, e v ≠ 0 := fun v => inv_ne_zero (hden0 v)

  have hew1 : ∀ v : Place K F, (P : ℤ) ≤ v.ord (e v - 1) := by
    intro v
    have hpow0 : t v ^ (P : ℤ) ≠ 0 := zpow_ne_zero _ (ht0 v)
    have hdenv : v.ord ((1 : F) + t v ^ (P : ℤ)) = 0 := by
      rw [v.ord_add_eq_of_lt one_ne_zero hpow0
        (by rw [v.ord_one, v.ord_zpow, htv v]; omega), v.ord_one]
    have heq : e v - 1 = -(t v ^ (P : ℤ)) * ((1 : F) + t v ^ (P : ℤ))⁻¹ := by
      simp only [he]
      linear_combination mul_inv_cancel₀ (hden0 v)
    rw [heq, v.ord_mul (neg_ne_zero.mpr hpow0) (inv_ne_zero (hden0 v)),
      v.ord_neg, v.ord_zpow, v.ord_inv, hdenv, neg_zero, add_zero, htv v]
    omega

  have hew' : ∀ v : Place K F, ∀ w' ∈ T, w' ≠ v → (P : ℤ) ≤ w'.ord (e v) := by
    intro v w' hw' hw'v
    have hpow0 : t v ^ (P : ℤ) ≠ 0 := zpow_ne_zero _ (ht0 v)
    have hordneg := htT v w' hw' hw'v
    have hlt : w'.ord (t v ^ (P : ℤ)) < w'.ord (1 : F) := by
      rw [w'.ord_one, w'.ord_zpow, hordneg]; omega
    have hdenw' : w'.ord ((1 : F) + t v ^ (P : ℤ)) = (P : ℤ) * w'.ord (t v) := by
      rw [add_comm, w'.ord_add_eq_of_lt hpow0 one_ne_zero hlt, w'.ord_zpow]
    rw [he, w'.ord_inv, hdenw', hordneg]
    omega

  refine ⟨T.sum fun w => e w * β w, fun w hw => ?_⟩

  have hsplit : (T.sum fun v => e v * β v) - β w
      = (e w - 1) * β w + (T.erase w).sum fun v => e v * β v := by
    rw [← Finset.sum_erase_add T _ hw]; ring
  rw [hsplit]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  ·
    rcases eq_or_ne (β w) 0 with hβ0 | hβ0
    · rw [hβ0, mul_zero]; simp
    · refine key w _ (Or.inr ?_)
      have hew10 : e w - 1 ≠ 0 := fun h => by
        have := hew1 w; rw [h, w.ord_zero] at this; omega
      rw [w.ord_mul hew10 hβ0]
      have := hew1 w
      have hbd := hPbd w hw w hw
      omega
  ·
    refine key w _ ?_
    refine w.wa_ord_finsetSum_ge (T.erase w) (fun v => e v * β v) (-n w) ?_
    intro w' hw'
    rcases eq_or_ne (β w') 0 with hβ0 | hβ0
    · exact Or.inl (show e w' * β w' = 0 by rw [hβ0, mul_zero])
    · refine Or.inr ?_
      rw [w.ord_mul (he0 w') hβ0]
      have hw'T := Finset.mem_of_mem_erase hw'
      have hw'w := Finset.ne_of_mem_erase hw'
      have := hew' w' w hw hw'w.symm
      have hbd := hPbd w hw w' hw'T
      omega

end S_AlgebraicCurve_Place_exists_forall_adicValuation_sub_le
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_forall_adicValuation_sub_le (solution)
