-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_forall_ord_eq_finset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f67a8ab7-f1e7-55ac-aa57-4ac4a7626053

import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_forall_ord_eq_finset
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option Elab.async false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.ord"
p2m_open "AlgebraicCurve"

namespace WC1bSolAW

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_neg_impl (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  simp only [Place.ord, Valuation.map_neg]

theorem add_ne_zero_of_ord_lt (v : Place K F) {f g : F} (hlt : v.ord f < v.ord g) :
    f + g ≠ 0 := by
  intro h0
  rw [eq_neg_of_add_eq_zero_right h0, ord_neg_impl] at hlt
  exact lt_irrefl _ hlt

theorem ord_add_eq_of_ord_lt (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (hlt : v.ord f < v.ord g) : v.ord (f + g) = v.ord f := by
  have hval : v.adicValuation g < v.adicValuation f := by
    rw [← WithZero.log_lt_log (v.adicValuation_ne_zero hg) (v.adicValuation_ne_zero hf)]
    simp only [Place.ord] at hlt
    omega
  simp only [Place.ord]
  rw [Valuation.map_add_eq_of_lt_left _ hval]

theorem ord_lt_zero_of_notMem (v : Place K F) {f : F} (hf : f ≠ 0) (h : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  by_contra hcon
  exact h (v.mem_of_ord_nonneg hf (not_lt.mp hcon))

theorem exists_mem_notMem_of_ne {v w : Place K F} (hvw : v ≠ w) :
    ∃ x : F, x ≠ 0 ∧ x ∈ v.toValuationSubring ∧ x ∉ w.toValuationSubring := by
  have hle : ¬(v.toValuationSubring ≤ w.toValuationSubring) := fun hle =>
    hvw (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ hle w.ne_top'))
  obtain ⟨x, hxv, hxw⟩ := SetLike.not_le_iff_exists.mp hle
  exact ⟨x, fun h0 => hxw (h0 ▸ w.toValuationSubring.zero_mem), hxv, hxw⟩

theorem exists_ord_pos_ord_neg_of_ne {v w : Place K F} (hvw : v ≠ w) :
    ∃ z : F, z ≠ 0 ∧ 0 < v.ord z ∧ w.ord z < 0 := by
  obtain ⟨x, hx0, hxv, hxw⟩ := exists_mem_notMem_of_ne hvw
  obtain ⟨y, hy0, hyw, hyv⟩ := exists_mem_notMem_of_ne hvw.symm
  have hy0' : y⁻¹ ≠ 0 := inv_ne_zero hy0
  refine ⟨x * y⁻¹, mul_ne_zero hx0 hy0', ?_, ?_⟩
  · rw [v.ord_mul hx0 hy0', v.ord_inv]
    have h1 := v.ord_nonneg_of_mem hxv
    have h2 := ord_lt_zero_of_notMem v hy0 hyv
    omega
  · rw [w.ord_mul hx0 hy0', w.ord_inv]
    have h1 := ord_lt_zero_of_notMem w hx0 hxw
    have h2 := w.ord_nonneg_of_mem hyw
    omega

theorem ord_finsetSum_gt {ι : Type*} (v : Place K F) (s : Finset ι) (g : ι → F) (m : ℤ) :
    (∀ i ∈ s, g i ≠ 0 ∧ m < v.ord (g i)) →
      s.sum g = 0 ∨ (s.sum g ≠ 0 ∧ m < v.ord (s.sum g)) := by
  classical
  induction s using Finset.cons_induction with
  | empty => exact fun _ => Or.inl Finset.sum_empty
  | cons i s hi ih =>
      intro h
      rw [Finset.sum_cons]
      obtain ⟨hgi0, hgim⟩ := h i (Finset.mem_cons.mpr (Or.inl rfl))
      rcases ih (fun j hj => h j (Finset.mem_cons.mpr (Or.inr hj))) with h0 | ⟨hne, hlt⟩
      · rw [h0, add_zero]
        exact Or.inr ⟨hgi0, hgim⟩
      · rcases eq_or_ne (g i + s.sum g) 0 with hz | hz
        · exact Or.inl hz
        · refine Or.inr ⟨hz, ?_⟩
          exact lt_of_lt_of_le (lt_min hgim hlt) (v.min_ord_le_ord_add hgi0 hne hz)

theorem exists_separating (v : Place K F) (S : Finset (Place K F)) :
    ∃ t : F, t ≠ 0 ∧ 0 < v.ord t ∧ ∀ w ∈ S, w ≠ v → w.ord t < 0 := by
  classical
  induction S using Finset.cons_induction with
  | empty =>
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
      have hπ0 : (π : F) ≠ 0 := by
        simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
      refine ⟨(π : F), hπ0, ?_, fun w hw => absurd hw (Finset.notMem_empty w)⟩
      rw [v.ord_coe_irreducible hπ]
      omega
  | cons w₀ S' hw₀ ih =>
      obtain ⟨t₁, ht₁0, ht₁v, ht₁S⟩ := ih
      rcases eq_or_ne w₀ v with heq | hw₀v
      · refine ⟨t₁, ht₁0, ht₁v, ?_⟩
        intro w hw hwv
        rcases Finset.mem_cons.mp hw with h | h
        · exact absurd (h.trans heq) hwv
        · exact ht₁S w h hwv
      · obtain ⟨t₂, ht₂0, ht₂v, ht₂w⟩ := exists_ord_pos_ord_neg_of_ne (Ne.symm hw₀v)

        set M : ℕ :=
          ((Finset.cons w₀ S' hw₀).sup fun w => (1 - w.ord t₁).toNat) + 1 with hM
        have hM1 : 1 ≤ (M : ℤ) := by
          rw [hM]; push_cast; omega
        have hMw : ∀ w ∈ Finset.cons w₀ S' hw₀, -(M : ℤ) < w.ord t₁ := by
          intro w hw
          have h1 : (1 - w.ord t₁).toNat
              ≤ (Finset.cons w₀ S' hw₀).sup fun w' => (1 - w'.ord t₁).toNat :=
            Finset.le_sup (f := fun w' => (1 - w'.ord t₁).toNat) hw
          have h3 : ((1 - w.ord t₁).toNat : ℤ)
              ≤ (((Finset.cons w₀ S' hw₀).sup fun w' => (1 - w'.ord t₁).toNat : ℕ) : ℤ) := by
            exact_mod_cast h1
          rw [hM]; push_cast; omega
        have hpow0 : t₂ ^ (M : ℤ) ≠ 0 := zpow_ne_zero _ ht₂0
        have hw₀lt : w₀.ord (t₂ ^ (M : ℤ)) < w₀.ord t₁ := by
          rw [w₀.ord_zpow]
          have h5 : (M : ℤ) * w₀.ord t₂ ≤ (M : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left (by omega) (by omega)
          have h6 := hMw w₀ (Finset.mem_cons.mpr (Or.inl rfl))
          linarith
        have hu0 : t₁ + t₂ ^ (M : ℤ) ≠ 0 := by
          have h := add_ne_zero_of_ord_lt w₀ hw₀lt
          rwa [add_comm (t₂ ^ (M : ℤ)) t₁] at h
        refine ⟨t₁ + t₂ ^ (M : ℤ), hu0, ?_, ?_⟩
        ·
          have hposM : 0 < v.ord (t₂ ^ (M : ℤ)) := by
            rw [v.ord_zpow]
            exact mul_pos (by omega) ht₂v
          exact lt_of_lt_of_le (lt_min ht₁v hposM) (v.min_ord_le_ord_add ht₁0 hpow0 hu0)
        · intro w hw hwv
          rcases Finset.mem_cons.mp hw with heqw | hwS'
          ·
            rw [heqw, add_comm t₁ (t₂ ^ (M : ℤ)),
              ord_add_eq_of_ord_lt w₀ hpow0 ht₁0 hw₀lt, w₀.ord_zpow]
            have h5 : (M : ℤ) * w₀.ord t₂ ≤ (M : ℤ) * (-1) :=
              mul_le_mul_of_nonneg_left (by omega) (by omega)
            linarith
          ·
            have hward := ht₁S w hwS' hwv
            rcases le_or_gt 0 (w.ord t₂) with hpos | hneg
            · have hlt : w.ord t₁ < w.ord (t₂ ^ (M : ℤ)) := by
                rw [w.ord_zpow]
                have h7 : 0 ≤ (M : ℤ) * w.ord t₂ := mul_nonneg (by omega) hpos
                linarith
              rw [ord_add_eq_of_ord_lt w ht₁0 hpow0 hlt]
              exact hward
            · have hlt : w.ord (t₂ ^ (M : ℤ)) < w.ord t₁ := by
                rw [w.ord_zpow]
                have h5 : (M : ℤ) * w.ord t₂ ≤ (M : ℤ) * (-1) :=
                  mul_le_mul_of_nonneg_left (by omega) (by omega)
                have h6 := hMw w (Finset.mem_cons.mpr (Or.inr hwS'))
                linarith
              rw [add_comm t₁ (t₂ ^ (M : ℤ)),
                ord_add_eq_of_ord_lt w hpow0 ht₁0 hlt, w.ord_zpow]
              have h5 : (M : ℤ) * w.ord t₂ ≤ (M : ℤ) * (-1) :=
                mul_le_mul_of_nonneg_left (by omega) (by omega)
              linarith

theorem exists_forall_ord_eq_finset (S : Finset (Place K F)) (n : Place K F → ℤ) :
    ∃ g : F, g ≠ 0 ∧ ∀ v ∈ S, v.ord g = n v := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · exact ⟨1, one_ne_zero, fun v hv => absurd hv (Finset.notMem_empty v)⟩

  have hsep : ∀ v : Place K F, ∃ t : F, t ≠ 0 ∧ 0 < v.ord t ∧
      ∀ w ∈ S, w ≠ v → w.ord t < 0 := fun v => exists_separating v S
  choose t ht0 htv htS using hsep

  have hunif : ∀ v : Place K F, ∃ π : v.toValuationSubring, Irreducible π := fun v =>
    IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  choose π hπ using hunif
  have hπ0 : ∀ v : Place K F, ((π v : F)) ≠ 0 := by
    intro v
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using (hπ v).ne_zero
  set a : Place K F → F := fun v => ((π v : F)) ^ (n v) with ha
  have ha0 : ∀ v, a v ≠ 0 := by
    intro v
    simp only [ha]
    exact zpow_ne_zero _ (hπ0 v)
  have hav : ∀ v, v.ord (a v) = n v := by
    intro v
    simp only [ha]
    rw [v.ord_zpow, v.ord_coe_irreducible (hπ v), mul_one]

  set P : ℕ := (S.sup fun v => S.sup fun w => (n v - v.ord (a w)).toNat) + 1 with hP
  have hP1 : 1 ≤ (P : ℤ) := by
    rw [hP]; push_cast; omega
  have hPbound : ∀ v ∈ S, ∀ w ∈ S, n v - v.ord (a w) < (P : ℤ) := by
    intro v hv w hw
    have h1 : (n v - v.ord (a w)).toNat
        ≤ S.sup fun w' => (n v - v.ord (a w')).toNat :=
      Finset.le_sup (f := fun w' => (n v - v.ord (a w')).toNat) hw
    have h2 : (S.sup fun w' => (n v - v.ord (a w')).toNat)
        ≤ S.sup fun v' => S.sup fun w' => (n v' - v'.ord (a w')).toNat :=
      Finset.le_sup (f := fun v' => S.sup fun w' => (n v' - v'.ord (a w')).toNat) hv
    have h3 : ((n v - v.ord (a w)).toNat : ℤ)
        ≤ ((S.sup fun v' => S.sup fun w' => (n v' - v'.ord (a w')).toNat : ℕ) : ℤ) := by
      exact_mod_cast le_trans h1 h2
    rw [hP]; push_cast; omega

  have hpow0 : ∀ v : Place K F, t v ^ (P : ℤ) ≠ 0 := fun v => zpow_ne_zero _ (ht0 v)
  have hltden : ∀ v : Place K F, v.ord (1 : F) < v.ord (t v ^ (P : ℤ)) := by
    intro v
    rw [v.ord_one, v.ord_zpow]
    exact mul_pos (by omega) (htv v)
  have hden : ∀ v : Place K F, (1 : F) + t v ^ (P : ℤ) ≠ 0 := fun v =>
    add_ne_zero_of_ord_lt v (hltden v)
  have hdenord : ∀ v : Place K F, v.ord ((1 : F) + t v ^ (P : ℤ)) = 0 := by
    intro v
    rw [ord_add_eq_of_ord_lt v one_ne_zero (hpow0 v) (hltden v), v.ord_one]
  have hdenord' : ∀ v : Place K F, ∀ w ∈ S, w ≠ v →
      w.ord ((1 : F) + t v ^ (P : ℤ)) = (P : ℤ) * w.ord (t v) := by
    intro v w hw hwv
    have hneg : w.ord (t v ^ (P : ℤ)) < w.ord (1 : F) := by
      rw [w.ord_one, w.ord_zpow]
      have h1 := htS v w hw hwv
      have h5 : (P : ℤ) * w.ord (t v) ≤ (P : ℤ) * (-1) :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      linarith
    rw [add_comm ((1 : F)) (t v ^ (P : ℤ)),
      ord_add_eq_of_ord_lt w (hpow0 v) one_ne_zero hneg, w.ord_zpow]

  set u : Place K F → F := fun v => a v * ((1 : F) + t v ^ (P : ℤ))⁻¹ with hu
  have hu0 : ∀ v, u v ≠ 0 := by
    intro v
    simp only [hu]
    exact mul_ne_zero (ha0 v) (inv_ne_zero (hden v))
  have huord : ∀ v, v.ord (u v) = n v := by
    intro v
    simp only [hu]
    rw [v.ord_mul (ha0 v) (inv_ne_zero (hden v)), v.ord_inv, hdenord v, hav v]
    omega
  have huord' : ∀ v : Place K F, ∀ w ∈ S, w ≠ v →
      w.ord (u v) = w.ord (a v) - (P : ℤ) * w.ord (t v) := by
    intro v w hw hwv
    simp only [hu]
    rw [w.ord_mul (ha0 v) (inv_ne_zero (hden v)), w.ord_inv, hdenord' v w hw hwv]
    ring

  have htail : ∀ v ∈ S, ∀ w ∈ S, w ≠ v → n v < v.ord (u w) := by
    intro v hv w hw hwv
    have h1 : v.ord (u w) = v.ord (a w) - (P : ℤ) * v.ord (t w) :=
      huord' w v hv (Ne.symm hwv)
    have h2 := htS w v hv (Ne.symm hwv)
    have h3 := hPbound v hv w hw
    have h5 : (P : ℤ) * v.ord (t w) ≤ (P : ℤ) * (-1) :=
      mul_le_mul_of_nonneg_left (by omega) (by omega)
    rw [h1]
    linarith

  have hmain : ∀ v ∈ S, S.sum u ≠ 0 ∧ v.ord (S.sum u) = n v := by
    intro v hv
    have hsplit : S.sum u = u v + (S.erase v).sum u :=
      (Finset.add_sum_erase S u hv).symm
    have hcond : ∀ w ∈ S.erase v, u w ≠ 0 ∧ n v < v.ord (u w) := by
      intro w hw
      obtain ⟨hwv, hwS⟩ := Finset.mem_erase.mp hw
      exact ⟨hu0 w, htail v hv w hwS hwv⟩
    rcases ord_finsetSum_gt v (S.erase v) u (n v) hcond with h0 | ⟨hne, hlt⟩
    · rw [hsplit, h0, add_zero]
      exact ⟨hu0 v, huord v⟩
    · have hltu : v.ord (u v) < v.ord ((S.erase v).sum u) := by
        rw [huord v]; exact hlt
      constructor
      · rw [hsplit]
        exact add_ne_zero_of_ord_lt v hltu
      · rw [hsplit, ord_add_eq_of_ord_lt v (hu0 v) hne hltu]
        exact huord v
  obtain ⟨v₀, hv₀⟩ := hSne
  exact ⟨S.sum u, (hmain v₀ hv₀).1, fun v hv => (hmain v hv).2⟩

end WC1bSolAW

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_exists_forall_ord_eq_finset.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (S : Finset (AlgebraicCurve.Place K F)) (n : AlgebraicCurve.Place K F → ℤ) :
    ∃ g : F, g ≠ 0 ∧ ∀ v ∈ S, v.ord g = n v :=
  AlgebraicCurve.WC1bSolAW.exists_forall_ord_eq_finset S n

end

end S_AlgebraicCurve_Place_exists_forall_ord_eq_finset
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_forall_ord_eq_finset (solution)
