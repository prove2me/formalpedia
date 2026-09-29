-- Prove2me | solution 1 for AutomorphicForm.exists_isHaarMeasure_centralizer_forall_isFundamentalDomain_op_inter_eq_mul_log_and_isOrbitalIntegralOn_centralScalar_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8e42e032-8194-583f-9717-af4d43247b88

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdelicHaar_exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isHaarMeasure_centralizer_forall_isFundamentalDomain_op_inter_eq_mul_log_and_isOrbitalIntegralOn_centralScalar_iff
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace P2mCentralNormalisation

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

local notation "𝔾" => AutomorphicForm.AdelicGL2 (𝓞 K) K

theorem isMulRightInvariant_of_isHaarMeasure (μ : Measure (AdelicGL2 (𝓞 K) K)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ = c • adelicGLHaar (Fin 2) (𝓞 K) K :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul μ (adelicGLHaar (Fin 2) (𝓞 K) K)⟩
  rw [hc]
  infer_instance

theorem isHaarMeasure_inv (μ : Measure (AdelicGL2 (𝓞 K) K)) [μ.IsHaarMeasure] :
    μ.inv.IsHaarMeasure := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isMulRightInvariant_of_isHaarMeasure K μ
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (AdelicGL2 (𝓞 K) K)) := inferInstance
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior μ.inv (K₀ : Set (AdelicGL2 (𝓞 K) K))
    K₀.isCompact K₀.interior_nonempty ?_ ?_
  · rw [Measure.inv_apply]
    have hsub : (interior (K₀ : Set (AdelicGL2 (𝓞 K) K)))⁻¹ ⊆ (K₀ : Set (AdelicGL2 (𝓞 K) K))⁻¹ :=
      Set.inv_subset_inv.2 interior_subset
    have hpos : 0 < μ (interior (K₀ : Set (AdelicGL2 (𝓞 K) K)))⁻¹ :=
      (isOpen_interior.inv).measure_pos μ (K₀.interior_nonempty.inv)
    exact (hpos.trans_le (measure_mono hsub)).ne'
  · rw [Measure.inv_apply]
    exact K₀.isCompact.inv.measure_lt_top.ne

theorem inv_eq_self_of_isHaarMeasure (μ : Measure (AdelicGL2 (𝓞 K) K)) [μ.IsHaarMeasure] :
    μ.inv = μ := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI := isHaarMeasure_inv K μ
  set c : ℝ≥0 := μ.inv.haarScalarFactor μ with hc_def
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv μ) = (c * c) • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul]
  have hμ : μ = (c * c) • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (AdelicGL2 (𝓞 K) K)) := inferInstance
  have hK : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K₀ = 1 * μ K₀ := by
    conv_rhs => rw [hμ]
    rw [one_mul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hKpos : 0 < μ K₀ :=
    lt_of_lt_of_le (isOpen_interior.measure_pos μ K₀.interior_nonempty) (measure_mono interior_subset)
  have hcc : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hKpos.ne' K₀.isCompact.measure_lt_top.ne).1 hK
  have hc1 : c = 1 := by
    have h : c * c = 1 := by exact_mod_cast hcc
    have hR : (c : ℝ) * c = 1 := by exact_mod_cast h
    rcases mul_self_eq_one_iff.1 hR with h1 | h1
    · exact_mod_cast h1
    · exfalso
      have := c.coe_nonneg
      linarith
  rw [hc, hc1, one_smul]

section Central

variable (u : (AdeleRing (𝓞 K) K)ˣ)

theorem centralScalar_mul_comm (g : 𝔾) :
    AutomorphicForm.centralScalar (𝓞 K) K u * g = g * AutomorphicForm.centralScalar (𝓞 K) K u := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (u : AdeleRing (𝓞 K) K) (fun r' => mul_comm _ r')
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).eq i) j

theorem conj_centralScalar (x : 𝔾) :
    x⁻¹ * AutomorphicForm.centralScalar (𝓞 K) K u * x = AutomorphicForm.centralScalar (𝓞 K) K u := by
  rw [mul_assoc, centralScalar_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mem_centralizer_centralScalar (g : 𝔾) :
    g ∈ Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (centralScalar_mul_comm K u g).symm

def centEquiv : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾) ≃ₜ* 𝔾 where
  toFun t := (t : 𝔾)
  invFun g := ⟨g, mem_centralizer_centralScalar K u g⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk continuous_id _

theorem centEquiv_apply (t : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)) :
    centEquiv K u t = (t : 𝔾) := rfl

theorem coe_centEquiv_symm_apply (g : 𝔾) : ((centEquiv K u).symm g : 𝔾) = g := rfl

abbrev ΓZ : Subgroup (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)) :=
  ((globalPoints (𝓞 K) K).range).subgroupOf
    (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾))

def eqΓ : (globalPoints (𝓞 K) K).range ≃ (ΓZ K u).op where
  toFun g := ⟨MulOpposite.op ⟨((g : 𝔾))⁻¹, mem_centralizer_centralScalar K u _⟩, by
    rw [Subgroup.mem_op, MulOpposite.unop_op, Subgroup.mem_subgroupOf]
    exact Subgroup.inv_mem _ g.2⟩
  invFun x := ⟨(((MulOpposite.unop (x : (Subgroup.centralizer
      ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾))ᵐᵒᵖ)) :
      Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)) : 𝔾)⁻¹, by
    refine Subgroup.inv_mem _ ?_
    have hx := x.2
    rw [Subgroup.mem_op, Subgroup.mem_subgroupOf] at hx
    exact hx⟩
  left_inv g := by
    apply Subtype.ext
    simp only [MulOpposite.unop_op, inv_inv]
  right_inv x := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    apply Subtype.ext
    simp only [MulOpposite.unop_op, inv_inv]

theorem eqΓ_smul (g : (globalPoints (𝓞 K) K).range)
    (t : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)) :
    ((eqΓ K u g • t : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)) : 𝔾) =
      (t : 𝔾) * ((g : 𝔾))⁻¹ := by
  rw [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop]
  rfl

end Central

theorem ideleNorm_inv (v : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm K v⁻¹ = (NumberField.TateGlobal.ideleNorm K v)⁻¹ := by
  simp [NumberField.TateGlobal.ideleNorm, map_inv]

theorem mem_band_inv_iff (g : 𝔾) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g⁻¹) ∈ Set.Icc b⁻¹ a⁻¹ ↔
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b := by
  rw [map_inv, ideleNorm_inv]
  have hN := NumberField.TateGlobal.ideleNorm_pos (F := K) (Matrix.GeneralLinearGroup.det g)
  have hb : 0 < b := ha.trans_le hab
  rw [Set.mem_Icc, Set.mem_Icc, inv_le_inv₀ hb hN, inv_le_inv₀ hN ha, and_comm]

theorem haar_inter_band_eq_of_isFundamentalDomain
    (C_H : ℝ≥0∞)
    (hC_H : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ Φ : Set 𝔾,
      Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} →
      IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) →
      adelicGLHaar (Fin 2) (𝓞 K) K Φ = C_H * ENNReal.ofReal (Real.log (b / a)))
    (Φ : Set 𝔾) (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ
      (adelicGLHaar (Fin 2) (𝓞 K) K))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    adelicGLHaar (Fin 2) (𝓞 K) K
        (Φ ∩ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) =
      C_H * ENNReal.ofReal (Real.log (b / a)) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  set η : Measure 𝔾 := adelicGLHaar (Fin 2) (𝓞 K) K with hη
  haveI : η.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  obtain ⟨S, hSsub, hSfd⟩ :=
    AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc K 1 2
  have hfin : η S ≠ ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K 1 2 one_pos one_lt_two S hSfd
    rw [Set.inter_eq_self_of_subset_left hSsub] at h
    exact h.ne
  have hSfd' : IsFundamentalDomain
      (Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) :
        Matrix.GeneralLinearGroup (Fin 2) K →* 𝔾).range S
      (η.restrict {g : 𝔾 | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc (1 : ℝ) 2}) := hSfd
  obtain ⟨C_T, hT0, hTt, hglob, hband⟩ :=
    NumberField.AdelicHaar.exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log
      (Fin 2) K η 1 2 one_pos one_lt_two S hSsub hSfd' hfin

  have h1 : η S = C_T * ENNReal.ofReal (Real.log (2 / 1)) := hband 1 2 one_pos one_le_two S hSsub hSfd'
  have h2 : η S = C_H * ENNReal.ofReal (Real.log (2 / 1)) := hC_H 1 2 one_pos one_le_two S hSsub hSfd
  have hlog0 : ENNReal.ofReal (Real.log (2 / 1)) ≠ 0 := by
    rw [div_one]
    exact (ENNReal.ofReal_pos.2 (Real.log_pos one_lt_two)).ne'
  have hCT : C_T = C_H :=
    (ENNReal.mul_left_inj hlog0 ENNReal.ofReal_ne_top).1 (h1.symm.trans h2)
  rw [← hCT]
  exact hglob Φ hΦ a b ha hab

theorem exists_bump_integral_eq (μ : Measure 𝔾) [μ.IsHaarMeasure] (r : ℝ) (hr : 0 ≤ r) :
    ∃ w : 𝔾 → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧ ∫ x, w x ∂μ = r := by
  classical
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  obtain ⟨C⟩ : Nonempty (TopologicalSpace.PositiveCompacts 𝔾) := inferInstance
  have hCpos : 0 < μ C :=
    lt_of_lt_of_le (isOpen_interior.measure_pos μ C.interior_nonempty) (measure_mono interior_subset)
  have hCtop : μ C < ⊤ := C.isCompact.measure_lt_top
  have hCreal : 0 < μ.real (C : Set 𝔾) := ENNReal.toReal_pos hCpos.ne' hCtop.ne
  have hCmeas : MeasurableSet (C : Set 𝔾) := C.isCompact.measurableSet
  refine ⟨fun x => r * (μ.real (C : Set 𝔾))⁻¹ * (C : Set 𝔾).indicator 1 x, fun x => ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg hr (inv_nonneg.2 ENNReal.toReal_nonneg))
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  · exact measurable_const.mul (measurable_const.indicator hCmeas)
  · refine HasCompactSupport.intro C.isCompact fun x hx => ?_
    simp [Set.indicator_of_notMem hx]
  · rw [integral_const_mul, integral_indicator_one hCmeas, mul_assoc, inv_mul_cancel₀ hCreal.ne', mul_one]

theorem main
    (C_H : ℝ≥0∞) (hC0 : C_H ≠ 0) (hCt : C_H ≠ ⊤)
    (hC_H : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ Φ : Set 𝔾,
      Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} →
      IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) →
      adelicGLHaar (Fin 2) (𝓞 K) K Φ = C_H * ENNReal.ofReal (Real.log (b / a)))
    (u : (AdeleRing (𝓞 K) K)ˣ) (C : ℝ≥0∞) (hC0' : C ≠ 0) (hCt' : C ≠ ⊤) :
    ∃ τ : Measure (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)),
      τ.IsHaarMeasure ∧ τ.IsMulRightInvariant ∧
      (∃ D : Set (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)),
        IsFundamentalDomain (ΓZ K u).op D τ) ∧
      (∀ D : Set (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)),
        IsFundamentalDomain (ΓZ K u).op D τ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
            (Matrix.GeneralLinearGroup.det (t : 𝔾)) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a))) ∧
      ∀ (c₀ : NNReal) (f : 𝔾 → ℂ) (I : ℂ),
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
            (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I ↔
          I = (((c₀ : ℝ) * (C_H / C).toReal : ℝ) : ℂ) * f (AutomorphicForm.centralScalar (𝓞 K) K u) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)) := ⟨rfl⟩
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  set μ : Measure 𝔾 := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  haveI : μ.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : μ.IsMulRightInvariant := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  set e := centEquiv K u with he
  have hesm : Measurable (e.symm : 𝔾 → Subgroup.centralizer
      ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)) := e.symm.continuous.measurable
  have hemb : MeasurableEmbedding (e.symm : 𝔾 → Subgroup.centralizer
      ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)) :=
    e.symm.toHomeomorph.measurableEmbedding

  set μc : Measure (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)) :=
    Measure.map e.symm μ with hμc
  haveI hμcH : μc.IsHaarMeasure := e.symm.isHaarMeasure_map μ
  haveI hμcR : μc.IsMulRightInvariant := by
    refine ⟨fun t => ?_⟩
    rw [hμc, Measure.map_map (measurable_mul_const t) hesm]
    have hcomp : ((fun s => s * t) ∘ (e.symm : 𝔾 → Subgroup.centralizer
        ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾))) =
        (e.symm : 𝔾 → _) ∘ fun g : 𝔾 => g * (t : 𝔾) := by
      funext g
      rfl
    rw [hcomp, ← Measure.map_map hesm (measurable_mul_const (t : 𝔾)), map_mul_right_eq_self]
  set s : ℝ≥0∞ := C / C_H with hs
  have hs0 : s ≠ 0 := by
    rw [hs]
    intro h
    rw [ENNReal.div_eq_zero_iff] at h
    exact h.elim hC0' hCt
  have hst : s ≠ ⊤ := ENNReal.div_ne_top hCt' hC0
  have hsC : s * C_H = C := ENNReal.div_mul_cancel hC0 hCt
  set τ : Measure (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)) :=
    s • μc with hτ
  haveI hτH : τ.IsHaarMeasure := Measure.IsHaarMeasure.smul μc hs0 hst
  haveI hτR : τ.IsMulRightInvariant := by rw [hτ]; infer_instance

  set fm : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾) ≃ᵐ 𝔾 :=
    (e.toHomeomorph.trans (Homeomorph.inv 𝔾)).toMeasurableEquiv with hfm_def
  have hfm : ∀ t : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾),
      fm t = ((t : 𝔾))⁻¹ := fun _ => rfl
  have hmapμc : Measure.map fm μc = μ := by
    have hcomp : (fm : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾) → 𝔾) ∘
        (e.symm : 𝔾 → _) = fun g : 𝔾 => g⁻¹ := by
      funext g
      rfl
    rw [hμc, Measure.map_map fm.measurable hesm, hcomp, ← Measure.inv_def, inv_eq_self_of_isHaarMeasure]
  have hmap : Measure.map fm τ = s • μ := by
    rw [hτ, Measure.map_smul, hmapμc]
  have hqmp : Measure.QuasiMeasurePreserving fm τ (s • μ) := ⟨fm.measurable, by rw [hmap]⟩
  have hqmp' : Measure.QuasiMeasurePreserving fm.symm (s • μ) τ := by
    refine ⟨fm.symm.measurable, ?_⟩
    rw [← hmap, MeasurableEquiv.map_symm_map]
  have hsemi : ∀ (g : (globalPoints (𝓞 K) K).range)
      (x : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾)),
      fm (eqΓ K u g • x) = g • fm x := fun g x => by
    rw [hfm, hfm, eqΓ_smul, Subgroup.smul_def, smul_eq_mul, mul_inv_rev, inv_inv]
  refine ⟨τ, hτH, hτR, ?_, ?_, ?_⟩
  ·
    obtain ⟨Φ₀, hΦ₀⟩ := AutomorphicForm.exists_isFundamentalDomain_globalPoints_range K
    have hΦ₀' : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ (s • μ) :=
      hΦ₀.mono Measure.smul_absolutelyContinuous
    refine ⟨fm ⁻¹' Φ₀, ?_⟩
    exact hΦ₀'.preimage_of_equiv hqmp (eqΓ K u).bijective (fun g x => hsemi g x)
  ·
    intro D hD a b ha hab
    have hFD : IsFundamentalDomain (globalPoints (𝓞 K) K).range (fm '' D) (s • μ) :=
      hD.image_of_equiv fm.toEquiv hqmp' (eqΓ K u) (fun g x => hsemi g x)
    have hFDμ : IsFundamentalDomain (globalPoints (𝓞 K) K).range (fm '' D) μ :=
      hFD.mono (Measure.absolutelyContinuous_smul hs0)
    have hb : 0 < b := ha.trans_le hab
    have key := haar_inter_band_eq_of_isFundamentalDomain K C_H hC_H (fm '' D) hFDμ b⁻¹ a⁻¹
      (inv_pos.2 hb) ((inv_le_inv₀ hb ha).2 hab)
    have hset : D ∩ {t : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾) |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (t : 𝔾)) ∈ Set.Icc a b} =
        fm ⁻¹' (fm '' D ∩ {g : 𝔾 | NumberField.TateGlobal.ideleNorm K
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc b⁻¹ a⁻¹}) := by
      rw [Set.preimage_inter, fm.injective.preimage_image]
      congr 1
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hfm]
      exact (mem_band_inv_iff K (t : 𝔾) ha hab).symm
    calc τ (D ∩ {t : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾) |
            NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (t : 𝔾)) ∈ Set.Icc a b})
        = τ (fm ⁻¹' (fm '' D ∩ {g : 𝔾 | NumberField.TateGlobal.ideleNorm K
            (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc b⁻¹ a⁻¹})) := by rw [hset]
      _ = Measure.map fm τ (fm '' D ∩ {g : 𝔾 | NumberField.TateGlobal.ideleNorm K
            (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc b⁻¹ a⁻¹}) := (MeasurableEquiv.map_apply fm _).symm
      _ = s * (C_H * ENNReal.ofReal (Real.log (a⁻¹ / b⁻¹))) := by
          rw [hmap, Measure.smul_apply, smul_eq_mul, key]
      _ = C * ENNReal.ofReal (Real.log (b / a)) := by rw [inv_div_inv, ← mul_assoc, hsC]
  ·
    intro c₀ f I

    have hcoset : ∀ (w : 𝔾 → ℝ) (x : 𝔾),
        ∫ t : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾), w (t * x) ∂τ =
          s.toReal * ∫ g, w g ∂μ := by
      intro w x
      rw [hτ, integral_smul_measure, hμc, hemb.integral_map]
      have hrw : (fun g : 𝔾 => w ((((e.symm g : Subgroup.centralizer
          ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾))) : 𝔾) * x)) = fun g => w (g * x) := by
        funext g
        rfl
      rw [hrw, integral_mul_right_eq_self (fun g => w g) x]
      rfl
    have hsR : s.toReal * (C_H / C).toReal = 1 := by
      rw [← ENNReal.toReal_mul, ← mul_div_assoc, hsC, ENNReal.div_self hC0' hCt', ENNReal.toReal_one]

    have hrw : ∀ w : 𝔾 → ℝ, (fun x : 𝔾 => f (x⁻¹ * AutomorphicForm.centralScalar (𝓞 K) K u * x) * (w x : ℂ)) =
        fun x => f (AutomorphicForm.centralScalar (𝓞 K) K u) * (w x : ℂ) := fun w => by
      funext x
      rw [conj_centralScalar]
    constructor
    · rintro ⟨w, ⟨hw0, hwm, hwc, hw1⟩, rfl⟩
      rw [hrw w, integral_smul_nnreal_measure, integral_const_mul, integral_complex_ofReal]
      by_cases hf0 : f (AutomorphicForm.centralScalar (𝓞 K) K u) = 0
      · simp [hf0]
      · have h1 : ∫ t : Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set 𝔾),
            w (t * 1) ∂τ = 1 := hw1 1 (by rwa [inv_one, one_mul, mul_one])
        rw [hcoset w 1] at h1
        have hint : ∫ g, w g ∂μ = (C_H / C).toReal := by
          have h2 : (C_H / C).toReal * (s.toReal * ∫ g, w g ∂μ) = (C_H / C).toReal * 1 := by rw [h1]
          rwa [← mul_assoc, mul_comm ((C_H / C).toReal) s.toReal, hsR, one_mul, mul_one] at h2
        rw [hint]
        simp only [NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul]
        ring
    · rintro rfl
      obtain ⟨w, hw0, hwm, hwc, hint⟩ :=
        exists_bump_integral_eq K μ ((C_H / C).toReal) ENNReal.toReal_nonneg
      refine ⟨w, ⟨hw0, hwm, hwc, fun x _ => ?_⟩, ?_⟩
      · rw [hcoset w x, hint, hsR]
      · rw [hrw w, integral_smul_nnreal_measure, integral_const_mul, integral_complex_ofReal, hint]
        simp only [NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul]
        ring

end P2mCentralNormalisation

end

open MeasureTheory NumberField NumberField.AdelicHaar
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (C_H : ℝ≥0∞) (hC0 : C_H ≠ 0) (hCt : C_H ≠ ⊤)
    (hC_H : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K),
      Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} →
      IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) →
      adelicGLHaar (Fin 2) (𝓞 K) K Φ = C_H * ENNReal.ofReal (Real.log (b / a)))
    (u : (AdeleRing (𝓞 K) K)ˣ) (C : ℝ≥0∞) (hC0' : C ≠ 0) (hCt' : C ≠ ⊤) :
    ∃ τ : Measure (Subgroup.centralizer
        ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
      τ.IsHaarMeasure ∧ τ.IsMulRightInvariant ∧
      (∃ D : Set (Subgroup.centralizer
          ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
        IsFundamentalDomain
          (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf
            (Subgroup.centralizer
              ({AutomorphicForm.centralScalar (𝓞 K) K u} :
                Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))).op D τ) ∧
      (∀ D : Set (Subgroup.centralizer
          ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
        IsFundamentalDomain
          (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf
            (Subgroup.centralizer
              ({AutomorphicForm.centralScalar (𝓞 K) K u} :
                Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))).op D τ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
            (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a))) ∧
      ∀ (c₀ : NNReal) (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (I : ℂ),
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
            (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I ↔
          I = (((c₀ : ℝ) * (C_H / C).toReal : ℝ) : ℂ) * f (AutomorphicForm.centralScalar (𝓞 K) K u) :=
  P2mCentralNormalisation.main K C_H hC0 hCt hC_H u C hC0' hCt'

end S_AutomorphicForm_exists_isHaarMeasure_centralizer_forall_isFundamentalDomain_op_inter_eq_mul_log_and_isOrbitalIntegralOn_centralScalar_iff
end P2MW
export P2MW.S_AutomorphicForm_exists_isHaarMeasure_centralizer_forall_isFundamentalDomain_op_inter_eq_mul_log_and_isOrbitalIntegralOn_centralScalar_iff (solution)
