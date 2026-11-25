-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
-- name    : GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:42:14.256449+00:00
-- url     : https://prove2.me/theorems/f5c565ed-bc57-46f7-a7a6-9d43d42e8cba
-- title:
--   Idele Measure Norm One
-- statement:
--   Definitions and structural lemmas for Idele Measure Norm One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureNormOne.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_continuous_ideleModule
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_ideleModule
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_ideleModule_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isClosed_normOneSubgroup
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace Real
open scoped NumberField.AdeleRing ENNReal NNReal
namespace GroundTheory.Global
noncomputable section
section PosReal
instance isTopologicalGroup_posReal : IsTopologicalGroup {r : ℝ // 0 < r} where
  continuous_mul := ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_inv := (continuous_subtype_val.inv₀ fun r ↦ r.2.ne').subtype_mk _
instance locallyCompactSpace_posReal : LocallyCompactSpace {r : ℝ // 0 < r} :=
  (isOpen_Ioi (a := (0 : ℝ))).isOpenEmbedding_subtypeVal.locallyCompactSpace
def expPos (x : ℝ) : {r : ℝ // 0 < r} := ⟨exp x, exp_pos x⟩
@[simp] theorem coe_expPos (x : ℝ) : (expPos x : ℝ) = exp x := rfl
def expPosHomeomorph : ℝ ≃ₜ {r : ℝ // 0 < r} where
  toFun := expPos
  invFun r := log r
  left_inv x := log_exp x
  right_inv r := Subtype.ext (exp_log r.2)
  continuous_toFun := continuous_exp.subtype_mk _
  continuous_invFun := continuous_subtype_val.log fun r ↦ r.2.ne'
theorem expPos_add (x y : ℝ) : expPos (x + y) = expPos x * expPos y :=
  Subtype.ext (exp_add x y)
theorem measurable_expPos : Measurable expPos := expPosHomeomorph.continuous.measurable
def posRealMeasure : Measure {r : ℝ // 0 < r} :=
  Measure.comap Subtype.val (volume.withDensity fun t : ℝ ↦ ENNReal.ofReal t⁻¹)
theorem measurableEmbedding_posReal_val :
    MeasurableEmbedding (Subtype.val : {r : ℝ // 0 < r} → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Ioi
theorem posRealMeasure_eq_map_expPos : posRealMeasure = Measure.map expPos volume := by
  ext S hS
  rw [posRealMeasure, measurableEmbedding_posReal_val.comap_apply,
    withDensity_apply _ (measurableEmbedding_posReal_val.measurableSet_image' hS),
    Measure.map_apply measurable_expPos hS]
  set s : Set ℝ := expPos ⁻¹' S
  have hs : MeasurableSet s := measurable_expPos hS
  have himg : exp '' s = Subtype.val '' S := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨expPos x, hx, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      refine ⟨log r, ?_, exp_log r.2⟩
      change expPos (log r) ∈ S
      convert hr
      exact Subtype.ext (exp_log r.2)
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul hs
    (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt) (exp_injective.injOn)]
  rw [← setLIntegral_one]
  refine setLIntegral_congr_fun hs fun x _ ↦ ?_
  rw [abs_of_pos (exp_pos x), ← ENNReal.ofReal_mul (exp_pos x).le, mul_inv_cancel₀ (exp_pos x).ne',
    ENNReal.ofReal_one]
instance isHaarMeasure_posRealMeasure : posRealMeasure.IsHaarMeasure := by
  rw [posRealMeasure_eq_map_expPos]
  have h1 : (Measure.map expPos volume).IsMulLeftInvariant := by
    refine ⟨fun a ↦ ?_⟩
    rw [Measure.map_map (measurable_const_mul a) measurable_expPos]
    have : (fun x ↦ a * x) ∘ expPos = expPos ∘ (fun x ↦ log a + x) := by
      funext x
      simp only [Function.comp_apply, expPos_add]
      congr 1
      exact Subtype.ext (exp_log a.2).symm
    rw [this, ← Measure.map_map measurable_expPos (measurable_const_add _),
      map_add_left_eq_self]
  have h2 : IsFiniteMeasureOnCompacts (Measure.map expPos volume) := by
    refine ⟨fun C hC ↦ ?_⟩
    rw [Measure.map_apply measurable_expPos hC.isClosed.measurableSet]
    exact (expPosHomeomorph.isCompact_preimage.2 hC).measure_lt_top
  have h3 : (Measure.map expPos volume).IsOpenPosMeasure := by
    refine ⟨fun U hU hne ↦ ?_⟩
    rw [Measure.map_apply measurable_expPos hU.measurableSet]
    exact (hU.preimage expPosHomeomorph.continuous).measure_ne_zero volume
      (hne.preimage expPosHomeomorph.surjective)
  exact {}
end PosReal
section ModuleSection
open InfinitePlace InfinitePlace.Completion IdeleGroup
variable {K : Type*} [Field K]
def posRealElem (w : InfinitePlace K) (t : ℝ) : w.Completion :=
  open Classical in
  if hw : w.IsReal then (ringEquivRealOfIsReal hw).symm t
  else (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm (Real.sqrt t : ℂ)
theorem posRealElem_mul (w : InfinitePlace K) {s t : ℝ} (hs : 0 ≤ s) :
    posRealElem w (s * t) = posRealElem w s * posRealElem w t := by
  unfold posRealElem
  split_ifs with hw
  · exact map_mul _ s t
  · rw [Real.sqrt_mul hs, Complex.ofReal_mul, map_mul]
theorem posRealElem_one (w : InfinitePlace K) : posRealElem w 1 = 1 := by
  unfold posRealElem
  split_ifs with hw
  · exact map_one _
  · rw [Real.sqrt_one, Complex.ofReal_one, map_one]
theorem norm_posRealElem_pow (w : InfinitePlace K) {t : ℝ} (ht : 0 ≤ t) :
    ‖posRealElem w t‖ ^ w.mult = t := by
  unfold posRealElem
  split_ifs with hw
  · have h : ‖(ringEquivRealOfIsReal hw).symm t‖ = ‖t‖ :=
      (isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
        (map_zero (ringEquivRealOfIsReal hw).symm) t
    rw [h, mult, if_pos hw, pow_one, Real.norm_of_nonneg ht]
  · have hc := not_isReal_iff_isComplex.1 hw
    have h : ‖(ringEquivComplexOfIsComplex hc).symm (Real.sqrt t : ℂ)‖ = ‖(Real.sqrt t : ℂ)‖ :=
      (isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
        (map_zero (ringEquivComplexOfIsComplex hc).symm) _
    rw [h, mult, if_neg hw, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t),
      Real.sq_sqrt ht]
theorem posRealElem_ne_zero (w : InfinitePlace K) {t : ℝ} (ht : 0 < t) : posRealElem w t ≠ 0 := by
  intro h
  have := norm_posRealElem_pow w ht.le
  rw [h, norm_zero, zero_pow (by unfold mult; split_ifs <;> norm_num)] at this
  exact ht.ne this
theorem continuous_posRealElem (w : InfinitePlace K) : Continuous (posRealElem w) := by
  unfold posRealElem
  split_ifs with hw
  · exact (isometryEquivRealOfIsReal hw).symm.continuous
  · exact (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm.continuous.comp
      (Complex.continuous_ofReal.comp Real.continuous_sqrt)
def posRealToUnits (w : InfinitePlace K) : {r : ℝ // 0 < r} →* (w.Completion)ˣ where
  toFun t := Units.mk0 (posRealElem w t) (posRealElem_ne_zero w t.2)
  map_one' := Units.ext (posRealElem_one w)
  map_mul' s _ := Units.ext (posRealElem_mul w s.2.le)
theorem continuous_posRealToUnits (w : InfinitePlace K) : Continuous (posRealToUnits w) :=
  Units.continuous_iff.2 ⟨(continuous_posRealElem w).comp continuous_subtype_val,
    ((continuous_posRealElem w).comp continuous_subtype_val).inv₀ fun t ↦
      posRealElem_ne_zero w t.2⟩
variable [NumberField K]
def moduleSection (w : InfinitePlace K) : {r : ℝ // 0 < r} →* IdeleGroup K :=
  (infiniteEmbedding w).comp (posRealToUnits w)
theorem continuous_moduleSection (w : InfinitePlace K) : Continuous (moduleSection w) :=
  (continuous_infiniteEmbedding w).comp (continuous_posRealToUnits w)
@[simp]
theorem ideleModule_moduleSection (w : InfinitePlace K) (t : {r : ℝ // 0 < r}) :
    ideleModule K (moduleSection w t) = t := by
  refine Subtype.ext ?_
  rw [moduleSection, MonoidHom.comp_apply, ideleModule_infiniteEmbedding]
  exact norm_posRealElem_pow w t.2.le
end ModuleSection
section Splitting
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
instance secondCountableTopology_normOneSubgroup :
    SecondCountableTopology (normOneSubgroup K) :=
  IsEmbedding.subtypeVal.secondCountableTopology
instance locallyCompactSpace_normOneSubgroup : LocallyCompactSpace (normOneSubgroup K) :=
  (isClosed_normOneSubgroup K).isClosedEmbedding_subtypeVal.locallyCompactSpace
theorem mul_inv_moduleSection_mem (w : InfinitePlace K) (x : IdeleGroup K) :
    x * (moduleSection w (ideleModule K x))⁻¹ ∈ normOneSubgroup K := by
  rw [normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, ideleModule_moduleSection,
    mul_inv_cancel]
def normOneSplitting (w : InfinitePlace K) :
    IdeleGroup K ≃ₜ* normOneSubgroup K × {r : ℝ // 0 < r} where
  toFun x := (⟨x * (moduleSection w (ideleModule K x))⁻¹, mul_inv_moduleSection_mem w x⟩,
    ideleModule K x)
  invFun p := (p.1 : IdeleGroup K) * moduleSection w p.2
  left_inv x := by simp
  right_inv p := by
    obtain ⟨⟨u, hu⟩, t⟩ := p
    have hu' : ideleModule K u = 1 := hu
    refine Prod.ext (Subtype.ext ?_) ?_
    · simp [hu']
    · simp [hu']
  map_mul' x y := by
    refine Prod.ext (Subtype.ext ?_) (map_mul _ x y)
    change x * y * (moduleSection w (ideleModule K (x * y)))⁻¹ =
      x * (moduleSection w (ideleModule K x))⁻¹ * (y * (moduleSection w (ideleModule K y))⁻¹)
    simp only [map_mul, mul_inv]
    ac_rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ (continuous_ideleModule)
    exact (continuous_id.mul ((continuous_moduleSection w).comp continuous_ideleModule).inv)
      |>.subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_moduleSection w).comp continuous_snd)
@[simp]
theorem normOneSplitting_apply_snd (w : InfinitePlace K) (x : IdeleGroup K) :
    (normOneSplitting w x).2 = ideleModule K x :=
  rfl
@[simp]
theorem normOneSplitting_symm_apply (w : InfinitePlace K)
    (p : normOneSubgroup K × {r : ℝ // 0 < r}) :
    (normOneSplitting w).symm p = (p.1 : IdeleGroup K) * moduleSection w p.2 :=
  rfl
end Splitting
section ProdHaar
variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] [LocallyCompactSpace H] [SecondCountableTopology H]
theorem map_fst_restrict_eq_smul_haar (lam : Measure (G × H)) [lam.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] {S : Set H} (hν : ν S = 1) :
    Measure.map Prod.fst (lam.restrict (Set.univ ×ˢ S)) =
      lam.haarScalarFactor ((Measure.haar : Measure G).prod ν) • (Measure.haar : Measure G) := by
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul lam ((Measure.haar : Measure G).prod ν)]
  rw [Measure.restrict_smul, Measure.map_smul, ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.map_fst_prod, Measure.restrict_apply_univ, hν, one_smul]
theorem isHaarMeasure_map_fst_restrict (lam : Measure (G × H)) [lam.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] {S : Set H} (hν : ν S = 1) :
    (Measure.map Prod.fst (lam.restrict (Set.univ ×ˢ S))).IsHaarMeasure := by
  rw [map_fst_restrict_eq_smul_haar lam ν hν]
  exact Measure.IsHaarMeasure.nnreal_smul _
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
end ProdHaar
section NormOneMeasure
open IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
def posRealUnitInterval : Set {r : ℝ // 0 < r} := Subtype.val ⁻¹' Set.Icc 1 (exp 1)
theorem measurableSet_posRealUnitInterval : MeasurableSet posRealUnitInterval :=
  measurable_subtype_coe measurableSet_Icc
theorem posRealMeasure_posRealUnitInterval : posRealMeasure posRealUnitInterval = 1 := by
  rw [posRealMeasure_eq_map_expPos, Measure.map_apply measurable_expPos
    measurableSet_posRealUnitInterval]
  have : expPos ⁻¹' posRealUnitInterval = Set.Icc 0 1 := by
    ext x
    simp only [posRealUnitInterval, Set.mem_preimage, Set.mem_Icc, coe_expPos]
    rw [one_le_exp_iff, exp_le_exp]
  rw [this, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
variable {K}
def normOneMeasureAt (w : InfinitePlace K) : Measure (normOneSubgroup K) :=
  Measure.map Prod.fst
    (((ideleMeasure K).map (normOneSplitting w)).restrict (Set.univ ×ˢ posRealUnitInterval))
instance isHaarMeasure_map_normOneSplitting (w : InfinitePlace K) :
    ((ideleMeasure K).map (normOneSplitting w)).IsHaarMeasure :=
  ContinuousMulEquiv.isHaarMeasure_map _ _
instance isHaarMeasure_normOneMeasureAt (w : InfinitePlace K) :
    (normOneMeasureAt w).IsHaarMeasure :=
  isHaarMeasure_map_fst_restrict _ posRealMeasure posRealMeasure_posRealUnitInterval
end NormOneMeasure
section Independence
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
end Independence
section Canonical
open IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
def normOneMeasure : Measure (normOneSubgroup K) :=
  normOneMeasureAt (Classical.arbitrary (InfinitePlace K))
instance isHaarMeasure_normOneMeasure : (normOneMeasure K).IsHaarMeasure := by
  unfold normOneMeasure
  infer_instance
variable {K}
end Canonical
end
end GroundTheory.Global


