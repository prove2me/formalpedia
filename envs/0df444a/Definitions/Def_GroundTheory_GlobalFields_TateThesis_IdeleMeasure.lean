-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
-- name    : GroundTheory_GlobalFields_TateThesis_IdeleMeasure
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:30:31.850971+00:00
-- url     : https://prove2.me/theorems/18d1442b-6e72-489d-b681-3576c41864cf
-- title:
--   Idele Measure
-- statement:
--   Definitions and structural lemmas for Idele Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasure.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_toFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_standardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_Global_t2Space_adeleRing
import Theorems.Thm_GroundTheory_Global_t2Space_finiteAdeleRing
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
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing RestrictedProduct ENNReal NNReal
namespace GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
instance countable_ringOfIntegers : Countable (𝓞 K) :=
  (RingOfIntegers.basis K).repr.toEquiv.injective.countable
instance countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 K)) := by
  classical
  let f : HeightOneSpectrum (𝓞 K) → Finset (𝓞 K) := fun v ↦
    (IsNoetherian.noetherian v.asIdeal).choose
  refine Function.Injective.countable (f := f) fun v w h ↦ ?_
  have hv := (IsNoetherian.noetherian v.asIdeal).choose_spec
  have hw := (IsNoetherian.noetherian w.asIdeal).choose_spec
  ext1
  rw [← hv, ← hw]
  exact congrArg (fun s : Finset (𝓞 K) ↦ Submodule.span (𝓞 K) (s : Set (𝓞 K))) h
namespace IdeleGroup
def ordFinsupp (x : IdeleGroup K) : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v ↦ ord v x) (eventually_ord_eq_zero x)
instance countable_quotient_standardOpenSubgroup :
    Countable (IdeleGroup K ⧸ standardOpenSubgroup K) := by
  let g : IdeleGroup K ⧸ standardOpenSubgroup K → (HeightOneSpectrum (𝓞 K) →₀ ℤ) :=
    Quotient.lift (ordFinsupp K) fun x y hxy ↦ by
      have h := (QuotientGroup.leftRel_apply.1 hxy)
      rw [mem_standardOpenSubgroup_iff_ord] at h
      ext v
      have := h v
      rw [ord_mul, ord_inv] at this
      change ord v x = ord v y
      omega
  refine Function.Injective.countable (f := g) fun p q hpq ↦ ?_
  induction p using QuotientGroup.induction_on with | H x => ?_
  induction q using QuotientGroup.induction_on with | H y => ?_
  refine QuotientGroup.eq.2 ((mem_standardOpenSubgroup_iff_ord).2 fun v ↦ ?_)
  have := congrArg (fun f ↦ f v) hpq
  simp only [g, Quotient.lift_mk, ordFinsupp] at this
  change ord v x = ord v y at this
  rw [ord_mul, ord_inv]
  omega
end IdeleGroup
section SecondCountable
instance secondCountableTopology_units {M : Type*} [Monoid M]
    [TopologicalSpace M] [SecondCountableTopology M] : SecondCountableTopology Mˣ :=
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology
instance secondCountableTopology_units_infiniteAdeleRing :
    SecondCountableTopology (InfiniteAdeleRing K)ˣ :=
  secondCountableTopology_units
instance compactSpace_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    CompactSpace (v.adicCompletionIntegers K) :=
  isCompact_iff_compactSpace.1 (isCompact_adicCompletionIntegers v)
instance secondCountableTopology_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (v.adicCompletionIntegers K) :=
  EMetric.secondCountable_of_sigmaCompact _
instance secondCountableTopology_units_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (v.adicCompletionIntegers K)ˣ :=
  secondCountableTopology_units
namespace IdeleGroup
instance secondCountableTopology_standardOpenSubgroup :
    SecondCountableTopology (standardOpenSubgroup K) :=
  (standardOpenSubgroupEquiv K).toHomeomorph.isEmbedding.secondCountableTopology
instance secondCountableTopology : SecondCountableTopology (IdeleGroup K) := by
  let U : IdeleGroup K ⧸ standardOpenSubgroup K → Set (IdeleGroup K) :=
    fun q ↦ Set.range ((q.out * ·) ∘ ((↑) : standardOpenSubgroup K → IdeleGroup K))
  have hU : ∀ q, SecondCountableTopology (U q) := fun q ↦ by
    have he : IsEmbedding ((q.out * ·) ∘ ((↑) : standardOpenSubgroup K → IdeleGroup K)) :=
      (Homeomorph.mulLeft q.out).isEmbedding.comp IsEmbedding.subtypeVal
    have h := he.toHomeomorph.symm.isEmbedding.secondCountableTopology
    exact h
  refine secondCountableTopology_of_countable_cover (U := U) (fun q ↦ ?_) ?_
  · simp only [U, Set.range_comp]
    exact (Homeomorph.mulLeft q.out).isOpenMap _
      (by rw [Subtype.range_val]; exact isOpen_standardOpenSubgroup K)
  · refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨(x : IdeleGroup K ⧸ _), ?_⟩
    refine ⟨⟨(Quotient.out (x : IdeleGroup K ⧸ standardOpenSubgroup K))⁻¹ * x, ?_⟩, by simp⟩
    exact QuotientGroup.leftRel_apply.1 (Quotient.exact (Quotient.out_eq _))
instance secondCountableTopology_finite :
    SecondCountableTopology (FiniteAdeleRing (𝓞 K) K)ˣ := by
  have he : IsEmbedding (fun x : (FiniteAdeleRing (𝓞 K) K)ˣ ↦ (prodEquiv K).symm (1, x)) :=
    (prodEquiv K).symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkRight 1)
  exact he.secondCountableTopology
end IdeleGroup
end SecondCountable
section Borel
theorem isSigmaCompact_of_isOpen {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [LocallyCompactSpace X] {U : Set X} (hU : IsOpen U) :
    IsSigmaCompact U := by
  have h : ∀ x ∈ U, ∃ t ∈ 𝓝 x, t ⊆ U ∧ IsCompact t := fun x hx ↦
    local_compact_nhds (hU.mem_nhds hx)
  choose! t ht using h
  obtain ⟨T, hTU, hTc, hT⟩ := isOpen_biUnion_countable U (fun x ↦ interior (t x))
    fun _ _ ↦ isOpen_interior
  have hcov : ⋃ x ∈ T, t x = U := by
    refine subset_antisymm (Set.iUnion₂_subset fun x hx ↦ (ht x (hTU hx)).2.1) fun y hy ↦ ?_
    have hy' : y ∈ ⋃ x ∈ U, interior (t x) :=
      Set.mem_biUnion hy (mem_interior_iff_mem_nhds.2 (ht y hy).1)
    rw [← hT] at hy'
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 hy'
    exact Set.mem_biUnion hx (interior_subset hyx)
  rw [← hcov]
  exact isSigmaCompact_biUnion hTc fun x hx ↦ (ht x (hTU hx)).2.2.isSigmaCompact
theorem comap_eq_borel_of_continuous_injective {X Y : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y] {f : X → Y}
    (hf : Continuous f) (hinj : Function.Injective f) :
    MeasurableSpace.comap f ‹MeasurableSpace Y› = borel X := by
  refine le_antisymm ?_ ?_
  · have h := hf.borel_measurable
    rw [← BorelSpace.measurable_eq (α := Y)] at h
    exact h.comap_le
  · refine MeasurableSpace.generateFrom_le fun U hU ↦ ?_
    obtain ⟨k, hk, hkU⟩ := isSigmaCompact_of_isOpen hU
    have : U = f ⁻¹' ⋃ n, f '' k n := by
      rw [Set.preimage_iUnion, ← hkU]
      exact Set.iUnion_congr fun n ↦ (hinj.preimage_image _).symm
    rw [this]
    exact ⟨_, MeasurableSet.iUnion fun n ↦ ((hk n).image hf).isClosed.measurableSet, rfl⟩
theorem borelSpace_units {M : Type*} [Monoid M] [TopologicalSpace M]
    [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology Mˣ]
    [LocallyCompactSpace Mˣ] : BorelSpace Mˣ :=
  ⟨comap_eq_borel_of_continuous_injective Units.continuous_val Units.val_injective⟩
instance borelSpace_units_infiniteAdeleRing : BorelSpace (InfiniteAdeleRing K)ˣ :=
  borelSpace_units
instance borelSpace_units_finiteAdeleRing : BorelSpace (FiniteAdeleRing (𝓞 K) K)ˣ :=
  haveI : T2Space (FiniteAdeleRing (𝓞 K) K) := t2Space_finiteAdeleRing K
  borelSpace_units
instance IdeleGroup.borelSpace : BorelSpace (IdeleGroup K) :=
  haveI : T2Space 𝔸[K] := t2Space_adeleRing K
  borelSpace_units
end Borel
section UnitsMeasure
variable {F : Type*} [NormedField F] [LocallyCompactSpace F]
  [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
instance locallyCompactSpace_units_of_locallyCompact :
    LocallyCompactSpace Fˣ :=
  Units.isOpenEmbedding_val.locallyCompactSpace
instance borelSpace_units_of_locallyCompact : BorelSpace Fˣ :=
  borelSpace_units
theorem measurableEmbedding_units_val :
    MeasurableEmbedding (Units.val : Fˣ → F) :=
  Units.isOpenEmbedding_val.measurableEmbedding
def unitsMeasure (μ : Measure F) (m : ℕ) : Measure Fˣ :=
  Measure.comap Units.val (μ.withDensity fun x ↦ ENNReal.ofReal (‖x‖ ^ m)⁻¹)
variable (μ : Measure F) (m : ℕ)
theorem unitsMeasure_apply {s : Set Fˣ} (hs : MeasurableSet s) :
    unitsMeasure μ m s = ∫⁻ x in Units.val '' s, ENNReal.ofReal (‖x‖ ^ m)⁻¹ ∂μ := by
  rw [unitsMeasure, measurableEmbedding_units_val.comap_apply, withDensity_apply _
    (measurableEmbedding_units_val.measurableSet_image' hs)]
omit [LocallyCompactSpace F] [SecondCountableTopology F] in
theorem measurable_density_unitsMeasure :
    Measurable fun x : F ↦ ENNReal.ofReal (‖x‖ ^ m)⁻¹ :=
  ENNReal.measurable_ofReal.comp ((measurable_norm.pow_const m).inv)
theorem isMulLeftInvariant_unitsMeasure
    (hμ : ∀ a : F, a ≠ 0 → Measure.map (a * ·) μ = ENNReal.ofReal (‖a‖ ^ m)⁻¹ • μ) :
    (unitsMeasure μ m).IsMulLeftInvariant := by
  refine ⟨fun g ↦ Measure.ext fun s hs ↦ ?_⟩
  have hmul : Measurable (fun u : Fˣ ↦ g * u) := measurable_const_mul g
  rw [Measure.map_apply hmul hs, unitsMeasure_apply _ _ (hmul hs), unitsMeasure_apply _ _ hs]
  have himg : Units.val '' ((fun u : Fˣ ↦ g * u) ⁻¹' s) =
      (fun x : F ↦ (g : F) * x) ⁻¹' (Units.val '' s) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨g * u, hu, rfl⟩
    · rintro ⟨v, hv, hvx⟩
      refine ⟨g⁻¹ * v, by simpa using hv, ?_⟩
      simp only [Units.val_mul, hvx, Units.inv_mul_cancel_left]
  rw [himg]
  have hT : MeasurableSet (Units.val '' s) :=
    measurableEmbedding_units_val.measurableSet_image' hs
  have hf : Measurable (fun x : F ↦ (g : F) * x) := measurable_const_mul _
  have hρ := measurable_density_unitsMeasure (F := F) m
  have key : ∫⁻ x in (fun x : F ↦ (g : F) * x) ⁻¹' (Units.val '' s),
      ENNReal.ofReal (‖x‖ ^ m)⁻¹ ∂μ = ∫⁻ x in (fun x : F ↦ (g : F) * x) ⁻¹' (Units.val '' s),
      (fun y : F ↦ ENNReal.ofReal (‖((g⁻¹ : Fˣ) : F) * y‖ ^ m)⁻¹) ((g : F) * x) ∂μ :=
    setLIntegral_congr_fun (hf hT) fun x _ ↦ by
      simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [key, ← setLIntegral_map (g := fun x : F ↦ (g : F) * x)
    (f := fun y : F ↦ ENNReal.ofReal (‖((g⁻¹ : Fˣ) : F) * y‖ ^ m)⁻¹) hT
    (hρ.comp (measurable_const_mul _)) hf, hμ _ g.ne_zero,
    Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun hT fun y _ ↦ ?_
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg (norm_nonneg _) _))]
  congr 1
  have hg : ‖(g : F)‖ ≠ 0 := norm_ne_zero_iff.2 g.ne_zero
  rw [norm_mul, mul_pow, mul_inv, ← mul_assoc, ← mul_inv, Units.val_inv_eq_inv_val, norm_inv,
    inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hg), inv_one, one_mul]
theorem isFiniteMeasureOnCompacts_unitsMeasure
    [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasureOnCompacts (unitsMeasure μ m) := by
  refine ⟨fun C hC ↦ ?_⟩
  rw [unitsMeasure_apply _ _ hC.isClosed.measurableSet]
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn (f := fun u : Fˣ ↦ (‖(u : F)‖ ^ m)⁻¹)
    ((continuous_norm.comp Units.continuous_val).pow m |>.inv₀ fun u ↦
      pow_ne_zero _ (norm_ne_zero_iff.2 u.ne_zero)).continuousOn
  calc ∫⁻ x in Units.val '' C, ENNReal.ofReal (‖x‖ ^ m)⁻¹ ∂μ
      ≤ ∫⁻ _ in Units.val '' C, ENNReal.ofReal B ∂μ := by
        refine setLIntegral_mono measurable_const fun x hx ↦ ?_
        obtain ⟨u, hu, rfl⟩ := hx
        exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
          ((Real.norm_eq_abs _).symm.le.trans (hB u hu)))
    _ = ENNReal.ofReal B * μ (Units.val '' C) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((hC.image Units.continuous_val).measure_lt_top)
theorem isOpenPosMeasure_unitsMeasure [μ.IsOpenPosMeasure] :
    (unitsMeasure μ m).IsOpenPosMeasure := by
  refine ⟨fun U hU hne ↦ ?_⟩
  rw [unitsMeasure, measurableEmbedding_units_val.comap_apply, ne_eq,
    withDensity_apply_eq_zero' (measurable_density_unitsMeasure m).aemeasurable]
  have h : {x : F | ENNReal.ofReal (‖x‖ ^ m)⁻¹ ≠ 0} ∩ Units.val '' U = Units.val '' U := by
    refine Set.inter_eq_right.2 ?_
    rintro _ ⟨u, -, rfl⟩
    simp [pow_pos (norm_pos_iff.2 u.ne_zero) m]
  rw [h]
  exact (Units.isOpenEmbedding_val.isOpenMap U hU).measure_ne_zero μ (hne.image _)
theorem isHaarMeasure_unitsMeasure [μ.IsAddHaarMeasure]
    (hμ : ∀ a : F, a ≠ 0 → Measure.map (a * ·) μ = ENNReal.ofReal (‖a‖ ^ m)⁻¹ • μ) :
    (unitsMeasure μ m).IsHaarMeasure :=
  haveI := isMulLeftInvariant_unitsMeasure μ m hμ
  haveI := isFiniteMeasureOnCompacts_unitsMeasure μ m
  haveI := isOpenPosMeasure_unitsMeasure μ m
  { }
end UnitsMeasure
section InfinitePlaces
open InfinitePlace InfinitePlace.Completion
variable {K}
def infinitePlaceMeasure (w : InfinitePlace K) : Measure w.Completion :=
  open Classical in
  if hw : w.IsReal then Measure.map (isometryEquivRealOfIsReal hw).symm volume
  else Measure.map (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm
    ((2 : ℝ≥0∞) • volume)
omit [NumberField K] in
theorem infinitePlaceMeasure_of_isReal {w : InfinitePlace K} (hw : w.IsReal) :
    infinitePlaceMeasure w = Measure.map (isometryEquivRealOfIsReal hw).symm volume :=
  dif_pos hw
omit [NumberField K] in
theorem infinitePlaceMeasure_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) :
    infinitePlaceMeasure w =
      Measure.map (isometryEquivComplexOfIsComplex hw).symm ((2 : ℝ≥0∞) • volume) := by
  rw [infinitePlaceMeasure, dif_neg (not_isReal_iff_isComplex.2 hw)]
instance isAddHaarMeasure_infinitePlaceMeasure (w : InfinitePlace K) :
    (infinitePlaceMeasure w).IsAddHaarMeasure := by
  by_cases hw : w.IsReal
  · rw [infinitePlaceMeasure_of_isReal hw]
    exact AddEquiv.isAddHaarMeasure_map _ (ringEquivRealOfIsReal hw).symm.toAddEquiv
      (isometryEquivRealOfIsReal hw).symm.continuous (isometryEquivRealOfIsReal hw).continuous
  · have hc := not_isReal_iff_isComplex.1 hw
    rw [infinitePlaceMeasure_of_isComplex hc]
    have : ((2 : ℝ≥0∞) • (volume : Measure ℂ)).IsAddHaarMeasure :=
      Measure.IsAddHaarMeasure.smul _ (by norm_num) (by simp)
    exact AddEquiv.isAddHaarMeasure_map _ (ringEquivComplexOfIsComplex hc).symm.toAddEquiv
      (isometryEquivComplexOfIsComplex hc).symm.continuous
      (isometryEquivComplexOfIsComplex hc).continuous
theorem map_mul_left_volume_complex {z : ℂ} (hz : z ≠ 0) :
    Measure.map (z * ·) (volume : Measure ℂ) = ENNReal.ofReal (‖z‖ ^ 2)⁻¹ • volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ z) = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := LinearMap.mulLeft ℝ z) (by rw [hdet]; positivity)
  rw [hdet, abs_of_nonneg (by positivity)] at h
  exact h
omit [NumberField K] in

theorem map_mul_left_infinitePlaceMeasure (w : InfinitePlace K) {a : w.Completion} (ha : a ≠ 0) :
    Measure.map (a * ·) (infinitePlaceMeasure w) =
      ENNReal.ofReal (‖a‖ ^ w.mult)⁻¹ • infinitePlaceMeasure w := by
  by_cases hw : w.IsReal
  · rw [infinitePlaceMeasure_of_isReal hw]
    set e := isometryEquivRealOfIsReal hw
    have he : ∀ y, a * e.symm y = e.symm (e a * y) := fun y ↦ by
      apply e.injective
      simp only [e, IsometryEquiv.apply_symm_apply]
      change ringEquivRealOfIsReal hw (a * (ringEquivRealOfIsReal hw).symm y) = _
      rw [map_mul, RingEquiv.apply_symm_apply]
      rfl
    have hea : e a ≠ 0 := by
      change ringEquivRealOfIsReal hw a ≠ 0
      exact (map_ne_zero_iff _ (ringEquivRealOfIsReal hw).injective).2 ha
    rw [Measure.map_map (measurable_const_mul a) e.symm.continuous.measurable]
    have : (a * ·) ∘ e.symm = e.symm ∘ (e a * ·) := funext he
    rw [this, ← Measure.map_map e.symm.continuous.measurable (measurable_const_mul _),
      Real.map_volume_mul_left hea, Measure.map_smul]
    congr 2
    have h0 : e 0 = 0 := map_zero (ringEquivRealOfIsReal hw)
    rw [abs_inv, ← Real.norm_eq_abs, e.isometry.norm_map_of_map_zero h0, mult, if_pos hw,
      pow_one]
  · have hc := not_isReal_iff_isComplex.1 hw
    rw [infinitePlaceMeasure_of_isComplex hc]
    set e := isometryEquivComplexOfIsComplex hc
    have he : ∀ y, a * e.symm y = e.symm (e a * y) := fun y ↦ by
      apply e.injective
      simp only [e, IsometryEquiv.apply_symm_apply]
      change ringEquivComplexOfIsComplex hc (a * (ringEquivComplexOfIsComplex hc).symm y) = _
      rw [map_mul, RingEquiv.apply_symm_apply]
      rfl
    have hea : e a ≠ 0 := by
      change ringEquivComplexOfIsComplex hc a ≠ 0
      exact (map_ne_zero_iff _ (ringEquivComplexOfIsComplex hc).injective).2 ha
    rw [Measure.map_map (measurable_const_mul a) e.symm.continuous.measurable]
    have : (a * ·) ∘ e.symm = e.symm ∘ (e a * ·) := funext he
    rw [this, ← Measure.map_map e.symm.continuous.measurable (measurable_const_mul _),
      Measure.map_smul, map_mul_left_volume_complex hea, smul_comm, Measure.map_smul]
    congr 2
    have h0 : e 0 = 0 := map_zero (ringEquivComplexOfIsComplex hc)
    rw [e.isometry.norm_map_of_map_zero h0, mult, if_neg hw]
def infinitePlaceUnitsMeasure (w : InfinitePlace K) : Measure (w.Completion)ˣ :=
  unitsMeasure (infinitePlaceMeasure w) w.mult
instance isHaarMeasure_infinitePlaceUnitsMeasure (w : InfinitePlace K) :
    (infinitePlaceUnitsMeasure w).IsHaarMeasure :=
  isHaarMeasure_unitsMeasure _ _ fun _ ha ↦ map_mul_left_infinitePlaceMeasure w ha
end InfinitePlaces
section IdeleMeasure
open InfinitePlace
def infiniteUnitsEquiv :
    (InfiniteAdeleRing K)ˣ ≃ₜ* Π w : InfinitePlace K, (w.Completion)ˣ :=
  ContinuousMulEquiv.piUnits
def infiniteIdeleMeasure : Measure (InfiniteAdeleRing K)ˣ :=
  Measure.map (infiniteUnitsEquiv K).symm
    (Measure.pi fun w : InfinitePlace K ↦ infinitePlaceUnitsMeasure w)
instance isHaarMeasure_infiniteIdeleMeasure : (infiniteIdeleMeasure K).IsHaarMeasure := by
  unfold infiniteIdeleMeasure
  have : (Measure.pi fun w : InfinitePlace K ↦ infinitePlaceUnitsMeasure w).IsHaarMeasure :=
    Measure.pi.isHaarMeasure _
  infer_instance
def finiteIntegralUnits : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (IdeleGroup.standardOpenSubgroup K).comap
    ((IdeleGroup.prodEquiv K).symm.toMulEquiv.toMonoidHom.comp (MonoidHom.inr _ _))
theorem isOpen_finiteIntegralUnits :
    IsOpen (finiteIntegralUnits K : Set (FiniteAdeleRing (𝓞 K) K)ˣ) :=
  (IdeleGroup.isOpen_standardOpenSubgroup K).preimage
    ((IdeleGroup.prodEquiv K).symm.continuous.comp (Continuous.prodMk_right 1))
theorem isCompact_finiteIntegralUnits :
    IsCompact (finiteIntegralUnits K : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  let φ : (Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) →
      (FiniteAdeleRing (𝓞 K) K)ˣ := fun p ↦
    IdeleGroup.toFinite K (IdeleGroup.ofIntegerUnits 1 p)
  have hφ : Continuous φ := (IdeleGroup.continuous_toFinite K).comp
    (IdeleGroup.continuous_ofIntegerUnits.comp (Continuous.prodMk_right 1))
  have h : (finiteIntegralUnits K : Set (FiniteAdeleRing (𝓞 K) K)ˣ) = Set.range φ := by
    ext x
    constructor
    · intro hx
      refine ⟨fun v ↦ IdeleGroup.localIntegerUnit v ⟨_, hx⟩, Units.ext ?_⟩
      rfl
    · rintro ⟨p, rfl⟩
      change (IdeleGroup.prodEquiv K).symm (1, φ p) ∈ IdeleGroup.standardOpenSubgroup K
      convert IdeleGroup.ofIntegerUnits_mem 1 p using 1
      exact Units.ext rfl
  rw [h]
  exact isCompact_range hφ
def finiteIntegralUnitsCompacts : PositiveCompacts (FiniteAdeleRing (𝓞 K) K)ˣ where
  carrier := finiteIntegralUnits K
  isCompact' := isCompact_finiteIntegralUnits K
  interior_nonempty' := by
    rw [(isOpen_finiteIntegralUnits K).interior_eq]
    exact ⟨1, one_mem _⟩
def finiteIdeleMeasure : Measure (FiniteAdeleRing (𝓞 K) K)ˣ :=
  Measure.haarMeasure (finiteIntegralUnitsCompacts K)
instance isHaarMeasure_finiteIdeleMeasure : (finiteIdeleMeasure K).IsHaarMeasure := by
  unfold finiteIdeleMeasure
  infer_instance
def ideleMeasure : Measure (IdeleGroup K) :=
  Measure.map (IdeleGroup.prodEquiv K).symm ((infiniteIdeleMeasure K).prod (finiteIdeleMeasure K))
instance isHaarMeasure_ideleMeasure : (ideleMeasure K).IsHaarMeasure := by
  unfold ideleMeasure
  infer_instance
end IdeleMeasure
section Preserving
end Preserving
end
end GroundTheory.Global


