-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:50.77239+00:00
-- url     : https://prove2.me/theorems/89ac9e22-60ed-475a-a796-c03e58f4b9ae
-- title:
--   Chart Meas Apply Of Subset
-- statement:
--   Definitions and structural lemmas for Chart Meas Apply Of Subset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ChartMeasApplyOfSubset.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff ENNReal
namespace GlobalTheory.ChartGlue
variable {n : ℕ} {X : Type*} [TopologicalSpace X] {ι : Type*}
def transDet (e e' : OpenPartialHomeomorph X (V n)) (y : X) : ℂ :=
  (fderiv ℂ (e' ∘ e.symm) (e y)).det
theorem isOpen_over (e : OpenPartialHomeomorph X (V n)) {S : Set X} (hS : IsOpen S) :
    IsOpen (e.target ∩ e.symm ⁻¹' S) := e.isOpen_inter_preimage_symm hS
theorem mem_over (e : OpenPartialHomeomorph X (V n)) {S : Set X} {y : X} (hy : y ∈ e.source)
    (hS : y ∈ S) : e y ∈ e.target ∩ e.symm ⁻¹' S :=
  ⟨e.map_source hy, by rwa [mem_preimage, e.left_inv hy]⟩
section Measure
variable [MeasurableSpace X]
def chartMeas (e : OpenPartialHomeomorph X (V n)) (ρ : X → ℝ≥0∞) : Measure X :=
  Measure.map e.symm ((volume.restrict e.target).withDensity (ρ ∘ e.symm))
def glueMeas (e : ι → OpenPartialHomeomorph X (V n)) (ρ : ι → X → ℝ≥0∞) : Measure X :=
  ⨆ i, chartMeas (e i) (ρ i)
variable [BorelSpace X]
theorem chartMeas_apply (e : OpenPartialHomeomorph X (V n)) (ρ : X → ℝ≥0∞) {A : Set X}
    (hA : MeasurableSet A) : chartMeas e ρ A = ∫⁻ v in e '' (e.source ∩ A), ρ (e.symm v) := by
  have h : AEMeasurable e.symm ((volume.restrict e.target).withDensity (ρ ∘ e.symm)) :=
    (e.continuousOn_symm.aemeasurable e.open_target.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [chartMeas, Measure.map_apply_of_aemeasurable h hA, withDensity_apply',
    Measure.restrict_restrict' e.open_target.measurableSet, e.image_source_inter_eq', inter_comm]
  rfl
theorem chartMeas_apply_of_subset (e : OpenPartialHomeomorph X (V n)) (ρ : X → ℝ≥0∞) {A : Set X}
    (hA : MeasurableSet A) (h : A ⊆ e.source) :
    chartMeas e ρ A = ∫⁻ v in e '' A, ρ (e.symm v) := by
  rw [chartMeas_apply e ρ hA, inter_eq_right.2 h]
theorem measurableSet_image (e : OpenPartialHomeomorph X (V n)) {A : Set X}
    (hA : MeasurableSet A) (h : A ⊆ e.source) : MeasurableSet (e '' A) := by
  have hm : Measurable (e.target.restrict e.symm) :=
    (continuousOn_iff_continuous_restrict.1 e.continuousOn_symm).measurable
  have := e.open_target.measurableSet.subtype_image (hm hA)
  rw [← inter_eq_right.2 h, e.image_source_inter_eq']
  convert this using 1
  ext v
  exact ⟨fun hv => ⟨⟨v, hv.1⟩, hv.2, rfl⟩, by rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩⟩
theorem chartMeas_eq (e e' : OpenPartialHomeomorph X (V n)) {ρ ρ' : X → ℝ≥0∞}
    (hd : DifferentiableOn ℂ (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source)) {A : Set X}
    (hA : MeasurableSet A) (h : A ⊆ e.source) (h' : A ⊆ e'.source)
    (hρ : ∀ y ∈ A, ρ y = ENNReal.ofReal (‖transDet e e' y‖ ^ 2) * ρ' y) :
    chartMeas e ρ A = chartMeas e' ρ' A := by
  have hm := measurableSet_image e hA h
  have him : e' '' A = (e' ∘ e.symm) '' (e '' A) := by
    rw [image_image]
    exact image_congr fun y hy => by simp only [Function.comp_apply, e.left_inv (h hy)]
  have hinj : InjOn (e' ∘ e.symm) (e '' A) := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hyz
    simp only [Function.comp_apply, e.left_inv (h hy), e.left_inv (h hz)] at hyz
    rw [e'.injOn (h' hy) (h' hz) hyz]
  have hder : ∀ v ∈ e '' A, HasFDerivWithinAt (e' ∘ e.symm)
      ((fderiv ℂ (e' ∘ e.symm) v).restrictScalars ℝ) (e '' A) v := by
    rintro _ ⟨y, hy, rfl⟩
    exact ((hd.differentiableAt ((isOpen_over e e'.open_source).mem_nhds
      (mem_over e (h hy) (h' hy)))).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [chartMeas_apply_of_subset e ρ hA h, chartMeas_apply_of_subset e' ρ' hA h', him,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hm hder hinj]
  refine setLIntegral_congr_fun hm ?_
  rintro _ ⟨y, hy, rfl⟩
  have hdet : ((fderiv ℂ (e' ∘ e.symm) (e y)).restrictScalars ℝ).det =
      Algebra.norm ℝ (transDet e e' y) :=
    LinearMap.det_restrictScalars (f := (fderiv ℂ (e' ∘ e.symm) (e y) : V n →ₗ[ℂ] V n))
  simp only [Function.comp_apply, e.left_inv (h hy), e'.left_inv (h' hy), hρ y hy, hdet]
  rw [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]
variable [SecondCountableTopology X]
theorem iSup_apply_of_compat (μ : ι → Measure X) (S : ι → Set X) (hS : ∀ i, IsOpen (S i))
    (h0 : ∀ i A, MeasurableSet A → μ i A = μ i (S i ∩ A))
    (hc : ∀ i j A, MeasurableSet A → A ⊆ S i → A ⊆ S j → μ i A = μ j A)
    (i : ι) {A : Set X} (hA : MeasurableSet A) (hAi : A ⊆ S i) : (⨆ j, μ j) A = μ i A := by
  obtain ⟨T, hT, hTS⟩ := TopologicalSpace.isOpen_iUnion_countable S hS
  obtain ⟨f, hf⟩ := (hT.insert i).exists_eq_range (insert_nonempty _ _)
  have hcov (j : ι) : S j ⊆ ⋃ m, disjointed (S ∘ f) m := by
    rw [iUnion_disjointed]
    intro y hy
    obtain ⟨l, hl, hy⟩ := mem_iUnion₂.1 (hTS.ge (mem_iUnion.2 ⟨j, hy⟩))
    obtain ⟨m, rfl⟩ := hf.le (mem_insert_of_mem _ hl)
    exact mem_iUnion.2 ⟨m, hy⟩
  have hD := MeasurableSet.disjointed (f := S ∘ f) fun m => (hS _).measurableSet
  let ν : Measure X := Measure.sum fun m => (μ (f m)).restrict (disjointed (S ∘ f) m)
  have hν (j : ι) (B : Set X) (hB : MeasurableSet B) (hBj : B ⊆ S j) : ν B = μ j B := by
    rw [Measure.sum_apply _ hB]
    conv_rhs => rw [← inter_eq_left.2 (hBj.trans (hcov j)), inter_iUnion,
      measure_iUnion ((disjoint_disjointed _).mono fun _ _ h =>
        h.mono inter_subset_right inter_subset_right) fun m => hB.inter (hD m)]
    refine tsum_congr fun m => ?_
    rw [Measure.restrict_apply hB]
    exact hc _ _ _ (hB.inter (hD m)) (inter_subset_right.trans (disjointed_subset (S ∘ f) m))
      (inter_subset_left.trans hBj)
  refine le_antisymm ?_ (Measure.le_iff'.1 (le_iSup μ i) A)
  rw [← hν i A hA hAi]
  refine Measure.le_iff'.1 (iSup_le fun j => Measure.le_iff.2 fun B hB => ?_) A
  rw [h0 j B hB, ← hν j _ ((hS j).measurableSet.inter hB) inter_subset_left]
  exact measure_mono inter_subset_right
theorem glueMeas_apply (e : ι → OpenPartialHomeomorph X (V n)) (ρ : ι → X → ℝ≥0∞)
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (i : ι) {A : Set X} (hA : MeasurableSet A) (h : A ⊆ (e i).source) :
    glueMeas e ρ A = chartMeas (e i) (ρ i) A :=
  iSup_apply_of_compat _ (fun i => (e i).source) (fun i => (e i).open_source)
    (fun i A hA => by
      rw [chartMeas_apply _ _ hA, chartMeas_apply_of_subset _ _
        ((e i).open_source.measurableSet.inter hA) inter_subset_left])
    (fun i j _ hA h h' => chartMeas_eq _ _ (hd i j) hA h h' fun y hy => hρ i j y (h hy) (h' hy))
    i hA h
end Measure
theorem differentiableOn_prod {κ : Type*} [Fintype κ] {f : κ → V n → ℂ} {U : Set (V n)}
    (h : ∀ a, DifferentiableOn ℂ (f a) U) : DifferentiableOn ℂ (fun v => ∏ a, f a v) U := by
  have := Finset.prod_induction (s := Finset.univ) f (fun g => DifferentiableOn ℂ g U)
    (fun _ _ => DifferentiableOn.mul) (differentiableOn_const 1) fun a _ => h a
  exact this.congr fun v _ => (Finset.prod_apply _ _ _).symm
theorem log_normSq_prod_zpow {κ : Type*} [Fintype κ] (g : κ → ℂ) (hg : ∀ a, g a ≠ 0) (m : κ → ℤ) :
    Real.log (‖∏ a, g a ^ m a‖ ^ 2) = ∑ a, m a * Real.log (‖g a‖ ^ 2) := by
  rw [norm_prod, ← Finset.prod_pow, Real.log_prod fun a _ =>
    pow_ne_zero _ (norm_ne_zero_iff.2 (zpow_ne_zero _ (hg a)))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [norm_zpow, Real.log_pow, Real.log_pow, Real.log_zpow]
  ring
variable [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
def freeAtlas (e : ι → OpenPartialHomeomorph X (V n)) (cover : ∀ y, ∃ i, y ∈ (e i).source)
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    {κ : Type*} [Fintype κ] [DecidableEq κ] (g : κ → ι → ι → X → ℂ)
    (holo_g : ∀ a i j, DifferentiableOn ℂ (g a i j ∘ (e i).symm) (ovl e i j))
    (g_ne : ∀ a i j y, y ∈ (e i).source → y ∈ (e j).source → g a i j y ≠ 0)
    (g_cocycle : ∀ a i j k y, y ∈ (e i).source → y ∈ (e j).source → y ∈ (e k).source →
      g a i k y = g a i j y * g a j k y)
    (ph : κ → ι → X → ℝ) (smooth_ph : ∀ a i, ContDiffOn ℝ ∞ (ph a i ∘ (e i).symm) (e i).target)
    (ph_trans : ∀ a i j y, y ∈ (e i).source → y ∈ (e j).source →
      ph a j y = ph a i y - Real.log (‖g a i j y‖ ^ 2))
    (a₀ : κ) (g_kap : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      g a₀ i j y = transDet (e i) (e j) y) : WeightedAtlas n X ι (κ → ℤ) where
  chart := e
  pick y := (cover y).choose
  mem_pick y := (cover y).choose_spec
  holo_trans := hd
  g m i j y := ∏ a, g a i j y ^ m a
  holo_g m i j := differentiableOn_prod (f := fun a v => g a i j ((e i).symm v) ^ m a)
    fun a => (holo_g a i j).zpow (Or.inl fun v hv => g_ne a i j _ ((e i).map_target hv.1) hv.2)
  g_ne m i j y hi hj := Finset.prod_ne_zero_iff.2 fun a _ => zpow_ne_zero _ (g_ne a i j y hi hj)
  g_cocycle m i j k y hi hj hk := by
    simp only [fun a => g_cocycle a i j k y hi hj hk, mul_zpow, Finset.prod_mul_distrib]
  g_add m m' i j y hi hj := by
    simp only [Pi.add_apply, fun a => zpow_add₀ (g_ne a i j y hi hj), Finset.prod_mul_distrib]
  ph m i y := ∑ a, m a * ph a i y
  smooth_ph m i := ContDiffOn.sum (f := fun a v => m a * ph a i ((e i).symm v))
    fun a _ => contDiffOn_const.mul (smooth_ph a i)
  ph_add m m' i y _ := by simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  ph_trans m i j y hi hj := by
    rw [log_normSq_prod_zpow _ fun a => g_ne a i j y hi hj, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [ph_trans a i j y hi hj, mul_sub]
  kap := Pi.single a₀ 1
  g_kap i j y hi hj := by
    rw [Fintype.prod_eq_single a₀ fun a ha => by rw [Pi.single_eq_of_ne ha, zpow_zero],
      Pi.single_eq_same, zpow_one]
    exact g_kap i j y hi hj
  mu := glueMeas e fun i y => ENNReal.ofReal (Real.exp (ph a₀ i y))
  mu_chart i A hA h := by
    rw [glueMeas_apply e _ hd _ i hA h, chartMeas_apply_of_subset _ _ hA h]
    · simp [Pi.single_apply]
    · intro i j y hi hj
      rw [← g_kap i j y hi hj, ph_trans a₀ i j y hi hj, ← ENNReal.ofReal_mul (sq_nonneg _),
        Real.exp_sub, Real.exp_log (pow_pos (norm_pos_iff.2 (g_ne a₀ i j y hi hj)) 2),
        mul_div_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.2 (g_ne a₀ i j y hi hj)))]
end GlobalTheory.ChartGlue


