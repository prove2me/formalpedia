-- Prove2me | solution 1 for AddUN.exists_levels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:43:36.576803+00:00
-- url     : https://prove2.me/submissions/334d0db9-b013-4be1-94da-eb9de5446c0f

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA
public import Theorems.Thm_AddUN_inner_subset
public import Theorems.Thm_AddUN_inner_mono
public import Theorems.Thm_AddUN_isOpen_inner
public import Theorems.Thm_AddUN_iUnion_inner
public import Theorems.Thm_AddUN_measurableSet_layer
public import Theorems.Thm_AddUN_determined_layer
public import Theorems.Thm_AddUN_exists_mem_layer
public import Theorems.Thm_MeasureTheory_Determined_compl
public import Theorems.Thm_MeasureTheory_Determined_diff
public import Theorems.Thm_MeasureTheory_flipSet_apply_of_mem
public import Theorems.Thm_MeasureTheory_flipSet_apply_of_notMem
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_length_revPrefix
public import Theorems.Thm_MeasureTheory_measurePreserving_flipSet
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip
attribute [local simp] MeasureTheory.length_revPrefix



set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
variable {U : Set (ℕ → Bool)}
namespace AddUN
theorem _root_.solution {K : Set (ℕ → Bool)} (hK : IsCompact K) (hKpos : cantorMeasure K ≠ 0) :
    ∃ M : ℕ → ℕ, Monotone M ∧ ∀ h : ℕ → ℕ, (∀ k, M k ≤ h k) →
      ∃ Good : Set (ℕ → Bool), MeasurableSet Good ∧ cantorMeasure Good ≠ 0 ∧
        ∀ u ∈ Good, ∀ y : ℕ → Bool, (∀ i, i ∉ range h → y i = u i) → y ∈ K := by
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  -- The part of the complement of `K` outside `inner Kᶜ m` is small for large `m`.
  have htend : Tendsto (fun m ↦ cantorMeasure (Kᶜ \ inner Kᶜ m)) atTop (𝓝 0) := by
    have hlim := tendsto_measure_iInter_atTop (μ := cantorMeasure)
      (s := fun m ↦ Kᶜ \ inner Kᶜ m)
      (fun m ↦ (hU.measurableSet.diff (isOpen_inner m).measurableSet).nullMeasurableSet)
      (fun m n hmn ↦ sdiff_subset_sdiff_right (inner_mono hmn)) ⟨0, measure_ne_top _ _⟩
    have hempty : ⋂ m, Kᶜ \ inner Kᶜ m = ∅ := by
      rw [← sdiff_iUnion, iUnion_inner hU, sdiff_self]
    rwa [hempty, measure_empty] at hlim
  let δ : ℕ → ℝ≥0∞ := fun k ↦ cantorMeasure K / 2 * 2⁻¹ ^ (k + 1) / 2 ^ (k + 1)
  have hδ : ∀ k, 0 < δ k := fun k ↦
    ENNReal.div_pos (mul_ne_zero (ENNReal.div_pos hKpos (by simp)).ne' (by simp)) (by simp)
  obtain ⟨M, hM, hMδ⟩ :=
    extraction_forall_of_eventually fun k ↦ htend.eventually_le_const (hδ k)
  refine ⟨M, hM.monotone, fun h hh ↦ ?_⟩
  classical
  -- The points with a modification on the range of `h` outside `K` are covered by `Cover`.
  let Cover : Set (ℕ → Bool) :=
    ⋃ k, ⋃ s ∈ ((Finset.range k).image h).powerset, flipSet s ⁻¹' layer Kᶜ M k
  have hCm : MeasurableSet Cover :=
    .iUnion fun k ↦ Finset.measurableSet_biUnion _ fun s _ ↦
      (measurePreserving_flipSet s).measurable (measurableSet_layer M k)
  have hk : ∀ k, cantorMeasure
      (⋃ s ∈ ((Finset.range k).image h).powerset, flipSet s ⁻¹' layer Kᶜ M k) ≤
      2 ^ k * cantorMeasure (layer Kᶜ M k) := fun k ↦ by
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hpre : ∀ s : Finset ℕ, cantorMeasure (flipSet s ⁻¹' layer Kᶜ M k) =
        cantorMeasure (layer Kᶜ M k) := fun s ↦
      (measurePreserving_flipSet s).measure_preimage (measurableSet_layer M k).nullMeasurableSet
    simp_rw [hpre]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
    refine mul_le_mul_left ?_ _
    have hcard : ((Finset.range k).image h).card ≤ k :=
      Finset.card_image_le.trans (Finset.card_range k).le
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) hcard
  have hsucc : ∀ k, 2 ^ (k + 1) * cantorMeasure (layer Kᶜ M (k + 1)) ≤
      cantorMeasure K / 2 * 2⁻¹ ^ (k + 1) := fun k ↦
    ENNReal.mul_le_of_le_div' ((measure_mono (sdiff_subset_sdiff_left (inner_subset _))).trans
      (hMδ k))
  have hCover : cantorMeasure Cover ≤ cantorMeasure Kᶜ + cantorMeasure K / 2 := by
    calc cantorMeasure Cover
        ≤ ∑' k, 2 ^ k * cantorMeasure (layer Kᶜ M k) :=
          (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hk)
      _ = 2 ^ 0 * cantorMeasure (layer Kᶜ M 0) +
            ∑' k, 2 ^ (k + 1) * cantorMeasure (layer Kᶜ M (k + 1)) :=
          tsum_eq_zero_add' ENNReal.summable
      _ ≤ cantorMeasure Kᶜ + ∑' k : ℕ, cantorMeasure K / 2 * 2⁻¹ ^ (k + 1) := by
          refine add_le_add ?_ (ENNReal.tsum_le_tsum hsucc)
          rw [pow_zero, one_mul]
          exact measure_mono (inner_subset _)
      _ = cantorMeasure Kᶜ + cantorMeasure K / 2 := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two,
            inv_inv, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
  refine ⟨Coverᶜ, hCm.compl, fun h0 ↦ ?_, fun u hu y hy ↦ by_contra fun hyK ↦ ?_⟩
  · -- The cover has measure less than `1`.
    have h1 : cantorMeasure Cover = 1 := by
      have := measure_add_measure_compl (μ := cantorMeasure) hCm
      rwa [h0, add_zero, measure_univ] at this
    have h2 : cantorMeasure Kᶜ + cantorMeasure K = 1 := by
      rw [add_comm, measure_add_measure_compl hK.isClosed.measurableSet, measure_univ]
    rw [h1, ← h2] at hCover
    exact (ENNReal.half_lt_self hKpos (measure_ne_top _ _)).not_ge
      ((ENNReal.add_le_add_iff_left (measure_ne_top _ _)).1 hCover)
  · -- A modification outside `K` puts `u` in the cover.
    obtain ⟨k, hyk⟩ := exists_mem_layer hU hM (y := y) hyK
    have hagree : ∀ i ∈ (↑(Finset.range (M k)) : Set ℕ),
        y i = flipSet (((Finset.range k).image h).filter fun i ↦ y i ≠ u i) u i := by
      intro i hi
      by_cases hne : y i = u i
      · rw [flipSet_apply_of_notMem (by simp [hne]), hne]
      · have hir : i ∈ range h := by_contra fun hnr ↦ hne (hy i hnr)
        obtain ⟨j, rfl⟩ := hir
        have hjk : j < k := by
          by_contra hjk
          have h1 := (hM.monotone (not_lt.1 hjk)).trans (hh j)
          have h2 := Finset.mem_range.1 (Finset.mem_coe.1 hi)
          omega
        rw [flipSet_apply_of_mem (Finset.mem_filter.2
          ⟨Finset.mem_image.2 ⟨j, Finset.mem_range.2 hjk, rfl⟩, hne⟩)]
        cases hy1 : y (h j) <;> cases hu1 : u (h j) <;> simp_all
    exact hu (mem_iUnion.2 ⟨k, mem_iUnion₂.2 ⟨_, Finset.mem_powerset.2 (Finset.filter_subset _ _),
      determined_layer hM.monotone k hagree hyk⟩⟩)
end AddUN
