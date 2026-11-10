-- Prove2me | solution 1 for AIMInventoryAudit.UnknownBound.theorem_7_full
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T15:34:28.774334+00:00
-- url     : https://prove2.me/submissions/d9f2c237-9766-4fc7-993e-5b3f6565a4a4

import Mathlib
import Definitions.Def_AIMInventoryAudit_UnknownBound_Costs

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace AIMTh7

open AIMInventory.UnknownBound AIMInventoryAudit.UnknownBound

/-! Part A: deterministic facts. -/

theorem loss_subgrad (h b y z : ℝ) (d : ℝ≥0) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    loss h b y d - loss h b z d ≤ signal h b y d * (y - z) := by
  unfold loss signal
  have hz1 : z - (d:ℝ) ≤ max (z - d) 0 := le_max_left _ _
  have hz2 : (d:ℝ) - z ≤ max ((d:ℝ) - z) 0 := le_max_left _ _
  have hz3 : 0 ≤ max (z - (d:ℝ)) 0 := le_max_right _ _
  have hz4 : 0 ≤ max ((d:ℝ) - z) 0 := le_max_right _ _
  have m1 := mul_le_mul_of_nonneg_left hz1 hh
  have m2 := mul_le_mul_of_nonneg_left hz2 hb
  have m3 := mul_nonneg hh hz3
  have m4 := mul_nonneg hb hz4
  split_ifs with hd
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ y - d), max_eq_right (by linarith : (d:ℝ) - y ≤ 0)]
    linarith
  · push_neg at hd
    rw [max_eq_right (by linarith : y - (d:ℝ) ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ (d:ℝ) - y)]
    linarith

theorem signal_abs (h b y : ℝ) (d : ℝ≥0) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    |signal h b y d| ≤ max b h := by
  unfold signal
  split_ifs
  · rw [abs_of_nonneg hh]; exact le_max_right _ _
  · rw [abs_neg, abs_of_nonneg hb]; exact le_max_left _ _

theorem loss_lip (h b y z : ℝ) (d : ℝ≥0) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    |loss h b y d - loss h b z d| ≤ max b h * |y - z| := by
  have a1 := loss_subgrad h b y z d hh hb
  have a2 := loss_subgrad h b z y d hh hb
  have s1 : signal h b y d * (y - z) ≤ max b h * |y - z| := by
    calc _ ≤ |signal h b y d * (y - z)| := le_abs_self _
      _ = |signal h b y d| * |y - z| := abs_mul _ _
      _ ≤ max b h * |y - z| :=
          mul_le_mul_of_nonneg_right (signal_abs h b y d hh hb) (abs_nonneg _)
  have s2 : signal h b z d * (z - y) ≤ max b h * |y - z| := by
    calc _ ≤ |signal h b z d * (z - y)| := le_abs_self _
      _ = |signal h b z d| * |z - y| := abs_mul _ _
      _ ≤ max b h * |z - y| :=
          mul_le_mul_of_nonneg_right (signal_abs h b z d hh hb) (abs_nonneg _)
      _ = max b h * |y - z| := by rw [abs_sub_comm]
  rw [abs_le]; constructor <;> linarith

theorem project_mem (a z : ℝ) (ha : 0 ≤ a) : 0 ≤ project a z ∧ project a z ≤ a := by
  unfold project
  exact ⟨le_max_right _ _, max_le (min_le_right _ _) ha⟩

theorem project_eq (a z : ℝ) (h0 : 0 ≤ z) (ha : z ≤ a) : project a z = z := by
  unfold project
  rw [min_eq_left ha, max_eq_left h0]

theorem continuous_project (a : ℝ) : Continuous (project a) := by
  unfold project
  exact (continuous_id.min continuous_const).max continuous_const

theorem project_sq (a z q : ℝ) (hq0 : 0 ≤ q) (hqa : q ≤ a) :
    (project a z - q) ^ 2 ≤ (z - q) ^ 2 := by
  unfold project
  rcases le_total z 0 with hz | hz
  · rw [min_eq_left (by linarith : z ≤ a), max_eq_right hz]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -z) (by linarith : (0:ℝ) ≤ 2 * q - z)]
  · rcases le_total z a with hza | hza
    · rw [min_eq_left hza, max_eq_left hz]
    · rw [min_eq_right hza, max_eq_left (by linarith : (0:ℝ) ≤ a)]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ z - a) (by linarith : (0:ℝ) ≤ z + a - 2 * q)]

theorem run_bound (δ b h y₁ : ℝ) (hδ : 0 < δ) (hy0 : 0 ≤ y₁) (hy1 : y₁ ≤ 1)
    (d : ℕ → ℝ≥0) (k : ℕ) :
    0 ≤ modAimRun δ b h y₁ d k ∧ modAimRun δ b h y₁ d k ≤ ((k:ℝ) + 1) ^ (δ / 2) := by
  cases k with
  | zero =>
    simp only [modAimRun, Nat.cast_zero, zero_add, Real.one_rpow]
    exact ⟨hy0, hy1⟩
  | succ k =>
    simp only [modAimRun]
    have hr : 0 ≤ radius δ (k + 1) := Real.rpow_nonneg (by positivity) _
    obtain ⟨h1, h2⟩ := project_mem (radius δ (k + 1)) _ hr
    refine ⟨h1, h2.trans ?_⟩
    unfold radius
    exact Real.rpow_le_rpow (by positivity) (by push_cast; linarith) (by linarith)

/-- One OGD step, pathwise, for a comparator inside the projection interval. -/
theorem ogd_step (δ b h y₁ q : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h) (hB : 0 < max b h)
    (ω : ℕ → ℝ≥0) (k : ℕ) (hq0 : 0 ≤ q) (hqr : q ≤ radius δ (k + 1)) :
    signal h b (modAimRun δ b h y₁ ω k) (ω k) * (modAimRun δ b h y₁ ω k - q) ≤
      max b h * Real.sqrt ((k:ℝ) + 1) / 2 *
          ((modAimRun δ b h y₁ ω k - q) ^ 2 - (modAimRun δ b h y₁ ω (k + 1) - q) ^ 2)
        + max b h / (2 * Real.sqrt ((k:ℝ) + 1)) := by
  have hrun : modAimRun δ b h y₁ ω (k + 1) = project (radius δ (k + 1))
      (modAimRun δ b h y₁ ω k - stepSize b h (k + 1) *
        signal h b (modAimRun δ b h y₁ ω k) (ω k)) := by
    simp only [modAimRun]
  rw [hrun]
  set x := modAimRun δ b h y₁ ω k with hx
  set g := signal h b x (ω k) with hg
  set B := max b h with hBdef
  set s := Real.sqrt ((k:ℝ) + 1) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  set ε := stepSize b h (k + 1) with hεdef
  have hε : ε = 1 / (B * s) := by
    rw [hεdef]; unfold stepSize; push_cast; rfl
  have hεB : B * s * ε = 1 := by rw [hε]; field_simp
  have hsq := project_sq (radius δ (k + 1)) (x - ε * g) q hq0 hqr
  have hgabs : |g| ≤ B := signal_abs h b x (ω k) hh hb
  have hg2 : g ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs g]
    exact pow_le_pow_left₀ (abs_nonneg g) hgabs 2
  have e1 : (x - ε * g - q) ^ 2 = (x - q) ^ 2 - 2 * ε * (g * (x - q)) + ε ^ 2 * g ^ 2 := by
    ring
  have m1 := mul_le_mul_of_nonneg_left hg2 (sq_nonneg ε)
  set x' := project (radius δ (k + 1)) (x - ε * g) with hx'
  have key : 2 * ε * (g * (x - q)) ≤ ((x - q) ^ 2 - (x' - q) ^ 2) + ε ^ 2 * B ^ 2 := by
    linarith
  have hc : 0 ≤ B * s / 2 := by positivity
  have k2 := mul_le_mul_of_nonneg_left key hc
  have e2 : B * s / 2 * (2 * ε * (g * (x - q))) = (B * s * ε) * (g * (x - q)) := by ring
  have e3 : B * s / 2 * (((x - q) ^ 2 - (x' - q) ^ 2) + ε ^ 2 * B ^ 2)
      = B * s / 2 * ((x - q) ^ 2 - (x' - q) ^ 2) + B / (2 * s) := by
    rw [hε]; field_simp
  rw [e2, hεB, one_mul, e3] at k2
  exact k2

/-! Part B: measurability and independence. -/

/-- The sigma-algebra of the first `k` demands. -/
def pre (k : ℕ) : MeasurableSpace (ℕ → ℝ≥0) :=
  ⨆ j ∈ Set.Iio k, MeasurableSpace.comap (fun ω : ℕ → ℝ≥0 => ω j) inferInstance

theorem signal_meas (h b : ℝ) : Measurable (fun p : ℝ × ℝ≥0 => signal h b p.1 p.2) := by
  unfold signal
  exact Measurable.ite (measurableSet_lt (measurable_coe_nnreal_real.comp measurable_snd)
    measurable_fst) measurable_const measurable_const

theorem run_meas (δ b h y₁ : ℝ) (k : ℕ) :
    Measurable[pre k] (fun ω : ℕ → ℝ≥0 => modAimRun δ b h y₁ ω k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hle : pre k ≤ pre (k + 1) := by
      unfold pre
      exact biSup_mono (fun j (hj : j < k) => (lt_trans hj (Nat.lt_succ_self k) : j < k + 1))
    have h1 : Measurable[pre (k + 1)] (fun ω : ℕ → ℝ≥0 => modAimRun δ b h y₁ ω k) :=
      ih.mono hle le_rfl
    have h2 : Measurable[pre (k + 1)] (fun ω : ℕ → ℝ≥0 => ω k) := by
      have : MeasurableSpace.comap (fun ω : ℕ → ℝ≥0 => ω k) inferInstance ≤ pre (k + 1) := by
        unfold pre
        exact le_iSup₂ (f := fun j (_ : j ∈ Set.Iio (k + 1)) =>
          MeasurableSpace.comap (fun ω : ℕ → ℝ≥0 => ω j) inferInstance) k (Nat.lt_succ_self k)
      exact (comap_measurable _).mono this le_rfl
    have h3 : Measurable[pre (k + 1)]
        (fun ω : ℕ → ℝ≥0 => signal h b (modAimRun δ b h y₁ ω k) (ω k)) :=
      (signal_meas h b).comp (h1.prodMk h2)
    have h4 := (continuous_project (radius δ (k + 1))).measurable.comp
      (h1.sub (h3.const_mul (stepSize b h (k + 1))))
    simp only [modAimRun]
    exact h4

theorem pre_le (k : ℕ) : pre k ≤ MeasurableSpace.pi := by
  unfold pre
  exact iSup₂_le (fun j _ => (measurable_pi_apply j).comap_le)

theorem run_measurable (δ b h y₁ : ℝ) (k : ℕ) :
    Measurable (fun ω : ℕ → ℝ≥0 => modAimRun δ b h y₁ ω k) :=
  (run_meas δ b h y₁ k).mono (pre_le k) le_rfl

theorem pathLaw_prob (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (pathLaw μ) := by
  have hPdef : pathLaw μ = Measure.infinitePi (fun _ : ℕ => μ) := rfl
  rw [hPdef]; infer_instance

theorem indep_integral (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (δ b h y₁ : ℝ) (k : ℕ)
    (F : ℝ × ℝ≥0 → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ p, |F p| ≤ C) :
    ∫ ω, F (modAimRun δ b h y₁ ω k, ω k) ∂(pathLaw μ)
      = ∫ ω, (∫ e, F (modAimRun δ b h y₁ ω k, e) ∂μ) ∂(pathLaw μ) := by
  have hPdef : pathLaw μ = Measure.infinitePi (fun _ : ℕ => μ) := rfl
  haveI : IsProbabilityMeasure (pathLaw μ) := pathLaw_prob μ
  have hXm' := run_meas δ b h y₁ k
  have hXm : Measurable (fun ω : ℕ → ℝ≥0 => modAimRun δ b h y₁ ω k) := run_measurable δ b h y₁ k
  have hYm : Measurable (fun ω : ℕ → ℝ≥0 => ω k) := measurable_pi_apply k
  have hind : IndepFun (fun ω : ℕ → ℝ≥0 => modAimRun δ b h y₁ ω k) (fun ω : ℕ → ℝ≥0 => ω k)
      (pathLaw μ) := by
    rw [IndepFun_iff_Indep]
    have hi : iIndep (fun j => MeasurableSpace.comap (fun ω : ℕ → ℝ≥0 => ω j) inferInstance)
        (pathLaw μ) := by
      have := iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ (x : ℝ≥0) => x)
        (fun _ => measurable_id)
      rw [hPdef]
      exact (iIndepFun_iff_iIndep (fun _ => inferInstance) (fun j (ω : ℕ → ℝ≥0) => ω j) _).1 this
    have h2 := indep_iSup_of_disjoint (fun j => (measurable_pi_apply j).comap_le) hi
      (S := Set.Iio k) (T := {k}) (by simp)
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h2 hXm'.comap_le) ?_
    exact le_iSup₂ (f := fun j (_ : j ∈ ({k} : Set ℕ)) =>
      MeasurableSpace.comap (fun ω : ℕ → ℝ≥0 => ω j) inferInstance) k rfl
  have hmap : (pathLaw μ).map (fun ω => (modAimRun δ b h y₁ ω k, ω k))
      = ((pathLaw μ).map (fun ω => modAimRun δ b h y₁ ω k)).prod μ := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hYm.aemeasurable).1 hind]
    congr 1
    rw [hPdef]
    exact Measure.infinitePi_map_eval _ k
  haveI : IsProbabilityMeasure ((pathLaw μ).map (fun ω => modAimRun δ b h y₁ ω k)) :=
    Measure.isProbabilityMeasure_map hXm.aemeasurable
  have hFi : Integrable F (((pathLaw μ).map (fun ω => modAimRun δ b h y₁ ω k)).prod μ) :=
    Integrable.of_bound hF.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun p => by rw [Real.norm_eq_abs]; exact hC p))
  calc ∫ ω, F (modAimRun δ b h y₁ ω k, ω k) ∂(pathLaw μ)
      = ∫ p, F p ∂((pathLaw μ).map (fun ω => (modAimRun δ b h y₁ ω k, ω k))) :=
        (integral_map (hXm.prodMk hYm).aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ p, F p ∂(((pathLaw μ).map (fun ω => modAimRun δ b h y₁ ω k)).prod μ) := by rw [hmap]
    _ = ∫ x, (∫ e, F (x, e) ∂μ) ∂((pathLaw μ).map (fun ω => modAimRun δ b h y₁ ω k)) :=
        integral_prod F hFi
    _ = ∫ ω, (∫ e, F (modAimRun δ b h y₁ ω k, e) ∂μ) ∂(pathLaw μ) :=
        integral_map hXm.aemeasurable
          (hF.stronglyMeasurable.integral_prod_right').aestronglyMeasurable


/-! Part C: the quantile. -/

theorem crit_iff (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (c y : ℝ) (hy : 0 ≤ y) :
    c ≤ AIMInventoryAudit.UnknownBound.cdf μ y ↔ ENNReal.ofReal c ≤ μ (Set.Iic y.toNNReal) := by
  have hset : {d : ℝ≥0 | (d : ℝ) ≤ y} = Set.Iic y.toNNReal := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    exact (Real.le_toNNReal_iff_coe_le hy).symm
  unfold AIMInventoryAudit.UnknownBound.cdf
  rw [hset, ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  rfl

theorem sInf_mem_A (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (c : ℝ≥0∞)
    (hne : {S : ℝ≥0 | c ≤ μ (Set.Iic S)}.Nonempty) :
    c ≤ μ (Set.Iic (sInf {S : ℝ≥0 | c ≤ μ (Set.Iic S)})) := by
  set s0 := sInf {S : ℝ≥0 | c ≤ μ (Set.Iic S)} with hs0
  have hmem : ∀ n : ℕ, c ≤ μ (Set.Iic (s0 + 1 / ((n:ℝ≥0) + 1))) := by
    intro n
    have hlt : s0 < s0 + 1 / ((n:ℝ≥0) + 1) := lt_add_of_pos_right _ (by positivity)
    obtain ⟨S, hS, hS2⟩ := exists_lt_of_csInf_lt hne hlt
    exact le_trans hS (measure_mono (Set.Iic_subset_Iic.2 hS2.le))
  have hanti : Antitone (fun n : ℕ => Set.Iic (s0 + 1 / ((n:ℝ≥0) + 1))) := by
    intro n m hnm
    apply Set.Iic_subset_Iic.2
    apply add_le_add le_rfl
    apply one_div_le_one_div_of_le (by positivity)
    exact add_le_add (Nat.cast_le.2 hnm) le_rfl
  have hint : (⋂ n : ℕ, Set.Iic (s0 + 1 / ((n:ℝ≥0) + 1))) = Set.Iic s0 := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Iic]
    constructor
    · intro hx
      by_contra hcon
      push_neg at hcon
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hcon)
      have h1 := (hx n).trans_lt (add_lt_add_of_le_of_lt le_rfl hn)
      rw [add_tsub_cancel_of_le hcon.le] at h1
      exact lt_irrefl _ h1
    · intro hx n
      exact hx.trans (le_add_of_nonneg_right (by positivity))
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hint] at ht
  exact ge_of_tendsto ht (Filter.Eventually.of_forall hmem)

theorem A_nonempty (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (c : ℝ) (hc : c < 1) :
    ∃ S : ℝ≥0, ENNReal.ofReal c ≤ μ (Set.Iic S) := by
  have hmono : Monotone (fun n : ℕ => Set.Iic (n : ℝ≥0)) :=
    fun n m hnm => Set.Iic_subset_Iic.2 (Nat.cast_le.2 hnm)
  have hU : (⋃ n : ℕ, Set.Iic (n : ℝ≥0)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    exact exists_nat_ge x
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hU, measure_univ] at ht
  have hlt : ENNReal.ofReal c < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hc
  obtain ⟨n, hn⟩ := ((tendsto_order.1 ht).1 _ hlt).exists
  exact ⟨n, hn.le⟩

theorem quantile_facts (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (h b : ℝ) (hb : 0 ≤ b)
    (hh : 0 ≤ h) (hendpoint : h = 0 → (criticalSet μ h b).Nonempty) :
    (criticalSet μ h b).Nonempty ∧ quantile μ h b ∈ criticalSet μ h b := by
  have hA : {S : ℝ≥0 | ENNReal.ofReal (b / (b + h)) ≤ μ (Set.Iic S)}.Nonempty := by
    rcases eq_or_lt_of_le hh with h0 | hpos
    · obtain ⟨y, hy0, hy⟩ := hendpoint h0.symm
      exact ⟨y.toNNReal, (crit_iff μ _ y hy0).1 hy⟩
    · have hc : b / (b + h) < 1 := by
        rw [div_lt_one (by linarith)]; linarith
      exact A_nonempty μ _ hc
  have hq0 : 0 ≤ quantile μ h b := NNReal.coe_nonneg _
  have hq : quantile μ h b ∈ criticalSet μ h b := by
    refine ⟨hq0, (crit_iff μ _ _ hq0).2 ?_⟩
    unfold quantile
    rw [Real.toNNReal_coe]
    unfold LostSalesOrderUpTo.Asymptotic.newsvendorLevel LostSalesOrderUpTo.Asymptotic.distribution
    exact sInf_mem_A μ _ hA
  exact ⟨⟨_, hq⟩, hq⟩

/-! Part D: cost facts. -/

theorem loss_nonneg (h b y : ℝ) (d : ℝ≥0) (hh : 0 ≤ h) (hb : 0 ≤ b) : 0 ≤ loss h b y d := by
  unfold loss
  exact add_nonneg (mul_nonneg hh (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))

theorem loss_cont (h b y : ℝ) : Continuous (fun d : ℝ≥0 => loss h b y d) := by
  unfold loss
  exact (continuous_const.mul ((continuous_const.sub NNReal.continuous_coe).max continuous_const)).add
    (continuous_const.mul ((NNReal.continuous_coe.sub continuous_const).max continuous_const))

theorem loss_joint (h b q : ℝ) :
    Measurable (fun p : ℝ × ℝ≥0 => loss h b p.1 p.2 - loss h b q p.2) := by
  apply Continuous.measurable
  unfold loss
  have c2 : Continuous (fun p : ℝ × ℝ≥0 => ((p.2 : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp continuous_snd
  exact ((continuous_const.mul ((continuous_fst.sub c2).max continuous_const)).add
    (continuous_const.mul ((c2.sub continuous_fst).max continuous_const))).sub
    ((continuous_const.mul ((continuous_const.sub c2).max continuous_const)).add
    (continuous_const.mul ((c2.sub continuous_const).max continuous_const)))

theorem diff_integrable (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (h b y q : ℝ)
    (hh : 0 ≤ h) (hb : 0 ≤ b) :
    Integrable (fun d => loss h b y d - loss h b q d) μ :=
  Integrable.of_bound ((loss_cont h b y).sub (loss_cont h b q)).measurable.aestronglyMeasurable
    (max b h * |y - q|) (Filter.Eventually.of_forall (fun d => by
      rw [Real.norm_eq_abs]; exact loss_lip h b y q d hh hb))

theorem cc_abs (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (h b y : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    |centeredCost μ h b y| ≤ max b h * |y - quantile μ h b| := by
  unfold centeredCost
  have := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun d => loss h b y d - loss h b (quantile μ h b) d)
    (C := max b h * |y - quantile μ h b|)
    (Filter.Eventually.of_forall (fun d => by
      rw [Real.norm_eq_abs]; exact loss_lip h b y (quantile μ h b) d hh hb))
  simpa [Real.norm_eq_abs] using this

theorem cc_meas (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (h b : ℝ) :
    Measurable (centeredCost μ h b) :=
  ((loss_joint h b (quantile μ h b)).stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

theorem G_meas (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (h b q : ℝ) :
    Measurable (fun x : ℝ => ∫ e, signal h b x e * (x - q) ∂μ) :=
  (((signal_meas h b).mul (measurable_fst.sub_const q)).stronglyMeasurable.integral_prod_right'
    (ν := μ)).measurable

theorem G_abs (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (h b q x : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    |∫ e, signal h b x e * (x - q) ∂μ| ≤ max b h * |x - q| := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun e => signal h b x e * (x - q))
    (C := max b h * |x - q|)
    (Filter.Eventually.of_forall (fun e => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (signal_abs h b x e hh hb) (abs_nonneg _)))
  simpa [Real.norm_eq_abs] using this

theorem cc_le_sig (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (h b y : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    centeredCost μ h b y ≤ ∫ e, signal h b y e * (y - quantile μ h b) ∂μ := by
  unfold centeredCost
  refine integral_mono (diff_integrable μ h b y _ hh hb) ?_
    (fun e => loss_subgrad h b y _ e hh hb)
  exact Integrable.of_bound
    (((signal_meas h b).comp (measurable_const.prodMk measurable_id)).mul_const _).aestronglyMeasurable
    (max b h * |y - quantile μ h b|) (Filter.Eventually.of_forall (fun e => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (signal_abs h b y e hh hb) (abs_nonneg _)))

theorem cc_run_int (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (δ b h y₁ : ℝ) (hδ : 0 < δ)
    (hb : 0 ≤ b) (hh : 0 ≤ h) (hy0 : 0 ≤ y₁) (hy1 : y₁ ≤ 1) (k : ℕ) :
    Integrable (fun ω => centeredCost μ h b (modAimRun δ b h y₁ ω k)) (pathLaw μ) := by
  haveI := pathLaw_prob μ
  refine Integrable.of_bound ((cc_meas μ h b).comp (run_measurable δ b h y₁ k)).aestronglyMeasurable
    (max b h * (((k:ℝ)+1)^(δ/2) + |quantile μ h b|)) (Filter.Eventually.of_forall (fun ω => ?_))
  have hr := run_bound δ b h y₁ hδ hy0 hy1 ω k
  rw [Real.norm_eq_abs]
  refine (cc_abs μ h b _ hh hb).trans (mul_le_mul_of_nonneg_left ?_ (le_max_of_le_left hb))
  exact abs_le.2 ⟨by linarith [le_abs_self (quantile μ h b), neg_abs_le (quantile μ h b)],
    by linarith [le_abs_self (quantile μ h b), neg_abs_le (quantile μ h b)]⟩

theorem sig_run_int (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (δ b h y₁ : ℝ) (hδ : 0 < δ)
    (hb : 0 ≤ b) (hh : 0 ≤ h) (hy0 : 0 ≤ y₁) (hy1 : y₁ ≤ 1) (q : ℝ) (k : ℕ) :
    Integrable (fun ω : ℕ → ℝ≥0 => signal h b (modAimRun δ b h y₁ ω k) (ω k) *
      (modAimRun δ b h y₁ ω k - q)) (pathLaw μ) := by
  haveI := pathLaw_prob μ
  have hm : Measurable (fun ω : ℕ → ℝ≥0 => signal h b (modAimRun δ b h y₁ ω k) (ω k) *
      (modAimRun δ b h y₁ ω k - q)) :=
    ((signal_meas h b).comp ((run_measurable δ b h y₁ k).prodMk (measurable_pi_apply k))).mul
      ((run_measurable δ b h y₁ k).sub_const q)
  refine Integrable.of_bound hm.aestronglyMeasurable (max b h * (((k:ℝ)+1)^(δ/2) + |q|))
    (Filter.Eventually.of_forall (fun ω => ?_))
  have hr := run_bound δ b h y₁ hδ hy0 hy1 ω k
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (signal_abs h b _ _ hh hb)
    (abs_le.2 ⟨by linarith [le_abs_self q, neg_abs_le q], by linarith [le_abs_self q, neg_abs_le q]⟩)
    (abs_nonneg _) (le_max_of_le_left hb)

theorem step_expect (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (δ b h y₁ : ℝ) (hδ : 0 < δ)
    (hb : 0 ≤ b) (hh : 0 ≤ h) (hy0 : 0 ≤ y₁) (hy1 : y₁ ≤ 1) (k : ℕ) :
    ∫ ω, centeredCost μ h b (modAimRun δ b h y₁ ω k) ∂(pathLaw μ) ≤
      ∫ ω, signal h b (modAimRun δ b h y₁ ω k) (ω k) *
        (modAimRun δ b h y₁ ω k - quantile μ h b) ∂(pathLaw μ) := by
  haveI := pathLaw_prob μ
  have hR0 : (0:ℝ) ≤ ((k:ℝ)+1)^(δ/2) := by positivity
  have hproj : ∀ ω : ℕ → ℝ≥0, project (((k:ℝ)+1)^(δ/2)) (modAimRun δ b h y₁ ω k)
      = modAimRun δ b h y₁ ω k :=
    fun ω => project_eq _ _ (run_bound δ b h y₁ hδ hy0 hy1 ω k).1
      (run_bound δ b h y₁ hδ hy0 hy1 ω k).2
  have hFm : Measurable (fun p : ℝ × ℝ≥0 => signal h b (project (((k:ℝ)+1)^(δ/2)) p.1) p.2 *
      (project (((k:ℝ)+1)^(δ/2)) p.1 - quantile μ h b)) :=
    ((signal_meas h b).comp (((continuous_project _).measurable.comp measurable_fst).prodMk
      measurable_snd)).mul (((continuous_project _).measurable.comp measurable_fst).sub_const _)
  have key := indep_integral μ δ b h y₁ k _ hFm
    (max b h * (((k:ℝ)+1)^(δ/2) + |quantile μ h b|)) (fun p => by
      have hp := project_mem (((k:ℝ)+1)^(δ/2)) p.1 hR0
      beta_reduce
      rw [abs_mul]
      exact mul_le_mul (signal_abs h b _ _ hh hb)
        (abs_le.2 ⟨by linarith [le_abs_self (quantile μ h b), neg_abs_le (quantile μ h b)],
          by linarith [le_abs_self (quantile μ h b), neg_abs_le (quantile μ h b)]⟩)
        (abs_nonneg _) (le_max_of_le_left hb))
  simp only [hproj] at key
  rw [key]
  refine integral_mono (cc_run_int μ δ b h y₁ hδ hb hh hy0 hy1 k) ?_
    (fun ω => cc_le_sig μ h b _ hh hb)
  refine Integrable.of_bound
    ((G_meas μ h b (quantile μ h b)).comp (run_measurable δ b h y₁ k)).aestronglyMeasurable
    (max b h * (((k:ℝ)+1)^(δ/2) + |quantile μ h b|)) (Filter.Eventually.of_forall (fun ω => ?_))
  have hr := run_bound δ b h y₁ hδ hy0 hy1 ω k
  rw [Real.norm_eq_abs]
  refine (G_abs μ h b _ _ hh hb).trans (mul_le_mul_of_nonneg_left ?_ (le_max_of_le_left hb))
  exact abs_le.2 ⟨by linarith [le_abs_self (quantile μ h b), neg_abs_le (quantile μ h b)],
    by linarith [le_abs_self (quantile μ h b), neg_abs_le (quantile μ h b)]⟩

/-! Part E: pathwise bounds. -/

theorem target_bound (δ b h y₁ : ℝ) (hδ : 0 < δ) (hy0 : 0 ≤ y₁) (hy1 : y₁ ≤ 1)
    (d : ℕ → ℝ≥0) (t : ℕ) (ht : 1 ≤ t) :
    0 ≤ modAimTarget δ b h y₁ d t ∧ modAimTarget δ b h y₁ d t ≤ (t:ℝ) ^ (δ / 2) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' ht
  have := run_bound δ b h y₁ hδ hy0 hy1 d s
  simp only [modAimTarget, Nat.add_sub_cancel]
  push_cast
  exact this

theorem ogd_t (δ b h y₁ q : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h) (hB : 0 < max b h)
    (ω : ℕ → ℝ≥0) (t : ℕ) (ht : 1 ≤ t) (hq0 : 0 ≤ q) (hqr : q ≤ (t:ℝ) ^ (δ / 2)) :
    signal h b (modAimTarget δ b h y₁ ω t) (ω (t-1)) * (modAimTarget δ b h y₁ ω t - q) ≤
      max b h * Real.sqrt t / 2 * ((modAimTarget δ b h y₁ ω t - q) ^ 2 -
        (modAimTarget δ b h y₁ ω (t+1) - q) ^ 2) + max b h / (2 * Real.sqrt t) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' ht
  have := ogd_step δ b h y₁ q hb hh hB ω s hq0 (by unfold radius; exact hqr)
  simp only [modAimTarget, Nat.add_sub_cancel]
  push_cast
  exact this

theorem tele (a D : ℕ → ℝ) (M : ℝ) (m : ℕ) (ha : ∀ t, 0 ≤ a t) (hmono : ∀ t, a t ≤ a (t+1)) :
    ∀ n, m ≤ n → (∀ t, m ≤ t → t ≤ n → D t ≤ M) →
      ∑ t ∈ Finset.Icc m n, a t * (D t - D (t+1)) ≤ a n * M - a n * D (n+1) := by
  intro n hmn
  induction n, hmn using Nat.le_induction with
  | base =>
    intro hD
    rw [Finset.Icc_self, Finset.sum_singleton]
    have h1 := mul_le_mul_of_nonneg_left (hD m le_rfl le_rfl) (ha m)
    nlinarith
  | succ n hmn ih =>
    intro hD
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := ih (fun t h1 h2 => hD t h1 (by omega))
    have h2 := hD (n+1) (by omega) le_rfl
    have h3 := mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 (hmono n))
    nlinarith

theorem sum_inv_sqrt (n : ℕ) : ∑ t ∈ Finset.Icc 1 n, 1 / Real.sqrt t ≤ 2 * Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hcast : ((n+1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
    have ha := Real.sq_sqrt (Nat.cast_nonneg (n+1) : (0:ℝ) ≤ ((n+1 : ℕ) : ℝ))
    have hc := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ (n : ℝ))
    have hapos : 0 < Real.sqrt ((n+1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hc0 := Real.sqrt_nonneg (n:ℝ)
    have key : 1 / Real.sqrt ((n+1:ℕ):ℝ) ≤ 2 * Real.sqrt ((n+1:ℕ):ℝ) - 2 * Real.sqrt n := by
      rw [div_le_iff₀ hapos]
      nlinarith [sq_nonneg (Real.sqrt ((n+1:ℕ):ℝ) - Real.sqrt n)]
    linarith

theorem sq_le_aux (x q r R : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ r) (hq0 : 0 ≤ q) (hq1 : q ≤ r)
    (hrR : r ≤ R) : (x - q) ^ 2 ≤ R ^ 2 := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ R - x + q) (by linarith : (0:ℝ) ≤ R + x - q)]

theorem rpow_back (q δ : ℝ) (hq0 : 0 ≤ q) (hδ : 0 < δ) : (q ^ (2/δ)) ^ (δ/2) = q := by
  rw [← Real.rpow_mul hq0, div_mul_div_comm, mul_comm 2 δ, div_self (mul_pos hδ two_pos).ne',
    Real.rpow_one]

theorem late_path (δ b h y₁ q : ℝ) (hδ : 0 < δ) (hb : 0 ≤ b) (hh : 0 ≤ h) (hB : 0 < max b h)
    (hy0 : 0 ≤ y₁) (hy1 : y₁ ≤ 1) (hq0 : 0 ≤ q) (ω : ℕ → ℝ≥0) (T : ℕ) :
    ∑ t ∈ (Finset.Icc 1 T).filter (fun t : ℕ => q ^ (2/δ) ≤ (t:ℝ)),
      signal h b (modAimTarget δ b h y₁ ω t) (ω (t-1)) * (modAimTarget δ b h y₁ ω t - q)
      ≤ max b h * Real.sqrt T * (T:ℝ) ^ δ / 2 + max b h * Real.sqrt T := by
  have hθ0 : 0 ≤ q ^ (2/δ) := Real.rpow_nonneg hq0 _
  have hfil : (Finset.Icc 1 T).filter (fun t : ℕ => q ^ (2/δ) ≤ (t:ℝ))
      = Finset.Icc (max 1 ⌈q ^ (2/δ)⌉₊) T := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff, Nat.ceil_le]
    tauto
  rw [hfil]
  have hqr : ∀ t, max 1 ⌈q ^ (2/δ)⌉₊ ≤ t → q ≤ (t:ℝ) ^ (δ/2) := by
    intro t ht
    have h1 : q ^ (2/δ) ≤ t := Nat.ceil_le.1 (le_trans (le_max_right _ _) ht)
    calc q = (q ^ (2/δ)) ^ (δ/2) := (rpow_back q δ hq0 hδ).symm
      _ ≤ (t:ℝ) ^ (δ/2) := Real.rpow_le_rpow hθ0 h1 (by linarith)
  have ht1 : ∀ t, max 1 ⌈q ^ (2/δ)⌉₊ ≤ t → 1 ≤ t := fun t ht => le_trans (le_max_left _ _) ht
  have hBn : 0 ≤ max b h := hB.le
  have hsT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hTd : 0 ≤ (T:ℝ) ^ δ := by positivity
  rcases lt_or_ge T (max 1 ⌈q ^ (2/δ)⌉₊) with hTm | hmT
  · rw [Finset.Icc_eq_empty (not_le.2 hTm), Finset.sum_empty]
    linarith [mul_nonneg (mul_nonneg hBn hsT) hTd, mul_nonneg hBn hsT]
  · have hstep : ∀ t ∈ Finset.Icc (max 1 ⌈q ^ (2/δ)⌉₊) T,
        signal h b (modAimTarget δ b h y₁ ω t) (ω (t-1)) * (modAimTarget δ b h y₁ ω t - q) ≤
        max b h * Real.sqrt t / 2 * ((modAimTarget δ b h y₁ ω t - q) ^ 2 -
          (modAimTarget δ b h y₁ ω (t+1) - q) ^ 2) + max b h / (2 * Real.sqrt t) :=
      fun t ht => ogd_t δ b h y₁ q hb hh hB ω t (ht1 t (Finset.mem_Icc.1 ht).1) hq0
        (hqr t (Finset.mem_Icc.1 ht).1)
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [Finset.sum_add_distrib]
    have htel := tele (fun t => max b h * Real.sqrt t / 2)
      (fun t => (modAimTarget δ b h y₁ ω t - q) ^ 2) ((T:ℝ) ^ δ) (max 1 ⌈q ^ (2/δ)⌉₊)
      (fun t => div_nonneg (mul_nonneg hBn (Real.sqrt_nonneg _)) zero_le_two)
      (fun t => by
        have hs := Real.sqrt_le_sqrt (show ((t:ℕ):ℝ) ≤ ((t+1:ℕ):ℝ) by push_cast; linarith)
        have := mul_le_mul_of_nonneg_left hs hBn
        show max b h * Real.sqrt t / 2 ≤ max b h * Real.sqrt ((t+1:ℕ):ℝ) / 2
        linarith) T hmT
      (fun t h1 h2 => by
        obtain ⟨hx0, hx1⟩ := target_bound δ b h y₁ hδ hy0 hy1 ω t (ht1 t h1)
        have hq := hqr t h1
        have htT : (t:ℝ) ^ (δ/2) ≤ (T:ℝ) ^ (δ/2) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast h2) (by linarith)
        have hsq : ((T:ℝ) ^ (δ/2)) ^ 2 = (T:ℝ) ^ δ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg T)]
          congr 1; push_cast; ring
        show (modAimTarget δ b h y₁ ω t - q) ^ 2 ≤ (T:ℝ) ^ δ
        rw [← hsq]
        exact sq_le_aux _ _ _ _ hx0 hx1 hq0 hq htT)
    beta_reduce at htel
    have hsum2 : ∑ t ∈ Finset.Icc (max 1 ⌈q ^ (2/δ)⌉₊) T, max b h / (2 * Real.sqrt t)
        ≤ max b h * Real.sqrt T := by
      have e : ∑ t ∈ Finset.Icc (max 1 ⌈q ^ (2/δ)⌉₊) T, max b h / (2 * Real.sqrt t)
          = max b h / 2 * ∑ t ∈ Finset.Icc (max 1 ⌈q ^ (2/δ)⌉₊) T, 1 / Real.sqrt t := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun t _ => ?_); ring
      have hs2 : ∑ t ∈ Finset.Icc (max 1 ⌈q ^ (2/δ)⌉₊) T, 1 / Real.sqrt t
          ≤ ∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt t :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left (le_max_left _ _))
          (fun _ _ _ => by positivity)
      have hs3 := sum_inv_sqrt T
      rw [e]
      have := mul_le_mul_of_nonneg_left (hs2.trans hs3) (div_nonneg hBn zero_le_two)
      linarith
    have hDT : 0 ≤ max b h * Real.sqrt T / 2 * (modAimTarget δ b h y₁ ω (T+1) - q) ^ 2 :=
      mul_nonneg (div_nonneg (mul_nonneg hBn hsT) zero_le_two) (sq_nonneg _)
    linarith

theorem early_term (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (δ b h y₁ : ℝ) (hδ : 0 < δ)
    (hb : 0 ≤ b) (hh : 0 ≤ h) (hy0 : 0 ≤ y₁) (hy1 : y₁ ≤ 1) (ω : ℕ → ℝ≥0) (t : ℕ) (ht : 1 ≤ t)
    (hlt : ¬ (quantile μ h b) ^ (2/δ) ≤ (t:ℝ)) :
    centeredCost μ h b (modAimTarget δ b h y₁ ω t) ≤ max b h * quantile μ h b := by
  have hq0 : 0 ≤ quantile μ h b := NNReal.coe_nonneg _
  obtain ⟨hx0, hx1⟩ := target_bound δ b h y₁ hδ hy0 hy1 ω t ht
  have h2 : (t:ℝ) ^ (δ/2) < ((quantile μ h b) ^ (2/δ)) ^ (δ/2) :=
    Real.rpow_lt_rpow (Nat.cast_nonneg t) (not_le.1 hlt) (by linarith)
  rw [rpow_back _ δ hq0 hδ] at h2
  refine (le_abs_self _).trans ((cc_abs μ h b _ hh hb).trans
    (mul_le_mul_of_nonneg_left ?_ (le_max_of_le_left hb)))
  rw [abs_le]; constructor <;> linarith

theorem card_early (θ : ℝ) (hθ : 0 ≤ θ) (T : ℕ) :
    (((Finset.Icc 1 T).filter (fun t : ℕ => ¬ θ ≤ (t:ℝ))).card : ℝ) ≤ θ := by
  have hsub : (Finset.Icc 1 T).filter (fun t : ℕ => ¬ θ ≤ (t:ℝ)) ⊆ Finset.Icc 1 ⌊θ⌋₊ := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_Icc, not_le] at ht ⊢
    exact ⟨ht.1.1, Nat.le_floor ht.2.le⟩
  calc _ ≤ ((Finset.Icc 1 ⌊θ⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = ⌊θ⌋₊ := by simp
    _ ≤ θ := Nat.floor_le hθ

theorem final_arith (B Q T u v w A C : ℝ) (hT : 0 < T) (hB : 0 ≤ B) (hu : 0 < u) (hv : 0 < v)
    (hw : 0 < w) (huvw : u * (v * w) = T) (hvv : v * v = T)
    (hA : A ≤ B * v * w / 2 + B * v) (hC : C ≤ B * Q) :
    1 / T * (A + C) ≤ B * (1 / u + 1 / v + Q / T) := by
  have h1u : 1 / u = v * w / T := by rw [div_eq_div_iff hu.ne' hT.ne', ← huvw]; ring
  have h1v : 1 / v = v / T := by rw [div_eq_div_iff hv.ne' hT.ne', ← hvv]; ring
  rw [h1u, h1v, show 1 / T * (A + C) = (A + C) / T by ring,
    show B * (v * w / T + v / T + Q / T) = B * (v * w + v + Q) / T by ring]
  apply (div_le_div_iff_of_pos_right hT).2
  nlinarith [mul_nonneg (mul_nonneg hB hv.le) hw.le]

theorem main_bound (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (δ b h y₁ : ℝ) (T : ℕ)
    (hδ : 0 < δ) (hb : 0 ≤ b) (hh : 0 ≤ h) (hB : 0 < max b h) (hy0 : 0 ≤ y₁) (hy1 : y₁ ≤ 1)
    (hT : 1 ≤ T) :
    Integrable (centeredAverage μ δ b h y₁ T) (pathLaw μ) ∧
    ∫ d, centeredAverage μ δ b h y₁ T d ∂pathLaw μ ≤ regretBound δ b h (quantile μ h b) T := by
  haveI := pathLaw_prob μ
  unfold regretBound
  simp only [Real.rpow_eq_pow]
  set q := quantile μ h b with hqdef
  have hq0 : 0 ≤ q := NNReal.coe_nonneg _
  have hint : ∀ t, Integrable (fun ω => centeredCost μ h b (modAimTarget δ b h y₁ ω t))
      (pathLaw μ) := fun t => cc_run_int μ δ b h y₁ hδ hb hh hy0 hy1 (t-1)
  have hfun : centeredAverage μ δ b h y₁ T = fun ω => (1/(T:ℝ)) *
      ∑ t ∈ Finset.Icc 1 T, centeredCost μ h b (modAimTarget δ b h y₁ ω t) := rfl
  have hI : Integrable (centeredAverage μ δ b h y₁ T) (pathLaw μ) := by
    rw [hfun]; exact (integrable_finset_sum _ (fun t _ => hint t)).const_mul _
  refine ⟨hI, ?_⟩
  rw [hfun, integral_const_mul, integral_finset_sum _ (fun t _ => hint t),
    ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 T) (fun t : ℕ => q ^ (2/δ) ≤ (t:ℝ))]
  have hE : ∑ t ∈ (Finset.Icc 1 T).filter (fun t : ℕ => ¬ q ^ (2/δ) ≤ (t:ℝ)),
      ∫ ω, centeredCost μ h b (modAimTarget δ b h y₁ ω t) ∂pathLaw μ ≤ max b h * q ^ (1 + 2/δ) := by
    calc _ ≤ ∑ t ∈ (Finset.Icc 1 T).filter (fun t : ℕ => ¬ q ^ (2/δ) ≤ (t:ℝ)), max b h * q := by
          apply Finset.sum_le_sum
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_Icc] at ht
          calc _ ≤ ∫ ω, max b h * q ∂pathLaw μ := integral_mono (hint t) (integrable_const _)
                (fun ω => early_term μ δ b h y₁ hδ hb hh hy0 hy1 ω t ht.1.1 ht.2)
            _ = max b h * q := by simp
      _ = (((Finset.Icc 1 T).filter (fun t : ℕ => ¬ q ^ (2/δ) ≤ (t:ℝ))).card : ℝ) * (max b h * q) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ q ^ (2/δ) * (max b h * q) :=
          mul_le_mul_of_nonneg_right (card_early _ (Real.rpow_nonneg hq0 _) T)
            (mul_nonneg hB.le hq0)
      _ = max b h * q ^ (1 + 2/δ) := by
          rw [Real.rpow_add' hq0 (by have := div_pos two_pos hδ; linarith : (0:ℝ) < 1 + 2/δ).ne',
            Real.rpow_one]; ring
  have hL : ∑ t ∈ (Finset.Icc 1 T).filter (fun t : ℕ => q ^ (2/δ) ≤ (t:ℝ)),
      ∫ ω, centeredCost μ h b (modAimTarget δ b h y₁ ω t) ∂pathLaw μ ≤
      max b h * Real.sqrt T * (T:ℝ) ^ δ / 2 + max b h * Real.sqrt T := by
    calc _ ≤ ∑ t ∈ (Finset.Icc 1 T).filter (fun t : ℕ => q ^ (2/δ) ≤ (t:ℝ)),
          ∫ ω, signal h b (modAimTarget δ b h y₁ ω t) (ω (t-1)) *
            (modAimTarget δ b h y₁ ω t - q) ∂pathLaw μ :=
          Finset.sum_le_sum (fun t _ => step_expect μ δ b h y₁ hδ hb hh hy0 hy1 (t-1))
      _ = ∫ ω, ∑ t ∈ (Finset.Icc 1 T).filter (fun t : ℕ => q ^ (2/δ) ≤ (t:ℝ)),
          signal h b (modAimTarget δ b h y₁ ω t) (ω (t-1)) *
            (modAimTarget δ b h y₁ ω t - q) ∂pathLaw μ :=
          (integral_finset_sum _ (fun t _ => sig_run_int μ δ b h y₁ hδ hb hh hy0 hy1 q (t-1))).symm
      _ ≤ ∫ ω, (max b h * Real.sqrt T * (T:ℝ) ^ δ / 2 + max b h * Real.sqrt T) ∂pathLaw μ :=
          integral_mono
            (integrable_finset_sum _ (fun t _ => sig_run_int μ δ b h y₁ hδ hb hh hy0 hy1 q (t-1)))
            (integrable_const _) (fun ω => late_path δ b h y₁ q hδ hb hh hB hy0 hy1 hq0 ω T)
      _ = _ := by simp
  have hTpos : (0:ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hL' := hL
  rw [Real.sqrt_eq_rpow] at hL'
  have huvw : (T:ℝ) ^ ((1/2:ℝ) - δ) * ((T:ℝ) ^ (1/2:ℝ) * (T:ℝ) ^ δ) = T := by
    rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos,
      show (1/2:ℝ) - δ + (1/2 + δ) = 1 by ring, Real.rpow_one]
  have hvv : (T:ℝ) ^ (1/2:ℝ) * (T:ℝ) ^ (1/2:ℝ) = T := by
    rw [← Real.rpow_add hTpos, show (1/2:ℝ) + 1/2 = 1 by norm_num, Real.rpow_one]
  exact final_arith (max b h) (q ^ (1 + 2/δ)) T ((T:ℝ) ^ ((1/2:ℝ) - δ)) ((T:ℝ) ^ (1/2:ℝ))
    ((T:ℝ) ^ δ) _ _ hTpos hB.le (Real.rpow_pos_of_pos hTpos _) (Real.rpow_pos_of_pos hTpos _)
    (Real.rpow_pos_of_pos hTpos _) huvw hvv hL' hE

/-! Part F: finite-cost and extended clauses. -/

theorem finite_facts (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (h b : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b)
    (hfin : extendedCost μ h b (quantile μ h b) < ⊤) (y : ℝ) :
    extendedCost μ h b y < ⊤ ∧ Integrable (loss h b y) μ ∧
      ENNReal.ofReal (realCost μ h b y) = extendedCost μ h b y := by
  have hq : Integrable (loss h b (quantile μ h b)) μ := by
    refine ⟨(loss_cont h b _).measurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun d => loss_nonneg h b _ d hh hb))]
    exact hfin
  have hy : Integrable (loss h b y) μ := by
    refine ((diff_integrable μ h b y (quantile μ h b) hh hb).add hq).congr
      (Filter.Eventually.of_forall (fun d => ?_))
    simp
  have heq : ENNReal.ofReal (realCost μ h b y) = extendedCost μ h b y :=
    ofReal_integral_eq_lintegral_ofReal hy
      (Filter.Eventually.of_forall (fun d => loss_nonneg h b y d hh hb))
  exact ⟨by rw [← heq]; exact ENNReal.ofReal_lt_top, hy, heq⟩

theorem realCost_nonneg (μ : Measure ℝ≥0) (h b y : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    0 ≤ realCost μ h b y :=
  integral_nonneg (fun d => loss_nonneg h b y d hh hb)

theorem avg_split (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (δ b h y₁ : ℝ) (T : ℕ)
    (hb : 0 ≤ b) (hh : 0 ≤ h) (hfin : extendedCost μ h b (quantile μ h b) < ⊤) (hT : 1 ≤ T)
    (ω : ℕ → ℝ≥0) :
    realAverage μ δ b h y₁ T ω =
      centeredAverage μ δ b h y₁ T ω + realCost μ h b (quantile μ h b) := by
  have hsplit : ∀ y, realCost μ h b y = centeredCost μ h b y + realCost μ h b (quantile μ h b) := by
    intro y
    unfold realCost centeredCost
    rw [integral_sub (finite_facts μ h b hh hb hfin y).2.1
      (finite_facts μ h b hh hb hfin (quantile μ h b)).2.1]
    ring
  unfold realAverage centeredAverage centeredSum
  rw [Finset.sum_congr rfl (fun t _ => hsplit (modAimTarget δ b h y₁ ω t)),
    Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
    mul_add, ← mul_assoc, one_div_mul_cancel (by exact_mod_cast (show T ≠ 0 by omega)), one_mul]

theorem ext_avg (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (δ b h y₁ : ℝ) (T : ℕ)
    (hb : 0 ≤ b) (hh : 0 ≤ h) (hfin : extendedCost μ h b (quantile μ h b) < ⊤) (hT : 1 ≤ T)
    (ω : ℕ → ℝ≥0) :
    extendedAverage μ δ b h y₁ T ω = ENNReal.ofReal (realAverage μ δ b h y₁ T ω) := by
  unfold extendedAverage realAverage
  rw [Finset.sum_congr rfl (fun t _ =>
      ((finite_facts μ h b hh hb hfin (modAimTarget δ b h y₁ ω t)).2.2).symm),
    ← ENNReal.ofReal_sum_of_nonneg
      (fun t _ => realCost_nonneg μ h b (modAimTarget δ b h y₁ ω t) hh hb),
    one_div_mul_eq_div, ENNReal.ofReal_div_of_pos (by exact_mod_cast (show 0 < T by omega)),
    ENNReal.ofReal_natCast]

theorem fin_pack (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (δ b h y₁ : ℝ) (T : ℕ)
    (hb : 0 ≤ b) (hh : 0 ≤ h) (hT : 1 ≤ T) (hfin : extendedCost μ h b (quantile μ h b) < ⊤)
    (hI : Integrable (centeredAverage μ δ b h y₁ T) (pathLaw μ)) :
    Integrable (realAverage μ δ b h y₁ T) (pathLaw μ) ∧
    ∫ d, realAverage μ δ b h y₁ T d ∂pathLaw μ =
      (∫ d, centeredAverage μ δ b h y₁ T d ∂pathLaw μ) + realCost μ h b (quantile μ h b) := by
  haveI := pathLaw_prob μ
  have hfun : realAverage μ δ b h y₁ T =
      fun ω => centeredAverage μ δ b h y₁ T ω + realCost μ h b (quantile μ h b) :=
    funext (avg_split μ δ b h y₁ T hb hh hfin hT)
  rw [hfun]
  refine ⟨hI.add (integrable_const _), ?_⟩
  rw [integral_add hI (integrable_const _)]
  simp

theorem ext_clause (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (δ b h y₁ : ℝ) (T : ℕ)
    (hb : 0 ≤ b) (hh : 0 ≤ h) (hT : 1 ≤ T) (hfin : extendedCost μ h b (quantile μ h b) < ⊤)
    (hI : Integrable (centeredAverage μ δ b h y₁ T) (pathLaw μ))
    (hbound : ∫ d, centeredAverage μ δ b h y₁ T d ∂pathLaw μ ≤ regretBound δ b h (quantile μ h b) T) :
    (∫⁻ d, extendedAverage μ δ b h y₁ T d ∂pathLaw μ) ≤
      extendedCost μ h b (quantile μ h b) + ENNReal.ofReal (regretBound δ b h (quantile μ h b) T) := by
  obtain ⟨hR, heq⟩ := fin_pack μ δ b h y₁ T hb hh hT hfin hI
  have hnn : 0 ≤ᵐ[pathLaw μ] realAverage μ δ b h y₁ T :=
    Filter.Eventually.of_forall (fun ω => by
      show 0 ≤ realAverage μ δ b h y₁ T ω
      unfold realAverage
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg (fun t _ => realCost_nonneg μ h b _ hh hb)))
  rw [lintegral_congr (fun ω => ext_avg μ δ b h y₁ T hb hh hfin hT ω),
    ← ofReal_integral_eq_lintegral_ofReal hR hnn, heq]
  refine (ENNReal.ofReal_add_le).trans ?_
  rw [add_comm]
  exact add_le_add ((finite_facts μ h b hh hb hfin _).2.2.le) (ENNReal.ofReal_le_ofReal hbound)

end AIMTh7

open MeasureTheory NNReal ENNReal AIMInventory.UnknownBound AIMInventoryAudit.UnknownBound in
theorem solution
    (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (δ b h y₁ : ℝ) (T : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (hB : 0 < max b h) (hendpoint : h = 0 → (criticalSet μ h b).Nonempty)
    (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (hT : 1 ≤ T) :
    (criticalSet μ h b).Nonempty ∧
    quantile μ h b ∈ criticalSet μ h b ∧
    (∀ y : ℝ, Integrable (fun d => loss h b y d - loss h b (quantile μ h b) d) μ) ∧
    Integrable (centeredAverage μ δ b h y₁ T) (pathLaw μ) ∧
    (∫ d, centeredAverage μ δ b h y₁ T d ∂pathLaw μ) ≤
      regretBound δ b h (quantile μ h b) T ∧
    (∫⁻ d, extendedAverage μ δ b h y₁ T d ∂pathLaw μ) ≤
      extendedCost μ h b (quantile μ h b) +
        ENNReal.ofReal (regretBound δ b h (quantile μ h b) T) ∧
    (extendedCost μ h b (quantile μ h b) < ⊤ →
      (∀ y : ℝ, extendedCost μ h b y < ⊤ ∧ Integrable (loss h b y) μ ∧
        ENNReal.ofReal (realCost μ h b y) = extendedCost μ h b y) ∧
      Integrable (realAverage μ δ b h y₁ T) (pathLaw μ) ∧
      (∫ d, realAverage μ δ b h y₁ T d ∂pathLaw μ) - realCost μ h b (quantile μ h b) =
        (∫ d, centeredAverage μ δ b h y₁ T d ∂pathLaw μ) ∧
      (∫ d, realAverage μ δ b h y₁ T d ∂pathLaw μ) - realCost μ h b (quantile μ h b) ≤
        regretBound δ b h (quantile μ h b) T) := by
  obtain ⟨hne, hqmem⟩ := AIMTh7.quantile_facts μ h b hb hh hendpoint
  obtain ⟨hI, hbound⟩ := AIMTh7.main_bound μ δ b h y₁ T hδ.1 hb hh hB hy₁.1 hy₁.2 hT
  refine ⟨hne, hqmem, fun y => AIMTh7.diff_integrable μ h b y _ hh hb, hI, hbound, ?_, ?_⟩
  · by_cases hfin : extendedCost μ h b (quantile μ h b) < ⊤
    · exact AIMTh7.ext_clause μ δ b h y₁ T hb hh hT hfin hI hbound
    · rw [not_lt, top_le_iff] at hfin
      rw [hfin, top_add]
      exact le_top
  · intro hfin
    obtain ⟨hR, heq⟩ := AIMTh7.fin_pack μ δ b h y₁ T hb hh hT hfin hI
    refine ⟨AIMTh7.finite_facts μ h b hh hb hfin, hR, ?_, ?_⟩
    · rw [heq]; ring
    · rw [heq]; linarith
