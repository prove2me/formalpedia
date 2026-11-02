-- Prove2me | solution 1 for AllocationIndices.Freezing.eps_index_star_near_optimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T15:07:31.479135+00:00
-- url     : https://prove2.me/submissions/ae362796-e45c-4d05-ac00-05da13f5349a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AllocationIndices_Freezing_optimal_value_le_max_index_stage
import Theorems.Thm_AllocationIndices_Freezing_eps_index_star_value_first_stage

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices AllocationIndices.Freezing

namespace EpsStarReduction

lemma value_abs_le {T : Type*} [MeasurableSpace T] (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} {M : ℝ} (hM : ∀ y, |r y| ≤ M) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {k : ℕ}
    (σ : MarkovBanditPolicy k T) (y : Fin k → T) :
    |markovBanditDiscountedValue P r a σ y| ≤ M / (1 - a) := by
  have hround : ∀ t, |markovBanditRoundReward P r σ y t| ≤ M := by
    intro t
    unfold markovBanditRoundReward
    have := norm_integral_le_of_norm_le_const (μ := markovBanditMeasure P σ y (t + 1))
      (f := fun h : MarkovBanditHistory k T (t + 1) ↦ r ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2)))
      (C := M) (Filter.Eventually.of_forall fun h ↦ by
        simpa [Real.norm_eq_abs] using hM _)
    simpa [Real.norm_eq_abs, probReal_univ] using this
  have hgeo : HasSum (fun t : ℕ ↦ M * a ^ t) (M * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0.le ha1).mul_left M
  have := tsum_of_norm_bounded hgeo (f := fun t ↦ a ^ t * markovBanditRoundReward P r σ y t)
    (fun t ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos ha0 t), mul_comm]
      exact mul_le_mul_of_nonneg_right (hround t) (pow_pos ha0 t).le)
  unfold markovBanditDiscountedValue
  rw [div_eq_mul_inv]
  simpa [Real.norm_eq_abs] using this

lemma measurable_of_trajStoppingTime {T : Type*} [MeasurableSpace T] {τ : (ℕ → T) → ℕ∞}
    (hτ : IsTrajStoppingTime τ) : Measurable τ := by
  have hle : ∀ n : ℕ, MeasurableSet {ω | τ ω ≤ (n : ℕ∞)} := by
    intro n
    have hF : trajectoryFiltration T n ≤ MeasurableSpace.pi := by
      apply Measurable.comap_le
      exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply _
    exact hF _ (hτ n)
  apply measurable_to_countable'
  intro m
  induction m using ENat.recTopCoe with
  | top =>
    have : τ ⁻¹' {⊤} = (⋃ n : ℕ, {ω | τ ω ≤ (n : ℕ∞)})ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        Set.mem_setOf_eq, not_exists]
      induction τ ω using ENat.recTopCoe with
      | top => simp
      | coe j =>
        simp only [ENat.coe_ne_top, false_iff, not_forall, not_not]
        exact ⟨j, le_rfl⟩
    rw [this]
    exact (MeasurableSet.iUnion hle).compl
  | coe n =>
    have : τ ⁻¹' {(n : ℕ∞)} =
        {ω | τ ω ≤ (n : ℕ∞)} ∩ ⋂ m : ℕ, ⋂ (_ : m < n), {ω | τ ω ≤ (m : ℕ∞)}ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
        Set.mem_iInter, Set.mem_compl_iff]
      induction τ ω using ENat.recTopCoe with
      | top => simp
      | coe j =>
        simp only [Nat.cast_inj, Nat.cast_le]
        constructor
        · rintro rfl; exact ⟨le_rfl, fun m hm h => by omega⟩
        · rintro ⟨h1, h2⟩
          by_contra hne
          exact h2 j (by omega) le_rfl
    rw [this]
    exact (hle n).inter (MeasurableSet.iInter fun m ↦ MeasurableSet.iInter fun _ ↦ (hle m).compl)

lemma discountPow_top (a : ℝ) : discountPow a ⊤ = 0 := rfl
lemma discountPow_coe (a : ℝ) (n : ℕ) : discountPow a (n : ℕ∞) = a ^ n := rfl

lemma discountedStoppedSum_one_eq {T : Type*} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (τ : (ℕ → T) → ℕ∞) (ω : ℕ → T) :
    discountedStoppedSum a (fun _ ↦ (1 : ℝ)) τ ω = (1 - discountPow a (τ ω)) / (1 - a) := by
  unfold discountedStoppedSum
  generalize τ ω = m
  induction m using ENat.recTopCoe with
  | top =>
    simp only [ENat.natCast_lt_top, if_true, mul_one]
    rw [tsum_geometric_of_lt_one ha0.le ha1]
    rw [discountPow_top]; simp [div_eq_mul_inv]
  | coe n =>
    rw [tsum_eq_sum (s := Finset.range n)]
    · rw [Finset.sum_congr rfl (g := fun t ↦ a ^ t)]
      · rw [geom_sum_eq (by linarith : a ≠ 1)]
        rw [discountPow_coe]
        have h1 : a - 1 ≠ 0 := by linarith
        have h2 : 1 - a ≠ 0 := by linarith
        field_simp
        ring
      · intro t ht
        simp [Finset.mem_range.mp ht]
    · intro t ht
      have : ¬ t < n := by simpa using ht
      simp [this]

lemma discountPow_bounds {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ∞) (hm : 1 ≤ m) :
    0 ≤ discountPow a m ∧ discountPow a m ≤ a := by
  induction m using ENat.recTopCoe with
  | top => rw [discountPow_top]; exact ⟨le_rfl, ha0.le⟩
  | coe n =>
    rw [discountPow_coe]
    have hn : 1 ≤ n := by exact_mod_cast hm
    refine ⟨(pow_pos ha0 n).le, ?_⟩
    calc a ^ n ≤ a ^ 1 := pow_le_pow_of_le_one ha0.le ha1.le hn
      _ = a := pow_one a

end EpsStarReduction

open EpsStarReduction

theorem solution {T : Type*} [MeasurableSpace T] [Countable T]
    [MeasurableSingletonClass T] (P : Kernel T T) [IsMarkovKernel P] {r : T → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ}
    {π : MarkovBanditPolicy k T} (hπ : IsEpsIndexStarPolicy P r a ε π) (x : Fin k → T) :
    (⨆ π' : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π' x) - ε / (1 - a) ≤
      markovBanditDiscountedValue P r a π x := by
  obtain ⟨M0, hM0⟩ := hr
  set M := max M0 0 with hMdef
  have hM : ∀ y, |r y| ≤ M := fun y ↦ (hM0 y).trans (le_max_left _ _)
  have hMnn : 0 ≤ M := le_max_right _ _
  have h1a : 0 < 1 - a := by linarith
  set B := M / (1 - a) with hBdef
  have hBnn : 0 ≤ B := div_nonneg hMnn h1a.le
  have hV : ∀ (σ : MarkovBanditPolicy k T) y, |markovBanditDiscountedValue P r a σ y| ≤ B :=
    fun σ y ↦ value_abs_le P hM ha0 ha1 σ y
  haveI : Nonempty (MarkovBanditPolicy k T) := ⟨π⟩
  set Vs : (Fin k → T) → ℝ :=
    fun y ↦ ⨆ σ : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a σ y with hVsdef
  have hbdd : ∀ y, BddAbove (Set.range fun σ : MarkovBanditPolicy k T ↦
      markovBanditDiscountedValue P r a σ y) := by
    intro y
    refine ⟨B, ?_⟩
    rintro _ ⟨σ, rfl⟩
    exact (le_abs_self _).trans (hV σ y)
  have hle_Vs : ∀ σ y, markovBanditDiscountedValue P r a σ y ≤ Vs y :=
    fun σ y ↦ le_ciSup (hbdd y) σ
  have hVs_le : ∀ y, Vs y ≤ B := fun y ↦ ciSup_le fun σ ↦ (le_abs_self _).trans (hV σ y)
  have hVs_ge : ∀ y, -B ≤ Vs y := fun y ↦
    (neg_le_of_abs_le (hV π y)).trans (hle_Vs π y)
  set S : Set ℝ := {d | ∃ (σ : MarkovBanditPolicy k T) (y : Fin k → T),
    IsEpsIndexStarPolicy P r a ε σ ∧ d = Vs y - markovBanditDiscountedValue P r a σ y}
    with hSdef
  have hmemS : ∀ σ y, IsEpsIndexStarPolicy P r a ε σ →
      Vs y - markovBanditDiscountedValue P r a σ y ∈ S := fun σ y hσ ↦ ⟨σ, y, hσ, rfl⟩
  have hSbdd : BddAbove S := by
    refine ⟨B + B, ?_⟩
    rintro _ ⟨σ, y, _, rfl⟩
    have h1 := hVs_le y
    have h2 := neg_le_of_abs_le (hV σ y)
    linarith
  set D := sSup S with hDdef
  have hleD : ∀ σ y, IsEpsIndexStarPolicy P r a ε σ →
      Vs y - markovBanditDiscountedValue P r a σ y ≤ D :=
    fun σ y hσ ↦ le_csSup hSbdd (hmemS σ y hσ)
  set c := ε / (1 - a) with hcdef
  have key : ∀ σ y, IsEpsIndexStarPolicy P r a ε σ → ∃ q : ℝ, 0 ≤ q ∧ q ≤ a ∧
      Vs y - markovBanditDiscountedValue P r a σ y ≤ c * (1 - q) + D * q := by
    intro σ y hσ
    obtain ⟨ρ, hρ, hsel⟩ := hσ
    obtain ⟨σ', hσ', hint2, hdec⟩ :=
      eps_index_star_value_first_stage P ⟨M0, hM0⟩ ha0 ha1 ρ hρ σ hsel y
    obtain ⟨hτ, hidx⟩ := hρ 0 (fun _ ↦ y)
    have hK1 := optimal_value_le_max_index_stage P ⟨M0, hM0⟩ ha0 ha1 y
      (ρ.arm 0 (fun _ ↦ y)) hτ
    set i := ρ.arm 0 (fun _ ↦ y) with hidef
    set τ := ρ.stop 0 (fun _ ↦ y) with hτdef
    set μ := markovChainMeasure P (y i) with hμdef
    haveI : IsProbabilityMeasure μ := by
      rw [hμdef]; unfold markovChainMeasure; infer_instance
    have hτm : Measurable τ := measurable_of_trajStoppingTime hτ.1
    set dp : (ℕ → T) → ℝ := fun ω ↦ discountPow a (τ ω) with hdpdef
    have hdpm : Measurable dp := (measurable_of_countable (discountPow a)).comp hτm
    have hdpb : ∀ ω, 0 ≤ dp ω ∧ dp ω ≤ a := fun ω ↦ discountPow_bounds ha0 ha1 _ (hτ.2 ω)
    have hdpint : Integrable dp μ :=
      Integrable.of_bound hdpm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hdpb ω).1]; linarith [(hdpb ω).2])
    set q := ∫ ω, dp ω ∂μ with hqdef
    have hpair : Measurable fun ω : ℕ → T ↦ (τ ω, ω (τ ω).toNat) := by
      refine hτm.prodMk ?_
      have hev : Measurable fun p : (ℕ → T) × ℕ∞ ↦ p.1 p.2.toNat :=
        measurable_from_prod_countable_left fun m ↦
          (measurable_pi_apply m.toNat : Measurable fun f : ℕ → T ↦ f m.toNat)
      exact hev.comp (measurable_id.prodMk hτm)
    have hg1m : Measurable fun ω : ℕ → T ↦
        dp ω * Vs (Function.update y i (ω (τ ω).toNat)) :=
      (measurable_of_countable (fun p : ℕ∞ × T ↦
        discountPow a p.1 * Vs (Function.update y i p.2))).comp hpair
    have hg1int : Integrable (fun ω : ℕ → T ↦
        dp ω * Vs (Function.update y i (ω (τ ω).toNat))) μ := by
      refine Integrable.of_bound hg1m.aestronglyMeasurable B
        (Filter.Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hdpb ω).1]
      have habs : |Vs (Function.update y i (ω (τ ω).toNat))| ≤ B :=
        abs_le.mpr ⟨hVs_ge _, hVs_le _⟩
      have : dp ω ≤ 1 := by linarith [(hdpb ω).2]
      calc dp ω * |Vs (Function.update y i (ω (τ ω).toNat))| ≤ 1 * B :=
            mul_le_mul this habs (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    have hW : stoppedTime P a τ (y i) = (1 - q) / (1 - a) := by
      unfold stoppedTime
      rw [show (fun ω ↦ discountedStoppedSum a (fun _ ↦ (1 : ℝ)) τ ω) =
          fun ω ↦ (1 - dp ω) / (1 - a) from
            funext fun ω ↦ discountedStoppedSum_one_eq ha0 ha1 τ ω]
      rw [integral_div, integral_sub (integrable_const 1) hdpint]
      simp [hqdef]
    have hq0 : 0 ≤ q := integral_nonneg fun ω ↦ (hdpb ω).1
    have hqa : q ≤ a := by
      have := integral_mono hdpint (integrable_const a) fun ω ↦ (hdpb ω).2
      simpa using this
    have hWpos : 0 < stoppedTime P a τ (y i) := by
      rw [hW]; exact div_pos (by linarith) h1a
    haveI : Nonempty (Fin k) := ⟨i⟩
    have hmax : (⨆ j, gittinsIndex P r a (y j)) ≤ stoppedRatio P r a τ (y i) + ε :=
      ciSup_le fun j ↦ by linarith [hidx j]
    have hRW : stoppedRatio P r a τ (y i) * stoppedTime P a τ (y i) =
        stoppedReward P r a τ (y i) := by
      unfold stoppedRatio; field_simp [hWpos.ne']
    have hdiff : (∫ ω, dp ω * Vs (Function.update y i (ω (τ ω).toNat)) ∂μ) -
        (∫ ω, dp ω * markovBanditDiscountedValue P r a (σ' ω)
          (Function.update y i (ω (τ ω).toNat)) ∂μ) ≤ D * q := by
      rw [← integral_sub hg1int hint2, hqdef, ← integral_const_mul]
      refine integral_mono (hg1int.sub hint2) (hdpint.const_mul D) fun ω ↦ ?_
      have h1 := hleD (σ' ω) (Function.update y i (ω (τ ω).toNat)) (hσ' ω)
      have h2 := (hdpb ω).1
      nlinarith
    refine ⟨q, hq0, hqa, ?_⟩
    have h2 := mul_le_mul_of_nonneg_right hmax hWpos.le
    have hcW : c * (1 - q) = ε * stoppedTime P a τ (y i) := by
      rw [hW, hcdef]; field_simp
    rw [hdec]
    have hK1' : Vs y ≤ (⨆ j, gittinsIndex P r a (y j)) * stoppedTime P a τ (y i) +
        ∫ ω, dp ω * Vs (Function.update y i (ω (τ ω).toNat)) ∂μ := hK1
    nlinarith
  have hD : D ≤ c := by
    by_contra hlt
    push Not at hlt
    have hDle : D ≤ c + a * (D - c) := by
      refine csSup_le ⟨_, hmemS π x hπ⟩ ?_
      rintro d ⟨σ, y, hσ, rfl⟩
      obtain ⟨q, hq0, hqa, h⟩ := key σ y hσ
      nlinarith [mul_nonneg (sub_nonneg.mpr hqa) (sub_nonneg.mpr hlt.le)]
    nlinarith
  have := hleD π x hπ
  show Vs x - c ≤ _
  linarith
