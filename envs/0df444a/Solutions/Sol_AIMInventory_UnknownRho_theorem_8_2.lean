-- Prove2me | solution 2 for AIMInventory.UnknownRho.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:28:35.211631+00:00
-- url     : https://prove2.me/submissions/52301ebd-b575-449e-8d3e-7cce042f1562

import Mathlib
import Definitions.Def_AIMInventory_UnknownRho_Model
import Theorems.Thm_AIMInventory_UnknownRho_restart_bound

-- carved verbatim out of submission 0706a959-4aa7-4a3d-815b-4d4823e8c718, lines 858-869

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open scoped ENNReal NNReal BigOperators
open AIMInventory
open AIMInventory.UnknownRho

lemma shift_map (P : DemandLaw) (k : ℕ) :
    Measure.map (fun (d : DemandPath) (n : ℕ) => d (n + k)) (CappedBaseStock.demandPathLaw P)
      = CappedBaseStock.demandPathLaw P := by
  unfold CappedBaseStock.demandPathLaw
  refine Measure.eq_infinitePi (fun _ : ℕ => P.law) ?_
  intro s t ht
  have hm : Measurable (fun (d : DemandPath) (n : ℕ) => d (n + k)) :=
    measurable_pi_lambda _ (fun n => measurable_pi_apply _)
  have hpre : (fun (d : DemandPath) (n : ℕ) => d (n + k)) ⁻¹' (Set.pi (↑s) t)
      = Set.pi (↑(s.image (fun i => i + k))) (fun j => t (j - k)) := by
    ext d
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro h j ⟨i, hi, rfl⟩
      have := h i hi
      rwa [Nat.add_sub_cancel]
    · intro h i hi
      have := h (i + k) ⟨i, hi, rfl⟩
      rwa [Nat.add_sub_cancel] at this
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)), hpre,
    Measure.infinitePi_pi _ (fun j _ => ht _)]
  rw [Finset.prod_image (by intro a _ b _ h; simpa using h)]
  exact Finset.prod_congr rfl (fun i _ => by rw [Nat.add_sub_cancel])

lemma measurable_W (θ : ℝ) (t : ℕ) : Measurable (fun d : DemandPath => W d θ t) := by
  induction t with
  | zero => simp [W]
  | succ t ih =>
    by_cases ht : t = 0
    · simp [W, ht]
    · simp only [W, ht, if_false]
      fun_prop

lemma firstBusyLength_eq (d : DemandPath) (θ : ℝ) :
    firstBusyLength d θ = ⨅ n : ℕ, if 1 ≤ n ∧ W d θ (n + 1) = 0 then (n : ℝ≥0∞) else ⊤ := by
  apply le_antisymm
  · refine le_iInf (fun n => ?_)
    split_ifs with h
    · exact sInf_le ⟨n, h.1, rfl, h.2⟩
    · exact le_top
  · refine le_sInf ?_
    rintro u ⟨n, h1, rfl, h⟩
    exact iInf_le_of_le n (by simp [h1, h])

lemma measurable_firstBusyLength (θ : ℝ) : Measurable (fun d : DemandPath => firstBusyLength d θ) := by
  simp_rw [firstBusyLength_eq]
  refine Measurable.iInf (fun n => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  have h : MeasurableSet {d : DemandPath | W d θ (n + 1) = 0} :=
    measurableSet_eq_fun (measurable_W θ (n+1)) measurable_const
  by_cases h1 : 1 ≤ n
  · simpa [h1] using h
  · simp [h1]

lemma lintegral_shift (P : DemandLaw) (k : ℕ) {f : DemandPath → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ d, f (fun n => d (n + k)) ∂CappedBaseStock.demandPathLaw P
      = ∫⁻ d, f d ∂CappedBaseStock.demandPathLaw P := by
  have hm : Measurable (fun (d : DemandPath) (n : ℕ) => d (n + k)) :=
    measurable_pi_lambda _ (fun n => measurable_pi_apply _)
  conv_rhs => rw [← shift_map P k]
  rw [lintegral_map hf hm]

lemma Z_nonneg (d : DemandPath) (θ : ℝ) : ∀ t, 0 ≤ Z d θ t
  | 0 => by simp [Z]
  | t + 1 => by
    simp only [Z]
    split_ifs
    · exact le_rfl
    · exact le_max_right _ _

lemma Z_succ (d : DemandPath) (θ : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    Z d θ (t + 1) = max (Z d θ t + θ / Real.sqrt (t : ℝ) - (d (t - 1) : ℝ)) 0 := by
  have : t ≠ 0 := by omega
  simp [Z, this]

lemma W_succ (d : DemandPath) (θ : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    W d θ (t + 1) = max (W d θ t + θ - (d (t - 1) : ℝ)) 0 := by
  have : t ≠ 0 := by omega
  simp [W, this]

lemma sqrt_step (t : ℕ) :
    1 / Real.sqrt ((t : ℝ) + 1) ≤ 2 * Real.sqrt ((t : ℝ) + 1) - 2 * Real.sqrt (t : ℝ) := by
  have hb : 0 < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have ha : 0 ≤ Real.sqrt (t : ℝ) := Real.sqrt_nonneg _
  have ha2 : Real.sqrt (t : ℝ) ^ 2 = t := Real.sq_sqrt (by positivity)
  have hb2 : Real.sqrt ((t : ℝ) + 1) ^ 2 = t + 1 := Real.sq_sqrt (by positivity)
  rw [div_le_iff₀ hb]
  nlinarith [sq_nonneg (Real.sqrt ((t : ℝ) + 1) - Real.sqrt (t : ℝ))]

lemma m_pos (c : Parameters) : 0 < m c := by
  unfold m
  have : 0 < max c.b c.h := lt_max_of_lt_left c.b_pos
  have := c.h_pos; have := c.gamma_pos; have := c.barY_pos
  positivity

lemma threshold_eq (c : Parameters) (ρ' : ℝ) (hρ : 0 < ρ') (hsmall : ρ' < m c) :
    threshold c ρ' = Nat.ceil ((m c / ρ') ^ 2) := by
  have h1 : 1 < m c / ρ' := by rw [lt_div_iff₀ hρ]; linarith
  have h2 : (1 : ℝ) < (m c / ρ') ^ 2 := by nlinarith
  have : 1 ≤ Nat.ceil ((m c / ρ') ^ 2) := Nat.one_le_iff_ne_zero.mpr
    (by intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  unfold threshold
  exact max_eq_right this

lemma threshold_pos (c : Parameters) (ρ' : ℝ) : 1 ≤ threshold c ρ' := le_max_left _ _

lemma Z_le_inflow (d : DemandPath) {θ : ℝ} (hθ : 0 ≤ θ) {s : ℕ} (hs : 1 ≤ s) (h0 : Z d θ s = 0) :
    ∀ j : ℕ, Z d θ (s + j) ≤ j * (θ / Real.sqrt (s : ℝ)) := by
  intro j
  induction j with
  | zero => simp [h0]
  | succ j ih =>
    have e : s + (j + 1) = (s + j) + 1 := by ring
    rw [e, Z_succ d _ (by omega)]
    have h1 : θ / Real.sqrt ((s + j : ℕ) : ℝ) ≤ θ / Real.sqrt (s : ℝ) := by
      apply div_le_div_of_nonneg_left hθ (Real.sqrt_pos.mpr (by exact_mod_cast hs))
      exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_add_right s j)
    have h2 : (0 : ℝ) ≤ d (s + j - 1) := NNReal.coe_nonneg _
    have h3 : 0 ≤ θ / Real.sqrt (s : ℝ) := by positivity
    have hc : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    have hexp : ((j : ℝ) + 1) * (θ / Real.sqrt (s : ℝ)) = j * (θ / Real.sqrt (s : ℝ)) + θ / Real.sqrt (s : ℝ) := by ring
    rw [hc]
    refine max_le ?_ (by positivity)
    linarith

lemma Z_le_W (c : Parameters) (d : DemandPath) (ρ' : ℝ) (hρ : 0 < ρ') (hsmall : ρ' < m c)
    {s : ℕ} (hs : threshold c ρ' ≤ s) (h0 : Z d (m c) s = 0) :
    ∀ j : ℕ, Z d (m c) (s + j) ≤ W (fun n => d (n + (s - 1))) ρ' (j + 1) := by
  have hs1 : 1 ≤ s := le_trans (threshold_pos c ρ') hs
  have hrate : ∀ t : ℕ, s ≤ t → m c / Real.sqrt (t : ℝ) ≤ ρ' := by
    intro t ht
    have hTx : (m c / ρ') ^ 2 ≤ (s : ℝ) := by
      have : (m c / ρ') ^ 2 ≤ (threshold c ρ' : ℝ) := by
        rw [threshold_eq c ρ' hρ hsmall]; exact Nat.le_ceil _
      exact this.trans (by exact_mod_cast hs)
    have h1 : m c / ρ' ≤ Real.sqrt (t : ℝ) :=
      Real.le_sqrt_of_sq_le (hTx.trans (by exact_mod_cast ht))
    have hm := m_pos c
    have hpos : 0 < Real.sqrt (t : ℝ) := lt_of_lt_of_le (by positivity) h1
    rw [div_le_iff₀ hpos]
    rw [div_le_iff₀ hρ] at h1
    linarith
  intro j
  induction j with
  | zero => simp [h0, W]
  | succ j ih =>
    have e : s + (j + 1) = (s + j) + 1 := by ring
    rw [e, Z_succ d _ (by omega), W_succ _ _ (by omega)]
    have hd : (d (s + j - 1) : ℝ) = ((fun n => d (n + (s - 1))) (j + 1 - 1) : ℝ) := by
      show (d (s + j - 1) : ℝ) = (d (j + 1 - 1 + (s - 1)) : ℝ)
      congr 2; omega
    rw [hd]
    have := hrate (s + j) (by omega)
    exact max_le_max (by linarith) le_rfl

lemma firstBusyLength_cases (d : DemandPath) (θ : ℝ) :
    firstBusyLength d θ = ⊤ ∨ ∃ n : ℕ, firstBusyLength d θ = n := by
  classical
  by_cases hex : ∃ n : ℕ, 1 ≤ n ∧ W d θ (n + 1) = 0
  · right
    refine ⟨Nat.find hex, le_antisymm ?_ ?_⟩
    · exact sInf_le ⟨Nat.find hex, (Nat.find_spec hex).1, rfl, (Nat.find_spec hex).2⟩
    · refine le_sInf ?_
      rintro u ⟨n, h1, rfl, h⟩
      exact_mod_cast Nat.find_min' hex ⟨h1, h⟩
  · left
    unfold firstBusyLength
    have : {u : ℝ≥0∞ | ∃ n : ℕ, 1 ≤ n ∧ u = (n : ℝ≥0∞) ∧ W d θ (n + 1) = 0} = ∅ := by
      ext u; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨n, h1, -, h⟩; exact hex ⟨n, h1, h⟩
    rw [this]; exact sInf_empty

lemma sum_inv_sqrt_le (T : ℕ) :
    ∑ s ∈ Finset.Icc 1 T, 1 / Real.sqrt (s : ℝ) ≤ 2 * Real.sqrt (T : ℝ) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := sqrt_step T
    push_cast
    linarith

lemma pointwise_claim (c : Parameters) (ρ' : ℝ) (hρ : 0 < ρ') (hsmall : ρ' < m c) (T : ℕ)
    (d : DemandPath) :
    ∑ t ∈ Finset.Icc 1 T, (if restartTime c ρ' d < (t : ℝ≥0∞) then ENNReal.ofReal (Z d (m c) t) else 0)
      ≤ ∑ s ∈ Finset.Icc 1 T, ENNReal.ofReal (m c / Real.sqrt (s : ℝ)) *
          (firstBusyLength (fun n => d (n + (s - 1))) ρ') ^ 2 := by
  classical
  have hm := m_pos c
  let B : ℕ → ℝ≥0∞ := fun s => firstBusyLength (fun n => d (n + (s - 1))) ρ'
  let g : ℕ → ℕ → ℝ≥0∞ := fun t s =>
    if (s < t ∧ Z d (m c) s = 0 ∧ threshold c ρ' < s ∧ ((t - s : ℕ) : ℝ≥0∞) < B s) then
      ENNReal.ofReal (m c / Real.sqrt (s : ℝ)) * ((t - s : ℕ) : ℝ≥0∞) else 0
  -- Step 1
  have step1 : ∀ t ∈ Finset.Icc 1 T,
      (if restartTime c ρ' d < (t : ℝ≥0∞) then ENNReal.ofReal (Z d (m c) t) else 0)
        ≤ ∑ s ∈ Finset.Icc 1 T, g t s := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    by_cases hr : restartTime c ρ' d < (t : ℝ≥0∞)
    · rw [if_pos hr]
      obtain ⟨u, ⟨t0, hthr, rfl, hZ0⟩, hu⟩ := sInf_lt_iff.mp hr
      have ht0 : t0 < t := by exact_mod_cast hu
      by_cases hZt : Z d (m c) t = 0
      · rw [hZt]; simp
      have hZtpos : 0 < Z d (m c) t := lt_of_le_of_ne (Z_nonneg _ _ _) (Ne.symm hZt)
      let P : ℕ → Prop := fun s => threshold c ρ' < s ∧ Z d (m c) s = 0
      have hP0 : P t0 := ⟨hthr, hZ0⟩
      set s := Nat.findGreatest P t with hsdef
      have hs_ge : t0 ≤ s := Nat.le_findGreatest ht0.le hP0
      have hPs : P s := Nat.findGreatest_spec (P := P) ht0.le hP0
      have hs_le : s ≤ t := Nat.findGreatest_le t
      have hst : s < t := by
        rcases lt_or_eq_of_le hs_le with h | h
        · exact h
        · exfalso; rw [h] at hPs; exact hZt hPs.2
      have hbetween : ∀ u, s < u → u ≤ t → 0 < Z d (m c) u := by
        intro u hsu hut
        have := Nat.findGreatest_is_greatest (P := P) hsu hut
        have hthu : threshold c ρ' < u := lt_of_lt_of_le hPs.1 hsu.le
        have : Z d (m c) u ≠ 0 := fun h => this ⟨hthu, h⟩
        exact lt_of_le_of_ne (Z_nonneg _ _ _) (Ne.symm this)
      have hs1 : 1 ≤ s := le_trans (threshold_pos c ρ') hPs.1.le
      -- the busy period is longer than t - s
      have hB : ((t - s : ℕ) : ℝ≥0∞) < B s := by
        by_contra hcon
        push_neg at hcon
        have hlt : B s < (((t - s : ℕ) : ℝ≥0∞) + 1) :=
          lt_of_le_of_lt hcon (by
            rw [← ENNReal.coe_natCast]
            exact ENNReal.lt_add_right (by simp) one_ne_zero)
        obtain ⟨v, ⟨n, hn1, rfl, hW⟩, hv⟩ := sInf_lt_iff.mp (show sInf _ < _ from hlt)
        have hnle : n ≤ t - s := by
          have : (n : ℝ≥0∞) < ((t - s : ℕ) : ℝ≥0∞) + 1 := hv
          have : (n : ℝ≥0∞) < ((t - s + 1 : ℕ) : ℝ≥0∞) := by rw [Nat.cast_succ]; exact this
          have := Nat.cast_lt.mp this
          omega
        have hzw := Z_le_W c d ρ' hρ hsmall (le_of_lt hPs.1) hPs.2 n
        rw [hW] at hzw
        have := hbetween (s + n) (by omega) (by omega)
        linarith
      have hZle := Z_le_inflow d hm.le hs1 hPs.2 (t - s)
      have e : s + (t - s) = t := by omega
      rw [e] at hZle
      have hterm : ENNReal.ofReal (Z d (m c) t) ≤ g t s := by
        simp only [g]
        rw [if_pos ⟨hst, hPs.2, hPs.1, hB⟩]
        calc ENNReal.ofReal (Z d (m c) t)
            ≤ ENNReal.ofReal (((t - s : ℕ) : ℝ) * (m c / Real.sqrt (s : ℝ))) :=
              ENNReal.ofReal_le_ofReal hZle
          _ = ENNReal.ofReal (m c / Real.sqrt (s : ℝ)) * ((t - s : ℕ) : ℝ≥0∞) := by
              rw [mul_comm, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      exact hterm.trans (Finset.single_le_sum (f := fun s => g t s) (fun _ _ => zero_le)
        (Finset.mem_Icc.mpr ⟨hs1, by omega⟩))
    · rw [if_neg hr]; exact zero_le
  -- Step 2
  have step2 : ∀ s ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T, g t s
      ≤ ENNReal.ofReal (m c / Real.sqrt (s : ℝ)) * (B s) ^ 2 := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    have hpos : ENNReal.ofReal (m c / Real.sqrt (s : ℝ)) ≠ 0 := by
      have : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hs.1)
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    rcases firstBusyLength_cases (fun n => d (n + (s - 1))) ρ' with hB | ⟨n, hn⟩
    · have : B s = ⊤ := hB
      rw [this]
      simp [ENNReal.mul_top hpos]
    · have hBn : B s = (n : ℝ≥0∞) := hn
      have hg : ∀ t, g t s = ENNReal.ofReal (m c / Real.sqrt (s : ℝ)) *
          (if (s < t ∧ Z d (m c) s = 0 ∧ threshold c ρ' < s ∧ t - s < n) then
            ((t - s : ℕ) : ℝ≥0∞) else 0) := by
        intro t
        simp only [g, hBn, Nat.cast_lt]
        split_ifs <;> simp
      simp_rw [hg, ← Finset.mul_sum]
      gcongr
      have hnat : ∑ t ∈ Finset.Icc 1 T, (if (s < t ∧ Z d (m c) s = 0 ∧ threshold c ρ' < s ∧ t - s < n) then
            ((t - s : ℕ) : ℝ≥0∞) else 0)
          ≤ ((n * n : ℕ) : ℝ≥0∞) := by
        have hcast : (∑ t ∈ Finset.Icc 1 T, (if (s < t ∧ Z d (m c) s = 0 ∧ threshold c ρ' < s ∧ t - s < n) then
            ((t - s : ℕ) : ℝ≥0∞) else 0)) = ((∑ t ∈ Finset.Icc 1 T,
              (if (s < t ∧ Z d (m c) s = 0 ∧ threshold c ρ' < s ∧ t - s < n) then (t - s) else 0) : ℕ) : ℝ≥0∞) := by
          rw [Nat.cast_sum]
          refine Finset.sum_congr rfl (fun t _ => ?_)
          split_ifs <;> simp
        rw [hcast]
        have hnat2 : (∑ t ∈ Finset.Icc 1 T,
              (if (s < t ∧ Z d (m c) s = 0 ∧ threshold c ρ' < s ∧ t - s < n) then (t - s) else 0)) ≤ n * n := by
          calc _ ≤ ∑ t ∈ Finset.Ioo s (s + n),
              (if (s < t ∧ Z d (m c) s = 0 ∧ threshold c ρ' < s ∧ t - s < n) then (t - s) else 0) := by
                apply Finset.sum_le_sum_of_ne_zero
                intro t _ hne
                by_contra hnot
                apply hne
                rw [Finset.mem_Ioo] at hnot
                rw [if_neg]
                rintro ⟨h1, -, -, h4⟩
                exact hnot ⟨h1, by omega⟩
            _ ≤ (Finset.Ioo s (s + n)).card • n := by
                apply Finset.sum_le_card_nsmul
                intro t _
                split_ifs with h
                · exact h.2.2.2.le
                · exact Nat.zero_le _
            _ ≤ n * n := by
                rw [smul_eq_mul, Nat.card_Ioo]
                exact Nat.mul_le_mul_right _ (by omega)
        exact_mod_cast hnat2
      calc _ ≤ ((n * n : ℕ) : ℝ≥0∞) := hnat
        _ = (B s) ^ 2 := by rw [hBn]; push_cast; ring
  calc _ ≤ ∑ t ∈ Finset.Icc 1 T, ∑ s ∈ Finset.Icc 1 T, g t s := Finset.sum_le_sum step1
    _ = ∑ s ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T, g t s := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum step2

theorem claim14_core (P : DemandLaw) (c : Parameters) (ρ' : ℝ) (T : ℕ)
    (hT : 1 ≤ T) (hρ : 0 < ρ') (hsmall : ρ' < m c) :
    ENNReal.ofReal (c.h / (T : ℝ)) *
      (∫⁻ d, ∑ t ∈ Finset.Icc 1 T,
        if restartTime c ρ' d < (t : ℝ≥0∞) then
          ENNReal.ofReal (Z d (m c) t) else 0
        ∂CappedBaseStock.demandPathLaw P) ≤
      ENNReal.ofReal (2 * c.h * m c / Real.sqrt (T : ℝ)) *
        busySecondMoment P ρ' := by
  have hm := m_pos c
  have hbm : Measurable (fun e : DemandPath => (firstBusyLength e ρ') ^ 2) :=
    (measurable_firstBusyLength ρ').pow_const 2
  have hint : (∫⁻ d, ∑ t ∈ Finset.Icc 1 T,
        (if restartTime c ρ' d < (t : ℝ≥0∞) then ENNReal.ofReal (Z d (m c) t) else 0)
        ∂CappedBaseStock.demandPathLaw P) ≤
      ENNReal.ofReal (2 * m c * Real.sqrt (T : ℝ)) * busySecondMoment P ρ' := by
    calc _ ≤ ∫⁻ d, ∑ s ∈ Finset.Icc 1 T, ENNReal.ofReal (m c / Real.sqrt (s : ℝ)) *
          (firstBusyLength (fun n => d (n + (s - 1))) ρ') ^ 2 ∂CappedBaseStock.demandPathLaw P :=
          lintegral_mono (fun d => pointwise_claim c ρ' hρ hsmall T d)
      _ = ∑ s ∈ Finset.Icc 1 T, ENNReal.ofReal (m c / Real.sqrt (s : ℝ)) * busySecondMoment P ρ' := by
          rw [lintegral_finset_sum]
          · refine Finset.sum_congr rfl (fun s _ => ?_)
            rw [lintegral_const_mul]
            · congr 1
              exact lintegral_shift P (s - 1) hbm
            · exact (hbm.comp (measurable_pi_lambda _ (fun n => measurable_pi_apply _)))
          · intro s _
            refine Measurable.const_mul ?_ _
            exact (hbm.comp (measurable_pi_lambda _ (fun n => measurable_pi_apply _)))
      _ = ENNReal.ofReal (∑ s ∈ Finset.Icc 1 T, m c / Real.sqrt (s : ℝ)) * busySecondMoment P ρ' := by
          rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun s _ => by positivity)]
      _ ≤ _ := by
          gcongr
          have := sum_inv_sqrt_le T
          calc ∑ s ∈ Finset.Icc 1 T, m c / Real.sqrt (s : ℝ)
              = m c * ∑ s ∈ Finset.Icc 1 T, 1 / Real.sqrt (s : ℝ) := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun s _ => by ring)
            _ ≤ m c * (2 * Real.sqrt (T : ℝ)) := mul_le_mul_of_nonneg_left this hm.le
            _ = 2 * m c * Real.sqrt (T : ℝ) := by ring
  calc ENNReal.ofReal (c.h / (T : ℝ)) * _ ≤ ENNReal.ofReal (c.h / (T : ℝ)) *
        (ENNReal.ofReal (2 * m c * Real.sqrt (T : ℝ)) * busySecondMoment P ρ') := by
        gcongr
    _ = ENNReal.ofReal (2 * c.h * m c / Real.sqrt (T : ℝ)) * busySecondMoment P ρ' := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by have := c.h_pos; positivity)]
        congr 2
        have hs : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hT)
        have hs2 : Real.sqrt (T : ℝ) ^ 2 = T := Real.sq_sqrt (by positivity)
        have hT0 : (T : ℝ) ≠ 0 := by positivity
        field_simp
        rw [hs2]

lemma measurable_Z (θ : ℝ) (t : ℕ) : Measurable (fun d : DemandPath => Z d θ t) := by
  induction t with
  | zero => simp [Z]
  | succ t ih =>
    by_cases ht : t = 0
    · simp [Z, ht]
    · simp only [Z, ht, if_false]
      fun_prop

lemma restartTime_eq (c : Parameters) (ρ' : ℝ) (d : DemandPath) :
    restartTime c ρ' d = ⨅ t : ℕ, if threshold c ρ' < t ∧ Z d (m c) t = 0 then (t : ℝ≥0∞) else ⊤ := by
  apply le_antisymm
  · refine le_iInf (fun n => ?_)
    split_ifs with h
    · exact sInf_le ⟨n, h.1, rfl, h.2⟩
    · exact le_top
  · refine le_sInf ?_
    rintro u ⟨n, h1, rfl, h⟩
    exact iInf_le_of_le n (by rw [if_pos ⟨h1, h⟩])

lemma measurable_restartTime (c : Parameters) (ρ' : ℝ) :
    Measurable (fun d : DemandPath => restartTime c ρ' d) := by
  simp_rw [restartTime_eq]
  refine Measurable.iInf (fun n => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  have h : MeasurableSet {d : DemandPath | Z d (m c) n = 0} :=
    measurableSet_eq_fun (measurable_Z _ n) measurable_const
  by_cases h1 : threshold c ρ' < n
  · simpa [h1] using h
  · simp [h1]

lemma ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hf : Integrable f μ
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
    calc ENNReal.ofReal ((∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal - (∫⁻ x, ENNReal.ofReal (-f x) ∂μ).toReal)
        ≤ ENNReal.ofReal ((∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal) :=
          ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := ∫⁻ x, ENNReal.ofReal (-f x) ∂μ)])
      _ ≤ _ := ENNReal.ofReal_toReal_le
  · rw [integral_undef hf]; simp

lemma count_le (T : ℕ) (K : ℝ≥0∞) :
    ∑ t ∈ Finset.Icc 1 T, (if (t : ℝ≥0∞) ≤ K then (1 : ℝ≥0∞) else 0) ≤ K := by
  classical
  rw [Finset.sum_boole]
  induction K using ENNReal.recTopCoe with
  | top => exact le_top
  | coe r =>
    have hsub : (Finset.Icc 1 T).filter (fun t : ℕ => (t : ℝ≥0∞) ≤ (r : ℝ≥0∞)) ⊆ Finset.Icc 1 ⌊r⌋₊ := by
      intro t ht
      rw [Finset.mem_filter, Finset.mem_Icc] at ht
      rw [Finset.mem_Icc]
      refine ⟨ht.1.1, Nat.le_floor ?_⟩
      have : ((t : ℝ≥0) : ℝ≥0∞) ≤ r := by simpa using ht.2
      exact_mod_cast this
    calc (((Finset.Icc 1 T).filter (fun t : ℕ => (t : ℝ≥0∞) ≤ (r : ℝ≥0∞))).card : ℝ≥0∞)
        ≤ ((Finset.Icc 1 ⌊r⌋₊).card : ℝ≥0∞) := by exact_mod_cast Finset.card_le_card hsub
      _ = (⌊r⌋₊ : ℝ≥0∞) := by simp
      _ ≤ r := by
          have : ((⌊r⌋₊ : ℝ≥0) : ℝ≥0∞) ≤ r := by exact_mod_cast Nat.floor_le (zero_le)
          simpa using this

lemma integrable_holding (P : DemandLaw) (S : ℝ) :
    Integrable (fun d : ℝ≥0 => max (S - (d : ℝ)) 0) P.law := by
  refine Integrable.mono' (integrable_const (max S 0)) ?_ ?_
  · exact (by fun_prop : Continuous fun d : ℝ≥0 => max (S - (d : ℝ)) 0).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le_max (by linarith [NNReal.coe_nonneg d]) le_rfl

lemma integrable_shortfall (P : DemandLaw) (S : ℝ) :
    Integrable (fun d : ℝ≥0 => max ((d : ℝ) - S) 0) P.law := by
  refine Integrable.mono' (P.finiteMean.add (integrable_const |S|)) ?_ ?_
  · exact (by fun_prop : Continuous fun d : ℝ≥0 => max ((d : ℝ) - S) 0).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    simp only [Pi.add_apply]
    refine max_le ?_ (by positivity)
    linarith [neg_abs_le S, le_abs_self S, NNReal.coe_nonneg d]

lemma Q_diff_le (P : DemandLaw) (c : Parameters) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    Q P c v - Q P c u ≤ c.h * (v - u) := by
  have hv : 0 ≤ v := hu.trans huv
  unfold Q LostSalesOrderUpTo.Asymptotic.backorderCost LostSalesOrderUpTo.Asymptotic.expectedHolding
    LostSalesOrderUpTo.Asymptotic.expectedShortfall
  simp only [Real.coe_toNNReal _ hu, Real.coe_toNNReal _ hv]
  have h1 : ∫ d : ℝ≥0, max (v - (d : ℝ)) 0 ∂P.law - ∫ d : ℝ≥0, max (u - (d : ℝ)) 0 ∂P.law ≤ v - u := by
    rw [← integral_sub (integrable_holding P v) (integrable_holding P u)]
    have : ∫ d : ℝ≥0, (v - u) ∂P.law = v - u := by simp
    rw [← this]
    refine integral_mono ((integrable_holding P v).sub (integrable_holding P u)) (integrable_const _) ?_
    intro d
    simp only
    have := le_max_left (u - (d : ℝ)) 0
    have := le_max_right (u - (d : ℝ)) 0
    have : max (v - (d : ℝ)) 0 ≤ max (u - (d : ℝ)) 0 + (v - u) := max_le (by linarith) (by linarith)
    linarith
  have h2 : ∫ d : ℝ≥0, max ((d : ℝ) - v) 0 ∂P.law ≤ ∫ d : ℝ≥0, max ((d : ℝ) - u) 0 ∂P.law := by
    refine integral_mono (integrable_shortfall P v) (integrable_shortfall P u) (fun d => ?_)
    exact max_le_max (by linarith) le_rfl
  have := c.h_pos; have := c.b_pos
  nlinarith

lemma step_mul (c : Parameters) (n : ℕ) :
    stepSize c (n + 1) * c.h = m c / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  have hmax : 0 < max c.b c.h := lt_max_of_lt_left c.b_pos
  have hs : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  unfold stepSize m
  field_simp

lemma stepSize_nonneg (c : Parameters) (n : ℕ) : 0 ≤ stepSize c (n + 1) := by
  have := c.gamma_pos; have := c.barY_pos
  have hmax : 0 < max c.b c.h := lt_max_of_lt_left c.b_pos
  unfold stepSize
  positivity

lemma target_lower (c : Parameters) (d : DemandPath) (n : ℕ)
    (h0 : 0 ≤ (aimState c d n).1) (h1 : (aimState c d n).1 ≤ c.barY) :
    (aimState c d n).1 - m c / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ (aimState c d (n + 1)).1 := by
  have hm := m_pos c
  have hr : 0 ≤ m c / Real.sqrt ((n + 1 : ℕ) : ℝ) := by positivity
  have hstep := stepSize_nonneg c n
  show _ ≤ max (min ((aimState c d n).1 - stepSize c (n + 1) *
        observedSlope c (aimState c d n).1 (d n)) c.barY) 0
  by_cases hd : (d n : ℝ) < (aimState c d n).1
  · simp only [observedSlope, hd, if_true]
    rw [step_mul]
    refine le_max_of_le_left (le_min le_rfl ?_)
    linarith
  · simp only [observedSlope, hd, if_false]
    have := c.b_pos
    refine le_max_of_le_left (le_min ?_ ?_)
    · nlinarith
    · linarith

lemma aim_inv (c : Parameters) (d : DemandPath) : ∀ n : ℕ,
    0 ≤ (aimState c d n).1 ∧ (aimState c d n).1 ≤ c.barY ∧
    0 ≤ (aimState c d n).2.2 ∧ (aimState c d n).2.2 ≤ c.barY ∧
    (aimState c d n).2.1 = max (aimState c d n).1 (aimState c d n).2.2 ∧
    (aimState c d n).2.2 - (aimState c d n).1 ≤ Z d (m c) (n + 1) ∧
    0 ≤ Z d (m c) (n + 1) := by
  intro n
  induction n with
  | zero =>
    refine ⟨c.initial_nonneg, c.initial_le, le_rfl, c.barY_pos.le, ?_, ?_, ?_⟩
    · show c.initial = max c.initial 0
      exact (max_eq_left c.initial_nonneg).symm
    · show (0 : ℝ) - c.initial ≤ Z d (m c) 1
      have : Z d (m c) 1 = 0 := by simp [Z]
      rw [this]; linarith [c.initial_nonneg]
    · exact Z_nonneg _ _ _
  | succ n ih =>
    obtain ⟨hτ0, hτ1, hx0, hx1, hl, he, hZ⟩ := ih
    have hy := c.barY_pos
    have hlow := target_lower c d n hτ0 hτ1
    have hτ'0 : 0 ≤ (aimState c d (n + 1)).1 := le_max_right _ _
    have hτ'1 : (aimState c d (n + 1)).1 ≤ c.barY := max_le (min_le_right _ _) hy.le
    have hx'0 : 0 ≤ (aimState c d (n + 1)).2.2 := le_max_right _ _
    have hlev : (aimState c d n).2.1 ≤ c.barY := by rw [hl]; exact max_le hτ1 hx1
    have hdn : (0 : ℝ) ≤ d n := NNReal.coe_nonneg _
    have hx'1 : (aimState c d (n + 1)).2.2 ≤ c.barY := max_le (by linarith) hy.le
    have hZn := Z_succ d (m c) (t := n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hZn
    refine ⟨hτ'0, hτ'1, hx'0, hx'1, rfl, ?_, Z_nonneg _ _ _⟩
    rw [hZn]
    show max ((aimState c d n).2.1 - (d n : ℝ)) 0 - (aimState c d (n + 1)).1 ≤ _
    have hlτ : (aimState c d n).2.1 - (aimState c d n).1 ≤ Z d (m c) (n + 1) := by
      rw [hl]
      rcases le_total (aimState c d n).1 (aimState c d n).2.2 with h | h
      · rw [max_eq_right h]; exact he
      · rw [max_eq_left h]; linarith
    rcases le_total ((aimState c d n).2.1 - (d n : ℝ)) 0 with h | h
    · rw [max_eq_right h]
      refine le_trans ?_ (le_max_right _ _)
      linarith
    · rw [max_eq_left h]
      refine le_trans ?_ (le_max_left _ _)
      push_cast at hlow ⊢; linarith

lemma aim_term_bound (P : DemandLaw) (c : Parameters) (d : DemandPath) {t : ℕ} (ht : 1 ≤ t) :
    Q P c (aimLevel c d t) - Q P c (aimTarget c d t) ≤ c.h * Z d (m c) t ∧
    Q P c (aimLevel c d t) - Q P c (aimTarget c d t) ≤ max c.b c.h * c.barY := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  obtain ⟨hτ0, hτ1, hx0, hx1, hl, he, hZ⟩ := aim_inv c d n
  have hlev : aimLevel c d (n + 1) = (aimState c d n).2.1 := by simp [aimLevel]
  have htar : aimTarget c d (n + 1) = (aimState c d n).1 := by simp [aimTarget]
  rw [hlev, htar]
  have huv : (aimState c d n).1 ≤ (aimState c d n).2.1 := by rw [hl]; exact le_max_left _ _
  have hQ := Q_diff_le P c hτ0 huv
  have hvZ : (aimState c d n).2.1 - (aimState c d n).1 ≤ Z d (m c) (n + 1) := by
    rw [hl]
    rcases le_total (aimState c d n).1 (aimState c d n).2.2 with h | h
    · rw [max_eq_right h]; exact he
    · rw [max_eq_left h]; linarith
  have hvy : (aimState c d n).2.1 - (aimState c d n).1 ≤ c.barY := by
    rw [hl]
    have : max (aimState c d n).1 (aimState c d n).2.2 ≤ c.barY := max_le hτ1 hx1
    linarith
  have hh := c.h_pos
  refine ⟨hQ.trans (mul_le_mul_of_nonneg_left hvZ hh.le), hQ.trans ?_⟩
  calc c.h * ((aimState c d n).2.1 - (aimState c d n).1) ≤ c.h * c.barY :=
        mul_le_mul_of_nonneg_left hvy hh.le
    _ ≤ max c.b c.h * c.barY :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) c.barY_pos.le

lemma aim_pointwise (P : DemandLaw) (c : Parameters) (ρ' : ℝ) (T : ℕ) (hT : 1 ≤ T) (d : DemandPath) :
    ENNReal.ofReal ((T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T,
        (Q P c (aimLevel c d t) - Q P c (aimTarget c d t)))
      ≤ ENNReal.ofReal (max c.b c.h * c.barY / (T : ℝ)) * restartTime c ρ' d +
        ENNReal.ofReal (c.h / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
          (if restartTime c ρ' d < (t : ℝ≥0∞) then ENNReal.ofReal (Z d (m c) t) else 0) := by
  classical
  have hh := c.h_pos
  have hmax : 0 < max c.b c.h := lt_max_of_lt_left c.b_pos
  have hy := c.barY_pos
  set M := max c.b c.h * c.barY with hM
  have hMpos : 0 ≤ M := by positivity
  let g : ℕ → ℝ := fun t => if restartTime c ρ' d < (t : ℝ≥0∞) then c.h * Z d (m c) t else M
  have hg0 : ∀ t, 0 ≤ g t := by
    intro t; simp only [g]; split_ifs
    · exact mul_nonneg hh.le (Z_nonneg _ _ _)
    · exact hMpos
  have hg : ∀ t ∈ Finset.Icc 1 T,
      Q P c (aimLevel c d t) - Q P c (aimTarget c d t) ≤ g t := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have := aim_term_bound P c d ht.1
    simp only [g]; split_ifs
    · exact this.1
    · exact this.2
  have h1 : (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, (Q P c (aimLevel c d t) - Q P c (aimTarget c d t))
      ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T, g t :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum hg) (by positivity)
  refine (ENNReal.ofReal_le_ofReal h1).trans ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun t _ => hg0 t)]
  have h2 : ∑ t ∈ Finset.Icc 1 T, ENNReal.ofReal (g t) ≤
      ENNReal.ofReal c.h * ∑ t ∈ Finset.Icc 1 T,
          (if restartTime c ρ' d < (t : ℝ≥0∞) then ENNReal.ofReal (Z d (m c) t) else 0) +
      ENNReal.ofReal M * restartTime c ρ' d := by
    calc ∑ t ∈ Finset.Icc 1 T, ENNReal.ofReal (g t)
        ≤ ∑ t ∈ Finset.Icc 1 T, (ENNReal.ofReal c.h *
            (if restartTime c ρ' d < (t : ℝ≥0∞) then ENNReal.ofReal (Z d (m c) t) else 0) +
            ENNReal.ofReal M * (if (t : ℝ≥0∞) ≤ restartTime c ρ' d then (1 : ℝ≥0∞) else 0)) := by
          refine Finset.sum_le_sum (fun t _ => ?_)
          simp only [g]
          by_cases hc : restartTime c ρ' d < (t : ℝ≥0∞)
          · rw [if_pos hc, if_pos hc, if_neg (not_le.mpr hc)]
            rw [ENNReal.ofReal_mul hh.le]; simp
          · rw [if_neg hc, if_neg hc, if_pos (not_lt.mp hc)]; simp
      _ = ENNReal.ofReal c.h * ∑ t ∈ Finset.Icc 1 T,
            (if restartTime c ρ' d < (t : ℝ≥0∞) then ENNReal.ofReal (Z d (m c) t) else 0) +
          ENNReal.ofReal M * ∑ t ∈ Finset.Icc 1 T,
            (if (t : ℝ≥0∞) ≤ restartTime c ρ' d then (1 : ℝ≥0∞) else 0) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := by gcongr; exact count_le T _
  calc ENNReal.ofReal ((T : ℝ)⁻¹) * ∑ t ∈ Finset.Icc 1 T, ENNReal.ofReal (g t)
      ≤ ENNReal.ofReal ((T : ℝ)⁻¹) * (ENNReal.ofReal c.h * ∑ t ∈ Finset.Icc 1 T,
          (if restartTime c ρ' d < (t : ℝ≥0∞) then ENNReal.ofReal (Z d (m c) t) else 0) +
          ENNReal.ofReal M * restartTime c ρ' d) := by gcongr
    _ = ENNReal.ofReal (M / (T : ℝ)) * restartTime c ρ' d +
        ENNReal.ofReal (c.h / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
          (if restartTime c ρ' d < (t : ℝ≥0∞) then ENNReal.ofReal (Z d (m c) t) else 0) := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), inv_mul_eq_div, inv_mul_eq_div, add_comm]

theorem theorem8_core (P : DemandLaw) (c : Parameters) (ρ' : ℝ) (T : ℕ)
    (hT : 1 ≤ T) (hρ : 0 < ρ') (hsmall : ρ' < m c) :
    ENNReal.ofReal (lambdaTwo P c T) ≤
      ENNReal.ofReal (max c.b c.h * c.barY / (T : ℝ)) *
        ((Nat.ceil ((m c / ρ') ^ 2) : ℝ≥0∞) + expectedK P ρ' (initialHeight c ρ')) +
      ENNReal.ofReal (2 * c.h * m c / Real.sqrt (T : ℝ)) *
        busySecondMoment P ρ' := by
  have hrest := AIMInventory.UnknownRho.restart_bound P c ρ' hρ hsmall
  have hcl := claim14_core P c ρ' T hT hρ hsmall
  unfold lambdaTwo
  calc ENNReal.ofReal (∫ d, ((T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T,
          (Q P c (aimLevel c d t) - Q P c (aimTarget c d t))) ∂CappedBaseStock.demandPathLaw P)
      ≤ ∫⁻ d, ENNReal.ofReal ((T : ℝ)⁻¹ * ∑ t ∈ Finset.Icc 1 T,
          (Q P c (aimLevel c d t) - Q P c (aimTarget c d t))) ∂CappedBaseStock.demandPathLaw P :=
        ofReal_integral_le_lintegral _
    _ ≤ ∫⁻ d, (ENNReal.ofReal (max c.b c.h * c.barY / (T : ℝ)) * restartTime c ρ' d +
        ENNReal.ofReal (c.h / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T,
          (if restartTime c ρ' d < (t : ℝ≥0∞) then ENNReal.ofReal (Z d (m c) t) else 0))
          ∂CappedBaseStock.demandPathLaw P := lintegral_mono (fun d => aim_pointwise P c ρ' T hT d)
    _ = ENNReal.ofReal (max c.b c.h * c.barY / (T : ℝ)) *
          (∫⁻ d, restartTime c ρ' d ∂CappedBaseStock.demandPathLaw P) +
        ENNReal.ofReal (c.h / (T : ℝ)) * (∫⁻ d, ∑ t ∈ Finset.Icc 1 T,
          (if restartTime c ρ' d < (t : ℝ≥0∞) then ENNReal.ofReal (Z d (m c) t) else 0)
          ∂CappedBaseStock.demandPathLaw P) := by
        rw [lintegral_add_left ((measurable_restartTime c ρ').const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl hrest) hcl

end

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open scoped ENNReal NNReal BigOperators
open AIMInventory.UnknownRho

theorem solution (P : DemandLaw) (c : Parameters) (ρ' : ℝ) (T : ℕ)
    (hNV : LostSalesOrderUpTo.Asymptotic.newsvendorLevel P.law c.h c.b ≤
      Real.toNNReal c.barY)
    (hT : 1 ≤ T) (hρ : 0 < ρ') (hsmall : ρ' < m c)
    (hmean : ρ' < CappedBaseStock.mean P) :
    ENNReal.ofReal (lambdaTwo P c T) ≤
      ENNReal.ofReal (max c.b c.h * c.barY / (T : ℝ)) *
        ((Nat.ceil ((m c / ρ') ^ 2) : ℝ≥0∞) + expectedK P ρ' (initialHeight c ρ')) +
      ENNReal.ofReal (2 * c.h * m c / Real.sqrt (T : ℝ)) *
        busySecondMoment P ρ' := by
  exact theorem8_core P c ρ' T hT hρ hsmall

end
