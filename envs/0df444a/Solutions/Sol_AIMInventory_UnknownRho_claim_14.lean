-- Prove2me | solution 1 for AIMInventory.UnknownRho.claim_14
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:50:12.949918+00:00
-- url     : https://prove2.me/submissions/91b96730-3713-4304-b888-3edb976e3bbb

import Mathlib
import Definitions.Def_AIMInventory_UnknownRho_Model
set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators


namespace AIMInventory.UnknownRho

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

lemma K_eq (d : DemandPath) (θ z : ℝ) :
    K d θ z = ⨅ n : ℕ, if z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ)) ≤ 0 then (n : ℝ≥0∞) else ⊤ := by
  apply le_antisymm
  · refine le_iInf (fun n => ?_)
    split_ifs with h
    · exact sInf_le ⟨n, rfl, h⟩
    · exact le_top
  · refine le_sInf ?_
    rintro u ⟨n, rfl, h⟩
    exact iInf_le_of_le n (by rw [if_pos h])

lemma measurable_K (θ z : ℝ) : Measurable (fun d : DemandPath => K d θ z) := by
  simp_rw [K_eq]
  refine Measurable.iInf (fun n => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  refine measurableSet_le ?_ measurable_const
  fun_prop

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

/-- A lintegral of a shifted measurable function. -/
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

lemma Z_le_sqrt (d : DemandPath) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∀ t : ℕ, Z d θ (t + 1) ≤ 2 * θ * Real.sqrt (t : ℝ)
  | 0 => by simp [Z]
  | t + 1 => by
    have ih := Z_le_sqrt d hθ t
    rw [Z_succ d θ (by omega)]
    have h1 := sqrt_step t
    have h2 : θ / Real.sqrt ((t + 1 : ℕ) : ℝ) ≤ θ * (2 * Real.sqrt ((t : ℝ) + 1) - 2 * Real.sqrt (t : ℝ)) := by
      push_cast
      calc θ / Real.sqrt ((t : ℝ) + 1) = θ * (1 / Real.sqrt ((t : ℝ) + 1)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 hθ
    have h3 := (NNReal.coe_nonneg (d (t + 1 - 1)))
    push_cast at h2 ⊢
    refine max_le ?_ (by positivity)
    nlinarith [Z_nonneg d θ (t + 1)]

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

lemma Z_threshold_le (c : Parameters) (d : DemandPath) (ρ' : ℝ) (hρ : 0 < ρ') (hsmall : ρ' < m c) :
    Z d (m c) (threshold c ρ') ≤ initialHeight c ρ' := by
  have hm := m_pos c
  set T := threshold c ρ' with hT
  have hT1 : 1 ≤ T := threshold_pos c ρ'
  rw [threshold_eq c ρ' hρ hsmall] at hT
  have hx : 1 < m c / ρ' := by rw [lt_div_iff₀ hρ]; linarith
  have hTle : (T : ℝ) ≤ 2 * (m c / ρ') ^ 2 := by
    rw [hT]
    have := Nat.ceil_lt_add_one (show 0 ≤ (m c / ρ') ^ 2 by positivity)
    nlinarith
  obtain ⟨k, hk⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
  have h1 := Z_le_sqrt d hm.le k
  rw [← hk] at h1
  have h2 : Real.sqrt (k : ℝ) ≤ Real.sqrt (T : ℝ) := Real.sqrt_le_sqrt (by rw [hk]; push_cast; linarith)
  have h3 : Real.sqrt (T : ℝ) ≤ Real.sqrt 2 * (m c / ρ') := by
    calc Real.sqrt (T : ℝ) ≤ Real.sqrt (2 * (m c / ρ') ^ 2) := Real.sqrt_le_sqrt hTle
      _ = Real.sqrt 2 * (m c / ρ') := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  unfold initialHeight
  calc Z d (m c) T ≤ 2 * m c * Real.sqrt (k : ℝ) := h1
    _ ≤ 2 * m c * (Real.sqrt 2 * (m c / ρ')) := by
        apply mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
    _ = 2 * Real.sqrt 2 * m c ^ 2 / ρ' := by ring

/-- Dominating fixed-inflow Lindley recursion started at height `z`. -/
def Yp (d : DemandPath) (θ z : ℝ) : ℕ → ℝ
  | 0 => z
  | j + 1 => max (Yp d θ z j + θ - (d j : ℝ)) 0

lemma Z_le_Yp (c : Parameters) (d : DemandPath) (ρ' : ℝ) (z : ℝ) (T : ℕ) (hT : 1 ≤ T)
    (hZ : Z d (m c) T ≤ z) (hrate : ∀ t : ℕ, T ≤ t → m c / Real.sqrt (t : ℝ) ≤ ρ') :
    ∀ j : ℕ, Z d (m c) (T + j) ≤ Yp (fun n => d (n + (T - 1))) ρ' z j := by
  intro j
  induction j with
  | zero => simpa [Yp] using hZ
  | succ j ih =>
    have e : T + (j + 1) = (T + j) + 1 := by ring
    rw [e, Z_succ d _ (by omega)]
    simp only [Yp]
    have hd : (d (T + j - 1) : ℝ) = ((fun n => d (n + (T - 1))) j : ℝ) := by
      show (d (T + j - 1) : ℝ) = (d (j + (T - 1)) : ℝ)
      congr 2; omega
    rw [hd]
    have := hrate (T + j) (by omega)
    exact max_le_max (by linarith) le_rfl

lemma Yp_eq (d : DemandPath) (θ z : ℝ) (hz : 0 < z) (n : ℕ)
    (hpos : ∀ i < n, 0 < z + ∑ r ∈ Finset.range i, (θ - (d r : ℝ)))
    (hn : z + ∑ r ∈ Finset.range n, (θ - (d r : ℝ)) ≤ 0) : Yp d θ z n = 0 := by
  have key : ∀ j, (∀ i ≤ j, 0 < z + ∑ r ∈ Finset.range i, (θ - (d r : ℝ))) →
      Yp d θ z j = z + ∑ r ∈ Finset.range j, (θ - (d r : ℝ)) := by
    intro j
    induction j with
    | zero => intro _; simp [Yp]
    | succ j ih =>
      intro h
      have h1 := ih (fun i hi => h i (by omega))
      have h2 := h (j + 1) le_rfl
      simp only [Yp]
      rw [h1, Finset.sum_range_succ] at *
      rw [max_eq_left (by linarith)]
      ring
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp at hn; linarith
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have h1 := key j (fun i hi => hpos i (by omega))
    simp only [Yp]
    rw [h1]
    rw [Finset.sum_range_succ] at hn
    rw [max_eq_right (by linarith)]

lemma restartTime_le (c : Parameters) (ρ' : ℝ) (hρ : 0 < ρ') (hsmall : ρ' < m c) (d : DemandPath) :
    restartTime c ρ' d ≤ (threshold c ρ' : ℝ≥0∞) +
      K (fun n => d (n + (threshold c ρ' - 1))) ρ' (initialHeight c ρ') := by
  classical
  have hm := m_pos c
  set T := threshold c ρ' with hT
  have hT1 : 1 ≤ T := threshold_pos c ρ'
  set z := initialHeight c ρ' with hz
  have hzpos : 0 < z := by
    rw [hz]; unfold initialHeight; positivity
  set d' : DemandPath := fun n => d (n + (T - 1)) with hd'
  by_cases hex : ∃ n : ℕ, z + ∑ i ∈ Finset.range n, (ρ' - (d' i : ℝ)) ≤ 0
  · have hK : K d' ρ' z = (Nat.find hex : ℕ) := by
      apply le_antisymm
      · exact sInf_le ⟨Nat.find hex, rfl, Nat.find_spec hex⟩
      · refine le_sInf ?_
        rintro u ⟨n, rfl, h⟩
        exact_mod_cast Nat.find_min' hex h
    rw [hK]
    set n := Nat.find hex with hn
    have hspec : z + ∑ i ∈ Finset.range n, (ρ' - (d' i : ℝ)) ≤ 0 := Nat.find_spec hex
    have hpos : ∀ i < n, 0 < z + ∑ r ∈ Finset.range i, (ρ' - (d' r : ℝ)) := by
      intro i hi
      have := Nat.find_min hex hi
      push_neg at this
      exact this
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0] at hspec; simp at hspec; linarith
      · exact h0
    have hrate : ∀ t : ℕ, T ≤ t → m c / Real.sqrt (t : ℝ) ≤ ρ' := by
      intro t ht
      have hTx : (m c / ρ') ^ 2 ≤ (T : ℝ) := by
        rw [hT, threshold_eq c ρ' hρ hsmall]; exact Nat.le_ceil _
      have : m c / ρ' ≤ Real.sqrt (t : ℝ) := by
        apply Real.le_sqrt_of_sq_le
        exact hTx.trans (by exact_mod_cast ht)
      rw [div_le_iff₀ (by have : 0 < m c / ρ' := by positivity
                          exact lt_of_lt_of_le this ‹_›)]
      rw [div_le_iff₀ hρ] at this
      linarith
    have hZY := Z_le_Yp c d ρ' z T hT1 (Z_threshold_le c d ρ' hρ hsmall) hrate n
    have hY := Yp_eq d' ρ' z hzpos n hpos hspec
    have hZ0 : Z d (m c) (T + n) = 0 := le_antisymm (hY ▸ hZY) (Z_nonneg _ _ _)
    calc restartTime c ρ' d ≤ ((T + n : ℕ) : ℝ≥0∞) :=
          sInf_le ⟨T + n, by omega, rfl, hZ0⟩
      _ = (T : ℝ≥0∞) + (n : ℝ≥0∞) := by push_cast; rfl
  · have hK : K d' ρ' z = ⊤ := by
      unfold K
      have : {u : ℝ≥0∞ | ∃ n : ℕ, u = (n : ℝ≥0∞) ∧
          z + ∑ i ∈ Finset.range n, (ρ' - (d' i : ℝ)) ≤ 0} = ∅ := by
        ext u; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨n, -, h⟩; exact hex ⟨n, h⟩
      rw [this]; exact sInf_empty
    rw [hK]; simp

theorem restart_core (P : DemandLaw) (c : Parameters) (ρ' : ℝ)
    (hρ : 0 < ρ') (hsmall : ρ' < m c) :
    (∫⁻ d, restartTime c ρ' d ∂CappedBaseStock.demandPathLaw P) ≤
      (Nat.ceil ((m c / ρ') ^ 2) : ℝ≥0∞) + expectedK P ρ' (initialHeight c ρ') := by
  have hT := threshold_eq c ρ' hρ hsmall
  rw [← hT]
  calc (∫⁻ d, restartTime c ρ' d ∂CappedBaseStock.demandPathLaw P)
      ≤ ∫⁻ d, ((threshold c ρ' : ℝ≥0∞) +
          K (fun n => d (n + (threshold c ρ' - 1))) ρ' (initialHeight c ρ'))
          ∂CappedBaseStock.demandPathLaw P := lintegral_mono (restartTime_le c ρ' hρ hsmall)
    _ = (threshold c ρ' : ℝ≥0∞) + expectedK P ρ' (initialHeight c ρ') := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      congr 1
      exact lintegral_shift P (threshold c ρ' - 1) (measurable_K ρ' (initialHeight c ρ'))

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

/-- Pointwise bound: the sum over `t` of the restarted queue lengths is bounded by
busy-period contributions started at each `s`. -/
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

end AIMInventory.UnknownRho

open AIMInventory.UnknownRho


theorem solution (P : DemandLaw) (c : Parameters) (ρ' : ℝ) (T : ℕ)
    (hT : 1 ≤ T) (hρ : 0 < ρ') (hsmall : ρ' < m c)
    (hmean : ρ' < CappedBaseStock.mean P) :
    ENNReal.ofReal (c.h / (T : ℝ)) *
      (∫⁻ d, ∑ t ∈ Finset.Icc 1 T,
        if restartTime c ρ' d < (t : ℝ≥0∞) then
          ENNReal.ofReal (Z d (m c) t) else 0
        ∂CappedBaseStock.demandPathLaw P) ≤
      ENNReal.ofReal (2 * c.h * m c / Real.sqrt (T : ℝ)) *
        busySecondMoment P ρ' := by
  exact claim14_core P c ρ' T hT hρ hsmall
