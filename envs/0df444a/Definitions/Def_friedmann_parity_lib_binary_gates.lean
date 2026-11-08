-- Prove2me | Definitions.Def_friedmann_parity_lib_binary_gates
-- name    : friedmann_parity_lib_binary_gates
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-08T03:46:01.771734+00:00
-- url     : https://prove2.me/theorems/16e33237-7ad2-4d79-af3b-5f905f083f6f
-- title:
--   Friedmann binary lower-bound family: deceleration-gate lemmas
-- statement:
--   A sorry-free library module that extends `friedmann_parity_lib_binary_ladders`. For the gate vertices $d1_i,d2_i,d3_i$ of the games $G_n$ it proves the best-edge property: the successor chosen by the next counter state has strictly larger valuation, under $\sigma_{b,s}$, than the alternative successor (`bestEdge_d1`, `bestEdge_d2`, `bestEdge_d3`). It also proves the bit-arithmetic facts about the counter value $b$ that these cases need.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 7(3:19), 2011, arXiv:1106.0778, §§6–8

import Definitions.Def_friedmann_parity_lib_binary_ladders

set_option autoImplicit false
set_option linter.unusedVariables false

namespace FriedmannParity

/-! ### Part 1: `HitsK`, `GKOrderProp`, Priorities, and Step Lemmas for `.d1`, `.d2`, `.d3`, `.g` -/

def HitsK (glob : Bool) (n b s : ℕ) (w : V_bin n) (i : Fin n) : Prop :=
  ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
    (u ∈ predPath glob n b s w ↔ u ∈ predPath glob n b s (.k i))

def PortalCR (glob : Bool) (n b s : ℕ) (w : V_bin n) : Prop :=
  if b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) then
    HitsPortal glob n b s w .r
  else
    HitsPortal glob n b s w .c

def GKOrderProp (glob : Bool) (n b s : ℕ) (i : Fin n) : Prop :=
  chooseTauEdge1 n b s (.g i) = true →
    ∀ w_p w_k,
      PortalCR glob n b s w_p →
      HitsK glob n b s w_k i →
      if (b.testBit i.val = true ∨ 3 * (n + 2 * i.val + 1) + 2 ≤ s) ∧
          ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) then
        ValueLT (G_bin n) (predVal glob n b s w_p) (predVal glob n b s w_k)
      else
        ValueLT (G_bin n) (predVal glob n b s w_k) (predVal glob n b s w_p)

lemma hitsK_refl (glob : Bool) (n b s : ℕ) (i : Fin n) :
    HitsK glob n b s (.k i) i :=
  fun _ _ => Iff.rfl

lemma hitsK_of_step (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (w : V_bin n) (i : Fin n) (hw : w ≠ .x)
    (hprio : (G_bin n).priority w < (G_bin n).priority .c)
    (hstep : HitsK glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w) i) :
    HitsK glob n b s w i := by
  have hpath : predPath glob n b s w =
      insert w (predPath glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w)) :=
    pred_path_step glob n b s hvalid w hw
  intro u hu
  rw [hpath, Finset.mem_insert]
  have hne : u ≠ w := by intro heq; subst heq; omega
  simp only [hne, false_or]
  exact hstep u hu

lemma prio_d1_odd (n : ℕ) (i : Fin n) : (G_bin n).priority (.d1 i) % 2 = 1 := by
  have := shift_bin_even n; dsimp [G_bin, priority_bin]; omega

lemma prio_d2_odd (n : ℕ) (i : Fin n) : (G_bin n).priority (.d2 i) % 2 = 1 := by
  have := shift_bin_even n; dsimp [G_bin, priority_bin]; omega

lemma prio_d3_odd (n : ℕ) (i : Fin n) : (G_bin n).priority (.d3 i) % 2 = 1 := by
  have := shift_bin_even n; dsimp [G_bin, priority_bin]; omega

lemma prio_g_even (n : ℕ) (i : Fin n) : (G_bin n).priority (.g i) % 2 = 0 := by
  have := shift_bin_even n; dsimp [G_bin, priority_bin]; omega

lemma prio_l2_lt_d1 (n : ℕ) (m : Fin (3 * n - 1)) (i : Fin n) :
    (G_bin n).priority (.l2 m) < (G_bin n).priority (.d1 i) := by
  have := m.isLt; dsimp [G_bin, priority_bin, shift_bin, baseL_bin, M_bin]; omega

lemma prio_l3_lt_d1 (n : ℕ) (m : Fin (3 * n - 1)) (i : Fin n) :
    (G_bin n).priority (.l3 m) < (G_bin n).priority (.d1 i) := by
  have := m.isLt; dsimp [G_bin, priority_bin, shift_bin, baseL_bin, M_bin]; omega

lemma prio_l1_lt_d1 (n : ℕ) (m : Fin (3 * n - 1)) (i : Fin n) :
    (G_bin n).priority (.l1 m) < (G_bin n).priority (.d1 i) := by
  have := m.isLt; dsimp [G_bin, priority_bin, shift_bin, baseL_bin, M_bin]; omega

lemma prio_d1_lt_d2 (n : ℕ) (i : Fin n) :
    (G_bin n).priority (.d1 i) < (G_bin n).priority (.d2 i) := by
  dsimp [G_bin, priority_bin]; omega

lemma prio_d2_lt_d3 (n : ℕ) (i : Fin n) :
    (G_bin n).priority (.d2 i) < (G_bin n).priority (.d3 i) := by
  dsimp [G_bin, priority_bin]; omega

lemma prio_d3_lt_g (n : ℕ) (i : Fin n) :
    (G_bin n).priority (.d3 i) < (G_bin n).priority (.g i) := by
  dsimp [G_bin, priority_bin]; omega

lemma prio_g_lt_r_2_odd (n : ℕ) (i : Fin n) :
    (G_bin n).priority (.g i) < (G_bin n).priority .r_2_odd := by
  have := i.isLt; dsimp [G_bin, priority_bin]; omega

lemma prio_g_lt_b (n : ℕ) (i : Fin n) (k : Fin (3 * (3 * n - 1))) :
    (G_bin n).priority (.g i) < (G_bin n).priority (.b k) :=
  lt_trans (prio_g_lt_r_2_odd n i) (prio_r_2_odd_lt_b n k)

lemma prio_g_lt_c_odd (n : ℕ) (i : Fin n) :
    (G_bin n).priority (.g i) < (G_bin n).priority .c_odd := by
  have := prio_g_lt_r_2_odd n i
  dsimp [G_bin, priority_bin, top_bin, Na_bin, M_bin] at this ⊢; omega

lemma prio_g_lt_c (n : ℕ) (i : Fin n) :
    (G_bin n).priority (.g i) < (G_bin n).priority .c := by
  have := prio_g_lt_c_odd n i
  dsimp [G_bin, priority_bin] at this ⊢; omega

lemma prio_d3_lt_c (n : ℕ) (i : Fin n) :
    (G_bin n).priority (.d3 i) < (G_bin n).priority .c :=
  lt_trans (prio_d3_lt_g n i) (prio_g_lt_c n i)

lemma prio_d2_lt_c (n : ℕ) (i : Fin n) :
    (G_bin n).priority (.d2 i) < (G_bin n).priority .c :=
  lt_trans (prio_d2_lt_d3 n i) (prio_d3_lt_c n i)

lemma prio_d1_lt_c (n : ℕ) (i : Fin n) :
    (G_bin n).priority (.d1 i) < (G_bin n).priority .c :=
  lt_trans (prio_d1_lt_d2 n i) (prio_d2_lt_c n i)

lemma step_g_true (glob : Bool) (n b s : ℕ) (i : Fin n)
    (htau : chooseTauEdge1 n b s (.g i) = true) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g i) = .k i := by
  change predTau0 n b s (.g i) = .k i
  unfold predTau0; rw [if_pos htau]; rfl

lemma step_g_false (glob : Bool) (n b s : ℕ) (i : Fin n)
    (htau : chooseTauEdge1 n b s (.g i) = false) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g i) = .d1 i := by
  change predTau0 n b s (.g i) = .d1 i
  unfold predTau0; rw [htau]; rfl

lemma step_d1_true (glob : Bool) (n b s : ℕ) (i : Fin n)
    (hce : chooseEdge1 glob n b s (.d1 i) = true) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d1 i) = .d2 i := by
  change predState0 glob n b s (.d1 i) = .d2 i
  unfold predState0; rw [if_pos hce]; rfl

lemma step_d1_false (glob : Bool) (n b s : ℕ) (i : Fin n)
    (hce : chooseEdge1 glob n b s (.d1 i) = false) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d1 i) = .lp1 (tap_bin n i) := by
  change predState0 glob n b s (.d1 i) = .lp1 (tap_bin n i)
  unfold predState0; rw [hce]; rfl

lemma step_d2_true (glob : Bool) (n b s : ℕ) (i : Fin n)
    (hce : chooseEdge1 glob n b s (.d2 i) = true) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d2 i) = .d3 i := by
  change predState0 glob n b s (.d2 i) = .d3 i
  unfold predState0; rw [if_pos hce]; rfl

lemma step_d2_false (glob : Bool) (n b s : ℕ) (i : Fin n)
    (hce : chooseEdge1 glob n b s (.d2 i) = false) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d2 i) = .lp2 (tap_bin n i) := by
  change predState0 glob n b s (.d2 i) = .lp2 (tap_bin n i)
  unfold predState0; rw [hce]; rfl

lemma step_d3_true (glob : Bool) (n b s : ℕ) (i : Fin n)
    (hce : chooseEdge1 glob n b s (.d3 i) = true) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d3 i) = .g i := by
  change predState0 glob n b s (.d3 i) = .g i
  unfold predState0; rw [if_pos hce]; rfl

lemma step_d3_false (glob : Bool) (n b s : ℕ) (i : Fin n)
    (hce : chooseEdge1 glob n b s (.d3 i) = false) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d3 i) = .lp3 (tap_bin n i) := by
  change predState0 glob n b s (.d3 i) = .lp3 (tap_bin n i)
  unfold predState0; rw [hce]; rfl

lemma hitsK_g (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (htau : chooseTauEdge1 n b s (.g i) = true) :
    HitsK glob n b s (.g i) i := by
  apply hitsK_of_step glob n b s hvalid (.g i) i (by rintro ⟨⟩) (prio_g_lt_c n i)
  rw [step_g_true glob n b s i htau]
  exact hitsK_refl glob n b s i

lemma hitsK_d3 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hce3 : chooseEdge1 glob n b s (.d3 i) = true)
    (htau : chooseTauEdge1 n b s (.g i) = true) :
    HitsK glob n b s (.d3 i) i := by
  apply hitsK_of_step glob n b s hvalid (.d3 i) i (by rintro ⟨⟩) (prio_d3_lt_c n i)
  rw [step_d3_true glob n b s i hce3]
  exact hitsK_g glob n b s hvalid i htau

lemma hitsK_d2 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hce2 : chooseEdge1 glob n b s (.d2 i) = true)
    (hce3 : chooseEdge1 glob n b s (.d3 i) = true)
    (htau : chooseTauEdge1 n b s (.g i) = true) :
    HitsK glob n b s (.d2 i) i := by
  apply hitsK_of_step glob n b s hvalid (.d2 i) i (by rintro ⟨⟩) (prio_d2_lt_c n i)
  rw [step_d2_true glob n b s i hce2]
  exact hitsK_d3 glob n b s hvalid i hce3 htau

/-! ### Part 2: Bit-Arithmetic Helpers and Exact `bestEdge1` Formulas -/

lemma testBit_two_pow_sub_one : ∀ (n i : ℕ), i < n → (2 ^ n - 1).testBit i = true
  | 0, _, hi => by omega
  | n + 1, 0, _ => by
    rw [testBit_zero_eq, decide_eq_true_eq]
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    omega
  | n + 1, i + 1, hi => by
    rw [Nat.testBit_succ]
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    have hdiv : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by omega
    rw [hdiv]
    exact testBit_two_pow_sub_one n i (by omega)

lemma lt_two_pow_sub_one_of_testBit_false {n b i : ℕ}
    (hbn : b < 2 ^ n) (hi : i < n) (hbit : b.testBit i = false) :
    b < 2 ^ n - 1 := by
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  by_contra hge
  have heq : b = 2 ^ n - 1 := by omega
  subst heq
  have htrue := testBit_two_pow_sub_one n i hi
  rw [hbit] at htrue
  contradiction

lemma testBit_succ_of_lowestZero :
    ∀ (k b i : ℕ), b.testBit k = false → (∀ j < k, b.testBit j = true) →
      (b + 1).testBit i = (if i < k then false else if i = k then true else b.testBit i)
  | 0, b, 0, hk, _ => by
    rw [testBit_zero_eq] at hk ⊢
    rw [decide_eq_false_iff_not] at hk
    simp only [lt_self_iff_false, ite_false, ite_true, decide_eq_true_eq]
    omega
  | 0, b, i + 1, hk, _ => by
    rw [testBit_zero_eq, decide_eq_false_iff_not] at hk
    have hdiv : (b + 1) / 2 = b / 2 := by omega
    rw [Nat.testBit_succ, Nat.testBit_succ, hdiv]
    rw [if_neg (by omega), if_neg (by omega)]
  | k + 1, b, 0, _, hall => by
    have h0 := hall 0 (by omega)
    rw [testBit_zero_eq, decide_eq_true_eq] at h0
    rw [testBit_zero_eq, if_pos (by omega), decide_eq_false_iff_not]
    omega
  | k + 1, b, i + 1, hk, hall => by
    have h0 := hall 0 (by omega)
    rw [testBit_zero_eq, decide_eq_true_eq] at h0
    have hdiv : (b + 1) / 2 = b / 2 + 1 := by omega
    have hk' : (b / 2).testBit k = false := by rw [← Nat.testBit_succ]; exact hk
    have hall' : ∀ j < k, (b / 2).testBit j = true := by
      intro j hj; rw [← Nat.testBit_succ]; exact hall (j + 1) (by omega)
    rw [Nat.testBit_succ, hdiv, testBit_succ_of_lowestZero k (b / 2) i hk' hall', Nat.testBit_succ]
    split_ifs <;> first | rfl | omega

lemma testBit_succ_eq (i : ℕ) {n b : ℕ} (hb : b < 2 ^ n - 1) :
    (b + 1).testBit i =
      (if i < lowestZero0 b n then false else if i = lowestZero0 b n then true else b.testBit i) :=
  testBit_succ_of_lowestZero (lowestZero0 b n) b i
    (testBit_lowestZero0 hb) (fun _ hj => testBit_of_lt_lowestZero0 hb hj)

lemma testBit_succ_of_lt {n b i : ℕ} (hb : b < 2 ^ n - 1) (hlt : i < lowestZero0 b n) :
    (b + 1).testBit i = false := by
  rw [testBit_succ_eq i hb, if_pos hlt]

lemma testBit_succ_of_eq {n b i : ℕ} (hb : b < 2 ^ n - 1) (heq : i = lowestZero0 b n) :
    (b + 1).testBit i = true := by
  rw [testBit_succ_eq i hb, if_neg (by omega), if_pos heq]

lemma testBit_succ_of_gt {n b i : ℕ} (hb : b < 2 ^ n - 1) (hgt : lowestZero0 b n < i) :
    (b + 1).testBit i = b.testBit i := by
  rw [testBit_succ_eq i hb, if_neg (by omega), if_neg (by omega)]

lemma d3Cut0_eq_uLim0_add_one {b n i : ℕ} (hil : i < lowestOne0 b n) :
    d3Cut0 b n = uLim0 b n + 1 := by
  unfold d3Cut0 uLim0
  split_ifs <;> omega

lemma bestEdge1_d3_of_tau_true (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (htau : chooseTauEdge1 n b s (.g i) = true) :
    bestEdge1 n b s (.d3 i) =
      decide ((b.testBit i.val = true ∨ 3 * (n + 2 * i.val + 1) + 2 ≤ s) ∧
        ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) := by
  rcases hvalid with ⟨hn, hbn, hs_lt⟩
  have hi := i.isLt
  by_cases hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
  · unfold bestEdge1 nextPair
    rw [if_neg (by omega), if_pos hs3]
    dsimp [chooseEdge1]
    rcases lt_trichotomy i.val (lowestZero0 b n) with hlt | heq | hgt
    · rw [testBit_succ_of_lt hs3.1 hlt]
      simp only [Bool.false_eq_true, ite_false]
      symm
      rw [decide_eq_false_iff_not]
      rintro ⟨_, hnot⟩
      exact hnot ⟨hs3.1, hlt, Or.inr hs3.2⟩
    · rw [testBit_succ_of_eq hs3.1 heq]
      have hnot_s3' : ¬(b + 1 < 2 ^ n - 1 ∧ i.val < lowestZero0 (b + 1) n ∧ 0 = S_close0 n (b + 1) + 3) := by
        unfold S_close0; omega
      rw [if_pos rfl, if_neg hnot_s3']
      symm
      rw [decide_eq_true_eq]
      refine ⟨Or.inr ?_, ?_⟩
      · have := hs3.2; unfold S_close0 at this; omega
      · omega
    · rw [testBit_succ_of_gt hs3.1 hgt]
      have hnot_s3' : ¬(b + 1 < 2 ^ n - 1 ∧ i.val < lowestZero0 (b + 1) n ∧ 0 = S_close0 n (b + 1) + 3) := by
        unfold S_close0; omega
      have hs_lt_T : s < 3 * (n + 2 * i.val + 1) + 2 := by
        have := hs3.2; unfold S_close0 at this; omega
      cases hbit : b.testBit i.val with
      | true =>
        rw [if_pos rfl, if_neg hnot_s3']
        symm; rw [decide_eq_true_eq]
        exact ⟨Or.inl rfl, by omega⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        symm; rw [decide_eq_false_iff_not]
        rintro ⟨h1 | h1, _⟩
        · exact h1
        · omega
  · by_cases hterm : b = 2 ^ n - 1 ∧ s = 9 * n - 4
    · have hbit : b.testBit i.val = true := by
        rw [hterm.1]; exact testBit_two_pow_sub_one n i.val hi
      unfold bestEdge1 nextPair
      rw [if_pos hterm]
      dsimp [chooseEdge1]
      rw [hbit, if_pos rfl, if_neg (by omega)]
      symm; rw [decide_eq_true_eq]
      exact ⟨Or.inl rfl, by omega⟩
    · unfold bestEdge1 nextPair
      rw [if_neg hterm, if_neg hs3]
      dsimp [chooseEdge1]
      cases hbit : b.testBit i.val with
      | true =>
        rw [if_pos rfl]
        by_cases hcond : b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ s + 1 = S_close0 n b + 3
        · rw [if_pos hcond]
          symm; rw [decide_eq_false_iff_not]
          rintro ⟨_, hnot⟩
          exact hnot ⟨hcond.1, hcond.2.1, Or.inl (by omega)⟩
        · rw [if_neg hcond]
          symm; rw [decide_eq_true_eq]
          refine ⟨Or.inl rfl, ?_⟩
          rintro ⟨hb_lt, hil, hs2 | hs3'⟩
          · exact hcond ⟨hb_lt, hil, by omega⟩
          · exact hs3 ⟨hb_lt, hs3'⟩
      | false =>
        have hb_lt : b < 2 ^ n - 1 := lt_two_pow_sub_one_of_testBit_false hbn hi hbit
        have hle_lz : lowestZero0 b n ≤ i.val := lowestZero0_le_of_testBit_false hi hbit
        simp only [Bool.false_eq_true, ite_false]
        by_cases hT : 3 * (n + 2 * i.val + 1) + 2 ≤ s
        · rw [if_pos (by omega)]
          symm; rw [decide_eq_true_eq]
          exact ⟨Or.inr hT, by omega⟩
        · dsimp [chooseTauEdge1] at htau
          rw [hbit, Bool.false_or, decide_eq_false hT, Bool.false_or, decide_eq_true_eq] at htau
          rcases htau with ⟨hb0, hil1, hlim⟩
          have hulim : uLim0 b n ≤ n := by
            have := lowestOne0_le b n; unfold uLim0; split_ifs <;> omega
          have hd3cut : i.val + 1 + (s + 1) < d3Cut0 b n := by
            rw [d3Cut0_eq_uLim0_add_one hil1]; omega
          have hRHS : decide ((False ∨ 3 * (n + 2 * i.val + 1) + 2 ≤ s) ∧
              ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) = false := by
            rw [decide_eq_false_iff_not]
            rintro ⟨h1 | h1, _⟩
            · exact h1
            · exact hT h1
          rw [if_neg (by omega), if_neg (by omega), hRHS]
          split_ifs with hmod
          · rw [decide_eq_false_iff_not, not_not]
            exact ⟨hb0, hd3cut⟩
          · rfl

lemma bestEdge1_d3_of_tau_false (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (htau : chooseTauEdge1 n b s (.g i) = false) :
    bestEdge1 n b s (.d3 i) = decide (3 * (n + 2 * i.val + 1) ≤ s ∨ s % 3 = 0) := by
  rcases hvalid with ⟨hn, hbn, hs_lt⟩
  have hi := i.isLt
  dsimp [chooseTauEdge1] at htau
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at htau
  rcases htau with ⟨⟨hbit, hnot_T2⟩, hnot_u⟩
  have hb_lt : b < 2 ^ n - 1 := lt_two_pow_sub_one_of_testBit_false hbn hi hbit
  have hle_lz : lowestZero0 b n ≤ i.val := lowestZero0_le_of_testBit_false hi hbit
  by_cases hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
  · have hlt_lz : lowestZero0 b n < i.val := by
      have := hs3.2; unfold S_close0 at this; omega
    unfold bestEdge1 nextPair
    rw [if_neg (by omega), if_pos hs3]
    dsimp [chooseEdge1]
    rw [testBit_succ_of_gt hs3.1 hlt_lz, hbit]
    simp only [Bool.false_eq_true, ite_false]
    symm; rw [decide_eq_false_iff_not]
    have := hs3.2; unfold S_close0 at this; omega
  · unfold bestEdge1 nextPair
    rw [if_neg (by omega), if_neg hs3]
    dsimp [chooseEdge1]
    rw [hbit]
    simp only [Bool.false_eq_true, ite_false]
    by_cases hT : 3 * (n + 2 * i.val + 1) ≤ s
    · rw [if_pos (by omega)]
      symm; rw [decide_eq_true_eq]
      exact Or.inl hT
    · rw [if_neg (by omega)]
      by_cases hTeq : s + 1 = 3 * (n + 2 * i.val + 1)
      · rw [if_pos hTeq]
        symm; rw [decide_eq_false_iff_not]
        omega
      · rw [if_neg hTeq]
        by_cases hmod : (s + 1) % 3 = 1
        · rw [if_pos hmod]
          have hLHS : (decide ¬(0 < b ∧ i.val + 1 + (s + 1) < d3Cut0 b n)) = true := by
            rw [decide_eq_true_eq]
            rintro ⟨hb0, hd3⟩
            by_cases hil1 : i.val < lowestOne0 b n
            · rw [d3Cut0_eq_uLim0_add_one hil1] at hd3
              exact hnot_u ⟨hb0, hil1, by omega⟩
            · have hbit1 := testBit_lowestOne0 hb0 hbn
              have hne1 : i.val ≠ lowestOne0 b n := by intro heq; rw [← heq, hbit] at hbit1; cases hbit1
              unfold d3Cut0 at hd3
              split_ifs at hd3 <;> omega
          rw [hLHS]; symm; rw [decide_eq_true_eq]
          exact Or.inr (by omega)
        · rw [if_neg hmod]
          symm; rw [decide_eq_false_iff_not]
          omega

lemma bestEdge1_d2_of_testBit_true (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hbit : b.testBit i.val = true) :
    bestEdge1 n b s (.d2 i) =
      decide ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
  rcases hvalid with ⟨hn, hbn, _⟩
  by_cases hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
  · have hne_lz : i.val ≠ lowestZero0 b n := by
      intro heq; have h := testBit_lowestZero0 hs3.1; rw [← heq, hbit] at h; cases h
    unfold bestEdge1 nextPair
    rw [if_neg (by omega), if_pos hs3]
    dsimp [chooseEdge1]
    by_cases hlt_lz : i.val < lowestZero0 b n
    · rw [testBit_succ_of_lt hs3.1 hlt_lz]
      simp only [Bool.false_eq_true, ite_false]
      rw [decide_eq_false (by omega)]
      symm; rw [decide_eq_false_iff_not, not_not]
      exact ⟨hs3.1, hlt_lz, Or.inr hs3.2⟩
    · rw [testBit_succ_of_gt hs3.1 (by omega), hbit, if_pos rfl, if_neg (by unfold S_close0; omega)]
      symm; rw [decide_eq_true_eq]
      omega
  · by_cases hterm : b = 2 ^ n - 1 ∧ s = 9 * n - 4
    · unfold bestEdge1 nextPair
      rw [if_pos hterm]
      dsimp [chooseEdge1]
      rw [hbit, if_pos rfl, if_neg (by omega)]
      symm; rw [decide_eq_true_eq]; omega
    · unfold bestEdge1 nextPair
      rw [if_neg hterm, if_neg hs3]
      dsimp [chooseEdge1]
      rw [hbit, if_pos rfl]
      by_cases hcond : b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ s + 1 = S_close0 n b + 3
      · rw [if_pos hcond]
        symm; rw [decide_eq_false_iff_not, not_not]
        exact ⟨hcond.1, hcond.2.1, Or.inl (by omega)⟩
      · rw [if_neg hcond]
        symm; rw [decide_eq_true_eq]
        rintro ⟨hb_lt, hil, hs2 | hs3'⟩
        · exact hcond ⟨hb_lt, hil, by omega⟩
        · exact hs3 ⟨hb_lt, hs3'⟩

lemma bestEdge1_d2_of_testBit_false (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hbit : b.testBit i.val = false) :
    bestEdge1 n b s (.d2 i) =
      decide (3 * (n + 2 * i.val + 1) + 1 ≤ s ∨ (s + 1 < 3 * (n + 2 * i.val + 1) ∧ s % 3 = 1)) := by
  rcases hvalid with ⟨hn, hbn, _⟩
  have hi := i.isLt
  have hb_lt : b < 2 ^ n - 1 := lt_two_pow_sub_one_of_testBit_false hbn hi hbit
  have hle_lz : lowestZero0 b n ≤ i.val := lowestZero0_le_of_testBit_false hi hbit
  by_cases hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
  · unfold bestEdge1 nextPair
    rw [if_neg (by omega), if_pos hs3]
    dsimp [chooseEdge1]
    by_cases heq_lz : i.val = lowestZero0 b n
    · rw [testBit_succ_of_eq hs3.1 heq_lz, if_pos rfl, if_neg (by unfold S_close0; omega)]
      symm; rw [decide_eq_true_eq]
      left; have := hs3.2; unfold S_close0 at this; omega
    · rw [testBit_succ_of_gt hs3.1 (by omega), hbit]
      simp only [Bool.false_eq_true, ite_false]
      rw [decide_eq_false (by omega)]
      symm; rw [decide_eq_false_iff_not]
      have := hs3.2; unfold S_close0 at this; omega
  · unfold bestEdge1 nextPair
    rw [if_neg (by omega), if_neg hs3]
    dsimp [chooseEdge1]
    rw [hbit]
    simp only [Bool.false_eq_true, ite_false]
    split_ifs with h1 h2
    · symm; rw [decide_eq_true_eq]; exact Or.inl (by omega)
    · symm; rw [decide_eq_false_iff_not]; omega
    · congr 1; ext; omega

lemma bestEdge1_d1_of_testBit_true (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hbit : b.testBit i.val = true) :
    bestEdge1 n b s (.d1 i) =
      decide ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ s = S_close0 n b + 2) := by
  rcases hvalid with ⟨hn, hbn, _⟩
  by_cases hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
  · have hne_lz : i.val ≠ lowestZero0 b n := by
      intro heq; have h := testBit_lowestZero0 hs3.1; rw [← heq, hbit] at h; cases h
    unfold bestEdge1 nextPair
    rw [if_neg (by omega), if_pos hs3]
    dsimp [chooseEdge1]
    rw [testBit_succ_eq i.val hs3.1]
    by_cases hlt_lz : i.val < lowestZero0 b n
    · rw [if_pos hlt_lz]
      simp only [Bool.false_eq_true, ite_false]
      rw [decide_eq_true (by omega)]
      symm; rw [decide_eq_true_eq]; omega
    · rw [if_neg hlt_lz, if_neg hne_lz, hbit, if_pos rfl, if_neg (by unfold S_close0; omega)]
      symm; rw [decide_eq_true_eq]; omega
  · by_cases hterm : b = 2 ^ n - 1 ∧ s = 9 * n - 4
    · unfold bestEdge1 nextPair
      rw [if_pos hterm]
      dsimp [chooseEdge1]
      rw [hbit, if_pos rfl, if_neg (by omega)]
      symm; rw [decide_eq_true_eq]; omega
    · unfold bestEdge1 nextPair
      rw [if_neg hterm, if_neg hs3]
      dsimp [chooseEdge1]
      rw [hbit, if_pos rfl]
      by_cases hcond : b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ s + 1 = S_close0 n b + 3
      · rw [if_pos hcond]
        symm; rw [decide_eq_false_iff_not, not_not]
        exact ⟨hcond.1, hcond.2.1, by omega⟩
      · rw [if_neg hcond]
        symm; rw [decide_eq_true_eq]
        rintro ⟨hb_lt, hil, hs2⟩
        exact hcond ⟨hb_lt, hil, by omega⟩

lemma bestEdge1_d1_of_testBit_false (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hbit : b.testBit i.val = false) :
    bestEdge1 n b s (.d1 i) =
      decide (3 * (n + 2 * i.val + 1) - 1 ≤ s ∨ s % 3 = 2) := by
  rcases hvalid with ⟨hn, hbn, _⟩
  have hi := i.isLt
  have hb_lt : b < 2 ^ n - 1 := lt_two_pow_sub_one_of_testBit_false hbn hi hbit
  by_cases hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
  · unfold bestEdge1 nextPair
    rw [if_neg (by omega), if_pos hs3]
    dsimp [chooseEdge1]
    have hnot_s3' : ¬(b + 1 < 2 ^ n - 1 ∧ i.val < lowestZero0 (b + 1) n ∧ 0 = S_close0 n (b + 1) + 3) := by
      unfold S_close0; omega
    cases hbit1 : (b + 1).testBit i.val with
    | true =>
      rw [if_pos rfl, if_neg hnot_s3']
      symm; rw [decide_eq_true_eq]
      right; have := hs3.2; unfold S_close0 at this; omega
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [decide_eq_true (by omega)]
      symm; rw [decide_eq_true_eq]
      right; have := hs3.2; unfold S_close0 at this; omega
  · unfold bestEdge1 nextPair
    rw [if_neg (by omega), if_neg hs3]
    dsimp [chooseEdge1]
    rw [hbit]
    simp only [Bool.false_eq_true, ite_false]
    by_cases hT : 3 * (n + 2 * i.val + 1) ≤ s + 1
    · rw [if_pos hT]
      symm; rw [decide_eq_true_eq]; exact Or.inl (by omega)
    · rw [if_neg hT]
      by_cases hmod : (s + 1) % 3 = 0
      · rw [if_pos hmod, decide_eq_true (by omega)]
        symm; rw [decide_eq_true_eq]; exact Or.inr (by omega)
      · rw [if_neg hmod]
        symm; rw [decide_eq_false_iff_not]; omega

/-! ### Part 3: Unified `GKOrderProp` and Ladder `HitsPortal` / `HitsWithTop` Helpers -/

lemma hitsWithTop_of_step_gt' (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (w p topV : V_bin n) (hw : w ≠ .x)
    (hprio : (G_bin n).priority topV < (G_bin n).priority w)
    (hstep : HitsWithTop glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w) p topV) :
    HitsWithTop glob n b s w p w := by
  have hnot_lt : ¬(predRank0 glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w) <
      predRank0 glob n b s topV) :=
    fun h => pred_not_mem_path_of_rank_lt glob n b s hvalid _ topV h hstep.2.1
  have hlt := predRank0_step_lt glob n b s hvalid w hw
  have h1 := hstep.1
  exact hitsWithTop_of_step_gt glob n b s hvalid w p topV hw (by omega) hprio hstep

lemma gkOrder_of_portalCR (glob : Bool) (n b s : ℕ) (_hvalid : ValidState n b s) (i : Fin n)
    (h_gk : GKOrderProp glob n b s i)
    (htau : chooseTauEdge1 n b s (.g i) = true)
    {w_p w_k : V_bin n}
    (hp : PortalCR glob n b s w_p)
    (hk : HitsK glob n b s w_k i) :
    if (b.testBit i.val = true ∨ 3 * (n + 2 * i.val + 1) + 2 ≤ s) ∧
        ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) then
      ValueLT (G_bin n) (predVal glob n b s w_p) (predVal glob n b s w_k)
    else
      ValueLT (G_bin n) (predVal glob n b s w_k) (predVal glob n b s w_p) :=
  h_gk htau w_p w_k hp hk

lemma portalCR_lp1 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    PortalCR glob n b s (.lp1 (tap_bin n i)) := by
  have hn := hvalid.1
  let m := tap_bin n i
  have hm1 : 1 ≤ m.val := by dsimp [m, tap_bin]; omega
  unfold PortalCR
  by_cases hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)
  · rw [if_pos hclose]
    rcases hclose with ⟨hb, hs2 | hs3⟩
    · exact (hitsWithTop_lp1_s_eq_close_add_two_aux glob n b s hvalid ⟨hb, hs2⟩ m.val m.isLt hm1).2.2
    · exact (hitsWithTop_lp1_s_eq_close_add_three_aux glob n b s hvalid ⟨hb, hs3⟩ m.val m.isLt hm1).2.2.2
  · rw [if_neg hclose]
    exact (hitsWithTop_lp1_not_close glob n b s hvalid m hclose).2

lemma portalCR_lp3 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    PortalCR glob n b s (.lp3 (tap_bin n i)) := by
  let m := tap_bin n i
  unfold PortalCR
  by_cases hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)
  · rw [if_pos hclose]
    rcases hclose with ⟨hb, hs2 | hs3⟩
    · exact (hitsWithTop_lp3_s_eq_close_add_two_aux glob n b s hvalid ⟨hb, hs2⟩ m.val m.isLt).2.2
    · exact (hitsWithTop_lp3_s_eq_close_add_three_aux glob n b s hvalid ⟨hb, hs3⟩ m.val m.isLt).2.2
  · rw [if_neg hclose]
    rcases Nat.eq_zero_or_pos s with hs0 | hs1
    · exact (hitsWithTop_lp3_not_close_zero_aux glob n b s hvalid hclose hs0 m.val m.isLt).2
    · exact (hitsWithTop_lp3_not_close_pos_aux glob n b s hvalid hclose hs1 m.val m.isLt).2

lemma portalCR_lp2 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n) :
    PortalCR glob n b s (.lp2 (tap_bin n i)) := by
  let m := tap_bin n i
  unfold PortalCR
  by_cases hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)
  · rw [if_pos hclose]
    rcases hclose with ⟨hb, hs2 | hs3⟩
    · exact (hitsWithTop_lp2_s_eq_close_add_two_aux glob n b s hvalid ⟨hb, hs2⟩ m.val m.isLt).2.2
    · exact (hitsWithTop_lp2_s_eq_close_add_three_aux glob n b s hvalid ⟨hb, hs3⟩ m.val m.isLt).2.2
  · rw [if_neg hclose]
    by_cases hs2 : s < 2
    · exact (hitsWithTop_lp2_not_close_lt_two_aux glob n b s hvalid hclose hs2 m.val m.isLt).2
    · exact (hitsWithTop_lp2_not_close_ge_two_aux glob n b s hvalid hclose (by omega) m.val m.isLt).2

def targetCR (n b s : ℕ) : V_bin n :=
  if b < 2 ^ n - 1 ∧ s = S_close0 n b + 2 then .r_a else .c

lemma targetCR_eq_c_of_lt_two (n b s : ℕ) (hs2 : s < 2) : targetCR n b s = .c := by
  unfold targetCR
  rw [if_neg]
  rintro ⟨_, h⟩
  unfold S_close0 at h
  omega

lemma hitsWithTop_lp1_targetCR (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hnot_s3 : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 3)) :
    let m := tap_bin n i
    HitsWithTop glob n b s (.lp1 m) (targetCR n b s)
      (.b ⟨3 * min m.val (s / 3), by have := m.isLt; omega⟩) := by
  have hn := hvalid.1
  let m := tap_bin n i
  have hm1 : 1 ≤ m.val := by dsimp [m, tap_bin]; omega
  unfold targetCR
  by_cases hs2 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 2
  · rw [if_pos hs2]
    exact (hitsWithTop_lp1_s_eq_close_add_two_aux glob n b s hvalid hs2 m.val m.isLt hm1).1
  · rw [if_neg hs2]
    have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
      rintro ⟨hb, h2 | h3⟩; exact hs2 ⟨hb, h2⟩; exact hnot_s3 ⟨hb, h3⟩
    exact (hitsWithTop_lp1_not_close glob n b s hvalid m hnot_close).1

lemma hitsWithTop_lp3_targetCR_pos (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hnot_s3 : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 3)) (hs1 : 1 ≤ s) :
    let m := tap_bin n i
    HitsWithTop glob n b s (.lp3 m) (targetCR n b s)
      (.b ⟨3 * min m.val ((s - 1) / 3) + 1, by have := m.isLt; omega⟩) := by
  let m := tap_bin n i
  unfold targetCR
  by_cases hs2 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 2
  · rw [if_pos hs2]
    exact (hitsWithTop_lp3_s_eq_close_add_two_aux glob n b s hvalid hs2 m.val m.isLt).1
  · rw [if_neg hs2]
    have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
      rintro ⟨hb, h2 | h3⟩; exact hs2 ⟨hb, h2⟩; exact hnot_s3 ⟨hb, h3⟩
    exact (hitsWithTop_lp3_not_close_pos_aux glob n b s hvalid hnot_close hs1 m.val m.isLt).1

lemma hitsWithTop_lp2_targetCR_ge_two (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hnot_s3 : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 3)) (hs2_ge : 2 ≤ s) :
    let m := tap_bin n i
    HitsWithTop glob n b s (.lp2 m) (targetCR n b s)
      (.b ⟨3 * min m.val ((s - 2) / 3) + 2, by have := m.isLt; omega⟩) := by
  let m := tap_bin n i
  unfold targetCR
  by_cases hs2 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 2
  · rw [if_pos hs2]
    exact (hitsWithTop_lp2_s_eq_close_add_two_aux glob n b s hvalid hs2 m.val m.isLt).1
  · rw [if_neg hs2]
    have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
      rintro ⟨hb, h2 | h3⟩; exact hs2 ⟨hb, h2⟩; exact hnot_s3 ⟨hb, h3⟩
    exact (hitsWithTop_lp2_not_close_ge_two_aux glob n b s hvalid hnot_close hs2_ge m.val m.isLt).1

/-! ### Part 4: `BestEdgeProp` for `.d3`, `.d2`, `.d1` -/

theorem bestEdge_d3 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (_h_portal : PortalOrderProp glob n b s) (i : Fin n) (h_gk : GKOrderProp glob n b s i) :
    BestEdgeProp glob n b s (.d3 i) := by
  intro _ _
  have hn := hvalid.1
  let m := tap_bin n i
  have hm1 : 1 ≤ m.val := by dsimp [m, tap_bin]; omega
  have he0 : edge0 n (.d3 i) = .lp3 m := rfl
  have he1 : edge1 n (.d3 i) = .g i := rfl
  by_cases htau : chooseTauEdge1 n b s (.g i) = true
  · have hbe_eq := bestEdge1_d3_of_tau_true n b s hvalid i htau
    have hgk := gkOrder_of_portalCR glob n b s hvalid i h_gk htau
      (portalCR_lp3 glob n b s hvalid i) (hitsK_g glob n b s hvalid i htau)
    by_cases hcond : (b.testBit i.val = true ∨ 3 * (n + 2 * i.val + 1) + 2 ≤ s) ∧
        ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))
    · have hbe : bestEdge1 n b s (.d3 i) = true := by rw [hbe_eq, decide_eq_true_eq]; exact hcond
      unfold bestEdge worstEdge
      rw [if_pos hbe, if_pos hbe, he0, he1]
      rw [if_pos hcond] at hgk
      exact hgk
    · have hbe : bestEdge1 n b s (.d3 i) = false := by rw [hbe_eq, decide_eq_false_iff_not]; exact hcond
      unfold bestEdge worstEdge
      rw [hbe, he0, he1]
      rw [if_neg hcond] at hgk
      exact hgk
  · have htau' : chooseTauEdge1 n b s (.g i) = false := Bool.eq_false_iff.mpr htau
    have hbe_eq := bestEdge1_d3_of_tau_false n b s hvalid i htau'
    have htau_cond := htau'
    dsimp [chooseTauEdge1] at htau_cond
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at htau_cond
    rcases htau_cond with ⟨⟨hbit, hlt_T2⟩, _⟩
    have hg_step := step_g_false glob n b s i htau'
    by_cases hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
    · have hlt_lz : lowestZero0 b n < i.val := by
        have := lowestZero0_le_of_testBit_false i.isLt hbit
        have := hs3.2; unfold S_close0 at this; omega
      have hs_lt_T : s < 3 * (n + 2 * i.val + 1) := by
        have := hs3.2; unfold S_close0 at this; omega
      have hmod2 : s % 3 = 2 := by have := hs3.2; unfold S_close0 at this; omega
      have hbe : bestEdge1 n b s (.d3 i) = false := by
        rw [hbe_eq, decide_eq_false_iff_not]; omega
      unfold bestEdge worstEdge
      rw [hbe, he0, he1]
      have hce1 : chooseEdge1 glob n b s (.d1 i) = false := by
        dsimp [chooseEdge1]
        rw [hbit, if_neg (by simp), if_neg (by omega)]
        cases glob <;> simp_all
      have hd1_step := step_d1_false glob n b s i hce1
      have hlp1_top := (hitsWithTop_lp1_s_eq_close_add_three_aux glob n b s hvalid hs3 m.val m.isLt hm1).2.1
      have hd1_top : HitsWithTop glob n b s (.d1 i) .r_2 .r_2_odd := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.d1 i) .r_2 .r_2_odd (by rintro ⟨⟩)
          (lt_trans (prio_d1_lt_d2 n i) (lt_trans (prio_d2_lt_d3 n i) (lt_trans (prio_d3_lt_g n i) (prio_g_lt_r_2_odd n i))))
        rw [hd1_step]; exact hlp1_top
      have hg_top : HitsWithTop glob n b s (.g i) .r_2 .r_2_odd := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.g i) .r_2 .r_2_odd (by rintro ⟨⟩)
          (prio_g_lt_r_2_odd n i)
        rw [hg_step]; exact hd1_top
      have hlp3_top := (hitsWithTop_lp3_s_eq_close_add_three_aux glob n b s hvalid hs3 m.val m.isLt).1
      exact predVal_lt_of_hitsWithTop_odd glob n b s hvalid hg_top hlp3_top
        (prio_l3_lt_r_2_odd n _) (prio_r_2_odd_odd n)
    · by_cases hce1 : chooseEdge1 glob n b s (.d1 i) = true
      · have hce1_cond : 3 * (n + 2 * i.val + 1) ≤ s ∨ s % 3 = 0 := by
          dsimp [chooseEdge1] at hce1
          rw [hbit, if_neg (by simp)] at hce1
          split_ifs at hce1 with hT
          · exact Or.inl hT
          · simp only [decide_eq_true_eq] at hce1; exact Or.inr (by omega)
          · exact Or.inr ‹_›
        have hce2 : chooseEdge1 glob n b s (.d2 i) = false := by
          dsimp [chooseEdge1]
          rw [hbit, if_neg (by simp), if_neg hlt_T2]
          split_ifs with hT
          · rfl
          · rfl
          · rw [decide_eq_false_iff_not]; omega
        have hbe : bestEdge1 n b s (.d3 i) = true := by
          rw [hbe_eq, decide_eq_true_eq]; exact hce1_cond
        unfold bestEdge worstEdge
        rw [if_pos hbe, if_pos hbe, he0, he1]
        have hd1_step := step_d1_true glob n b s i hce1
        have hd2_step := step_d2_false glob n b s i hce2
        by_cases hs0 : s = 0
        · have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
            unfold S_close0; omega
          let m0 : Fin (3 * n - 1) := ⟨0, by omega⟩
          have hlp3_top : HitsWithTop glob n b s (.lp3 m) .r_2 (.l3 m0) :=
            hitsWithTop_lp3_not_close_zero_r2_aux glob n b s hvalid hnot_close hs0 m.val m.isLt
          have hlp2_top : HitsWithTop glob n b s (.lp2 m) .r_2 (.l2 m0) :=
            hitsWithTop_lp2_not_close_lt_two_r2_aux glob n b s hvalid hnot_close (by omega) m.val m.isLt
          have hd2_top : HitsWithTop glob n b s (.d2 i) .r_2 (.d2 i) := by
            apply hitsWithTop_of_step_gt' glob n b s hvalid (.d2 i) .r_2 (.l2 m0) (by rintro ⟨⟩)
              (lt_trans (prio_l2_lt_d1 n m0 i) (prio_d1_lt_d2 n i))
            rw [hd2_step]; exact hlp2_top
          have hd1_top : HitsWithTop glob n b s (.d1 i) .r_2 (.d2 i) := by
            apply hitsWithTop_of_step_lt glob n b s hvalid (.d1 i) .r_2 (.d2 i) (by rintro ⟨⟩)
              (prio_d1_lt_d2 n i)
            rw [hd1_step]; exact hd2_top
          have hg_top : HitsWithTop glob n b s (.g i) .r_2 (.g i) := by
            apply hitsWithTop_of_step_gt' glob n b s hvalid (.g i) .r_2 (.d2 i) (by rintro ⟨⟩)
              (lt_trans (prio_d2_lt_d3 n i) (prio_d3_lt_g n i))
            rw [hg_step]; exact hd1_top
          exact predVal_lt_of_hitsWithTop_even glob n b s hvalid hlp3_top hg_top
            (lt_trans (prio_l3_lt_d1 n m0 i) (lt_trans (prio_d1_lt_d2 n i) (lt_trans (prio_d2_lt_d3 n i) (prio_d3_lt_g n i))))
            (prio_g_even n i)
        · have hs2_ge : 2 ≤ s := by dsimp [m, tap_bin] at *; omega
          have hlp3_top := hitsWithTop_lp3_targetCR_pos glob n b s hvalid i hs3 (by omega)
          have hlp2_top := hitsWithTop_lp2_targetCR_ge_two glob n b s hvalid i hs3 hs2_ge
          have hd2_top : HitsWithTop glob n b s (.d2 i) (targetCR n b s)
              (.b ⟨3 * min m.val ((s - 2) / 3) + 2, by have := m.isLt; omega⟩) := by
            apply hitsWithTop_of_step_lt glob n b s hvalid (.d2 i) (targetCR n b s) _ (by rintro ⟨⟩)
              (lt_trans (prio_d2_lt_d3 n i) (lt_trans (prio_d3_lt_g n i) (prio_g_lt_b n i _)))
            rw [hd2_step]; exact hlp2_top
          have hd1_top : HitsWithTop glob n b s (.d1 i) (targetCR n b s)
              (.b ⟨3 * min m.val ((s - 2) / 3) + 2, by have := m.isLt; omega⟩) := by
            apply hitsWithTop_of_step_lt glob n b s hvalid (.d1 i) (targetCR n b s) _ (by rintro ⟨⟩)
              (lt_trans (prio_d1_lt_d2 n i) (lt_trans (prio_d2_lt_d3 n i) (lt_trans (prio_d3_lt_g n i) (prio_g_lt_b n i _))))
            rw [hd1_step]; exact hd2_top
          have hg_top : HitsWithTop glob n b s (.g i) (targetCR n b s)
              (.b ⟨3 * min m.val ((s - 2) / 3) + 2, by have := m.isLt; omega⟩) := by
            apply hitsWithTop_of_step_lt glob n b s hvalid (.g i) (targetCR n b s) _ (by rintro ⟨⟩)
              (prio_g_lt_b n i _)
            rw [hg_step]; exact hd1_top
          apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hlp3_top hg_top
          · apply priority_b_strictMono; dsimp [m, tap_bin] at *; omega
          · exact prio_b_even n _
      · have hce1' : chooseEdge1 glob n b s (.d1 i) = false := Bool.eq_false_iff.mpr hce1
        have hs_lt_T : s < 3 * (n + 2 * i.val + 1) := by
          by_contra hge
          dsimp [chooseEdge1] at hce1'
          rw [hbit, if_neg (by simp), if_pos (by omega)] at hce1'
          cases hce1'
        have hd1_step := step_d1_false glob n b s i hce1'
        have hlp1_top := hitsWithTop_lp1_targetCR glob n b s hvalid i hs3
        have hd1_top : HitsWithTop glob n b s (.d1 i) (targetCR n b s)
            (.b ⟨3 * min m.val (s / 3), by have := m.isLt; omega⟩) := by
          apply hitsWithTop_of_step_lt glob n b s hvalid (.d1 i) (targetCR n b s) _ (by rintro ⟨⟩)
            (lt_trans (prio_d1_lt_d2 n i) (lt_trans (prio_d2_lt_d3 n i) (lt_trans (prio_d3_lt_g n i) (prio_g_lt_b n i _))))
          rw [hd1_step]; exact hlp1_top
        have hg_top : HitsWithTop glob n b s (.g i) (targetCR n b s)
            (.b ⟨3 * min m.val (s / 3), by have := m.isLt; omega⟩) := by
          apply hitsWithTop_of_step_lt glob n b s hvalid (.g i) (targetCR n b s) _ (by rintro ⟨⟩)
            (prio_g_lt_b n i _)
          rw [hg_step]; exact hd1_top
        by_cases hmod0 : s % 3 = 0
        · have hbe : bestEdge1 n b s (.d3 i) = true := by
            rw [hbe_eq, decide_eq_true_eq]; exact Or.inr hmod0
          unfold bestEdge worstEdge
          rw [if_pos hbe, if_pos hbe, he0, he1]
          by_cases hs0 : s = 0
          · have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
              unfold S_close0; omega
            have hlp3_top := (hitsWithTop_lp3_not_close_zero_aux glob n b s hvalid hnot_close hs0 m.val m.isLt).1
            rw [targetCR_eq_c_of_lt_two n b s (by omega)] at hg_top
            exact predVal_lt_of_hitsWithTop_odd glob n b s hvalid hlp3_top hg_top
              (prio_b_lt_c_odd n _) (prio_c_odd_odd n)
          · have hlp3_top := hitsWithTop_lp3_targetCR_pos glob n b s hvalid i hs3 (by omega)
            apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hlp3_top hg_top
            · apply priority_b_strictMono; dsimp [m, tap_bin] at *; omega
            · exact prio_b_even n _
        · have hbe : bestEdge1 n b s (.d3 i) = false := by
            rw [hbe_eq, decide_eq_false_iff_not]; omega
          unfold bestEdge worstEdge
          rw [hbe, he0, he1]
          have hlp3_top := hitsWithTop_lp3_targetCR_pos glob n b s hvalid i hs3 (by omega)
          apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hg_top hlp3_top
          · apply priority_b_strictMono; dsimp [m, tap_bin] at *; omega
          · exact prio_b_even n _

theorem bestEdge_d2 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (_h_portal : PortalOrderProp glob n b s) (i : Fin n) (h_gk : GKOrderProp glob n b s i) :
    BestEdgeProp glob n b s (.d2 i) := by
  intro _ _
  have hn := hvalid.1
  let m := tap_bin n i
  have he0 : edge0 n (.d2 i) = .lp2 m := rfl
  have he1 : edge1 n (.d2 i) = .d3 i := rfl
  cases hbit : b.testBit i.val with
  | true =>
    have hbe_eq := bestEdge1_d2_of_testBit_true n b s hvalid i hbit
    have htau : chooseTauEdge1 n b s (.g i) = true := by
      dsimp [chooseTauEdge1]; rw [hbit]; simp
    by_cases hs3_cut : b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ s = S_close0 n b + 3
    · have hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 := ⟨hs3_cut.1, hs3_cut.2.2⟩
      have hbe : bestEdge1 n b s (.d2 i) = false := by
        rw [hbe_eq, decide_eq_false_iff_not, not_not]
        exact ⟨hs3_cut.1, hs3_cut.2.1, Or.inr hs3_cut.2.2⟩
      unfold bestEdge worstEdge
      rw [hbe, he0, he1]
      have hce3 : chooseEdge1 glob n b s (.d3 i) = false := by
        dsimp [chooseEdge1]; rw [hbit, if_pos rfl, if_pos hs3_cut]
      have hd3_step := step_d3_false glob n b s i hce3
      have hlp3_top := (hitsWithTop_lp3_s_eq_close_add_three_aux glob n b s hvalid hs3 m.val m.isLt).1
      have hd3_top : HitsWithTop glob n b s (.d3 i) .r_2 (.d3 i) := by
        apply hitsWithTop_of_step_gt' glob n b s hvalid (.d3 i) .r_2 _ (by rintro ⟨⟩)
          (lt_trans (prio_l3_lt_d1 n _ i) (lt_trans (prio_d1_lt_d2 n i) (prio_d2_lt_d3 n i)))
        rw [hd3_step]; exact hlp3_top
      have hlp2_top := (hitsWithTop_lp2_s_eq_close_add_three_aux glob n b s hvalid hs3 m.val m.isLt).1
      exact predVal_lt_of_hitsWithTop_odd glob n b s hvalid hd3_top hlp2_top
        (lt_trans (prio_l2_lt_d1 n _ i) (lt_trans (prio_d1_lt_d2 n i) (prio_d2_lt_d3 n i)))
        (prio_d3_odd n i)
    · have hce3 : chooseEdge1 glob n b s (.d3 i) = true := by
        dsimp [chooseEdge1]; rw [hbit, if_pos rfl, if_neg hs3_cut]
      have hgk := gkOrder_of_portalCR glob n b s hvalid i h_gk htau
        (portalCR_lp2 glob n b s hvalid i) (hitsK_d3 glob n b s hvalid i hce3 htau)
      by_cases hcond : ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))
      · have hbe : bestEdge1 n b s (.d2 i) = true := by rw [hbe_eq, decide_eq_true_eq]; exact hcond
        unfold bestEdge worstEdge
        rw [if_pos hbe, if_pos hbe, he0, he1]
        rw [if_pos ⟨Or.inl hbit, hcond⟩] at hgk
        exact hgk
      · have hbe : bestEdge1 n b s (.d2 i) = false := by rw [hbe_eq, decide_eq_false_iff_not]; exact hcond
        unfold bestEdge worstEdge
        rw [hbe, he0, he1]
        rw [if_neg (fun h => hcond h.2)] at hgk
        exact hgk
  | false =>
    have hbe_eq := bestEdge1_d2_of_testBit_false n b s hvalid i hbit
    have hle_lz : lowestZero0 b n ≤ i.val := lowestZero0_le_of_testBit_false i.isLt hbit
    by_cases hT2 : 3 * (n + 2 * i.val + 1) + 2 ≤ s
    · have hbe : bestEdge1 n b s (.d2 i) = true := by
        rw [hbe_eq, decide_eq_true_eq]; exact Or.inl (by omega)
      unfold bestEdge worstEdge
      rw [if_pos hbe, if_pos hbe, he0, he1]
      have hce3 : chooseEdge1 glob n b s (.d3 i) = true := by
        dsimp [chooseEdge1]; rw [hbit, if_neg (by simp), if_pos (by omega)]
      have htau : chooseTauEdge1 n b s (.g i) = true := by
        dsimp [chooseTauEdge1]; rw [hbit, Bool.false_or, decide_eq_true hT2, Bool.true_or]
      have hgk := gkOrder_of_portalCR glob n b s hvalid i h_gk htau
        (portalCR_lp2 glob n b s hvalid i) (hitsK_d3 glob n b s hvalid i hce3 htau)
      rw [if_pos ⟨Or.inr hT2, by omega⟩] at hgk
      exact hgk
    · by_cases hT1 : s = 3 * (n + 2 * i.val + 1) + 1
      · have hbe : bestEdge1 n b s (.d2 i) = true := by
          rw [hbe_eq, decide_eq_true_eq]; exact Or.inl (by omega)
        unfold bestEdge worstEdge
        rw [if_pos hbe, if_pos hbe, he0, he1]
        have hce3 : chooseEdge1 glob n b s (.d3 i) = true := by
          dsimp [chooseEdge1]; rw [hbit, if_neg (by simp), if_pos (by omega)]
        have htau : chooseTauEdge1 n b s (.g i) = false := by
          have hulim : uLim0 b n ≤ n := by have := lowestOne0_le b n; unfold uLim0; split_ifs <;> omega
          dsimp [chooseTauEdge1]
          rw [hbit, Bool.false_or, decide_eq_false hT2, Bool.false_or, decide_eq_false_iff_not]
          omega
        have hce1 : chooseEdge1 glob n b s (.d1 i) = true := by
          dsimp [chooseEdge1]; rw [hbit, if_neg (by simp), if_pos (by omega)]
        have hce2 : chooseEdge1 glob n b s (.d2 i) = false := by
          dsimp [chooseEdge1]; rw [hbit, if_neg (by simp), if_neg hT2, if_pos (by omega)]
        have hd3_step := step_d3_true glob n b s i hce3
        have hg_step := step_g_false glob n b s i htau
        have hd1_step := step_d1_true glob n b s i hce1
        have hd2_step := step_d2_false glob n b s i hce2
        have hd2_top : HitsWithTop glob n b s (.d2 i) (.lp2 m) (.d2 i) :=
          hitsWithTop_of_step_eq glob n b s hvalid (.d2 i) (.lp2 m) (by rintro ⟨⟩) hd2_step
        have hd1_top : HitsWithTop glob n b s (.d1 i) (.lp2 m) (.d2 i) := by
          apply hitsWithTop_of_step_lt glob n b s hvalid (.d1 i) (.lp2 m) (.d2 i) (by rintro ⟨⟩)
            (prio_d1_lt_d2 n i)
          rw [hd1_step]; exact hd2_top
        have hg_top : HitsWithTop glob n b s (.g i) (.lp2 m) (.g i) := by
          apply hitsWithTop_of_step_gt' glob n b s hvalid (.g i) (.lp2 m) (.d2 i) (by rintro ⟨⟩)
            (lt_trans (prio_d2_lt_d3 n i) (prio_d3_lt_g n i))
          rw [hg_step]; exact hd1_top
        have hd3_top : HitsWithTop glob n b s (.d3 i) (.lp2 m) (.g i) := by
          apply hitsWithTop_of_step_lt glob n b s hvalid (.d3 i) (.lp2 m) (.g i) (by rintro ⟨⟩)
            (prio_d3_lt_g n i)
          rw [hd3_step]; exact hg_top
        exact predVal_lt_of_hitsWithTop_even_self glob n b s hvalid hd3_top (prio_g_even n i)
      · have hs_le_T : s ≤ 3 * (n + 2 * i.val + 1) := by omega
        by_cases hce3 : chooseEdge1 glob n b s (.d3 i) = true
        · have hce3_cond : s < 3 * (n + 2 * i.val + 1) ∧ glob = false ∧ s % 3 = 1 ∧
              ¬(0 < b ∧ i.val + 1 + s < d3Cut0 b n) := by
            dsimp [chooseEdge1] at hce3
            rw [hbit, if_neg (by simp), if_neg (by omega)] at hce3
            split_ifs at hce3 with hTeq hglob hmod
            · rw [decide_eq_true_eq] at hce3
              exact ⟨by omega, Bool.eq_false_iff.mpr hglob, hmod, hce3⟩
          rcases hce3_cond with ⟨hs_lt_T, hglob, hmod1, hnot_d3⟩
          have hbe : bestEdge1 n b s (.d2 i) = true := by
            rw [hbe_eq, decide_eq_true_eq]; exact Or.inr ⟨by omega, hmod1⟩
          unfold bestEdge worstEdge
          rw [if_pos hbe, if_pos hbe, he0, he1]
          have htau : chooseTauEdge1 n b s (.g i) = false := by
            dsimp [chooseTauEdge1]
            rw [hbit, Bool.false_or, decide_eq_false hT2, Bool.false_or, decide_eq_false_iff_not]
            rintro ⟨hb0, hil1, hlim⟩
            apply hnot_d3
            rw [d3Cut0_eq_uLim0_add_one hil1]
            exact ⟨hb0, by omega⟩
          have hce1 : chooseEdge1 glob n b s (.d1 i) = false := by
            dsimp [chooseEdge1]
            rw [hbit, if_neg (by simp), if_neg (by omega), if_neg (by simp [hglob]), if_neg (by omega)]
          have hs3 : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 3) := by
            unfold S_close0; omega
          have hd3_step := step_d3_true glob n b s i hce3
          have hg_step := step_g_false glob n b s i htau
          have hd1_step := step_d1_false glob n b s i hce1
          have hlp1_top := hitsWithTop_lp1_targetCR glob n b s hvalid i hs3
          have hd1_top : HitsWithTop glob n b s (.d1 i) (targetCR n b s)
              (.b ⟨3 * min m.val (s / 3), by have := m.isLt; omega⟩) := by
            apply hitsWithTop_of_step_lt glob n b s hvalid (.d1 i) (targetCR n b s) _ (by rintro ⟨⟩)
              (lt_trans (prio_d1_lt_d2 n i) (lt_trans (prio_d2_lt_d3 n i) (lt_trans (prio_d3_lt_g n i) (prio_g_lt_b n i _))))
            rw [hd1_step]; exact hlp1_top
          have hg_top : HitsWithTop glob n b s (.g i) (targetCR n b s)
              (.b ⟨3 * min m.val (s / 3), by have := m.isLt; omega⟩) := by
            apply hitsWithTop_of_step_lt glob n b s hvalid (.g i) (targetCR n b s) _ (by rintro ⟨⟩)
              (prio_g_lt_b n i _)
            rw [hg_step]; exact hd1_top
          have hd3_top : HitsWithTop glob n b s (.d3 i) (targetCR n b s)
              (.b ⟨3 * min m.val (s / 3), by have := m.isLt; omega⟩) := by
            apply hitsWithTop_of_step_lt glob n b s hvalid (.d3 i) (targetCR n b s) _ (by rintro ⟨⟩)
              (lt_trans (prio_d3_lt_g n i) (prio_g_lt_b n i _))
            rw [hd3_step]; exact hg_top
          by_cases hs2_lt : s < 2
          · have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
              unfold S_close0; omega
            have hlp2_top := (hitsWithTop_lp2_not_close_lt_two_aux glob n b s hvalid hnot_close hs2_lt m.val m.isLt).1
            rw [targetCR_eq_c_of_lt_two n b s hs2_lt] at hd3_top
            exact predVal_lt_of_hitsWithTop_odd glob n b s hvalid hlp2_top hd3_top
              (prio_b_lt_c_odd n _) (prio_c_odd_odd n)
          · have hlp2_top := hitsWithTop_lp2_targetCR_ge_two glob n b s hvalid i hs3 (by omega)
            apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hlp2_top hd3_top
            · apply priority_b_strictMono; dsimp [m, tap_bin] at *; omega
            · exact prio_b_even n _
        · have hce3' : chooseEdge1 glob n b s (.d3 i) = false := Bool.eq_false_iff.mpr hce3
          have hd3_step := step_d3_false glob n b s i hce3'
          by_cases hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
          · have hmod2 : s % 3 = 2 := by have := hs3.2; unfold S_close0 at this; omega
            have hbe : bestEdge1 n b s (.d2 i) = false := by
              rw [hbe_eq, decide_eq_false_iff_not]; omega
            unfold bestEdge worstEdge
            rw [hbe, he0, he1]
            have hlp3_top := (hitsWithTop_lp3_s_eq_close_add_three_aux glob n b s hvalid hs3 m.val m.isLt).1
            have hd3_top : HitsWithTop glob n b s (.d3 i) .r_2 (.d3 i) := by
              apply hitsWithTop_of_step_gt' glob n b s hvalid (.d3 i) .r_2 _ (by rintro ⟨⟩)
                (lt_trans (prio_l3_lt_d1 n _ i) (lt_trans (prio_d1_lt_d2 n i) (prio_d2_lt_d3 n i)))
              rw [hd3_step]; exact hlp3_top
            have hlp2_top := (hitsWithTop_lp2_s_eq_close_add_three_aux glob n b s hvalid hs3 m.val m.isLt).1
            exact predVal_lt_of_hitsWithTop_odd glob n b s hvalid hd3_top hlp2_top
              (lt_trans (prio_l2_lt_d1 n _ i) (lt_trans (prio_d1_lt_d2 n i) (prio_d2_lt_d3 n i)))
              (prio_d3_odd n i)
          · by_cases hcond : 3 * (n + 2 * i.val + 1) + 1 ≤ s ∨ (s + 1 < 3 * (n + 2 * i.val + 1) ∧ s % 3 = 1)
            · have hbe : bestEdge1 n b s (.d2 i) = true := by rw [hbe_eq, decide_eq_true_eq]; exact hcond
              unfold bestEdge worstEdge
              rw [if_pos hbe, if_pos hbe, he0, he1]
              have hs1_cond : s + 1 < 3 * (n + 2 * i.val + 1) ∧ s % 3 = 1 := by omega
              have hlp3_top := hitsWithTop_lp3_targetCR_pos glob n b s hvalid i hs3 (by omega)
              have hd3_top : HitsWithTop glob n b s (.d3 i) (targetCR n b s)
                  (.b ⟨3 * min m.val ((s - 1) / 3) + 1, by have := m.isLt; omega⟩) := by
                apply hitsWithTop_of_step_lt glob n b s hvalid (.d3 i) (targetCR n b s) _ (by rintro ⟨⟩)
                  (lt_trans (prio_d3_lt_g n i) (prio_g_lt_b n i _))
                rw [hd3_step]; exact hlp3_top
              by_cases hs2_lt : s < 2
              · have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
                  unfold S_close0; omega
                have hlp2_top := (hitsWithTop_lp2_not_close_lt_two_aux glob n b s hvalid hnot_close hs2_lt m.val m.isLt).1
                rw [targetCR_eq_c_of_lt_two n b s hs2_lt] at hd3_top
                exact predVal_lt_of_hitsWithTop_odd glob n b s hvalid hlp2_top hd3_top
                  (prio_b_lt_c_odd n _) (prio_c_odd_odd n)
              · have hlp2_top := hitsWithTop_lp2_targetCR_ge_two glob n b s hvalid i hs3 (by omega)
                apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hlp2_top hd3_top
                · apply priority_b_strictMono; dsimp [m, tap_bin] at *; omega
                · exact prio_b_even n _
            · have hbe : bestEdge1 n b s (.d2 i) = false := by rw [hbe_eq, decide_eq_false_iff_not]; exact hcond
              unfold bestEdge worstEdge
              rw [hbe, he0, he1]
              by_cases hs0 : s = 0
              · have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
                  unfold S_close0; omega
                let m0 : Fin (3 * n - 1) := ⟨0, by omega⟩
                have hlp3_top := hitsWithTop_lp3_not_close_zero_r2_aux glob n b s hvalid hnot_close hs0 m.val m.isLt
                have hlp2_top := hitsWithTop_lp2_not_close_lt_two_r2_aux glob n b s hvalid hnot_close (by omega) m.val m.isLt
                have hd3_top : HitsWithTop glob n b s (.d3 i) .r_2 (.d3 i) := by
                  apply hitsWithTop_of_step_gt' glob n b s hvalid (.d3 i) .r_2 (.l3 m0) (by rintro ⟨⟩)
                    (lt_trans (prio_l3_lt_d1 n m0 i) (lt_trans (prio_d1_lt_d2 n i) (prio_d2_lt_d3 n i)))
                  rw [hd3_step]; exact hlp3_top
                exact predVal_lt_of_hitsWithTop_odd glob n b s hvalid hd3_top hlp2_top
                  (lt_trans (prio_l2_lt_d1 n m0 i) (lt_trans (prio_d1_lt_d2 n i) (prio_d2_lt_d3 n i)))
                  (prio_d3_odd n i)
              · have hs2_ge : 2 ≤ s := by omega
                have hlp3_top := hitsWithTop_lp3_targetCR_pos glob n b s hvalid i hs3 (by omega)
                have hd3_top : HitsWithTop glob n b s (.d3 i) (targetCR n b s)
                    (.b ⟨3 * min m.val ((s - 1) / 3) + 1, by have := m.isLt; omega⟩) := by
                  apply hitsWithTop_of_step_lt glob n b s hvalid (.d3 i) (targetCR n b s) _ (by rintro ⟨⟩)
                    (lt_trans (prio_d3_lt_g n i) (prio_g_lt_b n i _))
                  rw [hd3_step]; exact hlp3_top
                have hlp2_top := hitsWithTop_lp2_targetCR_ge_two glob n b s hvalid i hs3 hs2_ge
                apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hd3_top hlp2_top
                · apply priority_b_strictMono; dsimp [m, tap_bin] at *; omega
                · exact prio_b_even n _

theorem bestEdge_d1 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (_h_portal : PortalOrderProp glob n b s) (i : Fin n) (h_gk : GKOrderProp glob n b s i) :
    BestEdgeProp glob n b s (.d1 i) := by
  intro _ _
  have hn := hvalid.1
  let m := tap_bin n i
  have hm1 : 1 ≤ m.val := by dsimp [m, tap_bin]; omega
  have he0 : edge0 n (.d1 i) = .lp1 m := rfl
  have he1 : edge1 n (.d1 i) = .d2 i := rfl
  cases hbit : b.testBit i.val with
  | true =>
    have hbe_eq := bestEdge1_d1_of_testBit_true n b s hvalid i hbit
    have htau : chooseTauEdge1 n b s (.g i) = true := by
      dsimp [chooseTauEdge1]; rw [hbit]; simp
    by_cases hs3_cut : b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ s = S_close0 n b + 3
    · have hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3 := ⟨hs3_cut.1, hs3_cut.2.2⟩
      have hbe : bestEdge1 n b s (.d1 i) = true := by
        rw [hbe_eq, decide_eq_true_eq]
        rintro ⟨_, _, hs2⟩; have := hs3_cut.2.2; omega
      unfold bestEdge worstEdge
      rw [if_pos hbe, if_pos hbe, he0, he1]
      have hce2 : chooseEdge1 glob n b s (.d2 i) = false := by
        dsimp [chooseEdge1]; rw [hbit, if_pos rfl, if_pos hs3_cut]
      have hd2_step := step_d2_false glob n b s i hce2
      have hlp1_top := (hitsWithTop_lp1_s_eq_close_add_three_aux glob n b s hvalid hs3 m.val m.isLt hm1).2.1
      have hlp2_top := (hitsWithTop_lp2_s_eq_close_add_three_aux glob n b s hvalid hs3 m.val m.isLt).1
      have hd2_top : HitsWithTop glob n b s (.d2 i) .r_2 (.d2 i) := by
        apply hitsWithTop_of_step_gt' glob n b s hvalid (.d2 i) .r_2 _ (by rintro ⟨⟩)
          (lt_trans (prio_l2_lt_d1 n _ i) (prio_d1_lt_d2 n i))
        rw [hd2_step]; exact hlp2_top
      exact predVal_lt_of_hitsWithTop_odd glob n b s hvalid hlp1_top hd2_top
        (lt_trans (prio_d2_lt_d3 n i) (lt_trans (prio_d3_lt_g n i) (prio_g_lt_r_2_odd n i)))
        (prio_r_2_odd_odd n)
    · have hce2 : chooseEdge1 glob n b s (.d2 i) = true := by
        dsimp [chooseEdge1]; rw [hbit, if_pos rfl, if_neg hs3_cut]
      have hce3 : chooseEdge1 glob n b s (.d3 i) = true := by
        dsimp [chooseEdge1]; rw [hbit, if_pos rfl, if_neg hs3_cut]
      have hgk := gkOrder_of_portalCR glob n b s hvalid i h_gk htau
        (portalCR_lp1 glob n b s hvalid i) (hitsK_d2 glob n b s hvalid i hce2 hce3 htau)
      by_cases hcond : ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ s = S_close0 n b + 2)
      · have hbe : bestEdge1 n b s (.d1 i) = true := by rw [hbe_eq, decide_eq_true_eq]; exact hcond
        unfold bestEdge worstEdge
        rw [if_pos hbe, if_pos hbe, he0, he1]
        have hcond' : ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
          rintro ⟨hb_lt, hil, hs2 | hs3⟩
          · exact hcond ⟨hb_lt, hil, hs2⟩
          · exact hs3_cut ⟨hb_lt, hil, hs3⟩
        rw [if_pos ⟨Or.inl hbit, hcond'⟩] at hgk
        exact hgk
      · have hbe : bestEdge1 n b s (.d1 i) = false := by rw [hbe_eq, decide_eq_false_iff_not]; exact hcond
        unfold bestEdge worstEdge
        rw [hbe, he0, he1]
        rw [not_not] at hcond
        have hcond' : ¬((b.testBit i.val = true ∨ 3 * (n + 2 * i.val + 1) + 2 ≤ s) ∧
            ¬(b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) := by
          rintro ⟨_, hnot⟩
          exact hnot ⟨hcond.1, hcond.2.1, Or.inl hcond.2.2⟩
        rw [if_neg hcond'] at hgk
        exact hgk
  | false =>
    have hbe_eq := bestEdge1_d1_of_testBit_false n b s hvalid i hbit
    have hle_lz : lowestZero0 b n ≤ i.val := lowestZero0_le_of_testBit_false i.isLt hbit
    by_cases hT2 : 3 * (n + 2 * i.val + 1) + 2 ≤ s
    · have hbe : bestEdge1 n b s (.d1 i) = true := by
        rw [hbe_eq, decide_eq_true_eq]; exact Or.inl (by omega)
      unfold bestEdge worstEdge
      rw [if_pos hbe, if_pos hbe, he0, he1]
      have hce2 : chooseEdge1 glob n b s (.d2 i) = true := by
        dsimp [chooseEdge1]; rw [hbit, if_neg (by simp), if_pos hT2]
      have hce3 : chooseEdge1 glob n b s (.d3 i) = true := by
        dsimp [chooseEdge1]; rw [hbit, if_neg (by simp), if_pos (by omega)]
      have htau : chooseTauEdge1 n b s (.g i) = true := by
        dsimp [chooseTauEdge1]; rw [hbit, Bool.false_or, decide_eq_true hT2, Bool.true_or]
      have hgk := gkOrder_of_portalCR glob n b s hvalid i h_gk htau
        (portalCR_lp1 glob n b s hvalid i) (hitsK_d2 glob n b s hvalid i hce2 hce3 htau)
      rw [if_pos ⟨Or.inr hT2, by omega⟩] at hgk
      exact hgk
    · by_cases hce2 : chooseEdge1 glob n b s (.d2 i) = true
      · have hce2_cond : s < 3 * (n + 2 * i.val + 1) ∧ glob = false ∧ s % 3 = 2 := by
          dsimp [chooseEdge1] at hce2
          rw [hbit, if_neg (by simp), if_neg hT2] at hce2
          split_ifs at hce2 with hT hglob
          · rw [decide_eq_true_eq] at hce2
            exact ⟨by omega, Bool.eq_false_iff.mpr hglob, hce2⟩
        rcases hce2_cond with ⟨hs_lt_T, hglob, hmod2⟩
        have hbe : bestEdge1 n b s (.d1 i) = true := by
          rw [hbe_eq, decide_eq_true_eq]; exact Or.inr hmod2
        unfold bestEdge worstEdge
        rw [if_pos hbe, if_pos hbe, he0, he1]
        have hce3 : chooseEdge1 glob n b s (.d3 i) = false := by
          dsimp [chooseEdge1]
          rw [hbit, if_neg (by simp), if_neg (by omega), if_neg (by omega), if_neg (by simp [hglob]), if_neg (by omega)]
        have hd2_step := step_d2_true glob n b s i hce2
        have hd3_step := step_d3_false glob n b s i hce3
        by_cases hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
        · have hlp1_top := (hitsWithTop_lp1_s_eq_close_add_three_aux glob n b s hvalid hs3 m.val m.isLt hm1).2.1
          have hlp3_top := (hitsWithTop_lp3_s_eq_close_add_three_aux glob n b s hvalid hs3 m.val m.isLt).1
          have hd3_top : HitsWithTop glob n b s (.d3 i) .r_2 (.d3 i) := by
            apply hitsWithTop_of_step_gt' glob n b s hvalid (.d3 i) .r_2 _ (by rintro ⟨⟩)
              (lt_trans (prio_l3_lt_d1 n _ i) (lt_trans (prio_d1_lt_d2 n i) (prio_d2_lt_d3 n i)))
            rw [hd3_step]; exact hlp3_top
          have hd2_top : HitsWithTop glob n b s (.d2 i) .r_2 (.d3 i) := by
            apply hitsWithTop_of_step_lt glob n b s hvalid (.d2 i) .r_2 (.d3 i) (by rintro ⟨⟩)
              (prio_d2_lt_d3 n i)
            rw [hd2_step]; exact hd3_top
          exact predVal_lt_of_hitsWithTop_odd glob n b s hvalid hlp1_top hd2_top
            (lt_trans (prio_d3_lt_g n i) (prio_g_lt_r_2_odd n i))
            (prio_r_2_odd_odd n)
        · have hlp1_top := hitsWithTop_lp1_targetCR glob n b s hvalid i hs3
          have hlp3_top := hitsWithTop_lp3_targetCR_pos glob n b s hvalid i hs3 (by omega)
          have hd3_top : HitsWithTop glob n b s (.d3 i) (targetCR n b s)
              (.b ⟨3 * min m.val ((s - 1) / 3) + 1, by have := m.isLt; omega⟩) := by
            apply hitsWithTop_of_step_lt glob n b s hvalid (.d3 i) (targetCR n b s) _ (by rintro ⟨⟩)
              (lt_trans (prio_d3_lt_g n i) (prio_g_lt_b n i _))
            rw [hd3_step]; exact hlp3_top
          have hd2_top : HitsWithTop glob n b s (.d2 i) (targetCR n b s)
              (.b ⟨3 * min m.val ((s - 1) / 3) + 1, by have := m.isLt; omega⟩) := by
            apply hitsWithTop_of_step_lt glob n b s hvalid (.d2 i) (targetCR n b s) _ (by rintro ⟨⟩)
              (lt_trans (prio_d2_lt_d3 n i) (lt_trans (prio_d3_lt_g n i) (prio_g_lt_b n i _)))
            rw [hd2_step]; exact hd3_top
          apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hlp1_top hd2_top
          · apply priority_b_strictMono; dsimp [m, tap_bin] at *; omega
          · exact prio_b_even n _
      · have hce2' : chooseEdge1 glob n b s (.d2 i) = false := Bool.eq_false_iff.mpr hce2
        have hd2_step := step_d2_false glob n b s i hce2'
        by_cases hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
        · have hmod2 : s % 3 = 2 := by have := hs3.2; unfold S_close0 at this; omega
          have hbe : bestEdge1 n b s (.d1 i) = true := by
            rw [hbe_eq, decide_eq_true_eq]; exact Or.inr hmod2
          unfold bestEdge worstEdge
          rw [if_pos hbe, if_pos hbe, he0, he1]
          have hlp1_top := (hitsWithTop_lp1_s_eq_close_add_three_aux glob n b s hvalid hs3 m.val m.isLt hm1).2.1
          have hlp2_top := (hitsWithTop_lp2_s_eq_close_add_three_aux glob n b s hvalid hs3 m.val m.isLt).1
          have hd2_top : HitsWithTop glob n b s (.d2 i) .r_2 (.d2 i) := by
            apply hitsWithTop_of_step_gt' glob n b s hvalid (.d2 i) .r_2 _ (by rintro ⟨⟩)
              (lt_trans (prio_l2_lt_d1 n _ i) (prio_d1_lt_d2 n i))
            rw [hd2_step]; exact hlp2_top
          exact predVal_lt_of_hitsWithTop_odd glob n b s hvalid hlp1_top hd2_top
            (lt_trans (prio_d2_lt_d3 n i) (lt_trans (prio_d3_lt_g n i) (prio_g_lt_r_2_odd n i)))
            (prio_r_2_odd_odd n)
        · by_cases hcond : 3 * (n + 2 * i.val + 1) - 1 ≤ s ∨ s % 3 = 2
          · have hbe : bestEdge1 n b s (.d1 i) = true := by rw [hbe_eq, decide_eq_true_eq]; exact hcond
            unfold bestEdge worstEdge
            rw [if_pos hbe, if_pos hbe, he0, he1]
            have hs2_ge : 2 ≤ s := by omega
            have hlp1_top := hitsWithTop_lp1_targetCR glob n b s hvalid i hs3
            have hlp2_top := hitsWithTop_lp2_targetCR_ge_two glob n b s hvalid i hs3 hs2_ge
            have hd2_top : HitsWithTop glob n b s (.d2 i) (targetCR n b s)
                (.b ⟨3 * min m.val ((s - 2) / 3) + 2, by have := m.isLt; omega⟩) := by
              apply hitsWithTop_of_step_lt glob n b s hvalid (.d2 i) (targetCR n b s) _ (by rintro ⟨⟩)
                (lt_trans (prio_d2_lt_d3 n i) (lt_trans (prio_d3_lt_g n i) (prio_g_lt_b n i _)))
              rw [hd2_step]; exact hlp2_top
            apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hlp1_top hd2_top
            · apply priority_b_strictMono; dsimp [m, tap_bin] at *; omega
            · exact prio_b_even n _
          · have hbe : bestEdge1 n b s (.d1 i) = false := by rw [hbe_eq, decide_eq_false_iff_not]; exact hcond
            unfold bestEdge worstEdge
            rw [hbe, he0, he1]
            have hlp1_top := hitsWithTop_lp1_targetCR glob n b s hvalid i hs3
            by_cases hs2_lt : s < 2
            · have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
                unfold S_close0; omega
              have hlp2_top := (hitsWithTop_lp2_not_close_lt_two_aux glob n b s hvalid hnot_close hs2_lt m.val m.isLt).1
              have hd2_top : HitsWithTop glob n b s (.d2 i) .c .c_odd := by
                apply hitsWithTop_of_step_lt glob n b s hvalid (.d2 i) .c .c_odd (by rintro ⟨⟩)
                  (lt_trans (prio_d2_lt_d3 n i) (lt_trans (prio_d3_lt_g n i) (prio_g_lt_c_odd n i)))
                rw [hd2_step]; exact hlp2_top
              rw [targetCR_eq_c_of_lt_two n b s hs2_lt] at hlp1_top
              exact predVal_lt_of_hitsWithTop_odd glob n b s hvalid hd2_top hlp1_top
                (prio_b_lt_c_odd n _) (prio_c_odd_odd n)
            · have hlp2_top := hitsWithTop_lp2_targetCR_ge_two glob n b s hvalid i hs3 (by omega)
              have hd2_top : HitsWithTop glob n b s (.d2 i) (targetCR n b s)
                  (.b ⟨3 * min m.val ((s - 2) / 3) + 2, by have := m.isLt; omega⟩) := by
                apply hitsWithTop_of_step_lt glob n b s hvalid (.d2 i) (targetCR n b s) _ (by rintro ⟨⟩)
                  (lt_trans (prio_d2_lt_d3 n i) (lt_trans (prio_d3_lt_g n i) (prio_g_lt_b n i _)))
                rw [hd2_step]; exact hlp2_top
              apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hd2_top hlp1_top
              · apply priority_b_strictMono; dsimp [m, tap_bin] at *; omega
              · exact prio_b_even n _

end FriedmannParity


