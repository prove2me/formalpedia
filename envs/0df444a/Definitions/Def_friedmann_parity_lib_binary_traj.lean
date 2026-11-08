-- Prove2me | Definitions.Def_friedmann_parity_lib_binary_traj
-- name    : friedmann_parity_lib_binary_traj
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-08T03:55:50.807377+00:00
-- url     : https://prove2.me/theorems/73cb65d7-0603-424a-9018-1355b6ae5f1a
-- title:
--   Friedmann binary lower-bound family: counter trajectory and uniqueness of improvement runs
-- statement:
--   A sorry-free library module that extends `friedmann_parity_lib_binary_paths_b`. It shows that one counter step is exactly one strategy-improvement step, for both the local and the global rule. A non-terminal counter state is improvable and the terminal one is not; the next counter state is a `LocalStep` or `GlobalStep` successor; and these successors are unique on player-0 vertices once all valuations have cycle priority $1$.
--
--   From this it derives the run-length bound: a complete run exists, and every complete run from the initial strategy has length at least $2^n$. It shows that $G_n$ is a sink game with a priority-1 sink, and that improvability and both step relations depend only on the player-0 part of a strategy. It also gives the transport lemmas that move a game along a bijection of vertex types.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 7(3:19), 2011, arXiv:1106.0778, §§6–8

import Definitions.Def_friedmann_parity_lib_binary_paths_b

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace FriedmannParity

/-! ### Part 1: `dagRank` and `IsSinkGame (G_bin n) (ι_bin n) .x` -/

def dagRank (n : ℕ) : V_bin n → ℕ
  | .x => 0
  | .z i => 10 * (n - 1 - i.val) + 2
  | .k i => 10 * (n - 1 - i.val) + 3
  | .g i => 10 * (n - 1 - i.val) + 4
  | .f i => 10 * (n - 1 - i.val) + 5
  | .hy i => 10 * (n - 1 - i.val) + 6
  | .hx i => 10 * (n - 1 - i.val) + 7
  | .h i => 10 * (n - 1 - i.val) + 8
  | .u i => 10 * (n - 1 - i.val) + 9
  | .rp i => 10 * n + 10 + i.val
  | .r => 11 * n + 10
  | .sp i => 11 * n + 11 + i.val
  | .s => 12 * n + 11
  | .c => 12 * n + 12
  | .c_odd => 12 * n + 13
  | .r_a => 12 * n + 14
  | .r_2 => 12 * n + 15
  | .r_2_odd => 12 * n + 16
  | .a j => 12 * n + 17 + j.val
  | .b k => 12 * n + 17 + 3 * (3 * n - 1) + k.val
  | .l1 _ => 12 * n + 18 + 6 * (3 * n - 1)
  | .l2 _ => 12 * n + 18 + 6 * (3 * n - 1)
  | .l3 _ => 12 * n + 18 + 6 * (3 * n - 1)
  | .lp1 m => 12 * n + 19 + 6 * (3 * n - 1) + m.val
  | .lp2 m => 12 * n + 19 + 6 * (3 * n - 1) + m.val
  | .lp3 m => 12 * n + 19 + 6 * (3 * n - 1) + m.val
  | .d3 _ => 12 * n + 20 + 7 * (3 * n - 1)
  | .d2 _ => 12 * n + 21 + 7 * (3 * n - 1)
  | .d1 _ => 12 * n + 22 + 7 * (3 * n - 1)

lemma edge1_legal (n : ℕ) : Legal (G_bin n) true (edge1 n) :=
  fun _ _ => Or.inr rfl

lemma step_edge1_x (n : ℕ) (σ : V_bin n → V_bin n) :
    step (G_bin n) σ (edge1 n) .x = .x := rfl

lemma dagRank_edge1_lt (n : ℕ) (v : V_bin n) (hv : v ≠ .x) :
    dagRank n (edge1 n v) < dagRank n v := by
  cases v with
  | x => contradiction
  | z i | k i | g i | f i | hy i | hx i | h i | u i | rp i | sp i | d1 i | d2 i | d3 i =>
    have hi := i.isLt
    dsimp [edge1]
    try split_ifs
    all_goals (dsimp [dagRank]; omega)
  | l1 m | l2 m | l3 m | lp1 m | lp2 m | lp3 m =>
    have hm := m.isLt
    dsimp [edge1]
    try split_ifs
    all_goals (dsimp [dagRank]; omega)
  | a j =>
    have hj := j.isLt
    dsimp [edge1]
    try split_ifs
    all_goals (dsimp [dagRank]; omega)
  | b k =>
    have hk := k.isLt
    have hb := (bTarget n k).isLt
    dsimp [edge1, dagRank]
    omega
  | r | s | r_2 | r_2_odd | r_a | c_odd | c =>
    dsimp [edge1]
    try split_ifs
    all_goals (dsimp [dagRank]; omega)

lemma dagRank_edge0_lt (n : ℕ) (v : V_bin n) (hown : (G_bin n).owner v = false) :
    dagRank n (edge0 n v) < dagRank n v := by
  cases v with
  | x | r_2_odd | r_a | c_odd | c | b _ | g _ | f _ | k _ =>
    dsimp [G_bin, owner_bin] at hown
    contradiction
  | z i | hy i | hx i | h i | u i | rp i | sp i | d1 i | d2 i | d3 i =>
    have hi := i.isLt
    dsimp [edge0, dagRank, tap_bin]
    omega
  | l1 m =>
    have hm := m.isLt
    dsimp only [G_bin, owner_bin] at hown
    dsimp only [edge0]
    split_ifs at hown ⊢
    dsimp [dagRank]; omega
  | l2 m | l3 m | lp1 m | lp2 m | lp3 m =>
    have hm := m.isLt
    dsimp [edge0, dagRank]
    omega
  | a j =>
    have hj := j.isLt
    dsimp only [G_bin, owner_bin] at hown
    dsimp only [edge0]
    split_ifs at hown ⊢ <;> (dsimp [dagRank]; omega)
  | r | s | r_2 =>
    dsimp [edge0, dagRank]
    omega

lemma dagRank_step_edge1_lt (n : ℕ) {σ : V_bin n → V_bin n}
    (hσ : Legal (G_bin n) false σ) (v : V_bin n) (hv : v ≠ .x) :
    dagRank n (step (G_bin n) σ (edge1 n) v) < dagRank n v := by
  unfold step
  split_ifs with hown
  · rcases hσ v hown with h0 | h1
    · rw [h0]; exact dagRank_edge0_lt n v hown
    · rw [h1]; exact dagRank_edge1_lt n v hv
  · exact dagRank_edge1_lt n v hv

lemma G_bin_reaches_x_aux (n : ℕ) :
    ∀ k (v : V_bin n), dagRank n v ≤ k → Relation.ReflTransGen (G_bin n).edge v .x
  | 0, v, hk => by
    by_cases hv : v = .x
    · subst hv; exact Relation.ReflTransGen.refl
    · have hlt := dagRank_edge1_lt n v hv
      omega
  | k + 1, v, hk => by
    by_cases hv : v = .x
    · subst hv; exact Relation.ReflTransGen.refl
    · have hlt := dagRank_edge1_lt n v hv
      exact Relation.ReflTransGen.head (Or.inr rfl)
        (G_bin_reaches_x_aux n k (edge1 n v) (by omega))

lemma G_bin_reaches_x (n : ℕ) (v : V_bin n) :
    Relation.ReflTransGen (G_bin n).edge v .x :=
  G_bin_reaches_x_aux n (dagRank n v) v le_rfl

lemma playValue_edge1_cyclePriority_eq_one (n : ℕ) (hn : 0 < n)
    {σ : V_bin n → V_bin n} (hσ : Legal (G_bin n) false σ) (v : V_bin n) :
    (playValue (G_bin n) σ (edge1 n) v).cyclePriority = 1 :=
  cyclePriority_eq_one_of_rank
    (G_bin_wellFormed n hn)
    (G_bin_sink_priority n)
    (step_edge1_x n σ)
    (dagRank n)
    (dagRank_step_edge1_lt n hσ)
    v

lemma validState_zero_zero (n : ℕ) (hn : 0 < n) : ValidState n 0 0 := by
  refine ⟨hn, Nat.two_pow_pos n, ?_⟩
  unfold maxStep0
  split_ifs <;> omega

lemma value_init_cyclePriority_eq_one (n : ℕ) (hn : 0 < n)
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v)
    (v : V_bin n) :
    (value (G_bin n) (ι_bin n) v).cyclePriority = 1 := by
  have hvalid := validState_zero_zero n hn
  have hinit : predState0 false n 0 0 = ι_bin n :=
    funext (predState0_zero_eq_init_all false n hn)
  rw [← hinit, (h_tau false n 0 0 hvalid).2 v]
  exact pred_cyclePriority_eq_one false n 0 0 hvalid v

lemma G_bin_isSinkGame (n : ℕ) (hn : 0 < n)
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v) :
    IsSinkGame (G_bin n) (ι_bin n) .x := by
  refine ⟨G_bin_wellFormed n hn, ι_bin_legal n, G_bin_sink_edge n,
    G_bin_sink_priority n, G_bin_gt_one_of_ne_sink n hn, G_bin_reaches_x n, ?_⟩
  intro σ hσ hAbove v
  have h1 : reward 1 ≤ reward (value (G_bin n) σ v).cyclePriority := by
    have h := reward_cyclePriority_le_of_valueLE (hAbove v)
    rwa [value_init_cyclePriority_eq_one n hn h_tau v] at h
  have h2 : reward (value (G_bin n) σ v).cyclePriority ≤ reward 1 := by
    have hle := value_le_playValue (G_bin_wellFormed n hn) σ (edge1_legal n) v
    have h := reward_cyclePriority_le_of_valueLE hle
    rwa [playValue_edge1_cyclePriority_eq_one n hn hσ v] at h
  exact reward_injective (le_antisymm h2 h1)

/-! ### Part 2: Bit-Carry Lemmas, Terminal State, and Non-Terminal Witness -/

lemma testBit_succ_of_all_true_of_false :
    ∀ (k b : ℕ), b.testBit k = false → (∀ i < k, b.testBit i = true) →
      (∀ i < k, (b + 1).testBit i = false) ∧
      (b + 1).testBit k = true ∧
      (∀ i, k < i → (b + 1).testBit i = b.testBit i)
  | 0, b, hk, _ => by
    rw [testBit_zero_eq, decide_eq_false_iff_not] at hk
    refine ⟨fun i hi => by omega, ?_, ?_⟩
    · rw [testBit_zero_eq, decide_eq_true_eq]; omega
    · intro i hi
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0) with ⟨j, rfl⟩
      rw [Nat.testBit_succ, Nat.testBit_succ]
      have hdiv : (b + 1) / 2 = b / 2 := by omega
      rw [hdiv]
  | k + 1, b, hk, hall => by
    have h0 : b % 2 = 1 := by
      have h := hall 0 (by omega)
      rwa [testBit_zero_eq, decide_eq_true_eq] at h
    have hdiv : (b + 1) / 2 = b / 2 + 1 := by omega
    have hk' : (b / 2).testBit k = false := by
      rw [← Nat.testBit_succ]; exact hk
    have hall' : ∀ i < k, (b / 2).testBit i = true := by
      intro i hi
      rw [← Nat.testBit_succ]
      exact hall (i + 1) (by omega)
    rcases testBit_succ_of_all_true_of_false k (b / 2) hk' hall' with ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rcases i with _ | j
      · rw [testBit_zero_eq, decide_eq_false_iff_not]; omega
      · rw [Nat.testBit_succ, hdiv]
        exact h1 j (by omega)
    · rw [Nat.testBit_succ, hdiv]
      exact h2
    · intro i hi
      rcases i with _ | j
      · omega
      · rw [Nat.testBit_succ, Nat.testBit_succ, hdiv]
        exact h3 j (by omega)

lemma testBit_succ_of_lt_lowestZero0 {b n i : ℕ} (hb : b < 2 ^ n - 1) (hi : i < lowestZero0 b n) :
    (b + 1).testBit i = false :=
  (testBit_succ_of_all_true_of_false (lowestZero0 b n) b
    (testBit_lowestZero0 hb) (fun _ hj => testBit_of_lt_lowestZero0 hb hj)).1 i hi

lemma testBit_succ_lowestZero0 {b n : ℕ} (hb : b < 2 ^ n - 1) :
    (b + 1).testBit (lowestZero0 b n) = true :=
  (testBit_succ_of_all_true_of_false (lowestZero0 b n) b
    (testBit_lowestZero0 hb) (fun _ hj => testBit_of_lt_lowestZero0 hb hj)).2.1

lemma testBit_succ_of_gt_lowestZero0 {b n i : ℕ} (hb : b < 2 ^ n - 1) (hi : lowestZero0 b n < i) :
    (b + 1).testBit i = b.testBit i :=
  (testBit_succ_of_all_true_of_false (lowestZero0 b n) b
    (testBit_lowestZero0 hb) (fun _ hj => testBit_of_lt_lowestZero0 hb hj)).2.2 i hi

lemma lowestOne0_succ_eq_lowestZero0 {b n : ℕ} (hb : b < 2 ^ n - 1) :
    lowestOne0 (b + 1) n = lowestZero0 b n := by
  have hpos : 0 < b + 1 := by omega
  have hlt : b + 1 < 2 ^ n := by omega
  have hle : lowestOne0 (b + 1) n ≤ lowestZero0 b n :=
    lowestOne0_le_of_testBit_true (lowestZero0_lt hb) (testBit_succ_lowestZero0 hb)
  by_contra hne
  have hlt' : lowestOne0 (b + 1) n < lowestZero0 b n := by omega
  have htrue := testBit_lowestOne0 hpos hlt
  have hfalse := testBit_succ_of_lt_lowestZero0 hb hlt'
  rw [htrue] at hfalse
  contradiction

lemma uLim0_le_n (b n : ℕ) : uLim0 b n ≤ n := by
  unfold uLim0
  have h := lowestOne0_le b n
  split_ifs <;> omega

def IsTerminal (n b s : ℕ) : Prop :=
  b = 2 ^ n - 1 ∧ s = 9 * n - 4

instance (n b s : ℕ) : Decidable (IsTerminal n b s) :=
  inferInstanceAs (Decidable (b = 2 ^ n - 1 ∧ s = 9 * n - 4))

lemma validState_nextPair {n b s : ℕ} (hvalid : ValidState n b s) :
    ValidState n (nextPair n b s).1 (nextPair n b s).2 := by
  rcases hvalid with ⟨hn, hb, hs⟩
  unfold nextPair
  split_ifs with hterm hwrap
  · exact ⟨hn, hb, hs⟩
  · refine ⟨hn, by omega, ?_⟩
    unfold maxStep0
    split_ifs <;> omega
  · refine ⟨hn, hb, ?_⟩
    by_cases hlt : b < 2 ^ n - 1
    · rw [maxStep0_of_lt hlt] at hs ⊢
      omega
    · have hb_eq : b = 2 ^ n - 1 := by omega
      unfold maxStep0 at hs ⊢
      rw [if_neg hlt] at hs ⊢
      omega

lemma chooseEdge1_two_pow_sub_one (glob : Bool) (n s : ℕ) (v : V_bin n) :
    chooseEdge1 glob n (2 ^ n - 1) s v = chooseEdge1 false n (2 ^ n - 1) s v := by
  cases v with
  | d1 i | d2 i | d3 i =>
    have hbit : (2 ^ n - 1).testBit i.val = true := testBit_two_pow_sub_one n i.val i.isLt
    simp [chooseEdge1, hbit]
  | a _ | l1 _ | l2 _ | l3 _ | lp1 _ | lp2 _ | lp3 _ =>
    simp [chooseEdge1]
  | _ => rfl

lemma chooseEdge1_terminal_eq_bestEdge1 (glob : Bool) (n b s : ℕ)
    (hterm : IsTerminal n b s) (v : V_bin n) :
    chooseEdge1 glob n b s v = bestEdge1 n b s v := by
  rcases hterm with ⟨rfl, rfl⟩
  unfold bestEdge1 nextPair
  rw [if_pos ⟨rfl, rfl⟩]
  exact chooseEdge1_two_pow_sub_one glob n (9 * n - 4) v

lemma predState0_terminal_eq_bestEdge (glob : Bool) (n b s : ℕ)
    (hterm : IsTerminal n b s) (v : V_bin n) :
    predState0 glob n b s v = bestEdge n b s v := by
  unfold predState0 bestEdge
  rw [chooseEdge1_terminal_eq_bestEdge1 glob n b s hterm v]

lemma value_le_bestEdge (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v)
    (h_best : ∀ glob n b s, ValidState n b s → ∀ v, BestEdgeProp glob n b s v)
    (v w : V_bin n) (hown : (G_bin n).owner v = false) (he : (G_bin n).edge v w) :
    ValueLE (G_bin n)
      (value (G_bin n) (predState0 glob n b s) w)
      (value (G_bin n) (predState0 glob n b s) (bestEdge n b s v)) := by
  rw [(h_tau glob n b s hvalid).2 w, (h_tau glob n b s hvalid).2 (bestEdge n b s v)]
  rcases edge_eq_bestEdge_or_worstEdge n b s v w he with rfl | rfl
  · exact valueLE_refl (G_bin n) _
  · by_cases hne : edge0 n v = edge1 n v
    · have hbw : worstEdge n b s v = bestEdge n b s v := by
        unfold worstEdge bestEdge; rw [hne]
      rw [hbw]
      exact valueLE_refl (G_bin n) _
    · exact Or.inr (h_best glob n b s hvalid v hown hne)

lemma not_improvable_of_terminal (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hterm : IsTerminal n b s)
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v)
    (h_best : ∀ glob n b s, ValidState n b s → ∀ v, BestEdgeProp glob n b s v) :
    ¬ Improvable (G_bin n) (predState0 glob n b s) := by
  rintro ⟨v, w, hown, he, hlt⟩
  have hle := value_le_bestEdge glob n b s hvalid h_tau h_best v w hown he
  rw [← predState0_terminal_eq_bestEdge glob n b s hterm v] at hle
  exact (valueLE_iff_not_valueLT (G_bin_priority_injective n hvalid.1) _ _).mp hle hlt

lemma witness_of_false_to_true {glob : Bool} {n b s : ℕ} {w : V_bin n}
    (hown : (G_bin n).owner w = false)
    (hne : edge0 n w ≠ edge1 n w)
    (hcur : chooseEdge1 glob n b s w = false)
    (hnext : ∀ g : Bool, chooseEdge1 g n (nextPair n b s).1 (nextPair n b s).2 w = true) :
    (G_bin n).owner w = false ∧
      edge0 n w ≠ edge1 n w ∧
      chooseEdge1 glob n b s w ≠ bestEdge1 n b s w ∧
      chooseEdge1 glob n (nextPair n b s).1 (nextPair n b s).2 w = bestEdge1 n b s w := by
  refine ⟨hown, hne, ?_, ?_⟩
  · unfold bestEdge1
    rw [hcur, hnext false]
    decide
  · unfold bestEdge1
    rw [hnext glob, hnext false]

lemma witness_of_true_to_false {glob : Bool} {n b s : ℕ} {w : V_bin n}
    (hown : (G_bin n).owner w = false)
    (hne : edge0 n w ≠ edge1 n w)
    (hcur : chooseEdge1 glob n b s w = true)
    (hnext : ∀ g : Bool, chooseEdge1 g n (nextPair n b s).1 (nextPair n b s).2 w = false) :
    (G_bin n).owner w = false ∧
      edge0 n w ≠ edge1 n w ∧
      chooseEdge1 glob n b s w ≠ bestEdge1 n b s w ∧
      chooseEdge1 glob n (nextPair n b s).1 (nextPair n b s).2 w = bestEdge1 n b s w := by
  refine ⟨hown, hne, ?_, ?_⟩
  · unfold bestEdge1
    rw [hcur, hnext false]
    decide
  · unfold bestEdge1
    rw [hnext glob, hnext false]

lemma nextPair_of_not_terminal_of_not_wrap {n b s : ℕ}
    (hnot_term : ¬ IsTerminal n b s)
    (hnot_wrap : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 3)) :
    nextPair n b s = (b, s + 1) := by
  unfold nextPair IsTerminal at *
  rw [if_neg hnot_term, if_neg hnot_wrap]

lemma exists_witness_of_not_terminal (glob : Bool) (n b s : ℕ)
    (hvalid : ValidState n b s) (hnot_term : ¬ IsTerminal n b s) :
    ∃ w : V_bin n,
      (G_bin n).owner w = false ∧
      edge0 n w ≠ edge1 n w ∧
      chooseEdge1 glob n b s w ≠ bestEdge1 n b s w ∧
      chooseEdge1 glob n (nextPair n b s).1 (nextPair n b s).2 w = bestEdge1 n b s w := by
  rcases hvalid with ⟨hn, hbn, hs⟩
  by_cases hclose : b < 2 ^ n - 1 ∧ S_close0 n b - 3 ≤ s
  · rcases hclose with ⟨hb, hs_ge⟩
    have hmax := maxStep0_of_lt hb
    have hk_lt : lowestZero0 b n < n := lowestZero0_lt hb
    have hk_bit : b.testBit (lowestZero0 b n) = false := testBit_lowestZero0 hb
    let i₀ : Fin n := ⟨lowestZero0 b n, hk_lt⟩
    have hi₀_bit : b.testBit i₀.val = false := hk_bit
    have hS_def : S_close0 n b = 3 * (n + 2 * i₀.val + 1) + 2 := rfl
    rcases (by omega :
        s = S_close0 n b - 3 ∨ s = S_close0 n b - 2 ∨ s = S_close0 n b - 1 ∨
        s = S_close0 n b ∨ s = S_close0 n b + 1 ∨ s = S_close0 n b + 2 ∨
        s = S_close0 n b + 3) with hs0 | hs1 | hs2 | hs3 | hs4 | hs5 | hs6
    · refine ⟨.d1 i₀, witness_of_false_to_true rfl (by nofun) ?_ ?_⟩
      · dsimp [chooseEdge1]
        rw [if_neg (by simp [hi₀_bit]), if_neg (by omega)]
        cases glob
        · simp only [Bool.false_eq_true, ite_false]
          exact if_neg (by omega)
        · simp only [ite_true, decide_eq_false_iff_not]
          omega
      · intro g
        rw [nextPair_of_not_terminal_of_not_wrap hnot_term (by omega)]
        dsimp [chooseEdge1]
        rw [if_neg (by simp [hi₀_bit]), if_pos (by omega)]
    · refine ⟨.d3 i₀, witness_of_false_to_true rfl (by nofun) ?_ ?_⟩
      · dsimp [chooseEdge1]
        rw [if_neg (by simp [hi₀_bit]), if_neg (by omega), if_pos (by omega)]
      · intro g
        rw [nextPair_of_not_terminal_of_not_wrap hnot_term (by omega)]
        dsimp [chooseEdge1]
        rw [if_neg (by simp [hi₀_bit]), if_pos (by omega)]
    · refine ⟨.d2 i₀, witness_of_false_to_true rfl (by nofun) ?_ ?_⟩
      · dsimp [chooseEdge1]
        rw [if_neg (by simp [hi₀_bit]), if_neg (by omega), if_pos (by omega)]
      · intro g
        rw [nextPair_of_not_terminal_of_not_wrap hnot_term (by omega)]
        dsimp [chooseEdge1]
        rw [if_neg (by simp [hi₀_bit]), if_pos (by omega)]
    · refine ⟨.hy i₀, witness_of_true_to_false rfl (by nofun) ?_ ?_⟩
      · have hhy := hyLim0_le_n b n s
        dsimp [chooseEdge1]
        rw [if_neg (by simp [hi₀_bit]), if_neg (by omega), if_pos ⟨hb, rfl⟩, decide_eq_true_eq]
        omega
      · intro g
        have hhy := hyLim0_le_n b n (s + 1)
        rw [nextPair_of_not_terminal_of_not_wrap hnot_term (by omega)]
        dsimp [chooseEdge1]
        rw [if_neg (by simp [hi₀_bit]), if_neg (by omega), if_pos ⟨hb, rfl⟩, decide_eq_false_iff_not]
        omega
    · refine ⟨.r_2, witness_of_false_to_true rfl (by nofun) ?_ ?_⟩
      · dsimp [chooseEdge1]
        rw [decide_eq_false_iff_not]
        omega
      · intro g
        rw [nextPair_of_not_terminal_of_not_wrap hnot_term (by omega)]
        dsimp [chooseEdge1]
        rw [decide_eq_true_eq]
        exact ⟨hb, Or.inl (by omega)⟩
    · refine ⟨.h i₀, witness_of_true_to_false rfl (by nofun) ?_ ?_⟩
      · have hhy := hyLim0_le_n b n s
        dsimp [chooseEdge1]
        rw [if_neg (by simp [hi₀_bit]), if_neg (by omega), if_pos ⟨hb, rfl⟩, decide_eq_true_eq]
        omega
      · intro g
        have hhy := hyLim0_le_n b n (s + 1)
        rw [nextPair_of_not_terminal_of_not_wrap hnot_term (by omega)]
        dsimp [chooseEdge1]
        rw [if_neg (by simp [hi₀_bit]), if_neg (by omega), if_pos ⟨hb, rfl⟩, decide_eq_false_iff_not]
        omega
    · refine ⟨.r_2, witness_of_true_to_false rfl (by nofun) ?_ ?_⟩
      · dsimp [chooseEdge1]
        rw [decide_eq_true_eq]
        exact ⟨hb, Or.inr hs6⟩
      · intro g
        have hnp : nextPair n b s = (b + 1, 0) := by
          unfold nextPair
          rw [if_neg (by unfold IsTerminal at hnot_term; omega), if_pos ⟨hb, hs6⟩]
        rw [hnp]
        dsimp [chooseEdge1]
        rw [decide_eq_false_iff_not]
        unfold S_close0
        omega
  · have hs_lt_9n4 : s < 9 * n - 4 := by
      by_cases hb : b < 2 ^ n - 1
      · have hk_lt : lowestZero0 b n < n := lowestZero0_lt hb
        have hS_def : S_close0 n b = 3 * (n + 2 * lowestZero0 b n + 1) + 2 := rfl
        omega
      · unfold maxStep0 at hs
        rw [if_neg hb] at hs
        unfold IsTerminal at hnot_term
        omega
    have hnot_wrap : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 3) := by omega
    have hnot_s2 : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 2) := by omega
    have hnot_s1_2 : ¬(b < 2 ^ n - 1 ∧ s + 1 = S_close0 n b + 2) := by omega
    have hnot_s1_3 : ¬(b < 2 ^ n - 1 ∧ s + 1 = S_close0 n b + 3) := by omega
    rcases (by omega : s = 9 * n - 6 ∨ s = 9 * n - 5 ∨ s < 9 * n - 6) with hs6 | hs5 | hslt
    · let m₀ : Fin (3 * n - 1) := ⟨3 * n - 2, by omega⟩
      have hm₀_val : m₀.val = 3 * n - 2 := rfl
      have hm₀_ne : m₀.val ≠ 0 := by omega
      have hown : (G_bin n).owner (.lp3 m₀) = false := by
        dsimp only [G_bin, owner_bin]; exact if_neg hm₀_ne
      have hne : edge0 n (.lp3 m₀) ≠ edge1 n (.lp3 m₀) := by
        dsimp [edge0, edge1]; rw [if_neg hm₀_ne]; nofun
      refine ⟨.lp3 m₀, witness_of_true_to_false hown hne ?_ ?_⟩
      · dsimp [chooseEdge1]
        rw [if_neg hm₀_ne, if_neg hnot_wrap, decide_eq_true_eq]
        omega
      · intro g
        rw [nextPair_of_not_terminal_of_not_wrap hnot_term hnot_wrap]
        dsimp [chooseEdge1]
        rw [if_neg hm₀_ne, if_neg hnot_s1_3, decide_eq_false_iff_not]
        omega
    · let m₀ : Fin (3 * n - 1) := ⟨3 * n - 2, by omega⟩
      have hm₀_val : m₀.val = 3 * n - 2 := rfl
      have hm₀_ne : m₀.val ≠ 0 := by omega
      have hown : (G_bin n).owner (.lp2 m₀) = false := by
        dsimp only [G_bin, owner_bin]; exact if_neg hm₀_ne
      have hne : edge0 n (.lp2 m₀) ≠ edge1 n (.lp2 m₀) := by
        dsimp [edge0, edge1]; rw [if_neg hm₀_ne]; nofun
      refine ⟨.lp2 m₀, witness_of_true_to_false hown hne ?_ ?_⟩
      · dsimp [chooseEdge1]
        rw [if_neg hm₀_ne, if_neg hnot_wrap, if_neg (by tauto), decide_eq_true_eq]
        omega
      · intro g
        rw [nextPair_of_not_terminal_of_not_wrap hnot_term hnot_wrap]
        dsimp [chooseEdge1]
        rw [if_neg hm₀_ne, if_neg hnot_s1_3, if_neg (by tauto), decide_eq_false_iff_not]
        omega
    · let j₀ : Fin (3 * (3 * n - 1)) := ⟨s + 2, by omega⟩
      have hj₀_val : j₀.val = s + 2 := rfl
      have hown : (G_bin n).owner (.a j₀) = false := by
        dsimp only [G_bin, owner_bin]
        exact if_neg (by dsimp [M_bin]; omega)
      have hne : edge0 n (.a j₀) ≠ edge1 n (.a j₀) := by
        dsimp only [edge0, edge1]
        rw [if_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
        nofun
      refine ⟨.a j₀, witness_of_false_to_true hown hne ?_ ?_⟩
      · dsimp [chooseEdge1]
        rw [if_neg (by omega)]
        split_ifs <;> (rw [decide_eq_false_iff_not]; omega)
      · intro g
        rw [nextPair_of_not_terminal_of_not_wrap hnot_term hnot_wrap]
        dsimp [chooseEdge1]
        rw [if_neg (by omega)]
        split_ifs <;> (rw [decide_eq_true_eq]; omega)

lemma valueLT_witness_of_not_terminal (glob : Bool) (n b s : ℕ)
    (hvalid : ValidState n b s) (hnot_term : ¬ IsTerminal n b s)
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v)
    (h_best : ∀ glob n b s, ValidState n b s → ∀ v, BestEdgeProp glob n b s v) :
    ∃ w : V_bin n, (G_bin n).owner w = false ∧
      ValueLT (G_bin n)
        (value (G_bin n) (predState0 glob n b s) (predState0 glob n b s w))
        (value (G_bin n) (predState0 glob n b s)
          (predState0 glob n (nextPair n b s).1 (nextPair n b s).2 w)) := by
  rcases exists_witness_of_not_terminal glob n b s hvalid hnot_term with
    ⟨w, hown, hne, hcur_ne, hnext_eq⟩
  have hcur_eq : predState0 glob n b s w = worstEdge n b s w := by
    unfold predState0 worstEdge
    cases hbest : bestEdge1 n b s w <;> cases hce : chooseEdge1 glob n b s w
    · simp [hbest, hce] at hcur_ne
    · rfl
    · rfl
    · simp [hbest, hce] at hcur_ne
  have hnext_pred : predState0 glob n (nextPair n b s).1 (nextPair n b s).2 w = bestEdge n b s w := by
    unfold predState0 bestEdge
    rw [hnext_eq]
  refine ⟨w, hown, ?_⟩
  rw [hcur_eq, hnext_pred, (h_tau glob n b s hvalid).2, (h_tau glob n b s hvalid).2]
  exact h_best glob n b s hvalid w hown hne

lemma improvable_of_not_terminal (glob : Bool) (n b s : ℕ)
    (hvalid : ValidState n b s) (hnot_term : ¬ IsTerminal n b s)
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v)
    (h_best : ∀ glob n b s, ValidState n b s → ∀ v, BestEdgeProp glob n b s v) :
    Improvable (G_bin n) (predState0 glob n b s) := by
  rcases valueLT_witness_of_not_terminal glob n b s hvalid hnot_term h_tau h_best with
    ⟨w, hown, hlt⟩
  exact ⟨w, predState0 glob n (nextPair n b s).1 (nextPair n b s).2 w,
    hown, predState0_legal glob n (nextPair n b s).1 (nextPair n b s).2 w hown, hlt⟩

lemma localStep_predState0 (n b s : ℕ)
    (hvalid : ValidState n b s) (hnot_term : ¬ IsTerminal n b s)
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v)
    (h_best : ∀ glob n b s, ValidState n b s → ∀ v, BestEdgeProp glob n b s v) :
    LocalStep (G_bin n)
      (predState0 false n b s)
      (predState0 false n (nextPair n b s).1 (nextPair n b s).2) := by
  apply localStep_of_best_edge
    (predState0_legal false n b s)
    (predState0_legal false n (nextPair n b s).1 (nextPair n b s).2)
  · intro _
    exact valueLT_witness_of_not_terminal false n b s hvalid hnot_term h_tau h_best
  · intro v w hown he
    exact value_le_bestEdge false n b s hvalid h_tau h_best v w hown he

/-! ### Part 2b: Global Step Transition Lemmas -/

lemma true_eq_decide_iff {P : Prop} [Decidable P] : (true = decide P) ↔ P := by
  rw [eq_comm, decide_eq_true_eq]

lemma false_eq_decide_iff {P : Prop} [Decidable P] : (false = decide P) ↔ ¬P := by
  rw [eq_comm, decide_eq_false_iff_not]

lemma decide_eq_decide_iff {P Q : Prop} [Decidable P] [Decidable Q] :
    (decide P = decide Q) ↔ (P ↔ Q) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]

lemma bit_carry_trichotomy {n b i : ℕ} (hb : b < 2 ^ n - 1) :
    (i < lowestZero0 b n ∧ b.testBit i = true ∧ (b + 1).testBit i = false) ∨
    (i = lowestZero0 b n ∧ b.testBit i = false ∧ (b + 1).testBit i = true) ∨
    (lowestZero0 b n < i ∧ (b + 1).testBit i = b.testBit i) := by
  rcases lt_trichotomy i (lowestZero0 b n) with hlt | rfl | hgt
  · exact Or.inl ⟨hlt, testBit_of_lt_lowestZero0 hb hlt, testBit_succ_of_lt_lowestZero0 hb hlt⟩
  · exact Or.inr (Or.inl ⟨rfl, testBit_lowestZero0 hb, testBit_succ_lowestZero0 hb⟩)
  · exact Or.inr (Or.inr ⟨hgt, testBit_succ_of_gt_lowestZero0 hb hgt⟩)

lemma chooseEdge1_zero_eq_false_glob (n b' : ℕ) (v : V_bin n)
    (hd1 : ∀ i, v ≠ .d1 i) :
    chooseEdge1 true n b' 0 v = chooseEdge1 false n b' 0 v := by
  have h2 : ¬(0 = S_close0 n b' + 2) := by unfold S_close0; omega
  have h3 : ¬(0 = S_close0 n b' + 3) := by unfold S_close0; omega
  have hmin : min 0 (S_close0 n b') = 0 := Nat.zero_min _
  cases v with
  | d1 i => exact False.elim (hd1 i rfl)
  | d2 i =>
    dsimp only [chooseEdge1]
    split_ifs <;> simp_all
  | d3 i =>
    dsimp only [chooseEdge1]
    split_ifs <;> simp_all
  | a j =>
    dsimp only [chooseEdge1]
    simp only [h2, h3, or_self, and_false, ite_false, hmin]
    split_ifs <;> rfl
  | l1 m | l2 m | l3 m | lp1 m | lp2 m | lp3 m =>
    dsimp only [chooseEdge1]
    simp only [h2, h3, and_false, ite_false]
  | _ => rfl

lemma glob_allowed_imp (n b s : ℕ) (hvalid : ValidState n b s) (hnot_term : ¬ IsTerminal n b s)
    (v : V_bin n) (hown : (G_bin n).owner v = false) :
    chooseEdge1 true n b s v = bestEdge1 n b s v →
      chooseEdge1 true n (nextPair n b s).1 (nextPair n b s).2 v = bestEdge1 n b s v := by
  by_cases hwrap : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
  · have hnp : nextPair n b s = (b + 1, 0) := by
      unfold nextPair IsTerminal at *
      rw [if_neg hnot_term, if_pos hwrap]
    unfold bestEdge1
    rw [hnp]
    dsimp only
    cases v with
    | d1 i =>
      rcases hwrap with ⟨hb, hs⟩
      have hl1 := lowestOne0_succ_eq_lowestZero0 hb
      have hS_def : S_close0 n b = 3 * (n + 2 * lowestZero0 b n + 1) + 2 := rfl
      have hS1_def : S_close0 n (b + 1) = 3 * (n + 2 * lowestZero0 (b + 1) n + 1) + 2 := rfl
      rcases bit_carry_trichotomy (i := i.val) hb with
        ⟨hlt, hbit0, hbit1⟩ | ⟨heq, hbit0, hbit1⟩ | ⟨hgt, hbit1⟩
      · dsimp only [chooseEdge1]
        simp only [hbit0, hbit1, hl1, and_true, and_false, true_and, false_and, ite_true, ite_false,
          Bool.true_eq_false, Bool.false_eq_true]
        try split_ifs
        all_goals
          try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
            false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
            and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
            iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
            imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
          try omega
      · dsimp only [chooseEdge1]
        simp only [hbit0, hbit1, hl1, and_true, and_false, true_and, false_and, ite_true, ite_false,
          Bool.true_eq_false, Bool.false_eq_true]
        try split_ifs
        all_goals
          try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
            false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
            and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
            iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
            imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
          try omega
      · cases hbit0 : b.testBit i.val <;>
        { dsimp only [chooseEdge1]
          simp only [hbit1, hbit0, hl1, and_true, and_false, true_and, false_and, ite_true, ite_false,
            Bool.true_eq_false, Bool.false_eq_true]
          try split_ifs
          all_goals
            try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
              false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
              and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
              iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
              imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
            try omega }
    | _ =>
      intro _
      exact chooseEdge1_zero_eq_false_glob n (b + 1) _ (by nofun)
  · have hnp := nextPair_of_not_terminal_of_not_wrap hnot_term hwrap
    unfold bestEdge1
    rw [hnp]
    dsimp only
    cases v with
    | a j | l1 j | l2 j | l3 j | lp1 j | lp2 j | lp3 j =>
      dsimp only [chooseEdge1]
      simp only [Nat.min_def, and_true, and_false, true_and, false_and, ite_true, ite_false,
        Bool.true_eq_false, Bool.false_eq_true]
      try split_ifs
      all_goals
        try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
          false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
          and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
          iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
          imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
        try omega
    | d1 i | d2 i | d3 i =>
      dsimp only [chooseEdge1]
      simp only [and_true, and_false, true_and, false_and, ite_true, ite_false,
        Bool.true_eq_false, Bool.false_eq_true]
      try split_ifs
      all_goals
        try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
          false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
          and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
          iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
          imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
        try omega
    | _ =>
      intro _
      rfl

lemma glob_optimal_next_wrap (n b : ℕ) (hn : 0 < n) (hb : b < 2 ^ n - 1)
    (v : V_bin n) (_hown : (G_bin n).owner v = false) :
    chooseEdge1 true n b (S_close0 n b + 3) v ≠ chooseEdge1 false n (b + 1) 0 v →
      chooseEdge1 true n (b + 1) 0 v = chooseEdge1 false n (b + 1) 1 v := by
  have hl1 := lowestOne0_succ_eq_lowestZero0 hb
  have hS_def : S_close0 n b = 3 * (n + 2 * lowestZero0 b n + 1) + 2 := rfl
  have hS1_def : S_close0 n (b + 1) = 3 * (n + 2 * lowestZero0 (b + 1) n + 1) + 2 := rfl
  cases v with
  | x | r_2_odd | r_a | c_odd | c | b _ | g _ | f _ | k _ =>
    intro _; rfl
  | z i =>
    intro _; rfl
  | r | s | r_2 | rp _ | sp _ =>
    intro _
    dsimp only [chooseEdge1, rActive0, sActive0]
    try split_ifs
    all_goals
      try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
        false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
        and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
        iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
        imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
      try omega
  | u i =>
    intro hne
    by_cases hlt : i.val < lowestZero0 b n
    · have hbit : b.testBit i.val = true := testBit_of_lt_lowestZero0 hb hlt
      have hb1 : (b + 1).testBit i.val = false := testBit_succ_of_lt_lowestZero0 hb hlt
      dsimp only [chooseEdge1] at hne ⊢
      try split_ifs at hne ⊢
      all_goals
        try simp only [hbit, hb1, and_true, true_and, and_false, false_and, or_true, true_or,
          or_false, false_or, iff_true, true_iff, iff_false, false_iff, decide_eq_true_eq,
          decide_eq_false_iff_not, true_eq_decide_iff, false_eq_decide_iff, decide_eq_decide_iff,
          Bool.true_eq_false, Bool.false_eq_true, eq_self, not_true_eq_false, not_false_eq_true,
          imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
        try omega
    · dsimp only [chooseEdge1]
      try split_ifs
      all_goals
        try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
          false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
          and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
          iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
          imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
        try omega
  | hy i | hx i | h i =>
    intro hne
    by_cases hlt : i.val < lowestZero0 b n
    · have hbit : b.testBit i.val = true := testBit_of_lt_lowestZero0 hb hlt
      have hb1 : (b + 1).testBit i.val = false := testBit_succ_of_lt_lowestZero0 hb hlt
      have hhy0 : hyLim0 (b + 1) n 0 = lowestZero0 b n := by
        unfold hyLim0; simp [hl1]
      exfalso
      apply hne
      dsimp only [chooseEdge1]
      rw [if_pos hbit, if_neg (by simp [hb1]), if_pos ⟨by omega, by omega, by omega⟩]
    · dsimp only [chooseEdge1]
      try split_ifs
      all_goals
        try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
          false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
          and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
          iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
          imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
        try omega
  | a j | l1 j | l2 j | l3 j | lp1 j | lp2 j | lp3 j =>
    dsimp only [chooseEdge1]
    simp only [Nat.min_def, and_true, and_false, true_and, false_and, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
    try split_ifs
    all_goals
      try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
        false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
        and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
        iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
        imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
      try omega
  | d1 i | d2 i | d3 i =>
    rcases bit_carry_trichotomy (i := i.val) hb with
      ⟨hlt, hbit0, hbit1⟩ | ⟨heq, hbit0, hbit1⟩ | ⟨hgt, hbit1⟩
    · dsimp only [chooseEdge1]
      simp only [hbit0, hbit1, hl1, and_true, and_false, true_and, false_and, ite_true, ite_false,
        Bool.true_eq_false, Bool.false_eq_true]
      try split_ifs
      all_goals
        try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
          false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
          and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
          iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
          imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
        try omega
    · dsimp only [chooseEdge1]
      simp only [hbit0, hbit1, hl1, and_true, and_false, true_and, false_and, ite_true, ite_false,
        Bool.true_eq_false, Bool.false_eq_true]
      try split_ifs
      all_goals
        try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
          false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
          and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
          iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
          imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
        try omega
    · cases hbit0 : b.testBit i.val <;>
      { dsimp only [chooseEdge1]
        simp only [hbit1, hbit0, hl1, and_true, and_false, true_and, false_and, ite_true, ite_false,
          Bool.true_eq_false, Bool.false_eq_true]
        try split_ifs
        all_goals
          try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
            false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
            and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
            iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
            imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
          try omega }

lemma glob_optimal_next_prewrap (n b : ℕ) (hn : 0 < n) (hb : b < 2 ^ n - 1)
    (v : V_bin n) (hown : (G_bin n).owner v = false) :
    chooseEdge1 true n b (S_close0 n b + 2) v ≠ chooseEdge1 false n b (S_close0 n b + 3) v →
      chooseEdge1 true n b (S_close0 n b + 3) v = chooseEdge1 false n (b + 1) 0 v := by
  have hl1 := lowestOne0_succ_eq_lowestZero0 hb
  have hS_def : S_close0 n b = 3 * (n + 2 * lowestZero0 b n + 1) + 2 := rfl
  have hS1_def : S_close0 n (b + 1) = 3 * (n + 2 * lowestZero0 (b + 1) n + 1) + 2 := rfl
  cases v with
  | x | r_2_odd | r_a | c_odd | c | b _ | g _ | f _ | k _ =>
    intro _; rfl
  | z i =>
    intro hne; exact False.elim (hne rfl)
  | r | r_2 | rp _ =>
    intro hne
    exfalso
    apply hne
    dsimp only [chooseEdge1, rActive0]
    try split_ifs
    all_goals
      try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
        false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
        and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
        iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
        imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
      try omega
  | s | sp _ =>
    intro _
    dsimp only [chooseEdge1, sActive0]
    try split_ifs
    all_goals
      try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
        false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
        and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
        iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
        imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
      try omega
  | u i =>
    have hu := uLim0_le_n b n
    intro hne
    exfalso
    apply hne
    dsimp only [chooseEdge1]
    try split_ifs
    all_goals
      try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
        false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
        and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
        iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
        imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
      try omega
  | hy i | hx i =>
    have hhy2 := hyLim0_le_n b n (S_close0 n b + 2)
    have hhy3 := hyLim0_le_n b n (S_close0 n b + 3)
    intro hne
    exfalso
    apply hne
    dsimp only [chooseEdge1]
    try split_ifs
    all_goals
      try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
        false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
        and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
        iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
        imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
      try omega
  | h i =>
    have hhy2 := hyLim0_le_n b n (S_close0 n b + 2)
    have hhy3 := hyLim0_le_n b n (S_close0 n b + 3)
    intro hne
    by_cases heq : i.val = lowestZero0 b n
    · have hb1 : (b + 1).testBit i.val = true := heq ▸ testBit_succ_lowestZero0 hb
      dsimp only [chooseEdge1]
      rw [if_pos hb1]
      try split_ifs
      all_goals
        try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
          false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
          and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
          iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
          imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
        try omega
    · exfalso
      apply hne
      dsimp only [chooseEdge1]
      try split_ifs
      all_goals
        try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
          false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
          and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
          iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
          imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
        try omega
  | a j =>
    intro hne
    exfalso
    apply hne
    dsimp only [chooseEdge1]
    rw [if_pos ⟨hb, Or.inl rfl⟩, if_pos ⟨hb, Or.inr rfl⟩]
  | l1 m | lp1 m | lp2 m | lp3 m =>
    have hm_ne : m.val ≠ 0 := by
      dsimp only [G_bin, owner_bin] at hown
      intro h0; rw [if_pos h0] at hown; contradiction
    dsimp only [chooseEdge1]
    simp only [hm_ne, hb, and_true, and_false, true_and, false_and, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
    try split_ifs
    all_goals
      try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
        false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
        and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
        iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
        imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
      try omega
  | l2 m | l3 m =>
    dsimp only [chooseEdge1]
    simp only [hb, and_true, and_false, true_and, false_and, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
    try split_ifs
    all_goals
      try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
        false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
        and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
        iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
        imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
      try omega
  | d1 i | d2 i | d3 i =>
    rcases bit_carry_trichotomy (i := i.val) hb with
      ⟨hlt, hbit0, hbit1⟩ | ⟨heq, hbit0, hbit1⟩ | ⟨hgt, hbit1⟩
    · dsimp only [chooseEdge1]
      simp only [hbit0, hbit1, hl1, and_true, and_false, true_and, false_and, ite_true, ite_false,
        Bool.true_eq_false, Bool.false_eq_true]
      try split_ifs
      all_goals
        try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
          false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
          and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
          iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
          imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
        try omega
    · dsimp only [chooseEdge1]
      simp only [hbit0, hbit1, hl1, and_true, and_false, true_and, false_and, ite_true, ite_false,
        Bool.true_eq_false, Bool.false_eq_true]
      try split_ifs
      all_goals
        try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
          false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
          and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
          iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
          imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
        try omega
    · cases hbit0 : b.testBit i.val <;>
      { dsimp only [chooseEdge1]
        simp only [hbit1, hbit0, hl1, and_true, and_false, true_and, false_and, ite_true, ite_false,
          Bool.true_eq_false, Bool.false_eq_true]
        try split_ifs
        all_goals
          try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
            false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
            and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
            iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
            imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
          try omega }

lemma glob_optimal_next_step (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot_s2 : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 2))
    (hnot_s3 : ¬(b < 2 ^ n - 1 ∧ s = S_close0 n b + 3))
    (v : V_bin n) (_hown : (G_bin n).owner v = false) :
    chooseEdge1 true n b s v ≠ chooseEdge1 false n b (s + 1) v →
      chooseEdge1 true n b (s + 1) v = chooseEdge1 false n b (s + 2) v := by
  rcases hvalid with ⟨hn, hbn, hs⟩
  have hS_def : S_close0 n b = 3 * (n + 2 * lowestZero0 b n + 1) + 2 := rfl
  have hs_le : b < 2 ^ n - 1 → s ≤ S_close0 n b + 1 := by
    intro hb
    have hmax := maxStep0_of_lt hb
    omega
  cases v with
  | x | r_2_odd | r_a | c_odd | c | b _ | g _ | f _ | k _ | z _ =>
    intro _; rfl
  | r | s | r_2 | rp _ | sp _ | u _ =>
    dsimp only [chooseEdge1, rActive0, sActive0]
    try split_ifs
    all_goals
      try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
        false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
        and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
        iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
        imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
      try omega
  | hy i | hx i | h i =>
    have hhy1 : hyLim0 b n (s + 2) = hyLim0 b n (s + 1) := by unfold hyLim0; simp
    have hhy0 : hyLim0 b n (s + 1) ≤ hyLim0 b n s := by
      unfold hyLim0
      by_cases htf : topFlip0 b n = true <;> simp [htf] <;> split_ifs <;> omega
    have hhy_s := hyLim0_le_n b n s
    have hhy_s1 := hyLim0_le_n b n (s + 1)
    dsimp only [chooseEdge1]
    rw [hhy1]
    try split_ifs
    all_goals
      try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
        false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
        and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
        iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
        imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
      try omega
  | a j =>
    by_cases hb : b < 2 ^ n - 1
    · have hk_lt := lowestZero0_lt hb
      dsimp only [chooseEdge1]
      simp only [hb, Nat.min_def, and_true, and_false, true_and, false_and, ite_true, ite_false,
        Bool.true_eq_false, Bool.false_eq_true]
      try split_ifs
      all_goals
        try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
          false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
          and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
          iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
          imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
        try omega
    · dsimp only [chooseEdge1]
      simp only [hb, Nat.min_def, and_true, and_false, true_and, false_and, ite_true, ite_false,
        Bool.true_eq_false, Bool.false_eq_true]
      try split_ifs
      all_goals
        try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
          false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
          and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
          iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
          imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
        try omega
  | l1 j | l2 j | l3 j | lp1 j | lp2 j | lp3 j =>
    dsimp only [chooseEdge1]
    simp only [and_true, and_false, true_and, false_and, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
    try split_ifs
    all_goals
      try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
        false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
        and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
        iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
        imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
      try omega
  | d1 i | d2 i | d3 i =>
    dsimp only [chooseEdge1]
    simp only [and_true, and_false, true_and, false_and, ite_true, ite_false,
      Bool.true_eq_false, Bool.false_eq_true]
    try split_ifs
    all_goals
      try simp only [decide_eq_true_eq, decide_eq_false_iff_not, true_eq_decide_iff,
        false_eq_decide_iff, decide_eq_decide_iff, Bool.true_eq_false, Bool.false_eq_true,
        and_true, true_and, and_false, false_and, or_true, true_or, or_false, false_or,
        iff_true, true_iff, iff_false, false_iff, eq_self, not_true_eq_false, not_false_eq_true,
        imp_self, imp_true_iff, false_imp_iff, true_imp_iff, ne_eq] at *
      try omega

lemma glob_optimal_next_imp (n b s : ℕ) (hvalid : ValidState n b s) (hnot_term : ¬ IsTerminal n b s)
    (v : V_bin n) (hown : (G_bin n).owner v = false) :
    chooseEdge1 true n b s v ≠ bestEdge1 n b s v →
      chooseEdge1 true n (nextPair n b s).1 (nextPair n b s).2 v =
        bestEdge1 n (nextPair n b s).1 (nextPair n b s).2 v := by
  by_cases hterm' : IsTerminal n (nextPair n b s).1 (nextPair n b s).2
  · intro _
    exact chooseEdge1_terminal_eq_bestEdge1 true n (nextPair n b s).1 (nextPair n b s).2 hterm' v
  · by_cases hwrap : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
    · rcases hwrap with ⟨hb, hs⟩
      subst hs
      have hnp1 : nextPair n b (S_close0 n b + 3) = (b + 1, 0) := by
        unfold nextPair IsTerminal at *
        rw [if_neg hnot_term, if_pos ⟨hb, rfl⟩]
      have hnp2 : nextPair n (b + 1) 0 = (b + 1, 1) := by
        unfold nextPair
        have hn := hvalid.1
        rw [if_neg (by omega), if_neg (by unfold S_close0; omega)]
      unfold bestEdge1
      rw [hnp1, hnp2]
      exact glob_optimal_next_wrap n b hvalid.1 hb v hown
    · have hnp1 := nextPair_of_not_terminal_of_not_wrap hnot_term hwrap
      by_cases hprewrap : b < 2 ^ n - 1 ∧ s = S_close0 n b + 2
      · rcases hprewrap with ⟨hb, hs⟩
        subst hs
        have hnp2 : nextPair n b (S_close0 n b + 2 + 1) = (b + 1, 0) := by
          unfold nextPair
          rw [if_neg (by unfold IsTerminal at hterm'; rw [hnp1] at hterm'; exact hterm'),
              if_pos ⟨hb, rfl⟩]
        unfold bestEdge1
        rw [hnp1, hnp2]
        exact glob_optimal_next_prewrap n b hvalid.1 hb v hown
      · have hnp2 : nextPair n b (s + 1) = (b, s + 2) := by
          unfold nextPair
          rw [if_neg (by unfold IsTerminal at hterm'; rw [hnp1] at hterm'; exact hterm'),
              if_neg (by omega)]
        unfold bestEdge1
        rw [hnp1, hnp2]
        exact glob_optimal_next_step n b s hvalid hprewrap hwrap v hown

lemma globalStep_predState0 (n b s : ℕ)
    (hvalid : ValidState n b s) (hnot_term : ¬ IsTerminal n b s)
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v)
    (h_best : ∀ glob n b s, ValidState n b s → ∀ v, BestEdgeProp glob n b s v) :
    GlobalStep (G_bin n)
      (predState0 true n b s)
      (predState0 true n (nextPair n b s).1 (nextPair n b s).2) := by
  set b' := (nextPair n b s).1
  set s' := (nextPair n b s).2
  have hvalid' : ValidState n b' s' := validState_nextPair hvalid
  have hal : Allowed (G_bin n) (predState0 true n b s) (predState0 true n b' s') := by
    refine ⟨predState0_legal true n b' s', ?_⟩
    intro v hown
    by_cases hce : chooseEdge1 true n b s v = bestEdge1 n b s v
    · have hce' : chooseEdge1 true n b' s' v = bestEdge1 n b s v :=
        glob_allowed_imp n b s hvalid hnot_term v hown hce
      have heq : predState0 true n b' s' v = predState0 true n b s v := by
        unfold predState0; rw [hce, hce']
      rw [heq]
      exact valueLE_refl (G_bin n) _
    · have hcur_worst : predState0 true n b s v = worstEdge n b s v := by
        unfold predState0 worstEdge
        cases hb1 : bestEdge1 n b s v <;> cases hc1 : chooseEdge1 true n b s v
        · simp [hb1, hc1] at hce
        · rfl
        · rfl
        · simp [hb1, hc1] at hce
      rcases edge_eq_bestEdge_or_worstEdge n b s v (predState0 true n b' s' v)
        (predState0_legal true n b' s' v hown) with hbest | hworst
      · rw [hbest]
        exact value_le_bestEdge true n b s hvalid h_tau h_best v
          (predState0 true n b s v) hown (predState0_legal true n b s v hown)
      · rw [hcur_worst, hworst]
        exact valueLE_refl (G_bin n) _
  have himp : Improvement (G_bin n) (predState0 true n b s) (predState0 true n b' s') :=
    ⟨hal, fun _ => valueLT_witness_of_not_terminal true n b s hvalid hnot_term h_tau h_best⟩
  apply globalStep_of_local_in_next (G_bin_wellFormed n hvalid.1) himp
  intro v w hown he hle
  by_cases hne : edge0 n v = edge1 n v
  · have hw_eq : w = predState0 true n b' s' v := by
      rcases he with rfl | rfl <;> { unfold predState0; split_ifs <;> simp [hne] }
    rw [hw_eq]
    exact valueLE_refl (G_bin n) _
  · by_cases hce : chooseEdge1 true n b s v = bestEdge1 n b s v
    · have hce' : chooseEdge1 true n b' s' v = bestEdge1 n b s v :=
        glob_allowed_imp n b s hvalid hnot_term v hown hce
      have hσ : predState0 true n b s v = bestEdge n b s v := by
        unfold predState0 bestEdge; rw [hce]
      have hσ' : predState0 true n b' s' v = bestEdge n b s v := by
        unfold predState0 bestEdge; rw [hce']
      rcases edge_eq_bestEdge_or_worstEdge n b s v w he with rfl | rfl
      · rw [hσ']
        exact valueLE_refl (G_bin n) _
      · exfalso
        have hlt : ValueLT (G_bin n)
            (value (G_bin n) (predState0 true n b s) (worstEdge n b s v))
            (value (G_bin n) (predState0 true n b s) (bestEdge n b s v)) := by
          rw [(h_tau true n b s hvalid).2, (h_tau true n b s hvalid).2]
          exact h_best true n b s hvalid v hown hne
        rw [← hσ] at hlt
        exact (valueLE_iff_not_valueLT (G_bin_priority_injective n hvalid.1) _ _).mp hle hlt
    · have hce' : chooseEdge1 true n b' s' v = bestEdge1 n b' s' v :=
        glob_optimal_next_imp n b s hvalid hnot_term v hown hce
      have hσ' : predState0 true n b' s' v = bestEdge n b' s' v := by
        unfold predState0 bestEdge; rw [hce']
      rw [hσ']
      exact value_le_bestEdge true n b' s' hvalid' h_tau h_best v w hown he

/-! ### Part 3: Trajectory `pairAt`, `run_bin`, and `HardInstance` on `G_bin n` -/

def pairAt (n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | t + 1 => nextPair n (pairAt n t).1 (pairAt n t).2

def run_bin (glob : Bool) (n : ℕ) (t : ℕ) : V_bin n → V_bin n :=
  predState0 glob n (pairAt n t).1 (pairAt n t).2

lemma validState_nextPair_all (n b s : ℕ) (hvalid : ValidState n b s) :
    ValidState n (nextPair n b s).1 (nextPair n b s).2 :=
  validState_nextPair hvalid

lemma validState_pairAt (n : ℕ) (hn : 0 < n) :
    ∀ t : ℕ, ValidState n (pairAt n t).1 (pairAt n t).2
  | 0 => validState_zero_zero n hn
  | t + 1 => validState_nextPair_all n (pairAt n t).1 (pairAt n t).2 (validState_pairAt n hn t)

def pot (n b s : ℕ) : ℕ :=
  (2 ^ n - 1 - b) * (9 * n + 4) + (maxStep0 n b - 1 - s)

lemma maxStep0_le_nine_mul (n b : ℕ) (_hn : 0 < n) : maxStep0 n b ≤ 9 * n + 3 := by
  unfold maxStep0
  split_ifs with hb
  · have := lowestZero0_lt hb
    omega
  · omega

lemma pot_nextPair_lt (n b s : ℕ) (hvalid : ValidState n b s) (hnot_term : ¬ IsTerminal n b s) :
    pot n (nextPair n b s).1 (nextPair n b s).2 < pot n b s := by
  have hvalid' := validState_nextPair hvalid
  rcases hvalid with ⟨hn, hbn, hs⟩
  unfold nextPair IsTerminal at *
  rw [if_neg hnot_term] at hvalid' ⊢
  split_ifs with hwrap
  · rcases hwrap with ⟨hb, hs_eq⟩
    have hmax_next := maxStep0_le_nine_mul n (b + 1) hn
    have hsub : 2 ^ n - 1 - b = (2 ^ n - 1 - (b + 1)) + 1 := by omega
    have hmul : (2 ^ n - 1 - b) * (9 * n + 4) =
        (2 ^ n - 1 - (b + 1)) * (9 * n + 4) + (9 * n + 4) := by
      rw [hsub, Nat.add_mul, Nat.one_mul]
    dsimp [pot]
    omega
  · rw [if_neg hwrap] at hvalid'
    have hs' : s + 1 < maxStep0 n b := hvalid'.2.2
    dsimp [pot]
    omega

lemma exists_terminal_from (n : ℕ) (hn : 0 < n) :
    ∀ k t, pot n (pairAt n t).1 (pairAt n t).2 ≤ k →
      ∃ d, IsTerminal n (pairAt n (t + d)).1 (pairAt n (t + d)).2 ∧
        ∀ j < d, ¬ IsTerminal n (pairAt n (t + j)).1 (pairAt n (t + j)).2
  | 0, t, hk => by
    by_cases hterm : IsTerminal n (pairAt n t).1 (pairAt n t).2
    · exact ⟨0, by simpa using hterm, fun j hj => by omega⟩
    · exfalso
      have hlt := pot_nextPair_lt n (pairAt n t).1 (pairAt n t).2 (validState_pairAt n hn t) hterm
      omega
  | k + 1, t, hk => by
    by_cases hterm : IsTerminal n (pairAt n t).1 (pairAt n t).2
    · exact ⟨0, by simpa using hterm, fun j hj => by omega⟩
    · have hlt := pot_nextPair_lt n (pairAt n t).1 (pairAt n t).2 (validState_pairAt n hn t) hterm
      have hk' : pot n (pairAt n (t + 1)).1 (pairAt n (t + 1)).2 ≤ k := by
        dsimp [pairAt]
        omega
      rcases exists_terminal_from n hn k (t + 1) hk' with ⟨d, hd1, hd2⟩
      refine ⟨d + 1, ?_, ?_⟩
      · have heq : t + (d + 1) = t + 1 + d := by omega
        rw [heq]
        exact hd1
      · intro j hj
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · simpa using hterm
        · have heq : t + j = t + 1 + (j - 1) := by omega
          rw [heq]
          exact hd2 (j - 1) (by omega)

lemma exists_T_bin (n : ℕ) (hn : 0 < n) :
    ∃ T, IsTerminal n (pairAt n T).1 (pairAt n T).2 ∧
      ∀ t < T, ¬ IsTerminal n (pairAt n t).1 (pairAt n t).2 := by
  rcases exists_terminal_from n hn (pot n (pairAt n 0).1 (pairAt n 0).2) 0 le_rfl with ⟨T, h1, h2⟩
  refine ⟨T, by simpa using h1, fun t ht => by simpa using h2 t ht⟩

def progress (b s : ℕ) : ℕ :=
  2 * b + if 0 < s then 1 else 0

lemma progress_nextPair_le (n b s : ℕ) :
    progress (nextPair n b s).1 (nextPair n b s).2 ≤ progress b s + 1 := by
  unfold nextPair
  split_ifs with h1 h2
  · dsimp [progress]; omega
  · rcases h2 with ⟨_, hs⟩
    have hs_pos : 0 < s := by unfold S_close0 at hs; omega
    dsimp [progress]
    rw [if_pos hs_pos]
    omega
  · dsimp [progress]
    split_ifs <;> omega

lemma progress_pairAt_le (n : ℕ) : ∀ t : ℕ, progress (pairAt n t).1 (pairAt n t).2 ≤ t
  | 0 => le_rfl
  | t + 1 => by
    dsimp [pairAt]
    exact le_trans (progress_nextPair_le n (pairAt n t).1 (pairAt n t).2)
      (Nat.add_le_add_right (progress_pairAt_le n t) 1)

lemma two_pow_le_of_terminal_pairAt (n T : ℕ) (hn : 0 < n)
    (hterm : IsTerminal n (pairAt n T).1 (pairAt n T).2) :
    2 ^ n ≤ T := by
  have hp := progress_pairAt_le n T
  rcases hterm with ⟨hb, hs⟩
  dsimp [progress] at hp
  rw [hb, hs, if_pos (by omega)] at hp
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  omega

section StrategyCongrOnFalse

variable {V : Type} [Fintype V] [DecidableEq V]

lemma improvable_congr_on_false {G : Game V} (hWF : WellFormed G) {σ₁ σ₂ : V → V}
    (hσ : ∀ v, G.owner v = false → σ₁ v = σ₂ v) :
    Improvable G σ₁ ↔ Improvable G σ₂ := by
  have hval := value_congr_on_false hWF hσ
  constructor <;> rintro ⟨v, w, hown, he, hlt⟩ <;> refine ⟨v, w, hown, he, ?_⟩
  · rwa [← hval (σ₂ v), ← hσ v hown, ← hval w]
  · rwa [hval (σ₁ v), hσ v hown, hval w]

lemma allowed_congr_on_false_left {G : Game V} (hWF : WellFormed G) {σ₁ σ₂ σ' : V → V}
    (hσ : ∀ v, G.owner v = false → σ₁ v = σ₂ v) :
    Allowed G σ₁ σ' ↔ Allowed G σ₂ σ' := by
  have hval := value_congr_on_false hWF hσ
  constructor <;> rintro ⟨hleg, hle⟩ <;> refine ⟨hleg, fun v hv => ?_⟩
  · have h := hle v hv
    rwa [hval (σ₁ v), hσ v hv, hval (σ' v)] at h
  · have h := hle v hv
    rwa [← hσ v hv, ← hval (σ₁ v), ← hval (σ' v)] at h

lemma improvement_congr_on_false_left {G : Game V} (hWF : WellFormed G) {σ₁ σ₂ σ' : V → V}
    (hσ : ∀ v, G.owner v = false → σ₁ v = σ₂ v) :
    Improvement G σ₁ σ' ↔ Improvement G σ₂ σ' := by
  have hval := value_congr_on_false hWF hσ
  constructor <;> rintro ⟨hal, himp⟩
  · refine ⟨(allowed_congr_on_false_left hWF hσ).mp hal, fun h2 => ?_⟩
    rcases himp ((improvable_congr_on_false hWF hσ).mpr h2) with ⟨v, hv, hlt⟩
    refine ⟨v, hv, ?_⟩
    rwa [hval (σ₁ v), hσ v hv, hval (σ' v)] at hlt
  · refine ⟨(allowed_congr_on_false_left hWF hσ).mpr hal, fun h1 => ?_⟩
    rcases himp ((improvable_congr_on_false hWF hσ).mp h1) with ⟨v, hv, hlt⟩
    refine ⟨v, hv, ?_⟩
    rwa [← hσ v hv, ← hval (σ₁ v), ← hval (σ' v)] at hlt

lemma localStep_congr_on_false_left {G : Game V} (hWF : WellFormed G) {σ₁ σ₂ σ' : V → V}
    (hσ : ∀ v, G.owner v = false → σ₁ v = σ₂ v) :
    LocalStep G σ₁ σ' ↔ LocalStep G σ₂ σ' := by
  have hval := value_congr_on_false hWF hσ
  constructor <;> rintro ⟨himp, hloc⟩
  · refine ⟨(improvement_congr_on_false_left hWF hσ).mp himp, fun v w hv he => ?_⟩
    have h := hloc v w hv he
    rwa [hval w, hval (σ' v)] at h
  · refine ⟨(improvement_congr_on_false_left hWF hσ).mpr himp, fun v w hv he => ?_⟩
    have h := hloc v w hv he
    rwa [← hval w, ← hval (σ' v)] at h

lemma globalStep_congr_on_false_left {G : Game V} (hWF : WellFormed G) {σ₁ σ₂ σ' : V → V}
    (hσ : ∀ v, G.owner v = false → σ₁ v = σ₂ v) :
    GlobalStep G σ₁ σ' ↔ GlobalStep G σ₂ σ' := by
  constructor <;> rintro ⟨himp, hglob⟩
  · refine ⟨(improvement_congr_on_false_left hWF hσ).mp himp, fun ρ hρ v => ?_⟩
    exact hglob ρ ((allowed_congr_on_false_left hWF hσ).mpr hρ) v
  · refine ⟨(improvement_congr_on_false_left hWF hσ).mpr himp, fun ρ hρ v => ?_⟩
    exact hglob ρ ((allowed_congr_on_false_left hWF hσ).mp hρ) v

end StrategyCongrOnFalse

lemma step_run_bin (glob : Bool) (n t : ℕ) (hn : 0 < n)
    (hnot_term : ¬ IsTerminal n (pairAt n t).1 (pairAt n t).2)
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v)
    (h_best : ∀ glob n b s, ValidState n b s → ∀ v, BestEdgeProp glob n b s v) :
    (if glob then GlobalStep (G_bin n) else LocalStep (G_bin n))
      (run_bin glob n t) (run_bin glob n (t + 1)) := by
  have hvalid := validState_pairAt n hn t
  cases glob
  · simpa [run_bin, pairAt] using
      localStep_predState0 n (pairAt n t).1 (pairAt n t).2 hvalid hnot_term h_tau h_best
  · simpa [run_bin, pairAt] using
      globalStep_predState0 n (pairAt n t).1 (pairAt n t).2 hvalid hnot_term h_tau h_best

lemma value_run_bin_cyclePriority_eq_one (glob : Bool) (n t : ℕ) (hn : 0 < n)
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v)
    (v : V_bin n) :
    (value (G_bin n) (run_bin glob n t) v).cyclePriority = 1 := by
  have hvalid := validState_pairAt n hn t
  unfold run_bin
  rw [(h_tau glob n (pairAt n t).1 (pairAt n t).2 hvalid).2 v]
  exact pred_cyclePriority_eq_one glob n (pairAt n t).1 (pairAt n t).2 hvalid v

lemma run_eq_run_bin_on_false (glob : Bool) (n T T' : ℕ) (hn : 0 < n)
    (hT : IsTerminal n (pairAt n T).1 (pairAt n T).2 ∧
      ∀ t < T, ¬ IsTerminal n (pairAt n t).1 (pairAt n t).2)
    {run' : ℕ → V_bin n → V_bin n}
    (hrun' : CompleteRun (G_bin n)
      (if glob then GlobalStep (G_bin n) else LocalStep (G_bin n)) (ι_bin n) T' run')
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v)
    (h_best : ∀ glob n b s, ValidState n b s → ∀ v, BestEdgeProp glob n b s v) :
    ∀ t, t ≤ T → t ≤ T' → ∀ v, (G_bin n).owner v = false → run' t v = run_bin glob n t v
  | 0, _, _, v, _ => by
    rw [hrun'.1]
    dsimp [run_bin, pairAt]
    exact (predState0_zero_eq_init_all glob n hn v).symm
  | t + 1, htT, htT', v, hv => by
    have ih := run_eq_run_bin_on_false glob n T T' hn hT hrun' h_tau h_best t (by omega) (by omega)
    have hWF := G_bin_wellFormed n hn
    have hstep_bin := step_run_bin glob n t hn (hT.2 t (by omega)) h_tau h_best
    have hstep_run := (hrun'.2.2.1 t (by omega)).2
    cases glob
    · simp only [Bool.false_eq_true, ite_false] at hstep_bin hstep_run
      have hstep_run' : LocalStep (G_bin n) (run_bin false n t) (run' (t + 1)) :=
        (localStep_congr_on_false_left hWF ih).mp hstep_run
      exact localStep_eq_on_false hWF
        (value_run_bin_cyclePriority_eq_one false n t hn h_tau)
        (G_bin_sink_edge n) (G_bin_sink_priority n) (G_bin_gt_one_of_ne_sink n hn)
        (predState0_legal false n (pairAt n t).1 (pairAt n t).2)
        hstep_run' hstep_bin v hv
    · simp only [ite_true] at hstep_bin hstep_run
      have hstep_run' : GlobalStep (G_bin n) (run_bin true n t) (run' (t + 1)) :=
        (globalStep_congr_on_false_left hWF ih).mp hstep_run
      exact (globalStep_eq_on_false hWF
        (value_run_bin_cyclePriority_eq_one true n (t + 1) hn h_tau)
        (G_bin_sink_edge n) (G_bin_sink_priority n) (G_bin_gt_one_of_ne_sink n hn)
        hstep_bin hstep_run' v hv).symm

lemma G_bin_hardInstance (glob : Bool) (n : ℕ) (hn : 0 < n)
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v)
    (h_best : ∀ glob n b s, ValidState n b s → ∀ v, BestEdgeProp glob n b s v) :
    HardInstance (G_bin n) (ι_bin n)
      (if glob then GlobalStep (G_bin n) else LocalStep (G_bin n)) (2 ^ n) := by
  rcases exists_T_bin n hn with ⟨T, hT_term, hT_not_term⟩
  have hcomplete : CompleteRun (G_bin n)
      (if glob then GlobalStep (G_bin n) else LocalStep (G_bin n))
      (ι_bin n) T (run_bin glob n) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext v
      dsimp [run_bin, pairAt]
      exact predState0_zero_eq_init_all glob n hn v
    · intro t _
      exact predState0_legal glob n (pairAt n t).1 (pairAt n t).2
    · intro t ht
      refine ⟨?_, step_run_bin glob n t hn (hT_not_term t ht) h_tau h_best⟩
      exact improvable_of_not_terminal glob n (pairAt n t).1 (pairAt n t).2
        (validState_pairAt n hn t) (hT_not_term t ht) h_tau h_best
    · exact not_improvable_of_terminal glob n (pairAt n T).1 (pairAt n T).2
        (validState_pairAt n hn T) hT_term h_tau h_best
  refine ⟨G_bin_wellFormed n hn, ι_bin_legal n, ⟨T, run_bin glob n, hcomplete⟩, ?_⟩
  intro T' run' hrun'
  have h2pow : 2 ^ n ≤ T := two_pow_le_of_terminal_pairAt n T hn hT_term
  have hT_le_T' : T ≤ T' := by
    by_contra hlt
    have hlt' : T' < T := by omega
    have heq_on_false := run_eq_run_bin_on_false glob n T T' hn ⟨hT_term, hT_not_term⟩
      hrun' h_tau h_best T' (by omega) le_rfl
    have himp_bin : Improvable (G_bin n) (run_bin glob n T') :=
      improvable_of_not_terminal glob n (pairAt n T').1 (pairAt n T').2
        (validState_pairAt n hn T') (hT_not_term T' hlt') h_tau h_best
    have himp_run' : Improvable (G_bin n) (run' T') :=
      (improvable_congr_on_false (G_bin_wellFormed n hn) heq_on_false).mpr himp_bin
    exact hrun'.2.2.2 himp_run'
  omega

/-! ### Part 4: Equivalence Transport to `Fin N` and Target Theorems -/

section EquivTransport

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def mapGame (e : V ≃ W) (G : Game V) : Game W where
  owner w := G.owner (e.symm w)
  priority w := G.priority (e.symm w)
  edge w₁ w₂ := G.edge (e.symm w₁) (e.symm w₂)

def mapStrat (e : V ≃ W) (σ : V → V) : W → W :=
  fun w => e (σ (e.symm w))

def mapVal (e : V ≃ W) (a : Valuation V) : Valuation W where
  cyclePriority := a.cyclePriority
  path := a.path.map e.toEmbedding
  length := a.length

omit [Fintype V] [DecidableEq V] in
lemma Valuation.ext_iff {a b : Valuation V} :
    a = b ↔ a.cyclePriority = b.cyclePriority ∧ a.path = b.path ∧ a.length = b.length := by
  cases a; cases b; simp

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma mapStrat_symm_mapStrat (e : V ≃ W) (σ : V → V) :
    mapStrat e.symm (mapStrat e σ) = σ := by
  ext v
  simp [mapStrat]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma mapStrat_mapStrat_symm (e : V ≃ W) (σ' : W → W) :
    mapStrat e (mapStrat e.symm σ') = σ' := by
  ext w
  simp [mapStrat]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma mapVal_injective (e : V ≃ W) : Function.Injective (mapVal e) := by
  intro a b h
  rw [Valuation.ext_iff] at h ⊢
  exact ⟨h.1, Finset.map_inj.mp h.2.1, h.2.2⟩

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma mapGame_wellFormed (e : V ≃ W) {G : Game V} (hWF : WellFormed G) :
    WellFormed (mapGame e G) := by
  refine ⟨fun w => ?_, fun w₁ w₂ h => e.symm.injective (hWF.2 h)⟩
  rcases hWF.1 (e.symm w) with ⟨u, hu⟩
  exact ⟨e u, by simp [mapGame, hu]⟩

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma mapGame_binary (e : V ≃ W) {G : Game V} (hBin : Binary G) :
    Binary (mapGame e G) := by
  intro w
  rcases hBin (e.symm w) with ⟨a, b, hab⟩
  refine ⟨e a, e b, fun u hu => ?_⟩
  rcases hab (e.symm u) hu with h | h
  · left; exact e.symm.injective (by simpa using h)
  · right; exact e.symm.injective (by simpa using h)

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma mapGame_priority_le (e : V ≃ W) {G : Game V} {B : ℕ}
    (hB : ∀ v, G.priority v ≤ B) (w : W) :
    (mapGame e G).priority w ≤ B :=
  hB (e.symm w)

omit [DecidableEq V] [DecidableEq W] in
lemma mapGame_edgeCount (e : V ≃ W) (G : Game V) :
    edgeCount (mapGame e G) = edgeCount G := by
  classical
  unfold edgeCount
  let f : (V × V) ≃ (W × W) := Equiv.prodCongr e e
  have hmap :
      Finset.univ.filter (fun p : W × W => (mapGame e G).edge p.1 p.2) =
        (Finset.univ.filter (fun p : V × V => G.edge p.1 p.2)).map f.toEmbedding := by
    ext ⟨w₁, w₂⟩
    rw [Finset.mem_filter]
    simp [Finset.mem_filter, mapGame, f]
  rw [hmap, Finset.card_map]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma mapStrat_legal (e : V ≃ W) {G : Game V} {player : Bool} {σ : V → V} :
    Legal (mapGame e G) player (mapStrat e σ) ↔ Legal G player σ := by
  constructor
  · intro h v hv
    have hw := h (e v) (by simp [mapGame, hv])
    simpa [mapGame, mapStrat] using hw
  · intro h w hw
    have hv := h (e.symm w) hw
    simpa [mapGame, mapStrat] using hv

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma step_mapGame (e : V ≃ W) (G : Game V) (σ τ : V → V) (v : V) :
    step (mapGame e G) (mapStrat e σ) (mapStrat e τ) (e v) = e (step G σ τ v) := by
  unfold step mapGame mapStrat
  simp only [e.symm_apply_apply]
  split_ifs <;> rfl

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma play_mapGame (e : V ≃ W) (G : Game V) (σ τ : V → V) (v : V) (t : ℕ) :
    play (mapGame e G) (mapStrat e σ) (mapStrat e τ) (e v) t = e (play G σ τ v t) := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    rw [play_succ, play_succ, step_mapGame, ih]

omit [DecidableEq V] [DecidableEq W] in
lemma mem_recurring_play_mapGame (e : V ≃ W) (G : Game V) (σ τ : V → V) (v u : V) :
    e u ∈ recurring (play (mapGame e G) (mapStrat e σ) (mapStrat e τ) (e v)) ↔
      u ∈ recurring (play G σ τ v) := by
  simp only [mem_recurring_iff, play_mapGame, e.injective.eq_iff]

omit [DecidableEq V] [DecidableEq W] in
lemma recurring_play_mapGame (e : V ≃ W) (G : Game V) (σ τ : V → V) (v : V) :
    recurring (play (mapGame e G) (mapStrat e σ) (mapStrat e τ) (e v)) =
      (recurring (play G σ τ v)).map e.toEmbedding := by
  ext w
  obtain ⟨u, rfl⟩ := e.surjective w
  simp [mem_recurring_play_mapGame]

lemma playValue_mapGame_cyclePriority (e : V ≃ W) (G : Game V) (σ τ : V → V) (v : V) :
    (playValue (mapGame e G) (mapStrat e σ) (mapStrat e τ) (e v)).cyclePriority =
      (playValue G σ τ v).cyclePriority := by
  rw [playValue_cyclePriority, playValue_cyclePriority, recurring_play_mapGame, Finset.sup_map]
  congr 1
  ext u
  simp [mapGame]

lemma cycleLeader_mapGame (e : V ≃ W) {G : Game V} (hWF : WellFormed G)
    (σ τ : V → V) (v : V) :
    cycleLeader (mapGame e G) (mapStrat e σ) (mapStrat e τ) (e v) =
      e (cycleLeader G σ τ v) := by
  apply (mapGame_wellFormed e hWF).2
  rw [← playValue_cyclePriority_eq_priority_cycleLeader,
      playValue_mapGame_cyclePriority,
      playValue_cyclePriority_eq_priority_cycleLeader]
  simp [mapGame]

lemma playValue_mapGame_length (e : V ≃ W) {G : Game V} (hWF : WellFormed G)
    (σ τ : V → V) (v : V) :
    (playValue (mapGame e G) (mapStrat e σ) (mapStrat e τ) (e v)).length =
      (playValue G σ τ v).length := by
  apply le_antisymm
  · apply length_le_of_play_eq_cycleLeader
    rw [play_mapGame, play_playValue_length, cycleLeader_mapGame e hWF]
  · apply length_le_of_play_eq_cycleLeader
    have h := play_playValue_length (mapGame e G) (mapStrat e σ) (mapStrat e τ) (e v)
    rw [play_mapGame, cycleLeader_mapGame e hWF] at h
    exact e.injective h

lemma playValue_mapGame_path (e : V ≃ W) {G : Game V} (hWF : WellFormed G)
    (σ τ : V → V) (v : V) :
    (playValue (mapGame e G) (mapStrat e σ) (mapStrat e τ) (e v)).path =
      (playValue G σ τ v).path.map e.toEmbedding := by
  ext w
  obtain ⟨u, rfl⟩ := e.surjective w
  have hmem : e u ∈ (playValue G σ τ v).path.map e.toEmbedding ↔ u ∈ (playValue G σ τ v).path := by
    simp
  rw [hmem, mem_playValue_path_iff, mem_playValue_path_iff]
  simp only [playValue_mapGame_length e hWF, playValue_mapGame_cyclePriority,
    play_mapGame, e.injective.eq_iff]
  simp only [mapGame, e.symm_apply_apply]

lemma playValue_mapGame (e : V ≃ W) {G : Game V} (hWF : WellFormed G)
    (σ τ : V → V) (v : V) :
    playValue (mapGame e G) (mapStrat e σ) (mapStrat e τ) (e v) =
      mapVal e (playValue G σ τ v) := by
  rw [Valuation.ext_iff]
  exact ⟨playValue_mapGame_cyclePriority e G σ τ v,
    playValue_mapGame_path e hWF σ τ v,
    playValue_mapGame_length e hWF σ τ v⟩

omit [Fintype V] [Fintype W] in
lemma mem_symmDiff_map (e : V ≃ W) (A B : Finset V) (u : V) :
    e u ∈ (A.map e.toEmbedding \ B.map e.toEmbedding) ∪
        (B.map e.toEmbedding \ A.map e.toEmbedding) ↔
      u ∈ (A \ B) ∪ (B \ A) := by
  simp [Finset.mem_union, Finset.mem_sdiff]

omit [Fintype V] [Fintype W] in
lemma setLT_mapGame (e : V ≃ W) (G : Game V) (A B : Finset V) :
    SetLT (mapGame e G) (A.map e.toEmbedding) (B.map e.toEmbedding) ↔ SetLT G A B := by
  constructor
  · rintro ⟨w, hw_mem, hw_max, hw_par⟩
    obtain ⟨u, rfl⟩ := e.surjective w
    refine ⟨u, (mem_symmDiff_map e A B u).mp hw_mem, ?_, ?_⟩
    · intro x hx
      have h := hw_max (e x) ((mem_symmDiff_map e A B x).mpr hx)
      simpa [mapGame] using h
    · simpa [mapGame] using hw_par
  · rintro ⟨u, hu_mem, hu_max, hu_par⟩
    refine ⟨e u, (mem_symmDiff_map e A B u).mpr hu_mem, ?_, ?_⟩
    · intro w hw
      obtain ⟨x, rfl⟩ := e.surjective w
      have h := hu_max x ((mem_symmDiff_map e A B x).mp hw)
      simpa [mapGame] using h
    · simpa [mapGame] using hu_par

omit [Fintype V] [Fintype W] in
lemma valueLT_mapGame (e : V ≃ W) (G : Game V) (a b : Valuation V) :
    ValueLT (mapGame e G) (mapVal e a) (mapVal e b) ↔ ValueLT G a b := by
  unfold ValueLT mapVal
  simp only [setLT_mapGame, Finset.map_inj]

omit [Fintype V] [Fintype W] in
lemma valueLE_mapGame (e : V ≃ W) (G : Game V) (a b : Valuation V) :
    ValueLE (mapGame e G) (mapVal e a) (mapVal e b) ↔ ValueLE G a b := by
  unfold ValueLE
  rw [(mapVal_injective e).eq_iff, valueLT_mapGame]

lemma optimalCounterstrategy_mapGame (e : V ≃ W) {G : Game V} (hWF : WellFormed G)
    (σ τ : V → V) :
    OptimalCounterstrategy (mapGame e G) (mapStrat e σ) (mapStrat e τ) ↔
      OptimalCounterstrategy G σ τ := by
  constructor
  · rintro ⟨hleg, hmin⟩
    refine ⟨(mapStrat_legal e).mp hleg, fun v τ' hτ' => ?_⟩
    have h := hmin (e v) (mapStrat e τ') ((mapStrat_legal e).mpr hτ')
    rwa [playValue_mapGame e hWF, playValue_mapGame e hWF, valueLE_mapGame] at h
  · rintro ⟨hleg, hmin⟩
    refine ⟨(mapStrat_legal e).mpr hleg, fun w τ' hτ' => ?_⟩
    obtain ⟨v, rfl⟩ := e.surjective w
    have hτ'_eq : τ' = mapStrat e (mapStrat e.symm τ') := (mapStrat_mapStrat_symm e τ').symm
    have hleg' : Legal G true (mapStrat e.symm τ') := by
      rw [hτ'_eq] at hτ'
      exact (mapStrat_legal e).mp hτ'
    have h := hmin v (mapStrat e.symm τ') hleg'
    rw [hτ'_eq, playValue_mapGame e hWF, playValue_mapGame e hWF, valueLE_mapGame]
    exact h

lemma value_mapGame (e : V ≃ W) {G : Game V} (hWF : WellFormed G)
    (σ : V → V) (v : V) :
    value (mapGame e G) (mapStrat e σ) (e v) = mapVal e (value G σ v) := by
  rcases exists_optimalCounterstrategy G hWF σ with ⟨τ, hτ⟩
  have hτ' : OptimalCounterstrategy (mapGame e G) (mapStrat e σ) (mapStrat e τ) :=
    (optimalCounterstrategy_mapGame e hWF σ τ).mpr hτ
  rw [value_eq_playValue_of_optimalCounterstrategy (mapGame_wellFormed e hWF) hτ' (e v),
      value_eq_playValue_of_optimalCounterstrategy hWF hτ v,
      playValue_mapGame e hWF]

lemma improvable_mapGame (e : V ≃ W) {G : Game V} (hWF : WellFormed G) (σ : V → V) :
    Improvable (mapGame e G) (mapStrat e σ) ↔ Improvable G σ := by
  constructor
  · rintro ⟨w₁, w₂, hown, he, hlt⟩
    obtain ⟨v₁, rfl⟩ := e.surjective w₁
    obtain ⟨v₂, rfl⟩ := e.surjective w₂
    refine ⟨v₁, v₂, by simpa [mapGame] using hown, by simpa [mapGame] using he, ?_⟩
    have hσv : mapStrat e σ (e v₁) = e (σ v₁) := by simp [mapStrat]
    rw [hσv, value_mapGame e hWF, value_mapGame e hWF, valueLT_mapGame] at hlt
    exact hlt
  · rintro ⟨v₁, v₂, hown, he, hlt⟩
    refine ⟨e v₁, e v₂, by simpa [mapGame] using hown, by simpa [mapGame] using he, ?_⟩
    have hσv : mapStrat e σ (e v₁) = e (σ v₁) := by simp [mapStrat]
    rw [hσv, value_mapGame e hWF, value_mapGame e hWF, valueLT_mapGame]
    exact hlt

lemma allowed_mapGame (e : V ≃ W) {G : Game V} (hWF : WellFormed G) (σ σ' : V → V) :
    Allowed (mapGame e G) (mapStrat e σ) (mapStrat e σ') ↔ Allowed G σ σ' := by
  constructor
  · rintro ⟨hleg, hle⟩
    refine ⟨(mapStrat_legal e).mp hleg, fun v hv => ?_⟩
    have h := hle (e v) (by simpa [mapGame] using hv)
    have hσv : mapStrat e σ (e v) = e (σ v) := by simp [mapStrat]
    have hσ'v : mapStrat e σ' (e v) = e (σ' v) := by simp [mapStrat]
    rwa [hσv, hσ'v, value_mapGame e hWF, value_mapGame e hWF, valueLE_mapGame] at h
  · rintro ⟨hleg, hle⟩
    refine ⟨(mapStrat_legal e).mpr hleg, fun w hw => ?_⟩
    obtain ⟨v, rfl⟩ := e.surjective w
    have h := hle v (by simpa [mapGame] using hw)
    have hσv : mapStrat e σ (e v) = e (σ v) := by simp [mapStrat]
    have hσ'v : mapStrat e σ' (e v) = e (σ' v) := by simp [mapStrat]
    rw [hσv, hσ'v, value_mapGame e hWF, value_mapGame e hWF, valueLE_mapGame]
    exact h

lemma improvement_mapGame (e : V ≃ W) {G : Game V} (hWF : WellFormed G) (σ σ' : V → V) :
    Improvement (mapGame e G) (mapStrat e σ) (mapStrat e σ') ↔ Improvement G σ σ' := by
  constructor
  · rintro ⟨hal, himp⟩
    refine ⟨(allowed_mapGame e hWF σ σ').mp hal, fun h => ?_⟩
    rcases himp ((improvable_mapGame e hWF σ).mpr h) with ⟨w, hw, hlt⟩
    obtain ⟨v, rfl⟩ := e.surjective w
    have hσv : mapStrat e σ (e v) = e (σ v) := by simp [mapStrat]
    have hσ'v : mapStrat e σ' (e v) = e (σ' v) := by simp [mapStrat]
    rw [hσv, hσ'v, value_mapGame e hWF, value_mapGame e hWF, valueLT_mapGame] at hlt
    exact ⟨v, by simpa [mapGame] using hw, hlt⟩
  · rintro ⟨hal, himp⟩
    refine ⟨(allowed_mapGame e hWF σ σ').mpr hal, fun h => ?_⟩
    rcases himp ((improvable_mapGame e hWF σ).mp h) with ⟨v, hv, hlt⟩
    have hσv : mapStrat e σ (e v) = e (σ v) := by simp [mapStrat]
    have hσ'v : mapStrat e σ' (e v) = e (σ' v) := by simp [mapStrat]
    refine ⟨e v, by simpa [mapGame] using hv, ?_⟩
    rw [hσv, hσ'v, value_mapGame e hWF, value_mapGame e hWF, valueLT_mapGame]
    exact hlt

lemma localStep_mapGame (e : V ≃ W) {G : Game V} (hWF : WellFormed G) (σ σ' : V → V) :
    LocalStep (mapGame e G) (mapStrat e σ) (mapStrat e σ') ↔ LocalStep G σ σ' := by
  constructor
  · rintro ⟨himp, hloc⟩
    refine ⟨(improvement_mapGame e hWF σ σ').mp himp, fun v u hv he => ?_⟩
    have h := hloc (e v) (e u) (by simpa [mapGame] using hv) (by simpa [mapGame] using he)
    have hσ'v : mapStrat e σ' (e v) = e (σ' v) := by simp [mapStrat]
    rwa [hσ'v, value_mapGame e hWF, value_mapGame e hWF, valueLE_mapGame] at h
  · rintro ⟨himp, hloc⟩
    refine ⟨(improvement_mapGame e hWF σ σ').mpr himp, fun w₁ w₂ hw he => ?_⟩
    obtain ⟨v, rfl⟩ := e.surjective w₁
    obtain ⟨u, rfl⟩ := e.surjective w₂
    have h := hloc v u (by simpa [mapGame] using hw) (by simpa [mapGame] using he)
    have hσ'v : mapStrat e σ' (e v) = e (σ' v) := by simp [mapStrat]
    rw [hσ'v, value_mapGame e hWF, value_mapGame e hWF, valueLE_mapGame]
    exact h

lemma globalStep_mapGame (e : V ≃ W) {G : Game V} (hWF : WellFormed G) (σ σ' : V → V) :
    GlobalStep (mapGame e G) (mapStrat e σ) (mapStrat e σ') ↔ GlobalStep G σ σ' := by
  constructor
  · rintro ⟨himp, hglob⟩
    refine ⟨(improvement_mapGame e hWF σ σ').mp himp, fun ρ hρ v => ?_⟩
    have h := hglob (mapStrat e ρ) ((allowed_mapGame e hWF σ ρ).mpr hρ) (e v)
    rwa [value_mapGame e hWF, value_mapGame e hWF, valueLE_mapGame] at h
  · rintro ⟨himp, hglob⟩
    refine ⟨(improvement_mapGame e hWF σ σ').mpr himp, fun ρ' hρ' w => ?_⟩
    obtain ⟨v, rfl⟩ := e.surjective w
    have hρ'_eq : ρ' = mapStrat e (mapStrat e.symm ρ') := (mapStrat_mapStrat_symm e ρ').symm
    have hρ : Allowed G σ (mapStrat e.symm ρ') := by
      rw [hρ'_eq] at hρ'
      exact (allowed_mapGame e hWF σ (mapStrat e.symm ρ')).mp hρ'
    have h := hglob (mapStrat e.symm ρ') hρ v
    rw [hρ'_eq, value_mapGame e hWF, value_mapGame e hWF, valueLE_mapGame]
    exact h

lemma step_rel_mapGame (e : V ≃ W) {G : Game V} (hWF : WellFormed G) (glob : Bool) (σ σ' : V → V) :
    (if glob then GlobalStep (mapGame e G) else LocalStep (mapGame e G))
      (mapStrat e σ) (mapStrat e σ') ↔
    (if glob then GlobalStep G else LocalStep G) σ σ' := by
  cases glob
  · exact localStep_mapGame e hWF σ σ'
  · exact globalStep_mapGame e hWF σ σ'

lemma completeRun_mapGame (e : V ≃ W) {G : Game V} (hWF : WellFormed G) (glob : Bool)
    (ι : V → V) (T : ℕ) (run : ℕ → V → V) :
    CompleteRun (mapGame e G)
      (if glob then GlobalStep (mapGame e G) else LocalStep (mapGame e G))
      (mapStrat e ι) T (fun t => mapStrat e (run t)) ↔
    CompleteRun G (if glob then GlobalStep G else LocalStep G) ι T run := by
  constructor
  · rintro ⟨h0, hleg, hstep, hterm⟩
    dsimp only at h0
    refine ⟨?_, fun t ht => (mapStrat_legal e).mp (hleg t ht), fun t ht => ?_,
      fun h => hterm ((improvable_mapGame e hWF (run T)).mpr h)⟩
    · rw [← mapStrat_symm_mapStrat e (run 0), h0, mapStrat_symm_mapStrat]
    · rcases hstep t ht with ⟨himp, hst⟩
      exact ⟨(improvable_mapGame e hWF (run t)).mp himp,
        (step_rel_mapGame e hWF glob (run t) (run (t + 1))).mp hst⟩
  · rintro ⟨h0, hleg, hstep, hterm⟩
    refine ⟨by dsimp only; rw [h0], fun t ht => (mapStrat_legal e).mpr (hleg t ht), fun t ht => ?_,
      fun h => hterm ((improvable_mapGame e hWF (run T)).mp h)⟩
    rcases hstep t ht with ⟨himp, hst⟩
    exact ⟨(improvable_mapGame e hWF (run t)).mpr himp,
      (step_rel_mapGame e hWF glob (run t) (run (t + 1))).mpr hst⟩

lemma hardInstance_mapGame (e : V ≃ W) {G : Game V} (glob : Bool) {ι : V → V} {iter : ℕ}
    (hHard : HardInstance G ι (if glob then GlobalStep G else LocalStep G) iter) :
    HardInstance (mapGame e G) (mapStrat e ι)
      (if glob then GlobalStep (mapGame e G) else LocalStep (mapGame e G)) iter := by
  rcases hHard with ⟨hWF, hleg, ⟨T, run, hrun⟩, hbound⟩
  refine ⟨mapGame_wellFormed e hWF, (mapStrat_legal e).mpr hleg,
    ⟨T, fun t => mapStrat e (run t), (completeRun_mapGame e hWF glob ι T run).mpr hrun⟩, ?_⟩
  intro T' run' hrun'
  have hrun'_eq : run' = fun t => mapStrat e (mapStrat e.symm (run' t)) := by
    ext t w; simp [mapStrat]
  rw [hrun'_eq] at hrun'
  exact hbound T' (fun t => mapStrat e.symm (run' t))
    ((completeRun_mapGame e hWF glob ι T' (fun t => mapStrat e.symm (run' t))).mp hrun')

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
lemma reflTransGen_mapGame (e : V ≃ W) {G : Game V} {u v : V}
    (h : Relation.ReflTransGen G.edge u v) :
    Relation.ReflTransGen (mapGame e G).edge (e u) (e v) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.tail ih (by simpa [mapGame] using hstep)

lemma isSinkGame_mapGame (e : V ≃ W) {G : Game V} {ι : V → V} {sink : V}
    (hSink : IsSinkGame G ι sink) :
    IsSinkGame (mapGame e G) (mapStrat e ι) (e sink) := by
  rcases hSink with ⟨hWF, hleg, hedge_sink, hprio_sink, hgt_one, hreach, hcp⟩
  refine ⟨mapGame_wellFormed e hWF, (mapStrat_legal e).mpr hleg,
    by simpa [mapGame] using hedge_sink,
    by simpa [mapGame] using hprio_sink,
    fun w hw => ?_,
    fun w => ?_,
    fun σ' hσ' hle w => ?_⟩
  · obtain ⟨v, rfl⟩ := e.surjective w
    have hv : v ≠ sink := fun h => hw (congrArg e h)
    simpa [mapGame] using hgt_one v hv
  · obtain ⟨v, rfl⟩ := e.surjective w
    exact reflTransGen_mapGame e (hreach v)
  · obtain ⟨v, rfl⟩ := e.surjective w
    have hσ'_eq : σ' = mapStrat e (mapStrat e.symm σ') := (mapStrat_mapStrat_symm e σ').symm
    have hleg_v : Legal G false (mapStrat e.symm σ') := by
      rw [hσ'_eq] at hσ'
      exact (mapStrat_legal e).mp hσ'
    have hle_v : ∀ u, ValueLE G (value G ι u) (value G (mapStrat e.symm σ') u) := by
      intro u
      have h := hle (e u)
      rw [hσ'_eq, value_mapGame e hWF, value_mapGame e hWF, valueLE_mapGame] at h
      exact h
    have hcp_v := hcp (mapStrat e.symm σ') hleg_v hle_v v
    rw [hσ'_eq, value_mapGame e hWF]
    exact hcp_v

end EquivTransport

theorem exponential_sink_family_of_bestEdge
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v)
    (h_best : ∀ glob n b s, ValidState n b s → ∀ v, BestEdgeProp glob n b s v) :
    ∃ C : ℕ, 0 < C ∧ ∀ global : Bool, ∀ n : ℕ, 0 < n →
      ∃ N : ℕ, ∃ G : Game (Fin N), ∃ ι : Fin N → Fin N, ∃ sink : Fin N,
        Binary G ∧ edgeCount G ≤ C * n ∧
        (∀ v, G.priority v ≤ C * n) ∧
        IsSinkGame G ι sink ∧
        HardInstance G ι (if global then GlobalStep G else LocalStep G) (2 ^ n) := by
  refine ⟨114, by decide, fun global n hn => ?_⟩
  let N := Fintype.card (V_bin n)
  let e : V_bin n ≃ Fin N := Fintype.equivFin (V_bin n)
  refine ⟨N, mapGame e (G_bin n), mapStrat e (ι_bin n), e .x, ?_, ?_, ?_, ?_, ?_⟩
  · exact mapGame_binary e (G_bin_binary n)
  · rw [mapGame_edgeCount]
    exact G_bin_edgeCount_le n hn
  · exact mapGame_priority_le e (G_bin_priority_le n hn)
  · exact isSinkGame_mapGame e (G_bin_isSinkGame n hn h_tau)
  · exact hardInstance_mapGame e global (G_bin_hardInstance global n hn h_tau h_best)

theorem exponential_binary_of_bestEdge
    (h_tau : ∀ glob n b s, ValidState n b s →
      OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
        ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v)
    (h_best : ∀ glob n b s, ValidState n b s → ∀ v, BestEdgeProp glob n b s v) :
    ExponentialBinary := by
  rcases exponential_sink_family_of_bestEdge h_tau h_best with ⟨C, hC, hfam⟩
  refine ⟨C, hC, fun global n hn => ?_⟩
  rcases hfam global n hn with ⟨N, G, ι, _sink, hbin, hedge, hprio, _hsink, hhard⟩
  exact ⟨N, G, ι, hbin, hedge, hprio, hhard⟩

end FriedmannParity


