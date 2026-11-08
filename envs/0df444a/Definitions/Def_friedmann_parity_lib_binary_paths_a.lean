-- Prove2me | Definitions.Def_friedmann_parity_lib_binary_paths_a
-- name    : friedmann_parity_lib_binary_paths_a
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-08T03:48:30.641467+00:00
-- url     : https://prove2.me/theorems/b7fc2963-a4b7-4051-b925-b3e928868871
-- title:
--   Friedmann binary lower-bound family: spine paths and optimality of the candidate counterstrategies
-- statement:
--   A sorry-free library module that extends `friedmann_parity_lib_binary_gates`. It describes the high-priority content of the paths of $\sigma_{b,s}$ along the spine of $G_n$. This includes the portal order between the top-level vertices $c$ and $r$ (`portalOrderProp_holds`), the increment lemmas for passing from $b$ to $b+1$, and the membership chains needed later.
--
--   Its main result, `predTau0_optimal`, states that the candidate reply $\tau_{b,s}$ is an optimal counterstrategy against $\sigma_{b,s}$, so that the valuation of $\sigma_{b,s}$ is the play valuation of $(\sigma_{b,s},\tau_{b,s})$. This module and `friedmann_parity_lib_binary_paths_b` together form one proof development, split in two for compilation size.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 7(3:19), 2011, arXiv:1106.0778, §§6–8

import Definitions.Def_friedmann_parity_lib_binary_gates

set_option autoImplicit false
set_option linter.unusedVariables false

namespace FriedmannParity

/-! ### Part 1: Priority Parities, Bounds, and Ladder Portal Lemmas -/

lemma prio_z_odd (n : ℕ) (i : Fin n) : (G_bin n).priority (.z i) % 2 = 1 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_f_odd (n : ℕ) (i : Fin n) : (G_bin n).priority (.f i) % 2 = 1 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_k_even (n : ℕ) (i : Fin n) : (G_bin n).priority (.k i) % 2 = 0 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_s_even (n : ℕ) : (G_bin n).priority .s % 2 = 0 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_r_even (n : ℕ) : (G_bin n).priority .r % 2 = 0 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_c_even (n : ℕ) : (G_bin n).priority .c % 2 = 0 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_hy_odd (n : ℕ) (i : Fin n) : (G_bin n).priority (.hy i) % 2 = 1 := by
  have h := shift_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_hx_odd (n : ℕ) (i : Fin n) : (G_bin n).priority (.hx i) % 2 = 1 := by
  have h := shift_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_h_even (n : ℕ) (i : Fin n) : (G_bin n).priority (.h i) % 2 = 0 := by
  have h := shift_bin_even n
  dsimp [G_bin, priority_bin]
  omega

lemma prio_ge_c_iff (n : ℕ) (u : V_bin n) :
    (G_bin n).priority .c ≤ (G_bin n).priority u ↔
      u = .c ∨ u = .r ∨ u = .s ∨ ∃ j : Fin n, u = .z j ∨ u = .f j ∨ u = .k j := by
  constructor
  · intro h
    cases u with
    | c => exact Or.inl rfl
    | r => exact Or.inr (Or.inl rfl)
    | s => exact Or.inr (Or.inr (Or.inl rfl))
    | z j => exact Or.inr (Or.inr (Or.inr ⟨j, Or.inl rfl⟩))
    | f j => exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inl rfl)⟩))
    | k j => exact Or.inr (Or.inr (Or.inr ⟨j, Or.inr (Or.inr rfl)⟩))
    | _ =>
      exfalso
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin] at h
      try split_ifs at h
      all_goals omega
  · rintro (rfl | rfl | rfl | ⟨j, rfl | rfl | rfl⟩) <;>
    { dsimp [G_bin, priority_bin]; omega }

lemma prio_gt_s_iff (n : ℕ) (u : V_bin n) :
    (G_bin n).priority .s < (G_bin n).priority u ↔
      ∃ j : Fin n, u = .z j ∨ u = .f j ∨ u = .k j := by
  constructor
  · intro h
    rcases (prio_ge_c_iff n u).mp (by dsimp [G_bin, priority_bin] at h ⊢; omega) with
      rfl | rfl | rfl | hj
    · dsimp [G_bin, priority_bin] at h; omega
    · dsimp [G_bin, priority_bin] at h; omega
    · dsimp [G_bin, priority_bin] at h; omega
    · exact hj
  · rintro ⟨j, rfl | rfl | rfl⟩ <;>
    { dsimp [G_bin, priority_bin]; omega }

def InLadderCore (n : ℕ) : V_bin n → Prop
  | .lp1 _ | .lp2 _ | .lp3 _ | .l1 _ | .l2 _ | .l3 _
  | .b _ | .a _ | .r_2_odd | .r_2 | .r_a | .c_odd => True
  | _ => False

lemma inLadderCore_ne_x (n : ℕ) (w : V_bin n) (hw : InLadderCore n w) : w ≠ .x := by
  cases w <;> simp [InLadderCore] at hw ⊢

lemma inLadderCore_prio_lt_c (n : ℕ) (w : V_bin n) (hw : InLadderCore n w) :
    (G_bin n).priority w < (G_bin n).priority .c := by
  cases w <;> simp [InLadderCore] at hw
  all_goals
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]
    try split_ifs
    all_goals omega

lemma inLadderCore_step (glob : Bool) (n b s : ℕ) (w : V_bin n) (hw : InLadderCore n w) :
    let w' := step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w
    w' = .c ∨ w' = .r ∨ InLadderCore n w' := by
  cases w <;> simp [InLadderCore] at hw
  all_goals
    dsimp [step, G_bin, owner_bin, predState0, predTau0, chooseTauEdge1, edge0, edge1]
    repeat' split_ifs
    all_goals simp [InLadderCore]

lemma hitsPortal_of_inLadderCore (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    ∀ k w, predRank0 glob n b s w ≤ k → InLadderCore n w →
      HitsPortal glob n b s w .c ∨ HitsPortal glob n b s w .r
  | 0, w, hk, hw => by
    exfalso
    have hlt := predRank0_step_lt glob n b s hvalid w (inLadderCore_ne_x n w hw)
    omega
  | k + 1, w, hk, hw => by
    have hne := inLadderCore_ne_x n w hw
    have hprio := inLadderCore_prio_lt_c n w hw
    have hlt := predRank0_step_lt glob n b s hvalid w hne
    rcases inLadderCore_step glob n b s w hw with hstep | hstep | hstep
    · left
      apply hitsPortal_of_step glob n b s hvalid w .c hne hprio
      rw [hstep]
      exact hitsPortal_refl glob n b s hvalid .c (by nofun)
    · right
      apply hitsPortal_of_step glob n b s hvalid w .r hne hprio
      rw [hstep]
      exact hitsPortal_refl glob n b s hvalid .r (by nofun)
    · rcases hitsPortal_of_inLadderCore glob n b s hvalid k _ (by omega) hstep with hc | hr
      · left; exact hitsPortal_of_step glob n b s hvalid w .c hne hprio hc
      · right; exact hitsPortal_of_step glob n b s hvalid w .r hne hprio hr

lemma not_both_d2_d3_of_not_dClosed0 (glob : Bool) (n b s : ℕ) (i : Fin n)
    (hd : dClosed0 n b s i = false)
    (hd2 : chooseEdge1 glob n b s (.d2 i) = true) :
    chooseEdge1 glob n b s (.d3 i) = false := by
  unfold dClosed0 at hd
  dsimp [chooseEdge1] at hd2 ⊢
  cases hbit : b.testBit i.val with
  | true =>
    simp [hbit] at hd
    simp [hbit, hd] at hd2
  | false =>
    simp [hbit] at hd hd2 ⊢
    omega

lemma hitsPortal_d1_of_not_dClosed0 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hd : dClosed0 n b s i = false) :
    HitsPortal glob n b s (.d1 i) .c ∨ HitsPortal glob n b s (.d1 i) .r := by
  have hp1 : (G_bin n).priority (.d1 i) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
  have hp2 : (G_bin n).priority (.d2 i) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
  have hp3 : (G_bin n).priority (.d3 i) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
  by_cases hc1 : chooseEdge1 glob n b s (.d1 i) = true
  · have hs1 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d1 i) = .d2 i := by
      dsimp [step, G_bin, owner_bin, predState0]; rw [if_pos hc1]; rfl
    by_cases hc2 : chooseEdge1 glob n b s (.d2 i) = true
    · have hs2 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d2 i) = .d3 i := by
        dsimp [step, G_bin, owner_bin, predState0]; rw [if_pos hc2]; rfl
      have hc3 := not_both_d2_d3_of_not_dClosed0 glob n b s i hd hc2
      have hs3 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d3 i) = .lp3 (tap_bin n i) := by
        dsimp [step, G_bin, owner_bin, predState0]; rw [hc3]; rfl
      rcases hitsPortal_of_inLadderCore glob n b s hvalid _ (.lp3 (tap_bin n i)) le_rfl trivial with h | h
      · left
        apply hitsPortal_of_step glob n b s hvalid (.d1 i) .c (by nofun) hp1
        rw [hs1]
        apply hitsPortal_of_step glob n b s hvalid (.d2 i) .c (by nofun) hp2
        rw [hs2]
        apply hitsPortal_of_step glob n b s hvalid (.d3 i) .c (by nofun) hp3
        rw [hs3]; exact h
      · right
        apply hitsPortal_of_step glob n b s hvalid (.d1 i) .r (by nofun) hp1
        rw [hs1]
        apply hitsPortal_of_step glob n b s hvalid (.d2 i) .r (by nofun) hp2
        rw [hs2]
        apply hitsPortal_of_step glob n b s hvalid (.d3 i) .r (by nofun) hp3
        rw [hs3]; exact h
    · have hc2' : chooseEdge1 glob n b s (.d2 i) = false := Bool.eq_false_of_not_eq_true hc2
      have hs2 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d2 i) = .lp2 (tap_bin n i) := by
        dsimp [step, G_bin, owner_bin, predState0]; rw [hc2']; rfl
      rcases hitsPortal_of_inLadderCore glob n b s hvalid _ (.lp2 (tap_bin n i)) le_rfl trivial with h | h
      · left
        apply hitsPortal_of_step glob n b s hvalid (.d1 i) .c (by nofun) hp1
        rw [hs1]
        apply hitsPortal_of_step glob n b s hvalid (.d2 i) .c (by nofun) hp2
        rw [hs2]; exact h
      · right
        apply hitsPortal_of_step glob n b s hvalid (.d1 i) .r (by nofun) hp1
        rw [hs1]
        apply hitsPortal_of_step glob n b s hvalid (.d2 i) .r (by nofun) hp2
        rw [hs2]; exact h
  · have hc1' : chooseEdge1 glob n b s (.d1 i) = false := Bool.eq_false_of_not_eq_true hc1
    have hs1 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d1 i) = .lp1 (tap_bin n i) := by
      dsimp [step, G_bin, owner_bin, predState0]; rw [hc1']; rfl
    rcases hitsPortal_of_inLadderCore glob n b s hvalid _ (.lp1 (tap_bin n i)) le_rfl trivial with h | h
    · left
      apply hitsPortal_of_step glob n b s hvalid (.d1 i) .c (by nofun) hp1
      rw [hs1]; exact h
    · right
      apply hitsPortal_of_step glob n b s hvalid (.d1 i) .r (by nofun) hp1
      rw [hs1]; exact h

lemma dClosed0_eq_false_of_tau_false (n b s : ℕ) (i : Fin n)
    (htau : chooseTauEdge1 n b s (.g i) = false) :
    dClosed0 n b s i = false := by
  dsimp [chooseTauEdge1] at htau
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at htau
  rcases htau with ⟨⟨hbit, hlt_T⟩, _⟩
  unfold dClosed0
  simp [hbit, hlt_T]

lemma hitsPortal_g_of_tau_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (htau : chooseTauEdge1 n b s (.g i) = false) :
    HitsPortal glob n b s (.g i) .c ∨ HitsPortal glob n b s (.g i) .r := by
  have hpg : (G_bin n).priority (.g i) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g i) = .d1 i := by
    dsimp [step, G_bin, owner_bin, predTau0]; rw [htau]; rfl
  rcases hitsPortal_d1_of_not_dClosed0 glob n b s hvalid i (dClosed0_eq_false_of_tau_false n b s i htau) with h | h
  · left; apply hitsPortal_of_step glob n b s hvalid (.g i) .c (by nofun) hpg; rw [hstep]; exact h
  · right; apply hitsPortal_of_step glob n b s hvalid (.g i) .r (by nofun) hpg; rw [hstep]; exact h

/-! ### Part 2: High-Priority Membership on the Spine and `portalOrderProp_holds` -/

lemma lt_n_of_hasHigherOne0 {b n i : ℕ} (h : hasHigherOne0 b n i = true) : i + 1 < n := by
  rcases (hasHigherOne0_iff b n i).mp h with ⟨j, hij, hjn, _⟩
  omega

lemma hasHigherOne0_succ_iff {b n i : ℕ} (hi1 : i + 1 < n) :
    hasHigherOne0 b n i = true ↔ b.testBit (i + 1) = true ∨ hasHigherOne0 b n (i + 1) = true := by
  rw [hasHigherOne0_iff, hasHigherOne0_iff]
  constructor
  · rintro ⟨j, hij, hjn, hbit⟩
    by_cases hj : j = i + 1
    · subst hj; exact Or.inl hbit
    · exact Or.inr ⟨j, by omega, hjn, hbit⟩
  · rintro (hbit | ⟨j, hij, hjn, hbit⟩)
    · exact ⟨i + 1, by omega, hi1, hbit⟩
    · exact ⟨j, by omega, hjn, hbit⟩

def highMemZ (n b : ℕ) (i : Fin n) : V_bin n → Prop
  | .z j => j = i ∨ (i.val < j.val ∧ b.testBit j.val = true)
  | .f j => i.val < j.val ∧ b.testBit j.val = true
  | .k j => i.val < j.val ∧ b.testBit j.val = true
  | _ => False

def highMemU (n b : ℕ) (m : Fin n) : V_bin n → Prop
  | .z j | .f j | .k j => m.val ≤ j.val ∧ b.testBit j.val = true
  | _ => False

def highMemF (n b : ℕ) (i : Fin n) : V_bin n → Prop
  | .z j | .f j | .k j => j = i ∨ (i.val < j.val ∧ b.testBit j.val = true)
  | _ => False

lemma uStillH0_succ_false_of_uStillH0_false (n b s : ℕ) (m : Fin n) (hm1 : m.val + 1 < n)
    (h : uStillH0 n b s m = false) :
    uStillH0 n b s ⟨m.val + 1, hm1⟩ = false := by
  unfold uStillH0 at h ⊢
  rw [decide_eq_false_iff_not] at h ⊢
  dsimp only
  intro hcond
  exact h ⟨hcond.1, by omega, by omega⟩

lemma uStillH0_succ_false_of_testBit_true (n b s : ℕ) (m : Fin n) (hm1 : m.val + 1 < n)
    (hbit : b.testBit m.val = true) :
    uStillH0 n b s ⟨m.val + 1, hm1⟩ = false := by
  unfold uStillH0
  rw [decide_eq_false_iff_not]
  dsimp only
  have hle := lowestOne0_le_of_testBit_true m.isLt hbit
  rintro ⟨_, hlt, _⟩
  omega

lemma uStillH0_succ_false_of_isBot0 (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hbot : isBot0 n b s i = true) (hi1 : i.val + 1 < n) :
    uStillH0 n b s ⟨i.val + 1, hi1⟩ = false := by
  rcases hvalid with ⟨_, hbn, _⟩
  unfold uStillH0 uLim0
  rw [decide_eq_false_iff_not]
  dsimp only
  rintro ⟨hb0, hlt_prev, hlt_lim⟩
  unfold isBot0 at hbot
  rw [Bool.or_eq_true, decide_eq_true_eq] at hbot
  rcases hbot with hbit | ⟨_, _, hs_ge⟩
  · have hle := lowestOne0_le_of_testBit_true i.isLt hbit
    omega
  · have hprev_lt := lowestOne0_lt hb0 hbn
    unfold S_close0 at hs_ge
    split_ifs at hlt_lim <;> omega

lemma mem_path_step_high (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (w u : V_bin n) (hw : w ≠ .x)
    (hprio : (G_bin n).priority w < (G_bin n).priority .c)
    (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s w ↔
      u ∈ predPath glob n b s (step (G_bin n) (predState0 glob n b s) (predTau0 n b s) w) := by
  rw [predPath, predVal, pred_path_step glob n b s hvalid w hw, Finset.mem_insert]
  have hne : u ≠ w := by intro heq; subst heq; omega
  simp [hne]

lemma highMem_z_and_u_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    ∀ k : ℕ,
      (∀ i : Fin n, n - i.val ≤ k →
        (∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false) →
        ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
          (u ∈ predPath glob n b s (.z i) ↔ highMemZ n b i u)) ∧
      (∀ m : Fin n, n - m.val ≤ k → 1 ≤ m.val →
        (b.testBit m.val = true ∨ hasHigherOne0 b n m.val = true) →
        uStillH0 n b s m = false →
        ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
          (u ∈ predPath glob n b s (.u m) ↔ highMemU n b m u))
  | 0 => ⟨fun i hk => by have := i.isLt; omega, fun m hk => by have := m.isLt; omega⟩
  | k + 1 => by
    rcases highMem_z_and_u_aux glob n b s hvalid k with ⟨ihZ, ihU⟩
    have hz : ∀ i : Fin n, n - i.val ≤ k + 1 →
        (∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false) →
        ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
          (u ∈ predPath glob n b s (.z i) ↔ highMemZ n b i u) := by
      intro i hk hstill u hu
      have hi := i.isLt
      rw [predPath, predVal, pred_path_step glob n b s hvalid (.z i) (by nofun), Finset.mem_insert]
      change u = .z i ∨ u ∈ predPath glob n b s (predState0 glob n b s (.z i)) ↔ highMemZ n b i u
      cases hhi : hasHigherOne0 b n i.val with
      | false =>
        have hce : chooseEdge1 glob n b s (.z i) = false := by
          dsimp [chooseEdge1]; rw [hhi, Bool.and_false]
        have hstep : predState0 glob n b s (.z i) = .x := by
          unfold predState0; rw [hce]; rfl
        rw [hstep, predPath, predVal, pred_path_x glob n b s hvalid]
        simp only [Finset.notMem_empty, or_false]
        have hall : ∀ j : Fin n, i.val < j.val → b.testBit j.val = false :=
          fun j hj => (hasHigherOne0_eq_false_iff b n i.val).mp hhi j.val hj j.isLt
        cases u with
        | z j =>
          dsimp [highMemZ]
          constructor
          · rintro ⟨rfl⟩; exact Or.inl rfl
          · rintro (rfl | ⟨hj, hbit⟩)
            · rfl
            · rw [hall j hj] at hbit; contradiction
        | f j | k j =>
          dsimp [highMemZ]
          simp only [reduceCtorEq, false_iff, not_and]
          intro hj; rw [hall j hj]; decide
        | _ =>
          dsimp [highMemZ]; simp
      | true =>
        have hi1 : i.val + 1 < n := lt_n_of_hasHigherOne0 hhi
        have hce : chooseEdge1 glob n b s (.z i) = true := by
          dsimp [chooseEdge1]; simp [hi1, hhi]
        have hstep : predState0 glob n b s (.z i) = .u ⟨i.val + 1, hi1⟩ := by
          unfold predState0; rw [if_pos hce]; dsimp [edge1]; rw [dif_pos hi1]
        rw [hstep]
        have hnext := (hasHigherOne0_succ_iff hi1).mp hhi
        have hmemU := ihU ⟨i.val + 1, hi1⟩ (by dsimp only; omega) (by dsimp only; omega) hnext (hstill hi1) u hu
        rw [hmemU]
        cases u with
        | z j =>
          dsimp [highMemU, highMemZ]
          constructor
          · rintro (h | ⟨hj, hbit⟩)
            · injection h with h'; subst h'; exact Or.inl rfl
            · exact Or.inr ⟨by omega, hbit⟩
          · rintro (rfl | ⟨hj, hbit⟩)
            · exact Or.inl rfl
            · exact Or.inr ⟨by omega, hbit⟩
        | f j | k j =>
          dsimp [highMemU, highMemZ]
          simp only [reduceCtorEq, false_or]
          exact ⟨fun ⟨hj, hbit⟩ => ⟨by omega, hbit⟩, fun ⟨hj, hbit⟩ => ⟨by omega, hbit⟩⟩
        | _ =>
          dsimp [highMemU, highMemZ]; simp
    refine ⟨hz, ?_⟩
    intro m hk hm1 hcond hstill u hu
    have hm := m.isLt
    have hp_u : (G_bin n).priority (.u m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    rw [mem_path_step_high glob n b s hvalid (.u m) u (by nofun) hp_u hu]
    have howner : (G_bin n).owner (.u m) = false := by
      dsimp [G_bin, owner_bin]; rw [if_neg (by omega)]
    have hstep_eq : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.u m) =
        predState0 glob n b s (.u m) := by
      unfold step; rw [if_pos howner]
    rw [hstep_eq]
    cases hbit : b.testBit m.val with
    | true =>
      have hce_u : chooseEdge1 glob n b s (.u m) = false := by
        dsimp [chooseEdge1]; split_ifs <;> simp_all
      have hpred_u : predState0 glob n b s (.u m) = .h m := by
        unfold predState0; rw [hce_u]; rfl
      rw [hpred_u]
      have hp_h : (G_bin n).priority (.h m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      have hp_hx : (G_bin n).priority (.hx m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      have hp_hy : (G_bin n).priority (.hy m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      have hp_g : (G_bin n).priority (.g m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      have hs_h : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h m) = .hx m := by
        unfold step G_bin owner_bin predState0; simp [chooseEdge1, hbit, edge0]
      have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx m) = .hy m := by
        unfold step G_bin owner_bin predState0; simp [chooseEdge1, hbit, edge0]
      have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy m) = .f m := by
        unfold step G_bin owner_bin predState0; simp [chooseEdge1, hbit, edge0]
      have hs_f : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f m) = .g m := rfl
      have hs_g : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g m) = .k m := by
        unfold step G_bin owner_bin predTau0; simp [chooseTauEdge1, hbit, edge1]
      have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k m) = .z m := rfl
      rw [mem_path_step_high glob n b s hvalid (.h m) u (by nofun) hp_h hu, hs_h,
          mem_path_step_high glob n b s hvalid (.hx m) u (by nofun) hp_hx hu, hs_hx,
          mem_path_step_high glob n b s hvalid (.hy m) u (by nofun) hp_hy hu, hs_hy]
      rw [predPath, predVal, pred_path_step glob n b s hvalid (.f m) (by nofun), hs_f, Finset.mem_insert]
      change u = .f m ∨ u ∈ predPath glob n b s (.g m) ↔ _
      rw [mem_path_step_high glob n b s hvalid (.g m) u (by nofun) hp_g hu, hs_g]
      rw [predPath, predVal, pred_path_step glob n b s hvalid (.k m) (by nofun), hs_k, Finset.mem_insert]
      change u = .f m ∨ u = .k m ∨ u ∈ predPath glob n b s (.z m) ↔ _
      have hstill_succ : ∀ hm1 : m.val + 1 < n, uStillH0 n b s ⟨m.val + 1, hm1⟩ = false :=
        fun hm1 => uStillH0_succ_false_of_testBit_true n b s m hm1 hbit
      rw [hz m hk hstill_succ u hu]
      cases u with
      | z j =>
        dsimp [highMemZ, highMemU]
        simp only [reduceCtorEq, false_or]
        constructor
        · rintro (rfl | ⟨hj, hbj⟩)
          · exact ⟨le_rfl, hbit⟩
          · exact ⟨by omega, hbj⟩
        · rintro ⟨hj, hbj⟩
          by_cases heq : j = m
          · exact Or.inl heq
          · exact Or.inr ⟨by omega, hbj⟩
      | f j =>
        dsimp [highMemZ, highMemU]
        simp only [reduceCtorEq, false_or]
        constructor
        · rintro (h | ⟨hj, hbj⟩)
          · injection h with h'; subst h'; exact ⟨le_rfl, hbit⟩
          · exact ⟨by omega, hbj⟩
        · rintro ⟨hj, hbj⟩
          by_cases heq : j = m
          · subst heq; exact Or.inl rfl
          · exact Or.inr ⟨by omega, hbj⟩
      | k j =>
        dsimp [highMemZ, highMemU]
        simp only [reduceCtorEq, false_or]
        constructor
        · rintro (h | ⟨hj, hbj⟩)
          · injection h with h'; subst h'; exact ⟨le_rfl, hbit⟩
          · exact ⟨by omega, hbj⟩
        · rintro ⟨hj, hbj⟩
          by_cases heq : j = m
          · subst heq; exact Or.inl rfl
          · exact Or.inr ⟨by omega, hbj⟩
      | _ =>
        dsimp [highMemZ, highMemU]; simp
    | false =>
      have hhi : hasHigherOne0 b n m.val = true := by
        rcases hcond with h1 | h2
        · rw [hbit] at h1; contradiction
        · exact h2
      have hm_succ : m.val + 1 < n := lt_n_of_hasHigherOne0 hhi
      have hce_u : chooseEdge1 glob n b s (.u m) = true := by
        dsimp [chooseEdge1]
        rw [if_neg (by omega), if_neg (by simp [hbit, hhi])]
        split_ifs with h3
        · rw [decide_eq_true_eq]
          unfold uStillH0 at hstill
          rw [decide_eq_false_iff_not] at hstill
          intro hlt
          exact hstill ⟨h3.1, h3.2, hlt⟩
        · rfl
      have hpred_u : predState0 glob n b s (.u m) = .u ⟨m.val + 1, hm_succ⟩ := by
        unfold predState0; rw [if_pos hce_u]; dsimp [edge1]; rw [dif_pos ⟨by omega, hm_succ⟩]
      rw [hpred_u]
      have hnext := (hasHigherOne0_succ_iff hm_succ).mp hhi
      have hstill_succ := uStillH0_succ_false_of_uStillH0_false n b s m hm_succ hstill
      rw [ihU ⟨m.val + 1, hm_succ⟩ (by dsimp only; omega) (by dsimp only; omega) hnext hstill_succ u hu]
      cases u with
      | z j | f j | k j =>
        dsimp [highMemU]
        constructor
        · rintro ⟨hj, hbj⟩; exact ⟨by omega, hbj⟩
        · rintro ⟨hj, hbj⟩
          have hne : j.val ≠ m.val := by intro heq; rw [heq, hbit] at hbj; contradiction
          exact ⟨by omega, hbj⟩
      | _ =>
        dsimp [highMemU]; rfl

lemma highMem_z (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hstill : ∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false)
    (u : V_bin n) (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s (.z i) ↔ highMemZ n b i u :=
  (highMem_z_and_u_aux glob n b s hvalid n).1 i (by omega) hstill u hu

lemma highMem_u (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (m : Fin n)
    (hm1 : 1 ≤ m.val) (hcond : b.testBit m.val = true ∨ hasHigherOne0 b n m.val = true)
    (hstill : uStillH0 n b s m = false)
    (u : V_bin n) (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s (.u m) ↔ highMemU n b m u :=
  (highMem_z_and_u_aux glob n b s hvalid n).2 m (by omega) hm1 hcond hstill u hu

lemma tau_true_of_isBot0 (n b s : ℕ) (i : Fin n) (hbot : isBot0 n b s i = true) :
    chooseTauEdge1 n b s (.g i) = true := by
  unfold isBot0 S_close0 at hbot
  dsimp [chooseTauEdge1]
  rcases Bool.or_eq_true_iff.mp hbot with hbit | h2
  · simp [hbit]
  · rw [decide_eq_true_eq] at h2
    rcases h2 with ⟨_, hik, hs⟩
    rw [← hik] at hs
    have hd : decide (3 * (n + 2 * i.val + 1) + 2 ≤ s) = true := decide_eq_true hs
    simp [hd]

lemma highMem_f_of_tau_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (htau : chooseTauEdge1 n b s (.g i) = true)
    (hstill : ∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false)
    (u : V_bin n) (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s (.f i) ↔ highMemF n b i u := by
  have hp_g : (G_bin n).priority (.g i) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
  have hs_f : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f i) = .g i := rfl
  have hs_g : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g i) = .k i := by
    unfold step G_bin owner_bin predTau0; rw [if_pos htau]; rfl
  have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k i) = .z i := rfl
  rw [predPath, predVal, pred_path_step glob n b s hvalid (.f i) (by nofun), hs_f, Finset.mem_insert]
  change u = .f i ∨ u ∈ predPath glob n b s (.g i) ↔ _
  rw [mem_path_step_high glob n b s hvalid (.g i) u (by nofun) hp_g hu, hs_g]
  rw [predPath, predVal, pred_path_step glob n b s hvalid (.k i) (by nofun), hs_k, Finset.mem_insert]
  change u = .f i ∨ u = .k i ∨ u ∈ predPath glob n b s (.z i) ↔ _
  rw [highMem_z glob n b s hvalid i hstill u hu]
  cases u with
  | z j =>
    dsimp [highMemZ, highMemF]
    simp
  | f j =>
    dsimp [highMemZ, highMemF]
    simp only [reduceCtorEq, false_or]
    exact ⟨fun h => h.elim (fun h' => by injection h' with h''; exact Or.inl h'') Or.inr,
           fun h => h.elim (fun h' => Or.inl (by subst h'; rfl)) Or.inr⟩
  | k j =>
    dsimp [highMemZ, highMemF]
    simp only [reduceCtorEq, false_or]
    exact ⟨fun h => h.elim (fun h' => by injection h' with h''; exact Or.inl h'') Or.inr,
           fun h => h.elim (fun h' => Or.inl (by subst h'; rfl)) Or.inr⟩
  | _ =>
    dsimp [highMemZ, highMemF]; simp

lemma highMem_f_of_isBot0 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hbot : isBot0 n b s i = true)
    (u : V_bin n) (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s (.f i) ↔ highMemF n b i u :=
  highMem_f_of_tau_true glob n b s hvalid i
    (tau_true_of_isBot0 n b s i hbot)
    (uStillH0_succ_false_of_isBot0 n b s hvalid i hbot)
    u hu

lemma rTarg0_lt_of_rActive0' (n b s : ℕ) (hbn : b < 2 ^ n) (hact : rActive0 n b s = true) :
    rTarg0 n b s < n := by
  unfold rActive0 at hact; rw [decide_eq_true_eq] at hact
  unfold rTarg0
  split_ifs with h2
  · exact lowestZero0_lt h2.1
  · rcases hact with hb0 | h2'
    · exact lowestOne0_lt hb0 hbn
    · exact False.elim (h2 h2')

lemma sTarg0_lt_of_sActive0' (n b s : ℕ) (hbn : b < 2 ^ n) (hact : sActive0 n b s = true) :
    sTarg0 n b s < n := by
  unfold sActive0 at hact; rw [decide_eq_true_eq] at hact
  unfold sTarg0
  split_ifs with h2
  · exact lowestZero0_lt h2.1
  · rcases hact with hb0 | h2'
    · exact lowestOne0_lt hb0 hbn
    · exact False.elim (h2 h2')

lemma isBot0_rTarg0 (n b s : ℕ) (hbn : b < 2 ^ n) (hact : rActive0 n b s = true) :
    isBot0 n b s ⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hbn hact⟩ = true := by
  unfold rActive0 at hact; rw [decide_eq_true_eq] at hact
  unfold isBot0 rTarg0
  rw [Bool.or_eq_true, decide_eq_true_eq]
  dsimp only
  split_ifs with h2
  · exact Or.inr ⟨h2.1, rfl, by omega⟩
  · rcases hact with hb0 | h2'
    · exact Or.inl (testBit_lowestOne0 hb0 hbn)
    · exact False.elim (h2 h2')

lemma isBot0_sTarg0 (n b s : ℕ) (hbn : b < 2 ^ n) (hact : sActive0 n b s = true) :
    isBot0 n b s ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hbn hact⟩ = true := by
  unfold sActive0 at hact; rw [decide_eq_true_eq] at hact
  unfold isBot0 sTarg0
  rw [Bool.or_eq_true, decide_eq_true_eq]
  dsimp only
  split_ifs with h2
  · exact Or.inr ⟨h2.1, rfl, by omega⟩
  · rcases hact with hb0 | h2'
    · exact Or.inl (testBit_lowestOne0 hb0 hbn)
    · exact False.elim (h2 h2')

lemma step_rp_of_eq_rTarg0 (glob : Bool) (n b s : ℕ) (m : Fin n)
    (hact : rActive0 n b s = true) (heq : m.val = rTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.rp m) = .f m := by
  change predState0 glob n b s (.rp m) = .f m
  by_cases hm0 : m.val = 0
  · unfold predState0
    have hce : chooseEdge1 glob n b s (.rp m) = true := by dsimp [chooseEdge1]; rw [if_pos hm0]
    rw [if_pos hce]
    simp [edge1, hm0]
  · have hce : chooseEdge1 glob n b s (.rp m) = false := by
      dsimp [chooseEdge1]
      rw [if_neg hm0]
      unfold rActive0 at hact; rw [decide_eq_true_eq] at hact
      unfold rTarg0 at heq
      split_ifs with h2
      · rw [if_pos h2] at heq; simp [heq]
      · rw [if_neg h2] at heq
        have hb0 : 0 < b := hact.resolve_right h2
        simp [hb0, heq]
    unfold predState0; rw [hce]; rfl

lemma step_rp_of_ne_rTarg0 (glob : Bool) (n b s : ℕ) (m : Fin n)
    (hm0 : m.val ≠ 0) (hne : m.val ≠ rTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.rp m) =
      .rp ⟨m.val - 1, by have := m.isLt; omega⟩ := by
  change predState0 glob n b s (.rp m) = _
  have hce : chooseEdge1 glob n b s (.rp m) = true := by
    dsimp [chooseEdge1]
    rw [if_neg hm0]
    unfold rTarg0 at hne
    split_ifs with h2
    · rw [if_pos h2] at hne; exact decide_eq_true hne
    · rw [if_neg h2] at hne; rw [decide_eq_true_eq]; rintro ⟨_, h⟩; exact hne h
  unfold predState0; rw [if_pos hce]; simp [edge1, hm0]

lemma highMem_rp_of_ge (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : rActive0 n b s = true) :
    ∀ k (m : Fin n), m.val - rTarg0 n b s ≤ k → rTarg0 n b s ≤ m.val →
      ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
        (u ∈ predPath glob n b s (.rp m) ↔
          highMemF n b ⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hvalid.2.1 hact⟩ u)
  | 0, m, hk, hge, u, hu => by
    have heq : m.val = rTarg0 n b s := by omega
    have hp_rp : (G_bin n).priority (.rp m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    rw [mem_path_step_high glob n b s hvalid (.rp m) u (by nofun) hp_rp hu,
        step_rp_of_eq_rTarg0 glob n b s m hact heq]
    have hm_eq : m = ⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hvalid.2.1 hact⟩ := Fin.ext heq
    rw [hm_eq]
    exact highMem_f_of_isBot0 glob n b s hvalid _ (isBot0_rTarg0 n b s hvalid.2.1 hact) u hu
  | k + 1, m, hk, hge, u, hu => by
    by_cases heq : m.val = rTarg0 n b s
    · exact highMem_rp_of_ge glob n b s hvalid hact 0 m (by omega) hge u hu
    · have hm0 : m.val ≠ 0 := by omega
      have hp_rp : (G_bin n).priority (.rp m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      rw [mem_path_step_high glob n b s hvalid (.rp m) u (by nofun) hp_rp hu,
          step_rp_of_ne_rTarg0 glob n b s m hm0 heq]
      exact highMem_rp_of_ge glob n b s hvalid hact k ⟨m.val - 1, by have := m.isLt; omega⟩
        (by dsimp only; omega) (by dsimp only; omega) u hu

lemma highMem_r_of_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : rActive0 n b s = false) (u : V_bin n) :
    u ∈ predPath glob n b s .r ↔ u = .r := by
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .r = .x := by
    unfold step G_bin owner_bin predState0 chooseEdge1; rw [if_pos rfl, hact]; rfl
  rw [predPath, predVal, pred_path_step glob n b s hvalid .r (by nofun), hstep,
      pred_path_x glob n b s hvalid]
  simp

lemma highMem_r_of_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : rActive0 n b s = true) (u : V_bin n)
    (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s .r ↔
      u = .r ∨ highMemF n b ⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hvalid.2.1 hact⟩ u := by
  have hn := hvalid.1
  have ht := rTarg0_lt_of_rActive0' n b s hvalid.2.1 hact
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .r = .rp ⟨n - 1, by omega⟩ := by
    unfold step G_bin owner_bin predState0 chooseEdge1
    rw [if_pos rfl, if_pos hact]
    dsimp [edge1]; rw [dif_pos hn]
  rw [predPath, predVal, pred_path_step glob n b s hvalid .r (by nofun), hstep, Finset.mem_insert]
  change u = .r ∨ u ∈ predPath glob n b s (.rp ⟨n - 1, by omega⟩) ↔ _
  rw [highMem_rp_of_ge glob n b s hvalid hact n ⟨n - 1, by omega⟩ (by dsimp only; omega) (by dsimp only; omega) u hu]

lemma step_sp_of_eq_sTarg0 (glob : Bool) (n b s : ℕ) (m : Fin n)
    (hact : sActive0 n b s = true) (heq : m.val = sTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.sp m) = .hx m := by
  change predState0 glob n b s (.sp m) = .hx m
  by_cases hm0 : m.val = 0
  · unfold predState0
    have hce : chooseEdge1 glob n b s (.sp m) = true := by dsimp [chooseEdge1]; rw [if_pos hm0]
    rw [if_pos hce]
    simp [edge1, hm0]
  · have hce : chooseEdge1 glob n b s (.sp m) = false := by
      dsimp [chooseEdge1]
      rw [if_neg hm0]
      unfold sActive0 at hact; rw [decide_eq_true_eq] at hact
      unfold sTarg0 at heq
      split_ifs with h2
      · rw [if_pos h2] at heq; simp [heq]
      · rw [if_neg h2] at heq
        have hb0 : 0 < b := hact.resolve_right h2
        simp [hb0, heq]
    unfold predState0; rw [hce]; rfl

lemma step_sp_of_ne_sTarg0 (glob : Bool) (n b s : ℕ) (m : Fin n)
    (hm0 : m.val ≠ 0) (hne : m.val ≠ sTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.sp m) =
      .sp ⟨m.val - 1, by have := m.isLt; omega⟩ := by
  change predState0 glob n b s (.sp m) = _
  have hce : chooseEdge1 glob n b s (.sp m) = true := by
    dsimp [chooseEdge1]
    rw [if_neg hm0]
    unfold sTarg0 at hne
    split_ifs with h2
    · rw [if_pos h2] at hne; exact decide_eq_true hne
    · rw [if_neg h2] at hne; rw [decide_eq_true_eq]; rintro ⟨_, h⟩; exact hne h
  unfold predState0; rw [if_pos hce]; simp [edge1, hm0]

lemma step_hx_of_eq_sTarg0 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (m : Fin n)
    (hact : sActive0 n b s = true) (heq : m.val = sTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx m) = .hy m := by
  change predState0 glob n b s (.hx m) = .hy m
  unfold sActive0 at hact; rw [decide_eq_true_eq] at hact
  unfold sTarg0 at heq
  have hce : chooseEdge1 glob n b s (.hx m) = false := by
    dsimp [chooseEdge1]
    split_ifs with hbit hlim hzero
    · rfl
    · exfalso
      rcases hlim with ⟨hb0, hlt_kp, hlt_hy⟩
      split_ifs at heq with h2
      · have hkp := lowestOne0_lt hb0 hvalid.2.1
        have hs_ge := h2.2
        unfold S_close0 at hs_ge
        unfold hyLim0 at hlt_hy
        split_ifs at hlt_hy <;> omega
      · omega
    · split_ifs at heq with h2
      · rw [decide_eq_false_iff_not]; omega
      · exfalso
        have hb0 : 0 < b := hact.resolve_right h2
        rw [heq, testBit_lowestOne0 hb0 hvalid.2.1] at hbit
        contradiction
    · exfalso
      split_ifs at heq with h2
      · exact hzero ⟨h2.1, heq⟩
      · have hb0 : 0 < b := hact.resolve_right h2
        rw [heq, testBit_lowestOne0 hb0 hvalid.2.1] at hbit
        contradiction
  unfold predState0; rw [hce]; rfl

lemma step_hy_of_eq_sTarg0 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (m : Fin n)
    (hact : sActive0 n b s = true) (heq : m.val = sTarg0 n b s) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy m) = .f m := by
  change predState0 glob n b s (.hy m) = .f m
  unfold sActive0 at hact; rw [decide_eq_true_eq] at hact
  unfold sTarg0 at heq
  have hce : chooseEdge1 glob n b s (.hy m) = false := by
    dsimp [chooseEdge1]
    split_ifs with hbit hlim hzero
    · rfl
    · exfalso
      rcases hlim with ⟨hb0, hlt_kp, hlt_hy⟩
      split_ifs at heq with h2
      · have hkp := lowestOne0_lt hb0 hvalid.2.1
        have hs_ge := h2.2
        unfold S_close0 at hs_ge
        unfold hyLim0 at hlt_hy
        split_ifs at hlt_hy <;> omega
      · omega
    · split_ifs at heq with h2
      · rw [decide_eq_false_iff_not]; omega
      · exfalso
        have hb0 : 0 < b := hact.resolve_right h2
        rw [heq, testBit_lowestOne0 hb0 hvalid.2.1] at hbit
        contradiction
    · exfalso
      split_ifs at heq with h2
      · exact hzero ⟨h2.1, heq⟩
      · have hb0 : 0 < b := hact.resolve_right h2
        rw [heq, testBit_lowestOne0 hb0 hvalid.2.1] at hbit
        contradiction
  unfold predState0; rw [hce]; rfl

lemma highMem_sp_of_ge (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : sActive0 n b s = true) :
    ∀ k (m : Fin n), m.val - sTarg0 n b s ≤ k → sTarg0 n b s ≤ m.val →
      ∀ u, (G_bin n).priority .c ≤ (G_bin n).priority u →
        (u ∈ predPath glob n b s (.sp m) ↔
          highMemF n b ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hact⟩ u)
  | 0, m, hk, hge, u, hu => by
    have heq : m.val = sTarg0 n b s := by omega
    have hp_sp : (G_bin n).priority (.sp m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    have hp_hx : (G_bin n).priority (.hx m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    have hp_hy : (G_bin n).priority (.hy m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    rw [mem_path_step_high glob n b s hvalid (.sp m) u (by nofun) hp_sp hu,
        step_sp_of_eq_sTarg0 glob n b s m hact heq,
        mem_path_step_high glob n b s hvalid (.hx m) u (by nofun) hp_hx hu,
        step_hx_of_eq_sTarg0 glob n b s hvalid m hact heq,
        mem_path_step_high glob n b s hvalid (.hy m) u (by nofun) hp_hy hu,
        step_hy_of_eq_sTarg0 glob n b s hvalid m hact heq]
    have hm_eq : m = ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hact⟩ := Fin.ext heq
    rw [hm_eq]
    exact highMem_f_of_isBot0 glob n b s hvalid _ (isBot0_sTarg0 n b s hvalid.2.1 hact) u hu
  | k + 1, m, hk, hge, u, hu => by
    by_cases heq : m.val = sTarg0 n b s
    · exact highMem_sp_of_ge glob n b s hvalid hact 0 m (by omega) hge u hu
    · have hm0 : m.val ≠ 0 := by omega
      have hp_sp : (G_bin n).priority (.sp m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      rw [mem_path_step_high glob n b s hvalid (.sp m) u (by nofun) hp_sp hu,
          step_sp_of_ne_sTarg0 glob n b s m hm0 heq]
      exact highMem_sp_of_ge glob n b s hvalid hact k ⟨m.val - 1, by have := m.isLt; omega⟩
        (by dsimp only; omega) (by dsimp only; omega) u hu

lemma highMem_s_of_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : sActive0 n b s = false) (u : V_bin n) :
    u ∈ predPath glob n b s .s ↔ u = .s := by
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .s = .x := by
    unfold step G_bin owner_bin predState0 chooseEdge1; rw [if_pos rfl, hact]; rfl
  rw [predPath, predVal, pred_path_step glob n b s hvalid .s (by nofun), hstep,
      pred_path_x glob n b s hvalid]
  simp

lemma highMem_s_of_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : sActive0 n b s = true) (u : V_bin n)
    (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s .s ↔
      u = .s ∨ highMemF n b ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hact⟩ u := by
  have hn := hvalid.1
  have ht := sTarg0_lt_of_sActive0' n b s hvalid.2.1 hact
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .s = .sp ⟨n - 1, by omega⟩ := by
    unfold step G_bin owner_bin predState0 chooseEdge1
    rw [if_pos rfl, if_pos hact]
    dsimp [edge1]; rw [dif_pos hn]
  rw [predPath, predVal, pred_path_step glob n b s hvalid .s (by nofun), hstep, Finset.mem_insert]
  change u = .s ∨ u ∈ predPath glob n b s (.sp ⟨n - 1, by omega⟩) ↔ _
  rw [highMem_sp_of_ge glob n b s hvalid hact n ⟨n - 1, by omega⟩ (by dsimp only; omega) (by dsimp only; omega) u hu]

lemma highMem_c_of_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : sActive0 n b s = false) (u : V_bin n) :
    u ∈ predPath glob n b s .c ↔ u = .c ∨ u = .s := by
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .c = .s := rfl
  rw [predPath, predVal, pred_path_step glob n b s hvalid .c (by nofun), hstep, Finset.mem_insert]
  change u = .c ∨ u ∈ predPath glob n b s .s ↔ _
  rw [highMem_s_of_false glob n b s hvalid hact u]

lemma highMem_c_of_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hact : sActive0 n b s = true) (u : V_bin n)
    (hu : (G_bin n).priority .c ≤ (G_bin n).priority u) :
    u ∈ predPath glob n b s .c ↔
      u = .c ∨ u = .s ∨ highMemF n b ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hact⟩ u := by
  have hstep : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .c = .s := rfl
  rw [predPath, predVal, pred_path_step glob n b s hvalid .c (by nofun), hstep, Finset.mem_insert]
  change u = .c ∨ u ∈ predPath glob n b s .s ↔ _
  rw [highMem_s_of_true glob n b s hvalid hact u hu]

lemma highMemF_lowestOne0_iff (n b : ℕ) (hb0 : 0 < b) (hbn : b < 2 ^ n) (j : Fin n) :
    (j = ⟨lowestOne0 b n, lowestOne0_lt hb0 hbn⟩ ∨
      (lowestOne0 b n < j.val ∧ b.testBit j.val = true)) ↔
      b.testBit j.val = true := by
  constructor
  · rintro (rfl | ⟨_, hbit⟩)
    · exact testBit_lowestOne0 hb0 hbn
    · exact hbit
  · intro hbit
    have hle := lowestOne0_le_of_testBit_true j.isLt hbit
    by_cases heq : j.val = lowestOne0 b n
    · left; exact Fin.ext heq
    · right; exact ⟨by omega, hbit⟩

theorem portalOrderProp_holds (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    PortalOrderProp glob n b s := by
  rcases hvalid with ⟨hn, hbn, hs_max⟩
  have hvalid' : ValidState n b s := ⟨hn, hbn, hs_max⟩
  unfold PortalOrderProp
  split_ifs with hbranch
  · intro w₁ w₂ hc hr
    rcases hbranch with ⟨hb_lt, hs12⟩
    have hk : lowestZero0 b n < n := lowestZero0_lt hb_lt
    let kFin : Fin n := ⟨lowestZero0 b n, hk⟩
    have hract : rActive0 n b s = true := by
      unfold rActive0; rw [decide_eq_true_eq]; right; exact ⟨hb_lt, by omega⟩
    have hrtarg : rTarg0 n b s = lowestZero0 b n := by
      unfold rTarg0; rw [if_pos ⟨hb_lt, by omega⟩]
    have hp_k : (G_bin n).priority .c ≤ (G_bin n).priority (.k kFin) := by
      dsimp [G_bin, priority_bin]; omega
    apply predVal_lt_of_setLT glob n b s hvalid'
    apply setLT_of_top_diff_even (G_bin_priority_injective n hn) (d := .k kFin)
    · rw [hc.2 (.k kFin) hp_k]
      cases hsact : sActive0 n b s with
      | false =>
        rw [highMem_c_of_false glob n b s hvalid' hsact]
        simp
      | true =>
        rw [highMem_c_of_true glob n b s hvalid' hsact (.k kFin) hp_k]
        have hb0 : 0 < b := by
          unfold sActive0 at hsact; rw [decide_eq_true_eq] at hsact
          rcases hsact with h | h; exact h; omega
        have hstarg : sTarg0 n b s = lowestOne0 b n := by
          unfold sTarg0; rw [if_neg (by omega)]
        simp only [reduceCtorEq, false_or, highMemF]
        rw [Fin.ext_iff]
        dsimp only [kFin]
        rw [hstarg]
        have hbit_k : b.testBit (lowestZero0 b n) = false := testBit_lowestZero0 hb_lt
        have hbit_kp : b.testBit (lowestOne0 b n) = true := testBit_lowestOne0 hb0 hbn
        rintro (heq | ⟨_, htrue⟩)
        · rw [heq, hbit_kp] at hbit_k; contradiction
        · rw [hbit_k] at htrue; contradiction
    · rw [hr.2 (.k kFin) hp_k, highMem_r_of_true glob n b s hvalid' hract (.k kFin) hp_k]
      right
      dsimp [highMemF, kFin]
      left
      exact Fin.ext hrtarg.symm
    · exact prio_k_even n kFin
    · intro u hu
      have hp_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by omega
      rw [hc.2 u hp_u, hr.2 u hp_u, highMem_r_of_true glob n b s hvalid' hract u hp_u]
      have hu_gt_s : (G_bin n).priority .s < (G_bin n).priority u := by
        dsimp [G_bin, priority_bin] at hu ⊢; omega
      rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨j, rfl | rfl | rfl⟩
      all_goals
        have hkj : lowestZero0 b n < j.val := by
          dsimp [G_bin, priority_bin, kFin] at hu; omega
        cases hsact : sActive0 n b s with
        | false =>
          have hb0 : b = 0 := by
            unfold sActive0 at hsact; rw [decide_eq_false_iff_not] at hsact; omega
          subst hb0
          rw [highMem_c_of_false glob n 0 s hvalid' hsact]
          simp only [reduceCtorEq, false_or, highMemF, Fin.ext_iff, hrtarg, Nat.zero_testBit, and_false, or_false]
          exact ⟨False.elim, fun h => by omega⟩
        | true =>
          have hb0 : 0 < b := by
            unfold sActive0 at hsact; rw [decide_eq_true_eq] at hsact
            rcases hsact with h | h; exact h; omega
          have hstarg : ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hbn hsact⟩ =
              (⟨lowestOne0 b n, lowestOne0_lt hb0 hbn⟩ : Fin n) := by
            apply Fin.ext
            dsimp only
            unfold sTarg0
            rw [if_neg (by omega)]
          rw [highMem_c_of_true glob n b s hvalid' hsact _ hp_u, hstarg]
          simp only [reduceCtorEq, false_or, highMemF]
          rw [highMemF_lowestOne0_iff n b hb0 hbn j]
          simp only [Fin.ext_iff, hrtarg]
          exact ⟨fun h => Or.inr ⟨hkj, h⟩, fun h => h.elim (by omega) And.right⟩
  · intro w₁ w₂ hr hc
    have hact_eq : rActive0 n b s = sActive0 n b s := by
      unfold rActive0 sActive0
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      omega
    have htarg_eq : rTarg0 n b s = sTarg0 n b s := by
      unfold rTarg0 sTarg0
      split_ifs <;> omega
    have hp_s : (G_bin n).priority .c ≤ (G_bin n).priority .s := by
      dsimp [G_bin, priority_bin]; omega
    apply predVal_lt_of_setLT glob n b s hvalid'
    apply setLT_of_top_diff_even (G_bin_priority_injective n hn) (d := .s)
    · rw [hr.2 .s hp_s]
      cases hract : rActive0 n b s with
      | false => rw [highMem_r_of_false glob n b s hvalid' hract]; nofun
      | true => rw [highMem_r_of_true glob n b s hvalid' hract .s hp_s]; simp [highMemF]
    · rw [hc.2 .s hp_s]
      cases hsact : sActive0 n b s with
      | false => rw [highMem_c_of_false glob n b s hvalid' hsact]; exact Or.inr rfl
      | true => rw [highMem_c_of_true glob n b s hvalid' hsact .s hp_s]; exact Or.inr (Or.inl rfl)
    · exact prio_s_even n
    · intro u hu
      have hp_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by omega
      have hne_c : u ≠ .c := by intro h; subst h; dsimp [G_bin, priority_bin] at hu; omega
      have hne_r : u ≠ .r := by intro h; subst h; dsimp [G_bin, priority_bin] at hu; omega
      have hne_s : u ≠ .s := by intro h; subst h; omega
      rw [hr.2 u hp_u, hc.2 u hp_u]
      cases hract : rActive0 n b s with
      | false =>
        have hsact : sActive0 n b s = false := hact_eq.symm.trans hract
        rw [highMem_r_of_false glob n b s hvalid' hract,
            highMem_c_of_false glob n b s hvalid' hsact]
        simp [hne_r, hne_c, hne_s]
      | true =>
        have hsact : sActive0 n b s = true := hact_eq.symm.trans hract
        rw [highMem_r_of_true glob n b s hvalid' hract u hp_u,
            highMem_c_of_true glob n b s hvalid' hsact u hp_u]
        have hfin_eq : (⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hbn hract⟩ : Fin n) =
            ⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hbn hsact⟩ := Fin.ext htarg_eq
        rw [hfin_eq]
        simp [hne_r, hne_c, hne_s]

/-! ### Part 3: Binary Increment Lemmas for `b + 1` at `s = S_close0 n b + 3` -/

lemma testBit_add_one_aux :
    ∀ (k b : ℕ), (∀ i < k, b.testBit i = true) → b.testBit k = false →
      (∀ i < k, (b + 1).testBit i = false) ∧
      (b + 1).testBit k = true ∧
      (∀ i, k < i → (b + 1).testBit i = b.testBit i)
  | 0, b, _, h0 => by
    rw [testBit_zero_eq, decide_eq_false_iff_not] at h0
    have hdiv : (b + 1) / 2 = b / 2 := by omega
    refine ⟨fun i hi => by omega, ?_, ?_⟩
    · rw [testBit_zero_eq, decide_eq_true_eq]; omega
    · intro i hi
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0) with ⟨j, rfl⟩
      rw [Nat.testBit_succ, Nat.testBit_succ, hdiv]
  | k + 1, b, h1, h0 => by
    have hb0 : b.testBit 0 = true := h1 0 (Nat.zero_lt_succ k)
    rw [testBit_zero_eq, decide_eq_true_eq] at hb0
    have hdiv : (b + 1) / 2 = b / 2 + 1 := by omega
    have h1' : ∀ i < k, (b / 2).testBit i = true := by
      intro i hi
      have h := h1 (i + 1) (Nat.succ_lt_succ hi)
      rwa [Nat.testBit_succ] at h
    have h0' : (b / 2).testBit k = false := by
      rwa [Nat.testBit_succ] at h0
    rcases testBit_add_one_aux k (b / 2) h1' h0' with ⟨ih_lt, ih_eq, ih_gt⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rcases i with _ | j
      · rw [testBit_zero_eq, decide_eq_false_iff_not]; omega
      · rw [Nat.testBit_succ, hdiv]
        exact ih_lt j (by omega)
    · rw [Nat.testBit_succ, hdiv]
      exact ih_eq
    · intro i hi
      rcases i with _ | j
      · omega
      · rw [Nat.testBit_succ, Nat.testBit_succ, hdiv]
        exact ih_gt j (by omega)

lemma testBit_add_one_of_lt_lowestZero0 {n b i : ℕ} (hb : b < 2 ^ n - 1)
    (hi : i < lowestZero0 b n) :
    (b + 1).testBit i = false :=
  (testBit_add_one_aux (lowestZero0 b n) b
    (fun _ hj => testBit_of_lt_lowestZero0 hb hj)
    (testBit_lowestZero0 hb)).1 i hi

lemma testBit_add_one_lowestZero0 {n b : ℕ} (hb : b < 2 ^ n - 1) :
    (b + 1).testBit (lowestZero0 b n) = true :=
  (testBit_add_one_aux (lowestZero0 b n) b
    (fun _ hj => testBit_of_lt_lowestZero0 hb hj)
    (testBit_lowestZero0 hb)).2.1

lemma testBit_add_one_of_gt_lowestZero0 {n b i : ℕ} (hb : b < 2 ^ n - 1)
    (hi : lowestZero0 b n < i) :
    (b + 1).testBit i = b.testBit i :=
  (testBit_add_one_aux (lowestZero0 b n) b
    (fun _ hj => testBit_of_lt_lowestZero0 hb hj)
    (testBit_lowestZero0 hb)).2.2 i hi

lemma lowestOne0_add_one {n b : ℕ} (hb : b < 2 ^ n - 1) :
    lowestOne0 (b + 1) n = lowestZero0 b n := by
  have hk := lowestZero0_lt hb
  have hle : lowestOne0 (b + 1) n ≤ lowestZero0 b n :=
    lowestOne0_le_of_testBit_true hk (testBit_add_one_lowestZero0 hb)
  have hbn1 : b + 1 < 2 ^ n := by omega
  have hbit := testBit_lowestOne0 (by omega : 0 < b + 1) hbn1
  by_contra hne
  have hlt : lowestOne0 (b + 1) n < lowestZero0 b n := by omega
  have hfalse := testBit_add_one_of_lt_lowestZero0 hb hlt
  rw [hbit] at hfalse
  contradiction

lemma hasHigherOne0_add_one_of_lt {n b i : ℕ} (hb : b < 2 ^ n - 1)
    (hi : i < lowestZero0 b n) :
    hasHigherOne0 (b + 1) n i = true := by
  rw [hasHigherOne0_iff]
  exact ⟨lowestZero0 b n, hi, lowestZero0_lt hb, testBit_add_one_lowestZero0 hb⟩

lemma hasHigherOne0_add_one_of_ge {n b i : ℕ} (hb : b < 2 ^ n - 1)
    (hi : lowestZero0 b n ≤ i) :
    hasHigherOne0 (b + 1) n i = hasHigherOne0 b n i := by
  rw [Bool.eq_iff_iff, hasHigherOne0_iff, hasHigherOne0_iff]
  constructor
  · rintro ⟨j, hij, hjn, hbit⟩
    rw [testBit_add_one_of_gt_lowestZero0 hb (by omega)] at hbit
    exact ⟨j, hij, hjn, hbit⟩
  · rintro ⟨j, hij, hjn, hbit⟩
    rw [← testBit_add_one_of_gt_lowestZero0 hb (by omega)] at hbit
    exact ⟨j, hij, hjn, hbit⟩

lemma eq_two_pow_iff_all_testBit_false :
    ∀ (n k x : ℕ), k < n → x < 2 ^ n →
      (∀ i < k, x.testBit i = false) → x.testBit k = true →
      (x = 2 ^ k ↔ ∀ j, k < j → j < n → x.testBit j = false)
  | 0, k, x, hkn, _, _, _ => by omega
  | n + 1, 0, x, _, hxn, _, hx0 => by
    rw [testBit_zero_eq, decide_eq_true_eq] at hx0
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    simp only [pow_zero]
    constructor
    · rintro rfl j hj _
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0) with ⟨m, rfl⟩
      rw [Nat.testBit_succ]
      exact Nat.zero_testBit m
    · intro hall
      by_contra hne
      have hdiv0 : 0 < x / 2 := by omega
      have hdivn : x / 2 < 2 ^ n := by omega
      rcases exists_testBit_true_of_pos_of_lt_two_pow n (x / 2) hdiv0 hdivn with ⟨m, hmn, hbit⟩
      have hfalse := hall (m + 1) (by omega) (by omega)
      rw [Nat.testBit_succ, hbit] at hfalse
      contradiction
  | n + 1, k + 1, x, hkn, hxn, hlt, hxk => by
    have hx0 : x.testBit 0 = false := hlt 0 (Nat.zero_lt_succ k)
    rw [testBit_zero_eq, decide_eq_false_iff_not] at hx0
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    have hpow_k : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hlt' : ∀ i < k, (x / 2).testBit i = false := by
      intro i hi
      have h := hlt (i + 1) (Nat.succ_lt_succ hi)
      rwa [Nat.testBit_succ] at h
    have hxk' : (x / 2).testBit k = true := by
      rwa [Nat.testBit_succ] at hxk
    have ih := eq_two_pow_iff_all_testBit_false n k (x / 2) (by omega) (by omega) hlt' hxk'
    constructor
    · intro hx j hj hjn
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0) with ⟨m, rfl⟩
      rw [Nat.testBit_succ]
      exact ih.mp (by omega) m (by omega) (by omega)
    · intro hall
      have hdiv_eq : x / 2 = 2 ^ k := by
        apply ih.mpr
        intro m hm hmn
        have h := hall (m + 1) (by omega) (by omega)
        rwa [Nat.testBit_succ] at h
      omega

lemma topFlip0_add_one {n b : ℕ} (hb : b < 2 ^ n - 1) :
    topFlip0 (b + 1) n = !hasHigherOne0 b n (lowestZero0 b n) := by
  unfold topFlip0
  rw [lowestOne0_add_one hb]
  have hk := lowestZero0_lt hb
  have hbn1 : b + 1 < 2 ^ n := by omega
  have hiff := eq_two_pow_iff_all_testBit_false n (lowestZero0 b n) (b + 1) hk hbn1
    (fun _ hi => testBit_add_one_of_lt_lowestZero0 hb hi)
    (testBit_add_one_lowestZero0 hb)
  cases hhi : hasHigherOne0 b n (lowestZero0 b n) with
  | true =>
    simp only [Bool.not_true, decide_eq_false_iff_not, not_and]
    intro _ heq
    rcases (hasHigherOne0_iff b n (lowestZero0 b n)).mp hhi with ⟨j, hkj, hjn, hbit⟩
    have hfalse := hiff.mp heq j hkj hjn
    rw [testBit_add_one_of_gt_lowestZero0 hb hkj, hbit] at hfalse
    contradiction
  | false =>
    simp only [Bool.not_false, decide_eq_true_eq]
    refine ⟨by omega, hiff.mpr ?_⟩
    intro j hkj hjn
    rw [testBit_add_one_of_gt_lowestZero0 hb hkj]
    exact (hasHigherOne0_eq_false_iff b n (lowestZero0 b n)).mp hhi j hkj hjn

/-! ### Part 4: Portal Membership, `uStillH0 = true` Chain, `predTau0_optimal`, and `hy / hx / h` -/

lemma mem_portal_zfk_iff_testBit (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    {w : V_bin n} (hport : HitsPortal glob n b s w .c ∨ HitsPortal glob n b s w .r)
    (j : Fin n) (hj : b < 2 ^ n - 1 → S_close0 n b + 1 ≤ s → lowestZero0 b n < j.val)
    (u : V_bin n) (hu : u = .z j ∨ u = .f j ∨ u = .k j) :
    u ∈ predPath glob n b s w ↔ b.testBit j.val = true := by
  rcases hvalid with ⟨hn, hbn, hs_max⟩
  have hvalid' : ValidState n b s := ⟨hn, hbn, hs_max⟩
  have hp_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by
    rcases hu with rfl | rfl | rfl <;> { dsimp [G_bin, priority_bin]; omega }
  have hne_c : u ≠ .c := by rcases hu with rfl | rfl | rfl <;> nofun
  have hne_r : u ≠ .r := by rcases hu with rfl | rfl | rfl <;> nofun
  have hne_s : u ≠ .s := by rcases hu with rfl | rfl | rfl <;> nofun
  have hF_iff : ∀ (t : Fin n),
      (t.val = lowestOne0 b n ∧ 0 < b) ∨ (t.val = lowestZero0 b n ∧ lowestZero0 b n < j.val) →
      (highMemF n b t u ↔ b.testBit j.val = true) := by
    intro t ht_cond
    rcases hu with rfl | rfl | rfl <;>
    { dsimp [highMemF]
      rcases ht_cond with ⟨ht_eq, hb0⟩ | ⟨ht_eq, hlt⟩
      · have hfin : t = ⟨lowestOne0 b n, lowestOne0_lt hb0 hbn⟩ := Fin.ext ht_eq
        rw [hfin]
        exact highMemF_lowestOne0_iff n b hb0 hbn j
      · rw [Fin.ext_iff, ht_eq]
        exact ⟨fun h => h.elim (by omega) And.right, fun h => Or.inr ⟨hlt, h⟩⟩ }
  rcases hport with hc | hr
  · rw [hc.2 u hp_u]
    cases hsact : sActive0 n b s with
    | false =>
      have hb0 : b = 0 := by
        unfold sActive0 at hsact; rw [decide_eq_false_iff_not] at hsact; omega
      subst hb0
      rw [highMem_c_of_false glob n 0 s hvalid' hsact, Nat.zero_testBit]
      simp [hne_c, hne_s]
    | true =>
      rw [highMem_c_of_true glob n b s hvalid' hsact u hp_u]
      simp only [hne_c, hne_s, false_or]
      apply hF_iff
      unfold sActive0 at hsact; rw [decide_eq_true_eq] at hsact
      unfold sTarg0
      split_ifs with h2
      · right; exact ⟨rfl, hj h2.1 (by omega)⟩
      · left; exact ⟨rfl, hsact.resolve_right h2⟩
  · rw [hr.2 u hp_u]
    cases hract : rActive0 n b s with
    | false =>
      have hb0 : b = 0 := by
        unfold rActive0 at hract; rw [decide_eq_false_iff_not] at hract; omega
      subst hb0
      rw [highMem_r_of_false glob n 0 s hvalid' hract, Nat.zero_testBit]
      simp [hne_r]
    | true =>
      rw [highMem_r_of_true glob n b s hvalid' hract u hp_u]
      simp only [hne_r, false_or]
      apply hF_iff
      unfold rActive0 at hract; rw [decide_eq_true_eq] at hract
      unfold rTarg0
      split_ifs with h2
      · right; exact ⟨rfl, hj h2.1 h2.2⟩
      · left; exact ⟨rfl, hract.resolve_right h2⟩

lemma mem_portal_of_s_eq_close_add_three (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hb : b < 2 ^ n - 1) (hs : s = S_close0 n b + 3)
    {w : V_bin n} (hport : HitsPortal glob n b s w .c ∨ HitsPortal glob n b s w .r)
    (u : V_bin n) (hu : (G_bin n).priority .s < (G_bin n).priority u) :
    u ∈ predPath glob n b s w ↔ highMemF n b ⟨lowestZero0 b n, lowestZero0_lt hb⟩ u := by
  have hp_u : (G_bin n).priority .c ≤ (G_bin n).priority u := by
    dsimp [G_bin, priority_bin] at hu ⊢; omega
  have hne_c : u ≠ .c := by intro h; subst h; dsimp [G_bin, priority_bin] at hu; omega
  have hne_r : u ≠ .r := by intro h; subst h; dsimp [G_bin, priority_bin] at hu; omega
  have hne_s : u ≠ .s := by intro h; subst h; omega
  rcases hport with hc | hr
  · have hsact : sActive0 n b s = true := by
      unfold sActive0; rw [decide_eq_true_eq]; exact Or.inr ⟨hb, by omega⟩
    have hstarg : (⟨sTarg0 n b s, sTarg0_lt_of_sActive0' n b s hvalid.2.1 hsact⟩ : Fin n) =
        ⟨lowestZero0 b n, lowestZero0_lt hb⟩ := by
      apply Fin.ext; dsimp only; unfold sTarg0; rw [if_pos ⟨hb, by omega⟩]
    rw [hc.2 u hp_u, highMem_c_of_true glob n b s hvalid hsact u hp_u, hstarg]
    simp [hne_c, hne_s]
  · have hract : rActive0 n b s = true := by
      unfold rActive0; rw [decide_eq_true_eq]; exact Or.inr ⟨hb, by omega⟩
    have hrtarg : (⟨rTarg0 n b s, rTarg0_lt_of_rActive0' n b s hvalid.2.1 hract⟩ : Fin n) =
        ⟨lowestZero0 b n, lowestZero0_lt hb⟩ := by
      apply Fin.ext; dsimp only; unfold rTarg0; rw [if_pos ⟨hb, by omega⟩]
    rw [hr.2 u hp_u, highMem_r_of_true glob n b s hvalid hract u hp_u, hrtarg]
    simp [hne_r]

lemma uLim0_le_lowestOne0 (b n : ℕ) : uLim0 b n ≤ lowestOne0 b n := by
  unfold uLim0; split_ifs <;> omega

lemma uLim0_le_hyLim0 (b n s : ℕ) : uLim0 b n ≤ hyLim0 b n s := by
  unfold uLim0 hyLim0; split_ifs <;> simp_all

lemma hitsWithTop_u_of_still (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hb0 : 0 < b) (m₀ : Fin n) (hm₀_eq : m₀.val = uLim0 b n - 1 - s)
    (hm₀_lt : m₀.val + s < uLim0 b n) :
    ∀ k (m : Fin n), m₀.val - m.val ≤ k → 1 ≤ m.val → m.val ≤ m₀.val →
      HitsWithTop glob n b s (.u m) (.g m₀) (.f m₀)
  | 0, m, hk, hm1, hle => by
    have hm_eq : m = m₀ := Fin.ext (by omega)
    subst hm_eq
    have hle_kp := uLim0_le_lowestOne0 b n
    have hle_hy := uLim0_le_hyLim0 b n s
    have hlt_kp : m.val < lowestOne0 b n := by omega
    have hlt_hy : m.val + s < hyLim0 b n s := by omega
    have hbit : b.testBit m.val = false := testBit_of_lt_lowestOne0 hb0 hvalid.2.1 hlt_kp
    have howner_u : (G_bin n).owner (.u m) = false := by
      dsimp [G_bin, owner_bin]; rw [if_neg (by omega)]
    have hce_u : chooseEdge1 glob n b s (.u m) = false := by
      dsimp [chooseEdge1]
      split_ifs with h1 h2 h3
      · rfl
      · rfl
      · rw [decide_eq_false_iff_not, not_not]; exact hm₀_lt
      · exfalso; exact h3 ⟨hb0, hlt_kp⟩
    have hs_u : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.u m) = .h m := by
      unfold step predState0; rw [if_pos howner_u, hce_u]; rfl
    have hce_h : chooseEdge1 glob n b s (.h m) = false := by
      dsimp [chooseEdge1]; rw [if_neg (by simp [hbit]), if_pos ⟨hb0, hlt_kp, hlt_hy⟩]
    have hs_h : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h m) = .hx m := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_h]; rfl
    have hce_hx : chooseEdge1 glob n b s (.hx m) = false := by
      dsimp [chooseEdge1]; rw [if_neg (by simp [hbit]), if_pos ⟨hb0, hlt_kp, hlt_hy⟩]
    have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx m) = .hy m := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hx]; rfl
    have hce_hy : chooseEdge1 glob n b s (.hy m) = false := by
      dsimp [chooseEdge1]; rw [if_neg (by simp [hbit]), if_pos ⟨hb0, hlt_kp, hlt_hy⟩]
    have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy m) = .f m := by
      unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hy]; rfl
    have hs_f : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f m) = .g m := rfl
    have hf : HitsWithTop glob n b s (.f m) (.g m) (.f m) :=
      hitsWithTop_of_step_eq glob n b s hvalid (.f m) (.g m) (by nofun) hs_f
    have hhy : HitsWithTop glob n b s (.hy m) (.g m) (.f m) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid (.hy m) (.g m) (.f m) (by nofun)
      · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      · rw [hs_hy]; exact hf
    have hhx : HitsWithTop glob n b s (.hx m) (.g m) (.f m) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid (.hx m) (.g m) (.f m) (by nofun)
      · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      · rw [hs_hx]; exact hhy
    have hh : HitsWithTop glob n b s (.h m) (.g m) (.f m) := by
      apply hitsWithTop_of_step_lt glob n b s hvalid (.h m) (.g m) (.f m) (by nofun)
      · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      · rw [hs_h]; exact hhx
    apply hitsWithTop_of_step_lt glob n b s hvalid (.u m) (.g m) (.f m) (by nofun)
    · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
    · rw [hs_u]; exact hh
  | k + 1, m, hk, hm1, hle => by
    by_cases heq : m.val = m₀.val
    · exact hitsWithTop_u_of_still glob n b s hvalid hb0 m₀ hm₀_eq hm₀_lt 0 m (by omega) hm1 hle
    · have hlt_m₀ : m.val < m₀.val := by omega
      have hle_kp := uLim0_le_lowestOne0 b n
      have hle_hy := uLim0_le_hyLim0 b n s
      have hlt_kp : m.val < lowestOne0 b n := by omega
      have hlt_u : m.val + 1 + s < uLim0 b n := by omega
      have hlt_hy : m.val + s < hyLim0 b n s := by omega
      have hbit : b.testBit m.val = false := testBit_of_lt_lowestOne0 hb0 hvalid.2.1 hlt_kp
      have hm_succ : m.val + 1 < n := by have := m₀.isLt; omega
      have hhi : hasHigherOne0 b n m.val = true := by
        rw [hasHigherOne0_iff]
        exact ⟨lowestOne0 b n, hlt_kp, lowestOne0_lt hb0 hvalid.2.1, testBit_lowestOne0 hb0 hvalid.2.1⟩
      have howner_u : (G_bin n).owner (.u m) = false := by
        dsimp [G_bin, owner_bin]; rw [if_neg (by omega)]
      have hce_u : chooseEdge1 glob n b s (.u m) = false := by
        dsimp [chooseEdge1]
        split_ifs with h1 h2 h3
        · rfl
        · rfl
        · rw [decide_eq_false_iff_not, not_not]; omega
        · exfalso; exact h3 ⟨hb0, hlt_kp⟩
      have hs_u : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.u m) = .h m := by
        unfold step predState0; rw [if_pos howner_u, hce_u]; rfl
      have hce_h : chooseEdge1 glob n b s (.h m) = false := by
        dsimp [chooseEdge1]; rw [if_neg (by simp [hbit]), if_pos ⟨hb0, hlt_kp, hlt_hy⟩]
      have hs_h : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.h m) = .hx m := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_h]; rfl
      have hce_hx : chooseEdge1 glob n b s (.hx m) = false := by
        dsimp [chooseEdge1]; rw [if_neg (by simp [hbit]), if_pos ⟨hb0, hlt_kp, hlt_hy⟩]
      have hs_hx : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hx m) = .hy m := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hx]; rfl
      have hce_hy : chooseEdge1 glob n b s (.hy m) = false := by
        dsimp [chooseEdge1]; rw [if_neg (by simp [hbit]), if_pos ⟨hb0, hlt_kp, hlt_hy⟩]
      have hs_hy : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.hy m) = .f m := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, hce_hy]; rfl
      have hs_f : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.f m) = .g m := rfl
      have htau : chooseTauEdge1 n b s (.g m) = true := by
        dsimp [chooseTauEdge1]
        have hd : decide (0 < b ∧ m.val < lowestOne0 b n ∧ m.val + 1 + s < uLim0 b n) = true :=
          decide_eq_true ⟨hb0, hlt_kp, hlt_u⟩
        simp [hd]
      have hs_g : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g m) = .k m := by
        unfold step G_bin owner_bin predTau0; rw [if_pos htau]; rfl
      have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k m) = .z m := rfl
      have hce_z : chooseEdge1 glob n b s (.z m) = true := by
        dsimp [chooseEdge1]; simp [hm_succ, hhi]
      have hs_z : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.z m) = .u ⟨m.val + 1, hm_succ⟩ := by
        unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce_z]; dsimp [edge1]; rw [dif_pos hm_succ]
      have ih := hitsWithTop_u_of_still glob n b s hvalid hb0 m₀ hm₀_eq hm₀_lt k ⟨m.val + 1, hm_succ⟩
        (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
      have hz : HitsWithTop glob n b s (.z m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.z m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin]; omega
        · rw [hs_z]; exact ih
      have hk_hit : HitsWithTop glob n b s (.k m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.k m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin]; omega
        · rw [hs_k]; exact hz
      have hg : HitsWithTop glob n b s (.g m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.g m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
        · rw [hs_g]; exact hk_hit
      have hf : HitsWithTop glob n b s (.f m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.f m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin]; omega
        · rw [hs_f]; exact hg
      have hhy : HitsWithTop glob n b s (.hy m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.hy m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
        · rw [hs_hy]; exact hf
      have hhx : HitsWithTop glob n b s (.hx m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.hx m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
        · rw [hs_hx]; exact hhy
      have hh : HitsWithTop glob n b s (.h m) (.g m₀) (.f m₀) := by
        apply hitsWithTop_of_step_lt glob n b s hvalid (.h m) (.g m₀) (.f m₀) (by nofun)
        · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
        · rw [hs_h]; exact hhx
      apply hitsWithTop_of_step_lt glob n b s hvalid (.u m) (.g m₀) (.f m₀) (by nofun)
      · dsimp [G_bin, priority_bin, top_bin, shift_bin, baseL_bin, M_bin, Na_bin]; omega
      · rw [hs_u]; exact hh

lemma predVal_lt_portal_of_hitsWithTop_still (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hb0 : 0 < b) (m₀ : Fin n) (hm₀_eq : m₀.val = uLim0 b n - 1 - s)
    (hm₀_lt : m₀.val + s < uLim0 b n)
    {w₁ w₂ : V_bin n}
    (hw₁ : HitsWithTop glob n b s w₁ (.g m₀) (.f m₀))
    (hw₂ : HitsPortal glob n b s w₂ .c ∨ HitsPortal glob n b s w₂ .r) :
    ValueLT (G_bin n) (predVal glob n b s w₁) (predVal glob n b s w₂) := by
  have hle_kp := uLim0_le_lowestOne0 b n
  have hkp_lt := lowestOne0_lt hb0 hvalid.2.1
  have hlt_kp : m₀.val < lowestOne0 b n := by omega
  have hbit_m₀ : b.testBit m₀.val = false := testBit_of_lt_lowestOne0 hb0 hvalid.2.1 hlt_kp
  have hs_lt : s < n := by omega
  have htau_m₀ : chooseTauEdge1 n b s (.g m₀) = false := by
    dsimp [chooseTauEdge1]
    simp only [hbit_m₀, Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨by omega, by omega⟩
  have hport_g := hitsPortal_g_of_tau_false glob n b s hvalid m₀ htau_m₀
  apply predVal_lt_of_setLT glob n b s hvalid
  apply setLT_of_top_diff_odd (G_bin_priority_injective n hvalid.1) (d := .f m₀)
  · exact hw₁.2.1
  · rw [mem_portal_zfk_iff_testBit glob n b s hvalid hw₂ m₀ (by unfold S_close0; omega) (.f m₀) (Or.inr (Or.inl rfl)),
        hbit_m₀]
    decide
  · exact prio_f_odd n m₀
  · intro u hu
    rw [hw₁.2.2 u hu]
    have hu_gt_s : (G_bin n).priority .s < (G_bin n).priority u := by
      dsimp [G_bin, priority_bin] at hu ⊢; omega
    rcases (prio_gt_s_iff n u).mp hu_gt_s with ⟨j, hu_eq⟩
    rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_g j (by unfold S_close0; omega) u hu_eq,
        mem_portal_zfk_iff_testBit glob n b s hvalid hw₂ j (by unfold S_close0; omega) u hu_eq]

lemma hitsWithTop_d1_k_of_dClosed0 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) (i : Fin n)
    (hd : dClosed0 n b s i = true) :
    HitsWithTop glob n b s (.d1 i) (.k i) (.g i) := by
  have hce1 : chooseEdge1 glob n b s (.d1 i) = true := by
    unfold dClosed0 at hd; dsimp [chooseEdge1]
    rcases Bool.or_eq_true_iff.mp hd with h1 | h2
    · rw [Bool.and_eq_true, decide_eq_true_eq] at h1; rw [if_pos h1.1, if_neg h1.2]
    · rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h2; rw [if_neg (by simp [h2.1]), if_pos (by omega)]
  have hce2 : chooseEdge1 glob n b s (.d2 i) = true := by
    unfold dClosed0 at hd; dsimp [chooseEdge1]
    rcases Bool.or_eq_true_iff.mp hd with h1 | h2
    · rw [Bool.and_eq_true, decide_eq_true_eq] at h1; rw [if_pos h1.1, if_neg h1.2]
    · rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h2; rw [if_neg (by simp [h2.1]), if_pos h2.2]
  have hce3 : chooseEdge1 glob n b s (.d3 i) = true := by
    unfold dClosed0 at hd; dsimp [chooseEdge1]
    rcases Bool.or_eq_true_iff.mp hd with h1 | h2
    · rw [Bool.and_eq_true, decide_eq_true_eq] at h1; rw [if_pos h1.1, if_neg h1.2]
    · rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h2; rw [if_neg (by simp [h2.1]), if_pos (by omega)]
  have htau : chooseTauEdge1 n b s (.g i) = true := by
    unfold dClosed0 at hd; dsimp [chooseTauEdge1]
    rcases Bool.or_eq_true_iff.mp hd with h1 | h2
    · rw [Bool.and_eq_true] at h1; simp [h1.1]
    · rw [Bool.and_eq_true, decide_eq_true_eq] at h2
      have hd' : decide (3 * (n + 2 * i.val + 1) + 2 ≤ s) = true := decide_eq_true h2.2
      simp [hd']
  have hs1 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d1 i) = .d2 i := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce1]; rfl
  have hs2 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d2 i) = .d3 i := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce2]; rfl
  have hs3 : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.d3 i) = .g i := by
    unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce3]; rfl
  have hsg : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.g i) = .k i := by
    unfold step G_bin owner_bin predTau0; rw [if_pos htau]; rfl
  have hg : HitsWithTop glob n b s (.g i) (.k i) (.g i) :=
    hitsWithTop_of_step_eq glob n b s hvalid (.g i) (.k i) (by nofun) hsg
  have hd3 : HitsWithTop glob n b s (.d3 i) (.k i) (.g i) := by
    apply hitsWithTop_of_step_lt glob n b s hvalid (.d3 i) (.k i) (.g i) (by nofun)
    · dsimp [G_bin, priority_bin]; omega
    · rw [hs3]; exact hg
  have hd2 : HitsWithTop glob n b s (.d2 i) (.k i) (.g i) := by
    apply hitsWithTop_of_step_lt glob n b s hvalid (.d2 i) (.k i) (.g i) (by nofun)
    · dsimp [G_bin, priority_bin]; omega
    · rw [hs2]; exact hd3
  apply hitsWithTop_of_step_lt glob n b s hvalid (.d1 i) (.k i) (.g i) (by nofun)
  · dsimp [G_bin, priority_bin]; omega
  · rw [hs1]; exact hd2

lemma predTau0_eq_of_ne_g (n b s : ℕ) (v : V_bin n)
    (howner : (G_bin n).owner v = true) (hne : ∀ i, v ≠ .g i) :
    predTau0 n b s v = edge0 n v ∧ edge1 n v = edge0 n v := by
  cases v with
  | rp _ | sp _ | l2 _ | l3 _ | r_2 | r | s | d1 _ | d2 _ | d3 _ | hy _ | hx _ | h _ | z _ =>
    contradiction
  | g i => exact False.elim (hne i rfl)
  | u i =>
    dsimp [G_bin, owner_bin] at howner
    split_ifs at howner with hi0
    refine ⟨rfl, ?_⟩
    dsimp [edge0, edge1]
    rw [dif_neg (by omega)]
  | l1 m =>
    dsimp [G_bin, owner_bin] at howner
    split_ifs at howner with hm0
    refine ⟨rfl, ?_⟩
    dsimp [edge0, edge1]
    rw [if_pos hm0]
    congr 1
    ext
    dsimp
    omega
  | lp1 m | lp2 m | lp3 m =>
    dsimp [G_bin, owner_bin] at howner
    split_ifs at howner with hm0
    refine ⟨rfl, ?_⟩
    simp [edge0, edge1, hm0]
  | a j =>
    dsimp [G_bin, owner_bin] at howner
    split_ifs at howner with hj
    refine ⟨rfl, ?_⟩
    rcases hj with hj0 | hj1
    · simp [edge0, edge1, hj0]
    · have hj1' : j.val = 3 * (3 * n - 1) - 1 := hj1
      simp [edge0, edge1, hj1']
  | x | r_2_odd | r_a | c_odd | c | b _ | f _ | k _ =>
    exact ⟨rfl, rfl⟩

theorem predTau0_optimal (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    OptimalCounterstrategy (G_bin n) (predState0 glob n b s) (predTau0 n b s) ∧
    ∀ v, value (G_bin n) (predState0 glob n b s) v = predVal glob n b s v := by
  apply optimalCounterstrategy_of_min_step (G_bin_wellFormed n hvalid.1) (predTau0_legal n b s)
  intro v w howner hedge
  cases v with
  | g i =>
    rcases hedge with rfl | rfl
    · -- w = edge0 n (.g i) = .d1 i
      unfold predTau0
      split_ifs with htau
      · right
        dsimp [edge0, edge1]
        cases hd : dClosed0 n b s i with
        | true =>
          exact predVal_lt_of_hitsWithTop_even_self glob n b s hvalid
            (hitsWithTop_d1_k_of_dClosed0 glob n b s hvalid i hd)
            (prio_g_even n i)
        | false =>
          have hport_d1 := hitsPortal_d1_of_not_dClosed0 glob n b s hvalid i hd
          cases hbit : b.testBit i.val with
          | true =>
            have hcond : b < 2 ^ n - 1 ∧ i.val < lowestZero0 b n ∧ s = S_close0 n b + 3 := by
              unfold dClosed0 at hd
              simp [hbit] at hd
              exact hd
            rcases hcond with ⟨hb_lt, hik, hs3⟩
            let kFin : Fin n := ⟨lowestZero0 b n, lowestZero0_lt hb_lt⟩
            have hp_c : (G_bin n).priority .c ≤ (G_bin n).priority (.k kFin) := by
              dsimp [G_bin, priority_bin]; omega
            have hp_s : (G_bin n).priority .s < (G_bin n).priority (.k kFin) := by
              dsimp [G_bin, priority_bin]; omega
            have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k i) = .z i := rfl
            have hstill : ∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false :=
              fun hi1 => uStillH0_succ_false_of_testBit_true n b s i hi1 hbit
            apply predVal_lt_of_setLT glob n b s hvalid
            apply setLT_of_top_diff_even (G_bin_priority_injective n hvalid.1) (d := .k kFin)
            · rw [predPath, predVal, pred_path_step glob n b s hvalid (.k i) (by nofun), hs_k, Finset.mem_insert]
              change V_bin.k kFin = V_bin.k i ∨ V_bin.k kFin ∈ predPath glob n b s (.z i) → False
              rw [highMem_z glob n b s hvalid i hstill (.k kFin) hp_c]
              dsimp [highMemZ, kFin]
              rw [testBit_lowestZero0 hb_lt]
              rintro (h | ⟨_, htrue⟩)
              · injection h with h'; have := Fin.ext_iff.mp h'; dsimp [kFin] at this; omega
              · contradiction
            · rw [mem_portal_of_s_eq_close_add_three glob n b s hvalid hb_lt hs3 hport_d1 (.k kFin) hp_s]
              exact Or.inl rfl
            · exact prio_k_even n kFin
            · intro u hu
              have hp_u_s : (G_bin n).priority .s < (G_bin n).priority u := by
                dsimp [G_bin, priority_bin] at hu ⊢; omega
              have hp_u_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
                dsimp [G_bin, priority_bin] at hu ⊢; omega
              rw [predPath, predVal, pred_path_step glob n b s hvalid (.k i) (by nofun), hs_k, Finset.mem_insert]
              change u = .k i ∨ u ∈ predPath glob n b s (.z i) ↔ _
              rw [highMem_z glob n b s hvalid i hstill u hp_u_c,
                  mem_portal_of_s_eq_close_add_three glob n b s hvalid hb_lt hs3 hport_d1 u hp_u_s]
              have hkFin_val : kFin.val = lowestZero0 b n := rfl
              rcases (prio_gt_s_iff n u).mp hp_u_s with ⟨j, rfl | rfl | rfl⟩
              · have hkj : lowestZero0 b n < j.val := by
                  dsimp [G_bin, priority_bin] at hu; omega
                dsimp [highMemZ, highMemF]
                simp only [reduceCtorEq, false_or, Fin.ext_iff]
                constructor
                · rintro (heq | ⟨_, hbj⟩)
                  · omega
                  · exact Or.inr ⟨hkj, hbj⟩
                · rintro (heq | ⟨_, hbj⟩)
                  · omega
                  · exact Or.inr ⟨by omega, hbj⟩
              · have hkj : lowestZero0 b n < j.val := by
                  dsimp [G_bin, priority_bin] at hu; omega
                dsimp [highMemZ, highMemF]
                simp only [reduceCtorEq, false_or]
                constructor
                · rintro ⟨_, hbj⟩
                  exact Or.inr ⟨hkj, hbj⟩
                · rintro (heq | ⟨_, hbj⟩)
                  · omega
                  · exact ⟨by omega, hbj⟩
              · have hkj : lowestZero0 b n < j.val := by
                  dsimp [G_bin, priority_bin] at hu; omega
                dsimp [highMemZ, highMemF]
                constructor
                · rintro (h | ⟨_, hbj⟩)
                  · injection h with h'; have := Fin.ext_iff.mp h'; omega
                  · exact Or.inr ⟨hkj, hbj⟩
                · rintro (heq | ⟨_, hbj⟩)
                  · omega
                  · exact Or.inr ⟨by omega, hbj⟩
          | false =>
            have hlt_T : ¬(3 * (n + 2 * i.val + 1) + 2 ≤ s) := by
              unfold dClosed0 at hd; simp [hbit] at hd; omega
            have hstill : 0 < b ∧ i.val < lowestOne0 b n ∧ i.val + 1 + s < uLim0 b n := by
              dsimp [chooseTauEdge1] at htau
              simp [hbit, hlt_T] at htau
              exact htau
            rcases hstill with ⟨hb0, hikp, hlt_u⟩
            have hle_kp := uLim0_le_lowestOne0 b n
            have hkp_lt := lowestOne0_lt hb0 hvalid.2.1
            let m₀ : Fin n := ⟨uLim0 b n - 1 - s, by omega⟩
            have hi1 : i.val + 1 < n := by omega
            have hhi : hasHigherOne0 b n i.val = true := by
              rw [hasHigherOne0_iff]
              exact ⟨lowestOne0 b n, hikp, hkp_lt, testBit_lowestOne0 hb0 hvalid.2.1⟩
            have hce_z : chooseEdge1 glob n b s (.z i) = true := by
              dsimp [chooseEdge1]; simp [hi1, hhi]
            have hs_z : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.z i) = .u ⟨i.val + 1, hi1⟩ := by
              unfold step G_bin owner_bin predState0; rw [if_pos rfl, if_pos hce_z]; dsimp [edge1]; rw [dif_pos hi1]
            have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k i) = .z i := rfl
            have hu_hit := hitsWithTop_u_of_still glob n b s hvalid hb0 m₀ rfl (by dsimp [m₀]; omega)
              n ⟨i.val + 1, hi1⟩ (by dsimp [m₀]; omega) (by dsimp only; omega) (by dsimp [m₀]; omega)
            have hz_hit : HitsWithTop glob n b s (.z i) (.g m₀) (.f m₀) := by
              apply hitsWithTop_of_step_lt glob n b s hvalid (.z i) (.g m₀) (.f m₀) (by nofun)
              · dsimp [G_bin, priority_bin, m₀]; omega
              · rw [hs_z]; exact hu_hit
            have hk_hit : HitsWithTop glob n b s (.k i) (.g m₀) (.f m₀) := by
              apply hitsWithTop_of_step_lt glob n b s hvalid (.k i) (.g m₀) (.f m₀) (by nofun)
              · dsimp [G_bin, priority_bin, m₀]; omega
              · rw [hs_k]; exact hz_hit
            exact predVal_lt_portal_of_hitsWithTop_still glob n b s hvalid hb0 m₀ rfl (by dsimp [m₀]; omega)
              hk_hit hport_d1
      · exact valueLE_refl (G_bin n) _
    · -- w = edge1 n (.g i) = .k i
      unfold predTau0
      split_ifs with htau
      · exact valueLE_refl (G_bin n) _
      · right
        dsimp [edge0, edge1]
        have htau_false : chooseTauEdge1 n b s (.g i) = false := Bool.eq_false_of_not_eq_true htau
        have hd := dClosed0_eq_false_of_tau_false n b s i htau_false
        have hport_d1 := hitsPortal_d1_of_not_dClosed0 glob n b s hvalid i hd
        have hcond := htau_false
        dsimp [chooseTauEdge1] at hcond
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hcond
        rcases hcond with ⟨⟨hbit, hlt_T⟩, hnot_still⟩
        have hstill : ∀ hi1 : i.val + 1 < n, uStillH0 n b s ⟨i.val + 1, hi1⟩ = false := by
          intro hi1
          unfold uStillH0
          rw [decide_eq_false_iff_not]
          dsimp only
          intro h
          exact hnot_still ⟨h.1, by omega, h.2.2⟩
        have hs_k : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.k i) = .z i := rfl
        have hk_path : predPath glob n b s (.k i) = insert (V_bin.k i) (predPath glob n b s (.z i)) :=
          by rw [predPath, predVal, pred_path_step glob n b s hvalid (.k i) (by nofun), hs_k]
        apply predVal_lt_of_setLT glob n b s hvalid
        apply setLT_of_top_diff_even (G_bin_priority_injective n hvalid.1) (d := .k i)
        · rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_d1 i (by unfold S_close0; omega) (.k i) (Or.inr (Or.inr rfl)),
              hbit]
          decide
        · rw [hk_path]
          exact Finset.mem_insert_self (V_bin.k i) _
        · exact prio_k_even n i
        · intro u hu
          have hp_u_s : (G_bin n).priority .s < (G_bin n).priority u := by
            dsimp [G_bin, priority_bin] at hu ⊢; omega
          have hp_u_c : (G_bin n).priority .c ≤ (G_bin n).priority u := by
            dsimp [G_bin, priority_bin] at hu ⊢; omega
          rw [hk_path, Finset.mem_insert]
          rw [highMem_z glob n b s hvalid i hstill u hp_u_c]
          rcases (prio_gt_s_iff n u).mp hp_u_s with ⟨j, hu_eq⟩
          have hij : i.val < j.val := by
            rcases hu_eq with rfl | rfl | rfl <;> { dsimp [G_bin, priority_bin] at hu; omega }
          rw [mem_portal_zfk_iff_testBit glob n b s hvalid hport_d1 j (by unfold S_close0; omega) u hu_eq]
          rcases hu_eq with rfl | rfl | rfl
          · dsimp [highMemZ]
            simp only [reduceCtorEq, false_or, Fin.ext_iff]
            exact ⟨fun h => Or.inr ⟨hij, h⟩, fun h => h.elim (by omega) And.right⟩
          · dsimp [highMemZ]
            simp only [reduceCtorEq, false_or]
            exact ⟨fun h => ⟨hij, h⟩, And.right⟩
          · dsimp [highMemZ]
            constructor
            · intro h; exact Or.inr ⟨hij, h⟩
            · rintro (h | ⟨_, h⟩)
              · injection h with h'; have := Fin.ext_iff.mp h'; omega
              · exact h
  | x | r_2_odd | r_a | c_odd | c | u _ | f _ | k _ | l1 _ | lp1 _ | lp2 _ | lp3 _ | a _ | b _ =>
    have htau_v := predTau0_eq_of_ne_g n b s _ howner (by nofun)
    rcases hedge with rfl | rfl
    · rw [htau_v.1]; exact valueLE_refl (G_bin n) _
    · rw [htau_v.1, htau_v.2]; exact valueLE_refl (G_bin n) _
  | rp _ | sp _ | l2 _ | l3 _ | r_2 | r | s | d1 _ | d2 _ | d3 _ | hy _ | hx _ | h _ | z _ =>
    contradiction

end FriedmannParity


