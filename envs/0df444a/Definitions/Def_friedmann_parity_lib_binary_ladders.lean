-- Prove2me | Definitions.Def_friedmann_parity_lib_binary_ladders
-- name    : friedmann_parity_lib_binary_ladders
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-08T03:44:22.822738+00:00
-- url     : https://prove2.me/theorems/b95bbdaf-e05a-4a45-ba1c-114471c682e6
-- title:
--   Friedmann binary lower-bound family: ladder and chain path lemmas
-- statement:
--   A sorry-free library module that extends `friedmann_parity_lib_binary_state`. It computes the plays and path sets of the strategies $\sigma_{b,s}$ through the ladder vertices $l1_m,l2_m,l3_m,lp1_m,lp2_m,lp3_m$ and the chains $a_j,b_j$ of the games $G_n$.
--
--   For each of these player-0 vertices it proves that the successor chosen by the next counter state has strictly larger valuation than the alternative successor. These are the cases `bestEdge_a`, `bestEdge_l1`–`bestEdge_lp3` and `bestEdge_r_2` of the best-edge property. Each comparison is reduced to a comparison of path sets, using the fact that all cycle priorities equal $1$.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 7(3:19), 2011, arXiv:1106.0778, §§6–8

import Definitions.Def_friedmann_parity_lib_binary_state

set_option autoImplicit false
set_option linter.unusedVariables false

namespace FriedmannParity

/-! ### Part 1: Priority, Rank, and Step Helpers for Ladders -/

def s_a0 (glob : Bool) (n b s : ℕ) : ℕ :=
  if b < 2 ^ n - 1 ∧ glob = true then min s (S_close0 n b) else s

def s_eff0 (glob : Bool) (n b s : ℕ) : ℕ :=
  if b < 2 ^ n - 1 ∧ glob = true ∧ s = S_close0 n b + 2 then S_close0 n b + 1 else s

lemma s_le_s_a0_add_one_of_not_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) :
    s ≤ s_a0 glob n b s + 1 := by
  rcases hvalid with ⟨_, _, hs⟩
  unfold s_a0
  split_ifs with h
  · have hmax := maxStep0_of_lt h.1
    omega
  · omega

lemma s_eff0_eq_s_of_not_close (glob : Bool) (n b s : ℕ)
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) :
    s_eff0 glob n b s = s := by
  unfold s_eff0
  rw [if_neg]
  rintro ⟨hb, _, hs2⟩
  exact hnot_close ⟨hb, Or.inl hs2⟩

lemma step_c_odd (glob : Bool) (n b s : ℕ) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .c_odd = .c := rfl

lemma step_r_a (glob : Bool) (n b s : ℕ) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .r_a = .r := rfl

lemma step_r_2_odd (glob : Bool) (n b s : ℕ) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .r_2_odd = .r_2 := rfl

lemma step_b (glob : Bool) (n b s : ℕ) (k : Fin (3 * (3 * n - 1))) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.b k) = .a (bTarget n k) := rfl

lemma step_a_zero (glob : Bool) (n b s : ℕ) (j : Fin (3 * (3 * n - 1))) (hj0 : j.val = 0) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.a j) = .c := by
  have hown : (G_bin n).owner (.a j) = true := by
    dsimp [G_bin, owner_bin]
    exact if_pos (Or.inl hj0)
  unfold step
  rw [if_neg (by simp [hown])]
  dsimp [predTau0, chooseTauEdge1, edge0]
  exact if_pos hj0

lemma step_a_top (glob : Bool) (n b s : ℕ) (j : Fin (3 * (3 * n - 1)))
    (hj0 : j.val ≠ 0) (hj1 : j.val = 3 * (3 * n - 1) - 1) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.a j) = .r_a := by
  have hown : (G_bin n).owner (.a j) = true := by
    dsimp [G_bin, owner_bin, M_bin]
    exact if_pos (Or.inr hj1)
  unfold step
  rw [if_neg (by simp [hown])]
  dsimp [predTau0, chooseTauEdge1, edge0]
  exact if_neg hj0

lemma step_a_pred (glob : Bool) (n b s : ℕ) (j : Fin (3 * (3 * n - 1)))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hj1 : 1 ≤ j.val) (hj_lt : j.val < 3 * (3 * n - 1) - 1)
    (hj_le : j.val ≤ s_a0 glob n b s + 1) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.a j) =
      .a ⟨j.val - 1, by have := j.isLt; omega⟩ := by
  have hj0 : j.val ≠ 0 := by omega
  have hown : (G_bin n).owner (.a j) = false := by
    dsimp [G_bin, owner_bin, M_bin]
    exact if_neg (by omega)
  have hce : chooseEdge1 glob n b s (.a j) = true := by
    dsimp [chooseEdge1]
    rw [if_neg hnot_close]
    change decide (1 ≤ j.val ∧ j.val < 3 * (3 * n - 1) - 1 ∧ j.val ≤ s_a0 glob n b s + 1) = true
    rw [decide_eq_true_eq]
    exact ⟨hj1, hj_lt, hj_le⟩
  unfold step
  rw [if_pos hown]
  unfold predState0
  rw [if_pos hce]
  dsimp [edge1, M_bin]
  rw [if_neg hj0, if_neg (by omega)]

lemma step_a_ra (glob : Bool) (n b s : ℕ) (j : Fin (3 * (3 * n - 1)))
    (hj1 : 1 ≤ j.val)
    (hra : (b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) ∨
      s_a0 glob n b s + 1 < j.val ∨ j.val = 3 * (3 * n - 1) - 1) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.a j) = .r_a := by
  have hj0 : j.val ≠ 0 := by omega
  by_cases hj_top : j.val = 3 * (3 * n - 1) - 1
  · exact step_a_top glob n b s j hj0 hj_top
  · have hown : (G_bin n).owner (.a j) = false := by
      dsimp [G_bin, owner_bin, M_bin]
      exact if_neg (by omega)
    have hce : chooseEdge1 glob n b s (.a j) = false := by
      by_cases hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)
      · dsimp [chooseEdge1]
        exact if_pos hclose
      · dsimp [chooseEdge1]
        rw [if_neg hclose]
        change decide (1 ≤ j.val ∧ j.val < 3 * (3 * n - 1) - 1 ∧ j.val ≤ s_a0 glob n b s + 1) = false
        rw [decide_eq_false_iff_not]
        rcases hra with h | h | h
        · exact False.elim (hclose h)
        · omega
        · exact False.elim (hj_top h)
    unfold step
    rw [if_pos hown]
    unfold predState0
    rw [hce]
    dsimp [edge0]
    exact if_neg hj0

/-! ### Part 2: `HitsWithTop` and `HitsPortal` for `.c_odd`, `.r_a`, `.r_2`, `.r_2_odd` -/

lemma hitsWithTop_c_odd (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    HitsWithTop glob n b s .c_odd .c .c_odd :=
  hitsWithTop_of_step_eq glob n b s hvalid .c_odd .c (by rintro ⟨⟩) rfl

lemma hitsPortal_c_odd (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    HitsPortal glob n b s .c_odd .c := by
  apply hitsPortal_of_step glob n b s hvalid .c_odd .c (by rintro ⟨⟩)
  · dsimp [G_bin, priority_bin]; omega
  · exact hitsPortal_refl glob n b s hvalid .c (by rintro ⟨⟩)

lemma hitsWithTop_r_a (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    HitsWithTop glob n b s .r_a .r .r_a :=
  hitsWithTop_of_step_eq glob n b s hvalid .r_a .r (by rintro ⟨⟩) rfl

lemma hitsPortal_r_a (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    HitsPortal glob n b s .r_a .r := by
  apply hitsPortal_of_step glob n b s hvalid .r_a .r (by rintro ⟨⟩)
  · dsimp [G_bin, priority_bin]; omega
  · exact hitsPortal_refl glob n b s hvalid .r (by rintro ⟨⟩)

lemma step_r_2_of_not_close (glob : Bool) (n b s : ℕ)
    (hnot : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .r_2 = .c_odd := by
  change predState0 glob n b s .r_2 = .c_odd
  unfold predState0
  have hce : chooseEdge1 glob n b s .r_2 = false := by
    dsimp [chooseEdge1]
    exact decide_eq_false hnot
  rw [hce]
  rfl

lemma step_r_2_of_close (glob : Bool) (n b s : ℕ)
    (hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) .r_2 = .r := by
  change predState0 glob n b s .r_2 = .r
  unfold predState0
  have hce : chooseEdge1 glob n b s .r_2 = true := by
    dsimp [chooseEdge1]
    exact decide_eq_true hclose
  rw [if_pos hce]
  rfl

lemma hitsWithTop_r_2_not_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) :
    HitsWithTop glob n b s .r_2 .c .c_odd := by
  apply hitsWithTop_of_step_lt glob n b s hvalid .r_2 .c .c_odd (by rintro ⟨⟩)
  · dsimp [G_bin, priority_bin]; omega
  · rw [step_r_2_of_not_close glob n b s hnot]
    exact hitsWithTop_c_odd glob n b s hvalid

lemma hitsPortal_r_2_not_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) :
    HitsPortal glob n b s .r_2 .c := by
  apply hitsPortal_of_step glob n b s hvalid .r_2 .c (by rintro ⟨⟩)
  · dsimp [G_bin, priority_bin]; omega
  · rw [step_r_2_of_not_close glob n b s hnot]
    exact hitsPortal_c_odd glob n b s hvalid

lemma hitsWithTop_r_2_odd_not_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) :
    HitsWithTop glob n b s .r_2_odd .c .c_odd := by
  have hn := hvalid.1
  apply hitsWithTop_of_step_lt glob n b s hvalid .r_2_odd .c .c_odd (by rintro ⟨⟩)
  · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin, baseL_bin]; omega
  · exact hitsWithTop_r_2_not_close glob n b s hvalid hnot

lemma hitsPortal_r_2_odd_not_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) :
    HitsPortal glob n b s .r_2_odd .c := by
  have hn := hvalid.1
  apply hitsPortal_of_step glob n b s hvalid .r_2_odd .c (by rintro ⟨⟩)
  · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin, baseL_bin]; omega
  · exact hitsPortal_r_2_not_close glob n b s hvalid hnot

lemma hitsWithTop_r_2_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) :
    HitsWithTop glob n b s .r_2 .r .r_2 :=
  hitsWithTop_of_step_eq glob n b s hvalid .r_2 .r (by rintro ⟨⟩) (step_r_2_of_close glob n b s hclose)

lemma hitsPortal_r_2_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) :
    HitsPortal glob n b s .r_2 .r := by
  apply hitsPortal_of_step glob n b s hvalid .r_2 .r (by rintro ⟨⟩)
  · dsimp [G_bin, priority_bin]; omega
  · rw [step_r_2_of_close glob n b s hclose]
    exact hitsPortal_refl glob n b s hvalid .r (by rintro ⟨⟩)

lemma hitsWithTop_r_2_odd_r_2 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s) :
    HitsWithTop glob n b s .r_2_odd .r_2 .r_2_odd :=
  hitsWithTop_of_step_eq glob n b s hvalid .r_2_odd .r_2 (by rintro ⟨⟩) rfl

lemma hitsWithTop_r_2_odd_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) :
    HitsWithTop glob n b s .r_2_odd .r .r_2 := by
  have hn := hvalid.1
  apply hitsWithTop_of_step_lt glob n b s hvalid .r_2_odd .r .r_2 (by rintro ⟨⟩)
  · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin, baseL_bin]; omega
  · exact hitsWithTop_r_2_close glob n b s hvalid hclose

lemma hitsPortal_r_2_odd_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) :
    HitsPortal glob n b s .r_2_odd .r := by
  have hn := hvalid.1
  apply hitsPortal_of_step glob n b s hvalid .r_2_odd .r (by rintro ⟨⟩)
  · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin, baseL_bin]; omega
  · exact hitsPortal_r_2_close glob n b s hvalid hclose

/-! ### Part 3: `HitsWithTop` and `HitsPortal` for `.a j` and `.b k` -/

lemma hitsWithTop_a_c_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) :
    ∀ (v : ℕ) (hv : v < 3 * (3 * n - 1)),
      v < 3 * (3 * n - 1) - 1 → v ≤ s_a0 glob n b s + 1 →
      HitsWithTop glob n b s (.a ⟨v, hv⟩) .c (.a ⟨v, hv⟩) ∧
      HitsPortal glob n b s (.a ⟨v, hv⟩) .c
  | 0, hv, _, _ => by
    have hn := hvalid.1
    have hstep := step_a_zero glob n b s ⟨0, hv⟩ rfl
    refine ⟨hitsWithTop_of_step_eq glob n b s hvalid (.a ⟨0, hv⟩) .c (by rintro ⟨⟩) hstep, ?_⟩
    apply hitsPortal_of_step glob n b s hvalid (.a ⟨0, hv⟩) .c (by rintro ⟨⟩)
    · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin]; omega
    · rw [hstep]
      exact hitsPortal_refl glob n b s hvalid .c (by rintro ⟨⟩)
  | v + 1, hv, hv_lt, hv_le => by
    have hn := hvalid.1
    have hstep := step_a_pred glob n b s ⟨v + 1, hv⟩ hnot_close (by dsimp; omega) hv_lt hv_le
    rcases hitsWithTop_a_c_aux glob n b s hvalid hnot_close v (by omega) (by omega) (by omega) with
      ⟨htop_prev, hport_prev⟩
    refine ⟨?_, ?_⟩
    · apply hitsWithTop_of_step_gt glob n b s hvalid (.a ⟨v + 1, hv⟩) .c (.a ⟨v, by omega⟩) (by rintro ⟨⟩)
      · dsimp [predRank0]; omega
      · dsimp [G_bin, priority_bin]; omega
      · rw [hstep]; exact htop_prev
    · apply hitsPortal_of_step glob n b s hvalid (.a ⟨v + 1, hv⟩) .c (by rintro ⟨⟩)
      · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin]; omega
      · rw [hstep]; exact hport_prev

lemma hitsWithTop_a_c (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (j : Fin (3 * (3 * n - 1)))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hj_lt : j.val < 3 * (3 * n - 1) - 1) (hj_le : j.val ≤ s_a0 glob n b s + 1) :
    HitsWithTop glob n b s (.a j) .c (.a j) :=
  (hitsWithTop_a_c_aux glob n b s hvalid hnot_close j.val j.isLt hj_lt hj_le).1

lemma hitsPortal_a_c (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (j : Fin (3 * (3 * n - 1)))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hj_lt : j.val < 3 * (3 * n - 1) - 1) (hj_le : j.val ≤ s_a0 glob n b s + 1) :
    HitsPortal glob n b s (.a j) .c :=
  (hitsWithTop_a_c_aux glob n b s hvalid hnot_close j.val j.isLt hj_lt hj_le).2

lemma hitsWithTop_a_r_a (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (j : Fin (3 * (3 * n - 1))) (hj1 : 1 ≤ j.val)
    (hra : (b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) ∨
      s_a0 glob n b s + 1 < j.val ∨ j.val = 3 * (3 * n - 1) - 1) :
    HitsWithTop glob n b s (.a j) .r_a (.a j) :=
  hitsWithTop_of_step_eq glob n b s hvalid (.a j) .r_a (by rintro ⟨⟩)
    (step_a_ra glob n b s j hj1 hra)

lemma hitsWithTop_a_r (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (j : Fin (3 * (3 * n - 1))) (hj1 : 1 ≤ j.val)
    (hra : (b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) ∨
      s_a0 glob n b s + 1 < j.val ∨ j.val = 3 * (3 * n - 1) - 1) :
    HitsWithTop glob n b s (.a j) .r .r_a := by
  have hj := j.isLt
  apply hitsWithTop_of_step_lt glob n b s hvalid (.a j) .r .r_a (by rintro ⟨⟩)
  · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin]; omega
  · rw [step_a_ra glob n b s j hj1 hra]
    exact hitsWithTop_r_a glob n b s hvalid

lemma hitsPortal_a_r (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (j : Fin (3 * (3 * n - 1))) (hj1 : 1 ≤ j.val)
    (hra : (b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) ∨
      s_a0 glob n b s + 1 < j.val ∨ j.val = 3 * (3 * n - 1) - 1) :
    HitsPortal glob n b s (.a j) .r := by
  have hj := j.isLt
  apply hitsPortal_of_step glob n b s hvalid (.a j) .r (by rintro ⟨⟩)
  · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin]; omega
  · rw [step_a_ra glob n b s j hj1 hra]
    exact hitsPortal_r_a glob n b s hvalid

lemma bTarget_val (n : ℕ) (k : Fin (3 * (3 * n - 1))) :
    (bTarget n k).val = if k.val ≤ 2 then k.val else k.val - 1 := by
  unfold bTarget
  split_ifs <;> rfl

lemma bTarget_lt_top (n : ℕ) (k : Fin (3 * (3 * n - 1))) :
    (bTarget n k).val < 3 * (3 * n - 1) - 1 := by
  have hk := k.isLt
  rw [bTarget_val]
  split_ifs <;> omega

lemma priority_a_bTarget_lt_b (n : ℕ) (k : Fin (3 * (3 * n - 1))) :
    (G_bin n).priority (.a (bTarget n k)) < (G_bin n).priority (.b k) := by
  dsimp [G_bin, priority_bin]
  rw [bTarget_val]
  split_ifs <;> omega

lemma priority_b_lt_c (n : ℕ) (k : Fin (3 * (3 * n - 1))) :
    (G_bin n).priority (.b k) < (G_bin n).priority .c := by
  have hk := k.isLt
  dsimp [G_bin, priority_bin, top_bin, Na_bin, M_bin]
  split_ifs <;> omega

lemma priority_b_lt_r_a (n : ℕ) (k : Fin (3 * (3 * n - 1))) :
    (G_bin n).priority (.b k) < (G_bin n).priority .r_a := by
  have hk := k.isLt
  dsimp [G_bin, priority_bin, top_bin, Na_bin, M_bin]
  split_ifs <;> omega

lemma hitsWithTop_b_c (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (k : Fin (3 * (3 * n - 1)))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hk_le : (bTarget n k).val ≤ s_a0 glob n b s + 1) :
    HitsWithTop glob n b s (.b k) .c (.b k) := by
  apply hitsWithTop_of_step_gt glob n b s hvalid (.b k) .c (.a (bTarget n k)) (by rintro ⟨⟩)
  · dsimp [predRank0]; omega
  · exact priority_a_bTarget_lt_b n k
  · rw [step_b]
    exact hitsWithTop_a_c glob n b s hvalid (bTarget n k) hnot_close (bTarget_lt_top n k) hk_le

lemma hitsPortal_b_c (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (k : Fin (3 * (3 * n - 1)))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hk_le : (bTarget n k).val ≤ s_a0 glob n b s + 1) :
    HitsPortal glob n b s (.b k) .c := by
  apply hitsPortal_of_step glob n b s hvalid (.b k) .c (by rintro ⟨⟩)
  · exact priority_b_lt_c n k
  · rw [step_b]
    exact hitsPortal_a_c glob n b s hvalid (bTarget n k) hnot_close (bTarget_lt_top n k) hk_le

lemma hitsWithTop_b_r_a (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (k : Fin (3 * (3 * n - 1))) (hk1 : 1 ≤ (bTarget n k).val)
    (hra : (b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) ∨
      s_a0 glob n b s + 1 < (bTarget n k).val) :
    HitsWithTop glob n b s (.b k) .r_a (.b k) := by
  apply hitsWithTop_of_step_gt glob n b s hvalid (.b k) .r_a (.a (bTarget n k)) (by rintro ⟨⟩)
  · dsimp [predRank0]; omega
  · exact priority_a_bTarget_lt_b n k
  · rw [step_b]
    exact hitsWithTop_a_r_a glob n b s hvalid (bTarget n k) hk1
      (hra.imp id Or.inl)

lemma hitsWithTop_b_r (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (k : Fin (3 * (3 * n - 1))) (hk1 : 1 ≤ (bTarget n k).val)
    (hra : (b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) ∨
      s_a0 glob n b s + 1 < (bTarget n k).val) :
    HitsWithTop glob n b s (.b k) .r .r_a := by
  apply hitsWithTop_of_step_lt glob n b s hvalid (.b k) .r .r_a (by rintro ⟨⟩)
  · exact priority_b_lt_r_a n k
  · rw [step_b]
    exact hitsWithTop_a_r glob n b s hvalid (bTarget n k) hk1
      (hra.imp id Or.inl)

lemma hitsPortal_b_r (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (k : Fin (3 * (3 * n - 1))) (hk1 : 1 ≤ (bTarget n k).val)
    (hra : (b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) ∨
      s_a0 glob n b s + 1 < (bTarget n k).val) :
    HitsPortal glob n b s (.b k) .r := by
  apply hitsPortal_of_step glob n b s hvalid (.b k) .r (by rintro ⟨⟩)
  · exact priority_b_lt_c n k
  · rw [step_b]
    exact hitsPortal_a_r glob n b s hvalid (bTarget n k) hk1
      (hra.imp id Or.inl)

lemma hitsPortal_a_zero (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (j : Fin (3 * (3 * n - 1))) (hj0 : j.val = 0) :
    HitsPortal glob n b s (.a j) .c := by
  have hn := hvalid.1
  have hstep := step_a_zero glob n b s j hj0
  apply hitsPortal_of_step glob n b s hvalid (.a j) .c (by rintro ⟨⟩)
  · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin]; omega
  · rw [hstep]
    exact hitsPortal_refl glob n b s hvalid .c (by rintro ⟨⟩)

/-! ### Part 4: Parity, Priority, and `BestEdgeProp` for `.r_2`, `.a`, `.l1`, `.l2`, `.l3` -/

lemma shift_bin_even (n : ℕ) : shift_bin n % 2 = 0 := by
  dsimp [shift_bin, baseL_bin, M_bin]; omega

lemma top_bin_even (n : ℕ) : top_bin n % 2 = 0 := by
  have h := shift_bin_even n
  dsimp [top_bin, Na_bin, M_bin]; omega

lemma prio_a_odd (n : ℕ) (j : Fin (3 * (3 * n - 1))) :
    (G_bin n).priority (.a j) % 2 = 1 := by
  have h := shift_bin_even n
  dsimp [G_bin, priority_bin]; omega

lemma prio_b_even (n : ℕ) (k : Fin (3 * (3 * n - 1))) :
    (G_bin n).priority (.b k) % 2 = 0 := by
  have h := shift_bin_even n
  dsimp [G_bin, priority_bin]
  split_ifs <;> omega

lemma prio_r_2_odd_odd (n : ℕ) : (G_bin n).priority .r_2_odd % 2 = 1 := by
  have h := shift_bin_even n
  dsimp [G_bin, priority_bin]; omega

lemma prio_r_a_odd (n : ℕ) : (G_bin n).priority .r_a % 2 = 1 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]; omega

lemma prio_r_2_even (n : ℕ) : (G_bin n).priority .r_2 % 2 = 0 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]; omega

lemma prio_c_odd_odd (n : ℕ) : (G_bin n).priority .c_odd % 2 = 1 := by
  have h := top_bin_even n
  dsimp [G_bin, priority_bin]; omega

lemma prio_b_lt_c_odd (n : ℕ) (k : Fin (3 * (3 * n - 1))) :
    (G_bin n).priority (.b k) < (G_bin n).priority .c_odd := by
  have hk := k.isLt
  dsimp [G_bin, priority_bin, top_bin, Na_bin, M_bin]
  split_ifs <;> omega

lemma prio_r_a_lt_r_2 (n : ℕ) :
    (G_bin n).priority .r_a < (G_bin n).priority .r_2 := by
  dsimp [G_bin, priority_bin]; omega

lemma prio_b_mono (n : ℕ) (k₁ k₂ : Fin (3 * (3 * n - 1))) (hlt : k₁.val < k₂.val) :
    (G_bin n).priority (.b k₁) < (G_bin n).priority (.b k₂) := by
  dsimp [G_bin, priority_bin]
  split_ifs <;> omega

lemma s_a0_eq_s_of_not_close_ext (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 1 ∨ s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) :
    s_a0 glob n b s = s := by
  rcases hvalid with ⟨_, _, hs⟩
  unfold s_a0
  split_ifs with h
  · have hmax := maxStep0_of_lt h.1
    omega
  · rfl

lemma bestEdge1_r_2_iff (n b s : ℕ) (hvalid : ValidState n b s) :
    bestEdge1 n b s .r_2 = true ↔
      (b < 2 ^ n - 1 ∧ (s = S_close0 n b + 1 ∨ s = S_close0 n b + 2)) := by
  rcases hvalid with ⟨hn, hb, hs⟩
  unfold bestEdge1 nextPair
  split_ifs with hterm hwrap
  · have : ¬(b < 2 ^ n - 1) := by omega
    simp [chooseEdge1, this]
  · dsimp [chooseEdge1]
    rw [decide_eq_true_eq]
    omega
  · dsimp [chooseEdge1]
    rw [decide_eq_true_eq]
    by_cases hb1 : b < 2 ^ n - 1
    · have := maxStep0_of_lt hb1; omega
    · omega

theorem bestEdge_r_2 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hportal : PortalOrderProp glob n b s) :
    BestEdgeProp glob n b s .r_2 := by
  intro _ _
  have hc : HitsPortal glob n b s .c_odd .c := hitsPortal_c_odd glob n b s hvalid
  have hr : HitsPortal glob n b s .r .r := hitsPortal_refl glob n b s hvalid .r (by rintro ⟨⟩)
  unfold PortalOrderProp at hportal
  by_cases hflip : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 1 ∨ s = S_close0 n b + 2)
  · have hbe : bestEdge1 n b s .r_2 = true := (bestEdge1_r_2_iff n b s hvalid).mpr hflip
    rw [if_pos hflip] at hportal
    unfold bestEdge worstEdge
    rw [if_pos hbe, if_pos hbe]
    exact hportal .c_odd .r hc hr
  · have hbe : bestEdge1 n b s .r_2 = false :=
      Bool.eq_false_of_not_eq_true (mt (bestEdge1_r_2_iff n b s hvalid).mp hflip)
    rw [if_neg hflip] at hportal
    unfold bestEdge worstEdge
    rw [hbe]
    exact hportal .r .c_odd hr hc

theorem bestEdge_a (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hportal : PortalOrderProp glob n b s) (j : Fin (3 * (3 * n - 1))) :
    BestEdgeProp glob n b s (.a j) := by
  intro hown _
  have hj_bounds : 1 ≤ j.val ∧ j.val < 3 * (3 * n - 1) - 1 := by
    dsimp [G_bin, owner_bin] at hown
    by_contra hnot
    have hor : j.val = 0 ∨ j.val = 3 * M_bin n - 1 := by
      have := j.isLt; dsimp [M_bin]; omega
    rw [if_pos hor] at hown
    contradiction
  rcases hj_bounds with ⟨hj1, hj_lt⟩
  have hj0 : j.val ≠ 0 := by omega
  let j' : Fin (3 * (3 * n - 1)) := ⟨j.val - 1, by omega⟩
  have he0 : edge0 n (.a j) = .r_a := by dsimp [edge0]; exact if_neg hj0
  have he1 : edge1 n (.a j) = .a j' := by
    dsimp [edge1, M_bin]
    rw [if_neg hj0, if_neg (by omega)]
  have hra_port : HitsPortal glob n b s .r_a .r := hitsPortal_r_a glob n b s hvalid
  by_cases hflip : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 1 ∨ s = S_close0 n b + 2)
  · have hbe : bestEdge1 n b s (.a j) = false := by
      rcases hvalid with ⟨hn, hb, hs⟩
      unfold bestEdge1 nextPair
      rw [if_neg (by omega), if_neg (by omega)]
      dsimp [chooseEdge1]
      rw [if_pos (by omega)]
    unfold bestEdge worstEdge
    rw [hbe, he0, he1]
    dsimp
    by_cases hj'0 : j'.val = 0
    · have hport_a := hitsPortal_a_zero glob n b s hvalid j' hj'0
      unfold PortalOrderProp at hportal
      rw [if_pos hflip] at hportal
      exact hportal (.a j') .r_a hport_a hra_port
    · by_cases hra_cond : (b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) ∨
          s_a0 glob n b s + 1 < j'.val
      · have htop := hitsWithTop_a_r_a glob n b s hvalid j' (by omega) (hra_cond.imp id Or.inl)
        exact predVal_lt_of_hitsWithTop_odd_self glob n b s hvalid htop (prio_a_odd n j')
      · have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) :=
          fun h => hra_cond (Or.inl h)
        have hj'_le : j'.val ≤ s_a0 glob n b s + 1 := by omega
        have hport_a := hitsPortal_a_c glob n b s hvalid j' hnot_close (by dsimp [j']; omega) hj'_le
        unfold PortalOrderProp at hportal
        rw [if_pos hflip] at hportal
        exact hportal (.a j') .r_a hport_a hra_port
  · by_cases hwrap : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
    · have hbe_iff : bestEdge1 n b s (.a j) = decide (j.val ≤ 1) := by
        unfold bestEdge1 nextPair
        rw [if_neg (by omega), if_pos hwrap]
        dsimp [chooseEdge1]
        rw [if_neg (by unfold S_close0; omega)]
        simp only [Bool.false_eq_true, and_false, ite_false]
        congr 1
        ext
        omega
      by_cases hj_le1 : j.val ≤ 1
      · have hbe : bestEdge1 n b s (.a j) = true := by rw [hbe_iff, decide_eq_true_eq]; exact hj_le1
        unfold bestEdge worstEdge
        rw [if_pos hbe, if_pos hbe, he0, he1]
        have hport_a := hitsPortal_a_zero glob n b s hvalid j' (by dsimp [j']; omega)
        unfold PortalOrderProp at hportal
        rw [if_neg hflip] at hportal
        exact hportal .r_a (.a j') hra_port hport_a
      · have hbe : bestEdge1 n b s (.a j) = false := by rw [hbe_iff, decide_eq_false_iff_not]; exact hj_le1
        unfold bestEdge worstEdge
        rw [hbe, he0, he1]
        dsimp
        have htop := hitsWithTop_a_r_a glob n b s hvalid j' (by dsimp [j']; omega)
          (Or.inl ⟨hwrap.1, Or.inr hwrap.2⟩)
        exact predVal_lt_of_hitsWithTop_odd_self glob n b s hvalid htop (prio_a_odd n j')
    · have hnot_ext : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 1 ∨ s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
        rintro ⟨hb, hs1 | hs2 | hs3⟩
        · exact hflip ⟨hb, Or.inl hs1⟩
        · exact hflip ⟨hb, Or.inr hs2⟩
        · exact hwrap ⟨hb, hs3⟩
      have hsa : s_a0 glob n b s = s := s_a0_eq_s_of_not_close_ext glob n b s hvalid hnot_ext
      have hbe_iff : bestEdge1 n b s (.a j) = decide (j'.val ≤ s + 1) := by
        unfold bestEdge1 nextPair
        split_ifs with hterm
        · dsimp [chooseEdge1]
          rw [if_neg (by omega)]
          simp only [Bool.false_eq_true, and_false, ite_false]
          dsimp [j']
          rw [decide_eq_true (by omega), decide_eq_true (by omega)]
        · dsimp [chooseEdge1]
          rw [if_neg (by omega)]
          simp only [Bool.false_eq_true, and_false, ite_false]
          dsimp [j']
          congr 1
          ext
          omega
      by_cases hj'_le : j'.val ≤ s + 1
      · have hbe : bestEdge1 n b s (.a j) = true := by rw [hbe_iff, decide_eq_true_eq]; exact hj'_le
        unfold bestEdge worstEdge
        rw [if_pos hbe, if_pos hbe, he0, he1]
        have hport_a := hitsPortal_a_c glob n b s hvalid j'
          (by rintro ⟨hb, hs2 | hs3⟩; exact hflip ⟨hb, Or.inr hs2⟩; exact hwrap ⟨hb, hs3⟩)
          (by dsimp [j']; omega) (by rw [hsa]; exact hj'_le)
        unfold PortalOrderProp at hportal
        rw [if_neg hflip] at hportal
        exact hportal .r_a (.a j') hra_port hport_a
      · have hbe : bestEdge1 n b s (.a j) = false := by rw [hbe_iff, decide_eq_false_iff_not]; exact hj'_le
        unfold bestEdge worstEdge
        rw [hbe, he0, he1]
        dsimp
        have htop := hitsWithTop_a_r_a glob n b s hvalid j' (by omega)
          (Or.inr (Or.inl (by rw [hsa]; omega)))
        exact predVal_lt_of_hitsWithTop_odd_self glob n b s hvalid htop (prio_a_odd n j')

lemma val_lt_r2_of_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    {w₀ : V_bin n} (k : Fin (3 * (3 * n - 1))) (hk1 : 1 ≤ (bTarget n k).val)
    (hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))
    (hw : HitsWithTop glob n b s w₀ .r .r_2) :
    ValueLT (G_bin n) (predVal glob n b s (.b k)) (predVal glob n b s w₀) :=
  predVal_lt_of_hitsWithTop_even glob n b s hvalid
    (hitsWithTop_b_r glob n b s hvalid k hk1 (Or.inl hclose))
    hw (prio_r_a_lt_r_2 n) (prio_r_2_even n)

lemma val_lt_b_of_s_eq_close_add_one (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hportal : PortalOrderProp glob n b s)
    {w₀ : V_bin n} (k : Fin (3 * (3 * n - 1))) (hk1 : 1 ≤ (bTarget n k).val)
    (hs1 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 1)
    (hw_top : HitsWithTop glob n b s w₀ .c .c_odd)
    (hw_port : HitsPortal glob n b s w₀ .c) :
    ValueLT (G_bin n) (predVal glob n b s w₀) (predVal glob n b s (.b k)) := by
  have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by omega
  by_cases hk_le : (bTarget n k).val ≤ s_a0 glob n b s + 1
  · exact predVal_lt_of_hitsWithTop_odd glob n b s hvalid
      hw_top (hitsWithTop_b_c glob n b s hvalid k hnot_close hk_le)
      (prio_b_lt_c_odd n k) (prio_c_odd_odd n)
  · unfold PortalOrderProp at hportal
    rw [if_pos ⟨hs1.1, Or.inl hs1.2⟩] at hportal
    exact hportal w₀ (.b k) hw_port (hitsPortal_b_r glob n b s hvalid k hk1 (Or.inr (by omega)))

lemma val_lt_b_of_not_close_ext_le (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    {w₀ : V_bin n} (k : Fin (3 * (3 * n - 1)))
    (hnot_ext : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 1 ∨ s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hk_le : (bTarget n k).val ≤ s + 1)
    (hw_top : HitsWithTop glob n b s w₀ .c .c_odd) :
    ValueLT (G_bin n) (predVal glob n b s w₀) (predVal glob n b s (.b k)) := by
  have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by omega
  have hsa := s_a0_eq_s_of_not_close_ext glob n b s hvalid hnot_ext
  exact predVal_lt_of_hitsWithTop_odd glob n b s hvalid
    hw_top (hitsWithTop_b_c glob n b s hvalid k hnot_close (by rw [hsa]; exact hk_le))
    (prio_b_lt_c_odd n k) (prio_c_odd_odd n)

lemma val_lt_r2_of_not_close_ext_gt (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hportal : PortalOrderProp glob n b s)
    {w₀ : V_bin n} (k : Fin (3 * (3 * n - 1))) (hk1 : 1 ≤ (bTarget n k).val)
    (hnot_ext : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 1 ∨ s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hk_gt : s + 1 < (bTarget n k).val)
    (hw_port : HitsPortal glob n b s w₀ .c) :
    ValueLT (G_bin n) (predVal glob n b s (.b k)) (predVal glob n b s w₀) := by
  have hsa := s_a0_eq_s_of_not_close_ext glob n b s hvalid hnot_ext
  unfold PortalOrderProp at hportal
  rw [if_neg (by omega)] at hportal
  exact hportal (.b k) w₀ (hitsPortal_b_r glob n b s hvalid k hk1 (Or.inr (by rw [hsa]; exact hk_gt))) hw_port

theorem bestEdge_l1 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hportal : PortalOrderProp glob n b s) (m : Fin (3 * n - 1)) :
    BestEdgeProp glob n b s (.l1 m) := by
  intro hown _
  have hm0 : m.val ≠ 0 := by
    dsimp [G_bin, owner_bin] at hown
    by_contra h0
    rw [if_pos h0] at hown
    contradiction
  let k : Fin (3 * (3 * n - 1)) := ⟨3 * m.val, by have := m.isLt; omega⟩
  have hbt : (bTarget n k).val = 3 * m.val - 1 := by
    rw [bTarget_val]; dsimp [k]; rw [if_neg (by omega)]
  have hk1 : 1 ≤ (bTarget n k).val := by omega
  have he0 : edge0 n (.l1 m) = .r_2_odd := by dsimp [edge0]; exact if_neg hm0
  have he1 : edge1 n (.l1 m) = .b k := rfl
  by_cases hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)
  · have hbe : bestEdge1 n b s (.l1 m) = false := by
      unfold bestEdge1 nextPair
      rcases hclose with ⟨hb, hs2 | hs3⟩
      · rw [if_neg (by omega), if_neg (by omega)]
        dsimp [chooseEdge1]
        rw [if_neg hm0, if_neg (by omega), if_pos ⟨hb, by omega⟩]
      · rw [if_neg (by omega), if_pos ⟨hb, hs3⟩]
        dsimp [chooseEdge1]
        rw [if_neg hm0, if_neg (by unfold S_close0; omega), if_neg (by unfold S_close0; omega),
            if_neg (by simp)]
        exact decide_eq_false (by omega)
    unfold bestEdge worstEdge
    rw [hbe, he0, he1]
    exact val_lt_r2_of_close glob n b s hvalid k hk1 hclose (hitsWithTop_r_2_odd_close glob n b s hvalid hclose)
  · by_cases hs1 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 1
    · have hbe : bestEdge1 n b s (.l1 m) = true := by
        unfold bestEdge1 nextPair
        rw [if_neg (by omega), if_neg (by omega)]
        dsimp [chooseEdge1]
        rw [if_neg hm0, if_pos ⟨hs1.1, rfl, by omega⟩]
      unfold bestEdge worstEdge
      rw [if_pos hbe, if_pos hbe, he0, he1]
      exact val_lt_b_of_s_eq_close_add_one glob n b s hvalid hportal k hk1 hs1
        (hitsWithTop_r_2_odd_not_close glob n b s hvalid hclose)
        (hitsPortal_r_2_odd_not_close glob n b s hvalid hclose)
    · have hnot_ext : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 1 ∨ s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
        rintro ⟨hb, h1 | h2 | h3⟩
        · exact hs1 ⟨hb, h1⟩
        · exact hclose ⟨hb, Or.inl h2⟩
        · exact hclose ⟨hb, Or.inr h3⟩
      have hbe_iff : bestEdge1 n b s (.l1 m) = decide ((bTarget n k).val ≤ s + 1) := by
        have hm := m.isLt
        unfold bestEdge1 nextPair
        by_cases hterm : b = 2 ^ n - 1 ∧ s = 9 * n - 4
        · rw [if_pos hterm]
          dsimp [chooseEdge1]
          rw [if_neg hm0, if_neg (by omega), if_neg (by omega), if_neg (by simp)]
          rw [hbt, decide_eq_true (by omega), decide_eq_true (by omega)]
        · rw [if_neg hterm, if_neg (by omega)]
          dsimp [chooseEdge1]
          rw [if_neg hm0, if_neg (by omega), if_neg (by omega), if_neg (by simp)]
          rw [hbt]
          congr 1; ext; omega
      by_cases hk_le : (bTarget n k).val ≤ s + 1
      · have hbe : bestEdge1 n b s (.l1 m) = true := by rw [hbe_iff, decide_eq_true_eq]; exact hk_le
        unfold bestEdge worstEdge
        rw [if_pos hbe, if_pos hbe, he0, he1]
        exact val_lt_b_of_not_close_ext_le glob n b s hvalid k hnot_ext hk_le
          (hitsWithTop_r_2_odd_not_close glob n b s hvalid hclose)
      · have hbe : bestEdge1 n b s (.l1 m) = false := by rw [hbe_iff, decide_eq_false_iff_not]; exact hk_le
        unfold bestEdge worstEdge
        rw [hbe, he0, he1]
        exact val_lt_r2_of_not_close_ext_gt glob n b s hvalid hportal k hk1 hnot_ext (by omega)
          (hitsPortal_r_2_odd_not_close glob n b s hvalid hclose)

theorem bestEdge_l3 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hportal : PortalOrderProp glob n b s) (m : Fin (3 * n - 1)) :
    BestEdgeProp glob n b s (.l3 m) := by
  intro _ _
  let k : Fin (3 * (3 * n - 1)) := ⟨3 * m.val + 1, by have := m.isLt; omega⟩
  have hbt : (bTarget n k).val = if m.val = 0 then 1 else 3 * m.val := by
    rw [bTarget_val]; dsimp [k]; split_ifs <;> omega
  have hk1 : 1 ≤ (bTarget n k).val := by rw [hbt]; split_ifs <;> omega
  have he0 : edge0 n (.l3 m) = .r_2 := rfl
  have he1 : edge1 n (.l3 m) = .b k := rfl
  by_cases hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)
  · have hbe : bestEdge1 n b s (.l3 m) = false := by
      unfold bestEdge1 nextPair
      rcases hclose with ⟨hb, hs2 | hs3⟩
      · rw [if_neg (by omega), if_neg (by omega)]
        dsimp [chooseEdge1]
        rw [if_neg (by omega), if_pos ⟨hb, by omega⟩]
      · rw [if_neg (by omega), if_pos ⟨hb, hs3⟩]
        dsimp [chooseEdge1]
        rw [if_neg (by unfold S_close0; omega), if_neg (by unfold S_close0; omega)]
        by_cases hm0 : m.val = 0
        · rw [if_pos hm0, if_neg (by simp)]; exact decide_eq_false (by omega)
        · rw [if_neg hm0, if_neg (by simp)]; exact decide_eq_false (by omega)
    unfold bestEdge worstEdge
    rw [hbe, he0, he1]
    exact val_lt_r2_of_close glob n b s hvalid k hk1 hclose (hitsWithTop_r_2_close glob n b s hvalid hclose)
  · by_cases hs1 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 1
    · have hbe : bestEdge1 n b s (.l3 m) = true := by
        unfold bestEdge1 nextPair
        rw [if_neg (by omega), if_neg (by omega)]
        dsimp [chooseEdge1]
        rw [if_pos ⟨hs1.1, rfl, by omega⟩]
      unfold bestEdge worstEdge
      rw [if_pos hbe, if_pos hbe, he0, he1]
      exact val_lt_b_of_s_eq_close_add_one glob n b s hvalid hportal k hk1 hs1
        (hitsWithTop_r_2_not_close glob n b s hvalid hclose)
        (hitsPortal_r_2_not_close glob n b s hvalid hclose)
    · have hnot_ext : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 1 ∨ s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
        rintro ⟨hb, h1 | h2 | h3⟩
        · exact hs1 ⟨hb, h1⟩
        · exact hclose ⟨hb, Or.inl h2⟩
        · exact hclose ⟨hb, Or.inr h3⟩
      have hbe_iff : bestEdge1 n b s (.l3 m) = decide ((bTarget n k).val ≤ s + 1) := by
        have hm := m.isLt
        unfold bestEdge1 nextPair
        by_cases hterm : b = 2 ^ n - 1 ∧ s = 9 * n - 4
        · rw [if_pos hterm]
          dsimp [chooseEdge1]
          rw [if_neg (by omega), if_neg (by omega), hbt]
          by_cases hm0 : m.val = 0
          · rw [if_pos hm0, if_pos hm0, if_neg (by simp), decide_eq_true (by omega), decide_eq_true (by omega)]
          · rw [if_neg hm0, if_neg hm0, if_neg (by simp), decide_eq_true (by omega), decide_eq_true (by omega)]
        · rw [if_neg hterm, if_neg (by omega)]
          dsimp [chooseEdge1]
          rw [if_neg (by omega), if_neg (by omega), hbt]
          by_cases hm0 : m.val = 0
          · rw [if_pos hm0, if_pos hm0, if_neg (by simp)]
          · rw [if_neg hm0, if_neg hm0, if_neg (by simp)]
      by_cases hk_le : (bTarget n k).val ≤ s + 1
      · have hbe : bestEdge1 n b s (.l3 m) = true := by rw [hbe_iff, decide_eq_true_eq]; exact hk_le
        unfold bestEdge worstEdge
        rw [if_pos hbe, if_pos hbe, he0, he1]
        exact val_lt_b_of_not_close_ext_le glob n b s hvalid k hnot_ext hk_le
          (hitsWithTop_r_2_not_close glob n b s hvalid hclose)
      · have hbe : bestEdge1 n b s (.l3 m) = false := by rw [hbe_iff, decide_eq_false_iff_not]; exact hk_le
        unfold bestEdge worstEdge
        rw [hbe, he0, he1]
        exact val_lt_r2_of_not_close_ext_gt glob n b s hvalid hportal k hk1 hnot_ext (by omega)
          (hitsPortal_r_2_not_close glob n b s hvalid hclose)

theorem bestEdge_l2 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hportal : PortalOrderProp glob n b s) (m : Fin (3 * n - 1)) :
    BestEdgeProp glob n b s (.l2 m) := by
  intro _ _
  let k : Fin (3 * (3 * n - 1)) := ⟨3 * m.val + 2, by have := m.isLt; omega⟩
  have hbt : (bTarget n k).val = if m.val = 0 then 2 else 3 * m.val + 1 := by
    rw [bTarget_val]; dsimp [k]; split_ifs <;> omega
  have hk1 : 1 ≤ (bTarget n k).val := by rw [hbt]; split_ifs <;> omega
  have he0 : edge0 n (.l2 m) = .r_2 := rfl
  have he1 : edge1 n (.l2 m) = .b k := rfl
  by_cases hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)
  · have hbe : bestEdge1 n b s (.l2 m) = false := by
      unfold bestEdge1 nextPair
      rcases hclose with ⟨hb, hs2 | hs3⟩
      · rw [if_neg (by omega), if_neg (by omega)]
        dsimp [chooseEdge1]
        rw [if_neg (by omega), if_pos ⟨hb, by omega⟩]
      · rw [if_neg (by omega), if_pos ⟨hb, hs3⟩]
        dsimp [chooseEdge1]
        rw [if_neg (by unfold S_close0; omega), if_neg (by unfold S_close0; omega)]
        by_cases hm0 : m.val = 0
        · rw [if_pos hm0, if_neg (by simp)]; exact decide_eq_false (by omega)
        · rw [if_neg hm0, if_neg (by simp)]; exact decide_eq_false (by omega)
    unfold bestEdge worstEdge
    rw [hbe, he0, he1]
    exact val_lt_r2_of_close glob n b s hvalid k hk1 hclose (hitsWithTop_r_2_close glob n b s hvalid hclose)
  · by_cases hs1 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 1
    · have hbe : bestEdge1 n b s (.l2 m) = true := by
        unfold bestEdge1 nextPair
        rw [if_neg (by omega), if_neg (by omega)]
        dsimp [chooseEdge1]
        rw [if_pos ⟨hs1.1, rfl, by omega⟩]
      unfold bestEdge worstEdge
      rw [if_pos hbe, if_pos hbe, he0, he1]
      exact val_lt_b_of_s_eq_close_add_one glob n b s hvalid hportal k hk1 hs1
        (hitsWithTop_r_2_not_close glob n b s hvalid hclose)
        (hitsPortal_r_2_not_close glob n b s hvalid hclose)
    · have hnot_ext : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 1 ∨ s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
        rintro ⟨hb, h1 | h2 | h3⟩
        · exact hs1 ⟨hb, h1⟩
        · exact hclose ⟨hb, Or.inl h2⟩
        · exact hclose ⟨hb, Or.inr h3⟩
      have hbe_iff : bestEdge1 n b s (.l2 m) = decide ((bTarget n k).val ≤ s + 1) := by
        have hm := m.isLt
        unfold bestEdge1 nextPair
        by_cases hterm : b = 2 ^ n - 1 ∧ s = 9 * n - 4
        · rw [if_pos hterm]
          dsimp [chooseEdge1]
          rw [if_neg (by omega), if_neg (by omega), hbt]
          by_cases hm0 : m.val = 0
          · rw [if_pos hm0, if_pos hm0, if_neg (by simp), decide_eq_true (by omega), decide_eq_true (by omega)]
          · rw [if_neg hm0, if_neg hm0, if_neg (by simp), decide_eq_true (by omega), decide_eq_true (by omega)]
        · rw [if_neg hterm, if_neg (by omega)]
          dsimp [chooseEdge1]
          rw [if_neg (by omega), if_neg (by omega), hbt]
          by_cases hm0 : m.val = 0
          · rw [if_pos hm0, if_pos hm0, if_neg (by simp)]
          · rw [if_neg hm0, if_neg hm0, if_neg (by simp)]
      by_cases hk_le : (bTarget n k).val ≤ s + 1
      · have hbe : bestEdge1 n b s (.l2 m) = true := by rw [hbe_iff, decide_eq_true_eq]; exact hk_le
        unfold bestEdge worstEdge
        rw [if_pos hbe, if_pos hbe, he0, he1]
        exact val_lt_b_of_not_close_ext_le glob n b s hvalid k hnot_ext hk_le
          (hitsWithTop_r_2_not_close glob n b s hvalid hclose)
      · have hbe : bestEdge1 n b s (.l2 m) = false := by rw [hbe_iff, decide_eq_false_iff_not]; exact hk_le
        unfold bestEdge worstEdge
        rw [hbe, he0, he1]
        exact val_lt_r2_of_not_close_ext_gt glob n b s hvalid hportal k hk1 hnot_ext (by omega)
          (hitsPortal_r_2_not_close glob n b s hvalid hclose)

/-! ### Part 5: Step, `HitsWithTop`, and `HitsPortal` for `.l*` and `.lp*` -/

lemma baseL_bin_even (n : ℕ) : baseL_bin n % 2 = 0 := by
  dsimp [baseL_bin]; omega

lemma prio_l1_even (n : ℕ) (m : Fin (3 * n - 1)) : (G_bin n).priority (.l1 m) % 2 = 0 := by
  have := baseL_bin_even n; dsimp [G_bin, priority_bin]; omega

lemma prio_l3_even (n : ℕ) (m : Fin (3 * n - 1)) : (G_bin n).priority (.l3 m) % 2 = 0 := by
  have := baseL_bin_even n; dsimp [G_bin, priority_bin]; omega

lemma prio_l2_even (n : ℕ) (m : Fin (3 * n - 1)) : (G_bin n).priority (.l2 m) % 2 = 0 := by
  have := baseL_bin_even n; dsimp [G_bin, priority_bin]; omega

lemma prio_l1_anti (n : ℕ) (m₁ m₂ : Fin (3 * n - 1)) (hlt : m₁.val < m₂.val) :
    (G_bin n).priority (.l1 m₂) < (G_bin n).priority (.l1 m₁) := by
  have := m₁.isLt; have := m₂.isLt
  dsimp [G_bin, priority_bin, M_bin]; omega

lemma prio_l3_anti (n : ℕ) (m₁ m₂ : Fin (3 * n - 1)) (hlt : m₁.val < m₂.val) :
    (G_bin n).priority (.l3 m₂) < (G_bin n).priority (.l3 m₁) := by
  have := m₁.isLt; have := m₂.isLt
  dsimp [G_bin, priority_bin, M_bin]; omega

lemma prio_l2_anti (n : ℕ) (m₁ m₂ : Fin (3 * n - 1)) (hlt : m₁.val < m₂.val) :
    (G_bin n).priority (.l2 m₂) < (G_bin n).priority (.l2 m₁) := by
  have := m₁.isLt; have := m₂.isLt
  dsimp [G_bin, priority_bin, M_bin]; omega

lemma prio_l1_lt_r_2_odd (n : ℕ) (m : Fin (3 * n - 1)) :
    (G_bin n).priority (.l1 m) < (G_bin n).priority .r_2_odd := by
  have := m.isLt; dsimp [G_bin, priority_bin, shift_bin, baseL_bin, M_bin]; omega

lemma prio_l3_lt_r_2_odd (n : ℕ) (m : Fin (3 * n - 1)) :
    (G_bin n).priority (.l3 m) < (G_bin n).priority .r_2_odd := by
  have := m.isLt; dsimp [G_bin, priority_bin, shift_bin, baseL_bin, M_bin]; omega

lemma prio_l2_lt_r_2_odd (n : ℕ) (m : Fin (3 * n - 1)) :
    (G_bin n).priority (.l2 m) < (G_bin n).priority .r_2_odd := by
  have := m.isLt; dsimp [G_bin, priority_bin, shift_bin, baseL_bin, M_bin]; omega

lemma prio_lp1_lt_l1 (n : ℕ) (m₁ m₂ : Fin (3 * n - 1)) :
    (G_bin n).priority (.lp1 m₁) < (G_bin n).priority (.l1 m₂) := by
  have := m₁.isLt; have := m₂.isLt; dsimp [G_bin, priority_bin, M_bin]; omega

lemma prio_lp3_lt_l3 (n : ℕ) (m₁ m₂ : Fin (3 * n - 1)) :
    (G_bin n).priority (.lp3 m₁) < (G_bin n).priority (.l3 m₂) := by
  have := m₁.isLt; have := m₂.isLt; dsimp [G_bin, priority_bin, M_bin]; omega

lemma prio_lp2_lt_l2 (n : ℕ) (m₁ m₂ : Fin (3 * n - 1)) :
    (G_bin n).priority (.lp2 m₁) < (G_bin n).priority (.l2 m₂) := by
  have := m₁.isLt; have := m₂.isLt; dsimp [G_bin, priority_bin, M_bin]; omega

lemma prio_r_2_odd_lt_b (n : ℕ) (k : Fin (3 * (3 * n - 1))) :
    (G_bin n).priority .r_2_odd < (G_bin n).priority (.b k) := by
  dsimp [G_bin, priority_bin]; split_ifs <;> omega

lemma prio_r_2_odd_lt_r_a (n : ℕ) :
    (G_bin n).priority .r_2_odd < (G_bin n).priority .r_a := by
  dsimp [G_bin, priority_bin, top_bin, Na_bin, M_bin]; omega

lemma step_l1_zero (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1)) (hm0 : m.val = 0) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.l1 m) =
      .b ⟨0, by have := m.isLt; omega⟩ := by
  have hown : (G_bin n).owner (.l1 m) = true := by dsimp [G_bin, owner_bin]; exact if_pos hm0
  unfold step
  rw [if_neg (by simp [hown])]
  dsimp [predTau0, chooseTauEdge1, edge0]
  exact if_pos hm0

lemma step_l1_pos_true (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1)) (hm0 : m.val ≠ 0)
    (hce : chooseEdge1 glob n b s (.l1 m) = true) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.l1 m) =
      .b ⟨3 * m.val, by have := m.isLt; omega⟩ := by
  have hown : (G_bin n).owner (.l1 m) = false := by dsimp [G_bin, owner_bin]; exact if_neg hm0
  unfold step; rw [if_pos hown]; unfold predState0; rw [if_pos hce]; rfl

lemma step_l1_pos_false (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1)) (hm0 : m.val ≠ 0)
    (hce : chooseEdge1 glob n b s (.l1 m) = false) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.l1 m) = .r_2_odd := by
  have hown : (G_bin n).owner (.l1 m) = false := by dsimp [G_bin, owner_bin]; exact if_neg hm0
  unfold step; rw [if_pos hown]; unfold predState0; rw [hce]; dsimp [edge0]; exact if_neg hm0

lemma step_l3_true (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1))
    (hce : chooseEdge1 glob n b s (.l3 m) = true) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.l3 m) =
      .b ⟨3 * m.val + 1, by have := m.isLt; omega⟩ := by
  change predState0 glob n b s (.l3 m) = _; unfold predState0; rw [if_pos hce]; rfl

lemma step_l3_false (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1))
    (hce : chooseEdge1 glob n b s (.l3 m) = false) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.l3 m) = .r_2 := by
  change predState0 glob n b s (.l3 m) = _; unfold predState0; rw [hce]; rfl

lemma step_l2_true (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1))
    (hce : chooseEdge1 glob n b s (.l2 m) = true) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.l2 m) =
      .b ⟨3 * m.val + 2, by have := m.isLt; omega⟩ := by
  change predState0 glob n b s (.l2 m) = _; unfold predState0; rw [if_pos hce]; rfl

lemma step_l2_false (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1))
    (hce : chooseEdge1 glob n b s (.l2 m) = false) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.l2 m) = .r_2 := by
  change predState0 glob n b s (.l2 m) = _; unfold predState0; rw [hce]; rfl

lemma step_lp1_zero (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1)) (hm0 : m.val = 0) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.lp1 m) = .l1 m := by
  have hown : (G_bin n).owner (.lp1 m) = true := by dsimp [G_bin, owner_bin]; exact if_pos hm0
  unfold step; rw [if_neg (by simp [hown])]; rfl

lemma step_lp3_zero (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1)) (hm0 : m.val = 0) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.lp3 m) = .l3 m := by
  have hown : (G_bin n).owner (.lp3 m) = true := by dsimp [G_bin, owner_bin]; exact if_pos hm0
  unfold step; rw [if_neg (by simp [hown])]; rfl

lemma step_lp2_zero (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1)) (hm0 : m.val = 0) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.lp2 m) = .l2 m := by
  have hown : (G_bin n).owner (.lp2 m) = true := by dsimp [G_bin, owner_bin]; exact if_pos hm0
  unfold step; rw [if_neg (by simp [hown])]; rfl

lemma step_lp1_pos_true (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1)) (hm0 : m.val ≠ 0)
    (hce : chooseEdge1 glob n b s (.lp1 m) = true) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.lp1 m) =
      .lp1 ⟨m.val - 1, by have := m.isLt; omega⟩ := by
  have hown : (G_bin n).owner (.lp1 m) = false := by dsimp [G_bin, owner_bin]; exact if_neg hm0
  unfold step; rw [if_pos hown]; unfold predState0; rw [if_pos hce]; dsimp [edge1]; exact dif_neg hm0

lemma step_lp1_pos_false (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1)) (hm0 : m.val ≠ 0)
    (hce : chooseEdge1 glob n b s (.lp1 m) = false) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.lp1 m) = .l1 m := by
  have hown : (G_bin n).owner (.lp1 m) = false := by dsimp [G_bin, owner_bin]; exact if_neg hm0
  unfold step; rw [if_pos hown]; unfold predState0; rw [hce]; rfl

lemma step_lp3_pos_true (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1)) (hm0 : m.val ≠ 0)
    (hce : chooseEdge1 glob n b s (.lp3 m) = true) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.lp3 m) =
      .lp3 ⟨m.val - 1, by have := m.isLt; omega⟩ := by
  have hown : (G_bin n).owner (.lp3 m) = false := by dsimp [G_bin, owner_bin]; exact if_neg hm0
  unfold step; rw [if_pos hown]; unfold predState0; rw [if_pos hce]; dsimp [edge1]; exact dif_neg hm0

lemma step_lp3_pos_false (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1)) (hm0 : m.val ≠ 0)
    (hce : chooseEdge1 glob n b s (.lp3 m) = false) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.lp3 m) = .l3 m := by
  have hown : (G_bin n).owner (.lp3 m) = false := by dsimp [G_bin, owner_bin]; exact if_neg hm0
  unfold step; rw [if_pos hown]; unfold predState0; rw [hce]; rfl

lemma step_lp2_pos_true (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1)) (hm0 : m.val ≠ 0)
    (hce : chooseEdge1 glob n b s (.lp2 m) = true) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.lp2 m) =
      .lp2 ⟨m.val - 1, by have := m.isLt; omega⟩ := by
  have hown : (G_bin n).owner (.lp2 m) = false := by dsimp [G_bin, owner_bin]; exact if_neg hm0
  unfold step; rw [if_pos hown]; unfold predState0; rw [if_pos hce]; dsimp [edge1]; exact dif_neg hm0

lemma step_lp2_pos_false (glob : Bool) (n b s : ℕ) (m : Fin (3 * n - 1)) (hm0 : m.val ≠ 0)
    (hce : chooseEdge1 glob n b s (.lp2 m) = false) :
    step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.lp2 m) = .l2 m := by
  have hown : (G_bin n).owner (.lp2 m) = false := by dsimp [G_bin, owner_bin]; exact if_neg hm0
  unfold step; rw [if_pos hown]; unfold predState0; rw [hce]; rfl

lemma hitsWithTop_l1_zero_c (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1)) (hm0 : m.val = 0) :
    HitsWithTop glob n b s (.l1 m) .c (.b ⟨0, by have := m.isLt; omega⟩) ∧
    HitsPortal glob n b s (.l1 m) .c := by
  let b0 : Fin (3 * (3 * n - 1)) := ⟨0, by have := m.isLt; omega⟩
  have hstep := step_l1_zero glob n b s m hm0
  have hb0_step : step (G_bin n) (predState0 glob n b s) (predTau0 n b s) (.b b0) =
      .a ⟨0, by have := m.isLt; omega⟩ := rfl
  have ha0_step := step_a_zero glob n b s ⟨0, by have := m.isLt; omega⟩ rfl
  have ha0_top : HitsWithTop glob n b s (.a ⟨0, by have := m.isLt; omega⟩) .c
      (.a ⟨0, by have := m.isLt; omega⟩) :=
    hitsWithTop_of_step_eq glob n b s hvalid _ .c (by rintro ⟨⟩) ha0_step
  have ha0_port := hitsPortal_a_zero glob n b s hvalid ⟨0, by have := m.isLt; omega⟩ rfl
  have hb0_top : HitsWithTop glob n b s (.b b0) .c (.b b0) := by
    apply hitsWithTop_of_step_gt glob n b s hvalid (.b b0) .c (.a ⟨0, by have := m.isLt; omega⟩) (by rintro ⟨⟩)
    · dsimp [predRank0]; omega
    · exact priority_a_bTarget_lt_b n b0
    · rw [hb0_step]; exact ha0_top
  have hb0_port : HitsPortal glob n b s (.b b0) .c := by
    apply hitsPortal_of_step glob n b s hvalid (.b b0) .c (by rintro ⟨⟩)
    · exact priority_b_lt_c n b0
    · rw [hb0_step]; exact ha0_port
  have hp_lt : (G_bin n).priority (.l1 m) < (G_bin n).priority (.b b0) :=
    lt_trans (prio_l1_lt_r_2_odd n m) (prio_r_2_odd_lt_b n b0)
  refine ⟨?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l1 m) .c (.b b0) (by rintro ⟨⟩) hp_lt
    rw [hstep]; exact hb0_top
  · apply hitsPortal_of_step glob n b s hvalid (.l1 m) .c (by rintro ⟨⟩)
      (lt_trans hp_lt (priority_b_lt_c n b0))
    rw [hstep]; exact hb0_port

lemma hitsWithTop_lp1_zero_c (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1)) (hm0 : m.val = 0) :
    HitsWithTop glob n b s (.lp1 m) .c (.b ⟨0, by have := m.isLt; omega⟩) ∧
    HitsPortal glob n b s (.lp1 m) .c := by
  let b0 : Fin (3 * (3 * n - 1)) := ⟨0, by have := m.isLt; omega⟩
  rcases hitsWithTop_l1_zero_c glob n b s hvalid m hm0 with ⟨hl_top, hl_port⟩
  have hstep := step_lp1_zero glob n b s m hm0
  have hp_lt : (G_bin n).priority (.lp1 m) < (G_bin n).priority (.b b0) :=
    lt_trans (prio_lp1_lt_l1 n m m) (lt_trans (prio_l1_lt_r_2_odd n m) (prio_r_2_odd_lt_b n b0))
  refine ⟨?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp1 m) .c (.b b0) (by rintro ⟨⟩) hp_lt
    rw [hstep]; exact hl_top
  · apply hitsPortal_of_step glob n b s hvalid (.lp1 m) .c (by rintro ⟨⟩)
      (lt_trans hp_lt (priority_b_lt_c n b0))
    rw [hstep]; exact hl_port

lemma priority_b_strictMono (n : ℕ) (k₁ k₂ : Fin (3 * (3 * n - 1))) (hlt : k₁.val < k₂.val) :
    (G_bin n).priority (.b k₁) < (G_bin n).priority (.b k₂) := by
  dsimp [G_bin, priority_bin]
  split_ifs <;> omega

lemma prio_l1_lt_l3 (n : ℕ) (m₁ m₂ : Fin (3 * n - 1)) (hle : m₂.val ≤ m₁.val) :
    (G_bin n).priority (.l1 m₁) < (G_bin n).priority (.l3 m₂) := by
  have := m₁.isLt; have := m₂.isLt
  dsimp [G_bin, priority_bin, M_bin]; omega

lemma prio_l3_lt_l2 (n : ℕ) (m₁ m₂ : Fin (3 * n - 1)) (hle : m₂.val ≤ m₁.val) :
    (G_bin n).priority (.l3 m₁) < (G_bin n).priority (.l2 m₂) := by
  have := m₁.isLt; have := m₂.isLt
  dsimp [G_bin, priority_bin, M_bin]; omega

lemma le_s_a0_add_one_of_not_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) :
    s ≤ s_a0 glob n b s + 1 := by
  have hs_lt := hvalid.2.2
  unfold s_a0
  by_cases h : b < 2 ^ n - 1 ∧ glob = true
  · rw [if_pos h]
    rw [maxStep0_of_lt h.1] at hs_lt
    have : ¬(s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) := fun hc => hnot_close ⟨h.1, hc⟩
    omega
  · rw [if_neg h]; omega

lemma hitsWithTop_b_c_of_le_s (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (k : Fin (3 * (3 * n - 1)))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hk_le : (bTarget n k).val ≤ s) :
    HitsWithTop glob n b s (.b k) .c (.b k) ∧ HitsPortal glob n b s (.b k) .c := by
  have hsa := le_s_a0_add_one_of_not_close glob n b s hvalid hnot_close
  exact ⟨hitsWithTop_b_c glob n b s hvalid k hnot_close (by omega),
    hitsPortal_b_c glob n b s hvalid k hnot_close (by omega)⟩

lemma hitsWithTop_l1_not_close_le (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hle : 3 * m.val ≤ s + 1) :
    HitsWithTop glob n b s (.l1 m) .c (.b ⟨3 * m.val, by have := m.isLt; omega⟩) ∧
    HitsPortal glob n b s (.l1 m) .c := by
  by_cases hm0 : m.val = 0
  · have hkeq : (⟨3 * m.val, by have := m.isLt; omega⟩ : Fin (3 * (3 * n - 1))) =
        ⟨0, by have := m.isLt; omega⟩ := by ext; dsimp; omega
    rw [hkeq]
    exact hitsWithTop_l1_zero_c glob n b s hvalid m hm0
  · let k : Fin (3 * (3 * n - 1)) := ⟨3 * m.val, by have := m.isLt; omega⟩
    have hce : chooseEdge1 glob n b s (.l1 m) = true := by
      dsimp [chooseEdge1]
      rw [if_neg hm0, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact decide_eq_true hle
    have hstep := step_l1_pos_true glob n b s m hm0 hce
    have hk_le : (bTarget n k).val ≤ s := by
      rw [bTarget_val]; dsimp [k]; split_ifs <;> omega
    rcases hitsWithTop_b_c_of_le_s glob n b s hvalid k hnot_close hk_le with ⟨hb_top, hb_port⟩
    have hp_lt : (G_bin n).priority (.l1 m) < (G_bin n).priority (.b k) :=
      lt_trans (prio_l1_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k)
    refine ⟨?_, ?_⟩
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.l1 m) .c (.b k) (by rintro ⟨⟩) hp_lt
      rw [hstep]; exact hb_top
    · apply hitsPortal_of_step glob n b s hvalid (.l1 m) .c (by rintro ⟨⟩)
        (lt_trans hp_lt (priority_b_lt_c n k))
      rw [hstep]; exact hb_port

lemma hitsWithTop_l1_not_close_gt (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hgt : s + 1 < 3 * m.val) :
    HitsWithTop glob n b s (.l1 m) .c .c_odd ∧ HitsPortal glob n b s (.l1 m) .c := by
  have hm0 : m.val ≠ 0 := by omega
  have hce : chooseEdge1 glob n b s (.l1 m) = false := by
    dsimp [chooseEdge1]
    rw [if_neg hm0, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact decide_eq_false (by omega)
  have hstep := step_l1_pos_false glob n b s m hm0 hce
  have hr2o_top : HitsWithTop glob n b s .r_2_odd .c .c_odd := by
    apply hitsWithTop_of_step_lt glob n b s hvalid .r_2_odd .c .c_odd (by rintro ⟨⟩)
    · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin]; omega
    · exact hitsWithTop_r_2_not_close glob n b s hvalid hnot_close
  have hr2o_port : HitsPortal glob n b s .r_2_odd .c := by
    apply hitsPortal_of_step glob n b s hvalid .r_2_odd .c (by rintro ⟨⟩)
    · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin]; omega
    · exact hitsPortal_r_2_not_close glob n b s hvalid hnot_close
  have hp_lt : (G_bin n).priority (.l1 m) < (G_bin n).priority .c_odd := by
    have := prio_l1_lt_r_2_odd n m
    dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at this ⊢; omega
  refine ⟨?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l1 m) .c .c_odd (by rintro ⟨⟩) hp_lt
    rw [hstep]; exact hr2o_top
  · apply hitsPortal_of_step glob n b s hvalid (.l1 m) .c (by rintro ⟨⟩)
      (by dsimp [G_bin, priority_bin] at hp_lt ⊢; omega)
    rw [hstep]; exact hr2o_port

lemma hitsWithTop_l3_not_close_le (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hle : (if m.val = 0 then 1 else 3 * m.val) ≤ s) :
    HitsWithTop glob n b s (.l3 m) .c (.b ⟨3 * m.val + 1, by have := m.isLt; omega⟩) ∧
    HitsPortal glob n b s (.l3 m) .c := by
  let k : Fin (3 * (3 * n - 1)) := ⟨3 * m.val + 1, by have := m.isLt; omega⟩
  have hce : chooseEdge1 glob n b s (.l3 m) = true := by
    dsimp [chooseEdge1]
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases hm0 : m.val = 0
    · rw [if_pos hm0, if_neg (by omega)]; rw [if_pos hm0] at hle; exact decide_eq_true hle
    · rw [if_neg hm0, if_neg (by omega)]; rw [if_neg hm0] at hle; exact decide_eq_true hle
  have hstep := step_l3_true glob n b s m hce
  have hk_le : (bTarget n k).val ≤ s := by
    rw [bTarget_val]; dsimp [k]; split_ifs at hle ⊢ <;> omega
  rcases hitsWithTop_b_c_of_le_s glob n b s hvalid k hnot_close hk_le with ⟨hb_top, hb_port⟩
  have hp_lt : (G_bin n).priority (.l3 m) < (G_bin n).priority (.b k) :=
    lt_trans (prio_l3_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k)
  refine ⟨?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l3 m) .c (.b k) (by rintro ⟨⟩) hp_lt
    rw [hstep]; exact hb_top
  · apply hitsPortal_of_step glob n b s hvalid (.l3 m) .c (by rintro ⟨⟩)
      (lt_trans hp_lt (priority_b_lt_c n k))
    rw [hstep]; exact hb_port

lemma hitsWithTop_l3_not_close_gt (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hgt : s < (if m.val = 0 then 1 else 3 * m.val)) :
    HitsWithTop glob n b s (.l3 m) .c .c_odd ∧ HitsPortal glob n b s (.l3 m) .c := by
  have hce : chooseEdge1 glob n b s (.l3 m) = false := by
    dsimp [chooseEdge1]
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases hm0 : m.val = 0
    · rw [if_pos hm0, if_neg (by omega)]; rw [if_pos hm0] at hgt; exact decide_eq_false (by omega)
    · rw [if_neg hm0, if_neg (by omega)]; rw [if_neg hm0] at hgt; exact decide_eq_false (by omega)
  have hstep := step_l3_false glob n b s m hce
  have hp_lt : (G_bin n).priority (.l3 m) < (G_bin n).priority .c_odd := by
    have := prio_l3_lt_r_2_odd n m
    dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at this ⊢; omega
  refine ⟨?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l3 m) .c .c_odd (by rintro ⟨⟩) hp_lt
    rw [hstep]; exact hitsWithTop_r_2_not_close glob n b s hvalid hnot_close
  · apply hitsPortal_of_step glob n b s hvalid (.l3 m) .c (by rintro ⟨⟩)
      (by dsimp [G_bin, priority_bin] at hp_lt ⊢; omega)
    rw [hstep]; exact hitsPortal_r_2_not_close glob n b s hvalid hnot_close

lemma hitsWithTop_l2_not_close_le (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hle : (if m.val = 0 then 2 else 3 * m.val + 1) ≤ s) :
    HitsWithTop glob n b s (.l2 m) .c (.b ⟨3 * m.val + 2, by have := m.isLt; omega⟩) ∧
    HitsPortal glob n b s (.l2 m) .c := by
  let k : Fin (3 * (3 * n - 1)) := ⟨3 * m.val + 2, by have := m.isLt; omega⟩
  have hce : chooseEdge1 glob n b s (.l2 m) = true := by
    dsimp [chooseEdge1]
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases hm0 : m.val = 0
    · rw [if_pos hm0, if_neg (by omega)]; rw [if_pos hm0] at hle; exact decide_eq_true hle
    · rw [if_neg hm0, if_neg (by omega)]; rw [if_neg hm0] at hle; exact decide_eq_true hle
  have hstep := step_l2_true glob n b s m hce
  have hk_le : (bTarget n k).val ≤ s := by
    rw [bTarget_val]; dsimp [k]; split_ifs at hle ⊢ <;> omega
  rcases hitsWithTop_b_c_of_le_s glob n b s hvalid k hnot_close hk_le with ⟨hb_top, hb_port⟩
  have hp_lt : (G_bin n).priority (.l2 m) < (G_bin n).priority (.b k) :=
    lt_trans (prio_l2_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k)
  refine ⟨?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l2 m) .c (.b k) (by rintro ⟨⟩) hp_lt
    rw [hstep]; exact hb_top
  · apply hitsPortal_of_step glob n b s hvalid (.l2 m) .c (by rintro ⟨⟩)
      (lt_trans hp_lt (priority_b_lt_c n k))
    rw [hstep]; exact hb_port

lemma hitsWithTop_l2_not_close_gt (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hgt : s < (if m.val = 0 then 2 else 3 * m.val + 1)) :
    HitsWithTop glob n b s (.l2 m) .c .c_odd ∧ HitsPortal glob n b s (.l2 m) .c := by
  have hce : chooseEdge1 glob n b s (.l2 m) = false := by
    dsimp [chooseEdge1]
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases hm0 : m.val = 0
    · rw [if_pos hm0, if_neg (by omega)]; rw [if_pos hm0] at hgt; exact decide_eq_false (by omega)
    · rw [if_neg hm0, if_neg (by omega)]; rw [if_neg hm0] at hgt; exact decide_eq_false (by omega)
  have hstep := step_l2_false glob n b s m hce
  have hp_lt : (G_bin n).priority (.l2 m) < (G_bin n).priority .c_odd := by
    have := prio_l2_lt_r_2_odd n m
    dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at this ⊢; omega
  refine ⟨?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l2 m) .c .c_odd (by rintro ⟨⟩) hp_lt
    rw [hstep]; exact hitsWithTop_r_2_not_close glob n b s hvalid hnot_close
  · apply hitsPortal_of_step glob n b s hvalid (.l2 m) .c (by rintro ⟨⟩)
      (by dsimp [G_bin, priority_bin] at hp_lt ⊢; omega)
    rw [hstep]; exact hitsPortal_r_2_not_close glob n b s hvalid hnot_close

lemma hitsWithTop_l1_s_eq_close_add_three (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1)) (hm0 : m.val ≠ 0)
    (hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3) :
    HitsWithTop glob n b s (.l1 m) .r_2_odd (.l1 m) ∧
    HitsWithTop glob n b s (.l1 m) .r_2 .r_2_odd ∧
    HitsWithTop glob n b s (.l1 m) .r .r_2 ∧
    HitsPortal glob n b s (.l1 m) .r := by
  have hce : chooseEdge1 glob n b s (.l1 m) = false := by
    dsimp [chooseEdge1]; rw [if_neg hm0, if_neg (by omega), if_pos hs3]
  have hstep := step_l1_pos_false glob n b s m hm0 hce
  have hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) := ⟨hs3.1, Or.inr hs3.2⟩
  have hp_r2o := prio_l1_lt_r_2_odd n m
  have hp_r2 : (G_bin n).priority (.l1 m) < (G_bin n).priority .r_2 := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_r2o ⊢; omega
  have hp_c : (G_bin n).priority (.l1 m) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin] at hp_r2 ⊢; omega
  refine ⟨hitsWithTop_of_step_eq glob n b s hvalid (.l1 m) .r_2_odd (by rintro ⟨⟩) hstep, ?_, ?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l1 m) .r_2 .r_2_odd (by rintro ⟨⟩) hp_r2o
    rw [hstep]; exact hitsWithTop_r_2_odd_r_2 glob n b s hvalid
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l1 m) .r .r_2 (by rintro ⟨⟩) hp_r2
    rw [hstep]; exact hitsWithTop_r_2_odd_close glob n b s hvalid hclose
  · apply hitsPortal_of_step glob n b s hvalid (.l1 m) .r (by rintro ⟨⟩) hp_c
    rw [hstep]; exact hitsPortal_r_2_odd_close glob n b s hvalid hclose

lemma hitsWithTop_l3_s_eq_close_add_three (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3) :
    HitsWithTop glob n b s (.l3 m) .r_2 (.l3 m) ∧
    HitsWithTop glob n b s (.l3 m) .r .r_2 ∧
    HitsPortal glob n b s (.l3 m) .r := by
  have hce : chooseEdge1 glob n b s (.l3 m) = false := by
    dsimp [chooseEdge1]; rw [if_neg (by omega), if_pos hs3]
  have hstep := step_l3_false glob n b s m hce
  have hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) := ⟨hs3.1, Or.inr hs3.2⟩
  have hp_r2o := prio_l3_lt_r_2_odd n m
  have hp_r2 : (G_bin n).priority (.l3 m) < (G_bin n).priority .r_2 := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_r2o ⊢; omega
  have hp_c : (G_bin n).priority (.l3 m) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin] at hp_r2 ⊢; omega
  refine ⟨hitsWithTop_of_step_eq glob n b s hvalid (.l3 m) .r_2 (by rintro ⟨⟩) hstep, ?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l3 m) .r .r_2 (by rintro ⟨⟩) hp_r2
    rw [hstep]; exact hitsWithTop_r_2_close glob n b s hvalid hclose
  · apply hitsPortal_of_step glob n b s hvalid (.l3 m) .r (by rintro ⟨⟩) hp_c
    rw [hstep]; exact hitsPortal_r_2_close glob n b s hvalid hclose

lemma hitsWithTop_l2_s_eq_close_add_three (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3) :
    HitsWithTop glob n b s (.l2 m) .r_2 (.l2 m) ∧
    HitsWithTop glob n b s (.l2 m) .r .r_2 ∧
    HitsPortal glob n b s (.l2 m) .r := by
  have hce : chooseEdge1 glob n b s (.l2 m) = false := by
    dsimp [chooseEdge1]; rw [if_neg (by omega), if_pos hs3]
  have hstep := step_l2_false glob n b s m hce
  have hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) := ⟨hs3.1, Or.inr hs3.2⟩
  have hp_r2o := prio_l2_lt_r_2_odd n m
  have hp_r2 : (G_bin n).priority (.l2 m) < (G_bin n).priority .r_2 := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_r2o ⊢; omega
  have hp_c : (G_bin n).priority (.l2 m) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin] at hp_r2 ⊢; omega
  refine ⟨hitsWithTop_of_step_eq glob n b s hvalid (.l2 m) .r_2 (by rintro ⟨⟩) hstep, ?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l2 m) .r .r_2 (by rintro ⟨⟩) hp_r2
    rw [hstep]; exact hitsWithTop_r_2_close glob n b s hvalid hclose
  · apply hitsPortal_of_step glob n b s hvalid (.l2 m) .r (by rintro ⟨⟩) hp_c
    rw [hstep]; exact hitsPortal_r_2_close glob n b s hvalid hclose

lemma hitsWithTop_l1_close_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1)) (hm0 : m.val ≠ 0)
    (hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))
    (hce : chooseEdge1 glob n b s (.l1 m) = true) :
    HitsWithTop glob n b s (.l1 m) .r_a (.b ⟨3 * m.val, by have := m.isLt; omega⟩) ∧
    HitsWithTop glob n b s (.l1 m) .r .r_a ∧
    HitsPortal glob n b s (.l1 m) .r := by
  let k : Fin (3 * (3 * n - 1)) := ⟨3 * m.val, by have := m.isLt; omega⟩
  have hk1 : 1 ≤ (bTarget n k).val := by rw [bTarget_val]; dsimp [k]; split_ifs <;> omega
  have hstep := step_l1_pos_true glob n b s m hm0 hce
  have hba_top := hitsWithTop_b_r_a glob n b s hvalid k hk1 (Or.inl hclose)
  have hbr_top := hitsWithTop_b_r glob n b s hvalid k hk1 (Or.inl hclose)
  have hbr_port := hitsPortal_b_r glob n b s hvalid k hk1 (Or.inl hclose)
  have hp_b : (G_bin n).priority (.l1 m) < (G_bin n).priority (.b k) :=
    lt_trans (prio_l1_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k)
  have hp_ra : (G_bin n).priority (.l1 m) < (G_bin n).priority .r_a :=
    lt_trans hp_b (priority_b_lt_r_a n k)
  have hp_c : (G_bin n).priority (.l1 m) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin] at hp_ra ⊢; omega
  refine ⟨?_, ?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l1 m) .r_a (.b k) (by rintro ⟨⟩) hp_b
    rw [hstep]; exact hba_top
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l1 m) .r .r_a (by rintro ⟨⟩) hp_ra
    rw [hstep]; exact hbr_top
  · apply hitsPortal_of_step glob n b s hvalid (.l1 m) .r (by rintro ⟨⟩) hp_c
    rw [hstep]; exact hbr_port

lemma hitsWithTop_l1_close_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1)) (hm0 : m.val ≠ 0)
    (hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))
    (hce : chooseEdge1 glob n b s (.l1 m) = false) :
    HitsWithTop glob n b s (.l1 m) .r .r_2 ∧ HitsPortal glob n b s (.l1 m) .r := by
  have hstep := step_l1_pos_false glob n b s m hm0 hce
  have hp_r2o := prio_l1_lt_r_2_odd n m
  have hp_r2 : (G_bin n).priority (.l1 m) < (G_bin n).priority .r_2 := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_r2o ⊢; omega
  have hp_c : (G_bin n).priority (.l1 m) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin] at hp_r2 ⊢; omega
  refine ⟨?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l1 m) .r .r_2 (by rintro ⟨⟩) hp_r2
    rw [hstep]; exact hitsWithTop_r_2_odd_close glob n b s hvalid hclose
  · apply hitsPortal_of_step glob n b s hvalid (.l1 m) .r (by rintro ⟨⟩) hp_c
    rw [hstep]; exact hitsPortal_r_2_odd_close glob n b s hvalid hclose

lemma hitsWithTop_l3_close_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))
    (hce : chooseEdge1 glob n b s (.l3 m) = true) :
    HitsWithTop glob n b s (.l3 m) .r_a (.b ⟨3 * m.val + 1, by have := m.isLt; omega⟩) ∧
    HitsWithTop glob n b s (.l3 m) .r .r_a ∧
    HitsPortal glob n b s (.l3 m) .r := by
  let k : Fin (3 * (3 * n - 1)) := ⟨3 * m.val + 1, by have := m.isLt; omega⟩
  have hk1 : 1 ≤ (bTarget n k).val := by rw [bTarget_val]; dsimp [k]; split_ifs <;> omega
  have hstep := step_l3_true glob n b s m hce
  have hba_top := hitsWithTop_b_r_a glob n b s hvalid k hk1 (Or.inl hclose)
  have hbr_top := hitsWithTop_b_r glob n b s hvalid k hk1 (Or.inl hclose)
  have hbr_port := hitsPortal_b_r glob n b s hvalid k hk1 (Or.inl hclose)
  have hp_b : (G_bin n).priority (.l3 m) < (G_bin n).priority (.b k) :=
    lt_trans (prio_l3_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k)
  have hp_ra : (G_bin n).priority (.l3 m) < (G_bin n).priority .r_a :=
    lt_trans hp_b (priority_b_lt_r_a n k)
  have hp_c : (G_bin n).priority (.l3 m) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin] at hp_ra ⊢; omega
  refine ⟨?_, ?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l3 m) .r_a (.b k) (by rintro ⟨⟩) hp_b
    rw [hstep]; exact hba_top
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l3 m) .r .r_a (by rintro ⟨⟩) hp_ra
    rw [hstep]; exact hbr_top
  · apply hitsPortal_of_step glob n b s hvalid (.l3 m) .r (by rintro ⟨⟩) hp_c
    rw [hstep]; exact hbr_port

lemma hitsWithTop_l3_close_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))
    (hce : chooseEdge1 glob n b s (.l3 m) = false) :
    HitsWithTop glob n b s (.l3 m) .r .r_2 ∧ HitsPortal glob n b s (.l3 m) .r := by
  have hstep := step_l3_false glob n b s m hce
  have hp_r2o := prio_l3_lt_r_2_odd n m
  have hp_r2 : (G_bin n).priority (.l3 m) < (G_bin n).priority .r_2 := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_r2o ⊢; omega
  have hp_c : (G_bin n).priority (.l3 m) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin] at hp_r2 ⊢; omega
  refine ⟨?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l3 m) .r .r_2 (by rintro ⟨⟩) hp_r2
    rw [hstep]; exact hitsWithTop_r_2_close glob n b s hvalid hclose
  · apply hitsPortal_of_step glob n b s hvalid (.l3 m) .r (by rintro ⟨⟩) hp_c
    rw [hstep]; exact hitsPortal_r_2_close glob n b s hvalid hclose

lemma hitsWithTop_l2_close_true (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))
    (hce : chooseEdge1 glob n b s (.l2 m) = true) :
    HitsWithTop glob n b s (.l2 m) .r_a (.b ⟨3 * m.val + 2, by have := m.isLt; omega⟩) ∧
    HitsWithTop glob n b s (.l2 m) .r .r_a ∧
    HitsPortal glob n b s (.l2 m) .r := by
  let k : Fin (3 * (3 * n - 1)) := ⟨3 * m.val + 2, by have := m.isLt; omega⟩
  have hk1 : 1 ≤ (bTarget n k).val := by rw [bTarget_val]; dsimp [k]; split_ifs <;> omega
  have hstep := step_l2_true glob n b s m hce
  have hba_top := hitsWithTop_b_r_a glob n b s hvalid k hk1 (Or.inl hclose)
  have hbr_top := hitsWithTop_b_r glob n b s hvalid k hk1 (Or.inl hclose)
  have hbr_port := hitsPortal_b_r glob n b s hvalid k hk1 (Or.inl hclose)
  have hp_b : (G_bin n).priority (.l2 m) < (G_bin n).priority (.b k) :=
    lt_trans (prio_l2_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k)
  have hp_ra : (G_bin n).priority (.l2 m) < (G_bin n).priority .r_a :=
    lt_trans hp_b (priority_b_lt_r_a n k)
  have hp_c : (G_bin n).priority (.l2 m) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin] at hp_ra ⊢; omega
  refine ⟨?_, ?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l2 m) .r_a (.b k) (by rintro ⟨⟩) hp_b
    rw [hstep]; exact hba_top
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l2 m) .r .r_a (by rintro ⟨⟩) hp_ra
    rw [hstep]; exact hbr_top
  · apply hitsPortal_of_step glob n b s hvalid (.l2 m) .r (by rintro ⟨⟩) hp_c
    rw [hstep]; exact hbr_port

lemma hitsWithTop_l2_close_false (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))
    (hce : chooseEdge1 glob n b s (.l2 m) = false) :
    HitsWithTop glob n b s (.l2 m) .r .r_2 ∧ HitsPortal glob n b s (.l2 m) .r := by
  have hstep := step_l2_false glob n b s m hce
  have hp_r2o := prio_l2_lt_r_2_odd n m
  have hp_r2 : (G_bin n).priority (.l2 m) < (G_bin n).priority .r_2 := by
    dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_r2o ⊢; omega
  have hp_c : (G_bin n).priority (.l2 m) < (G_bin n).priority .c := by
    dsimp [G_bin, priority_bin] at hp_r2 ⊢; omega
  refine ⟨?_, ?_⟩
  · apply hitsWithTop_of_step_lt glob n b s hvalid (.l2 m) .r .r_2 (by rintro ⟨⟩) hp_r2
    rw [hstep]; exact hitsWithTop_r_2_close glob n b s hvalid hclose
  · apply hitsPortal_of_step glob n b s hvalid (.l2 m) .r (by rintro ⟨⟩) hp_c
    rw [hstep]; exact hitsPortal_r_2_close glob n b s hvalid hclose

/-! ### Part 5b: Induction for `.lp1`, `.lp3`, `.lp2` in the 3 Regimes -/

lemma hitsWithTop_lp1_not_close_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) :
    ∀ (v : ℕ) (hv : v < 3 * n - 1),
      HitsWithTop glob n b s (.lp1 ⟨v, hv⟩) .c
        (.b ⟨3 * min v (s / 3), by omega⟩) ∧
      HitsPortal glob n b s (.lp1 ⟨v, hv⟩) .c
  | 0, hv => by
    simpa using hitsWithTop_lp1_zero_c glob n b s hvalid ⟨0, hv⟩ rfl
  | v + 1, hv => by
    let m : Fin (3 * n - 1) := ⟨v + 1, hv⟩
    have hm0 : m.val ≠ 0 := by dsimp [m]; omega
    by_cases hlt : s < 3 * (v + 1)
    · have hce : chooseEdge1 glob n b s (.lp1 m) = true := by
        dsimp [chooseEdge1]
        rw [if_neg (by omega), if_neg (by omega)]
        exact decide_eq_true hlt
      have hstep := step_lp1_pos_true glob n b s m hm0 hce
      rcases hitsWithTop_lp1_not_close_aux glob n b s hvalid hnot_close v (by omega) with ⟨htop, hport⟩
      let k : Fin (3 * (3 * n - 1)) := ⟨3 * min (v + 1) (s / 3), by omega⟩
      have hkeq : k = ⟨3 * min v (s / 3), by omega⟩ := by ext; dsimp [k]; omega
      have hp_b : (G_bin n).priority (.lp1 m) < (G_bin n).priority (.b k) :=
        lt_trans (prio_lp1_lt_l1 n m m) (lt_trans (prio_l1_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
      refine ⟨?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp1 m) .c (.b k) (by rintro ⟨⟩) hp_b
        rw [hstep, hkeq]; exact htop
      · apply hitsPortal_of_step glob n b s hvalid (.lp1 m) .c (by rintro ⟨⟩)
          (lt_trans hp_b (priority_b_lt_c n k))
        rw [hstep]; exact hport
    · have hce : chooseEdge1 glob n b s (.lp1 m) = false := by
        dsimp [chooseEdge1]
        rw [if_neg (by omega), if_neg (by omega)]
        exact decide_eq_false hlt
      have hstep := step_lp1_pos_false glob n b s m hm0 hce
      rcases hitsWithTop_l1_not_close_le glob n b s hvalid m hnot_close (by dsimp [m]; omega) with
        ⟨htop, hport⟩
      let k : Fin (3 * (3 * n - 1)) := ⟨3 * min (v + 1) (s / 3), by omega⟩
      have hkeq : k = ⟨3 * m.val, by have := m.isLt; omega⟩ := by ext; dsimp [k, m]; omega
      have hp_b : (G_bin n).priority (.lp1 m) < (G_bin n).priority (.b k) :=
        lt_trans (prio_lp1_lt_l1 n m m) (lt_trans (prio_l1_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
      refine ⟨?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp1 m) .c (.b k) (by rintro ⟨⟩) hp_b
        rw [hstep, hkeq]; exact htop
      · apply hitsPortal_of_step glob n b s hvalid (.lp1 m) .c (by rintro ⟨⟩)
          (lt_trans hp_b (priority_b_lt_c n k))
        rw [hstep]; exact hport

lemma hitsWithTop_lp1_not_close (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3))) :
    HitsWithTop glob n b s (.lp1 m) .c (.b ⟨3 * min m.val (s / 3), by have := m.isLt; omega⟩) ∧
    HitsPortal glob n b s (.lp1 m) .c :=
  hitsWithTop_lp1_not_close_aux glob n b s hvalid hnot_close m.val m.isLt

lemma hitsWithTop_lp3_not_close_zero_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hs0 : s = 0) :
    ∀ (v : ℕ) (hv : v < 3 * n - 1),
      HitsWithTop glob n b s (.lp3 ⟨v, hv⟩) .c .c_odd ∧
      HitsPortal glob n b s (.lp3 ⟨v, hv⟩) .c
  | 0, hv => by
    let m : Fin (3 * n - 1) := ⟨0, hv⟩
    have hstep := step_lp3_zero glob n b s m rfl
    rcases hitsWithTop_l3_not_close_gt glob n b s hvalid m hnot_close (by dsimp [m]; omega) with
      ⟨htop, hport⟩
    have hp_lt : (G_bin n).priority (.lp3 m) < (G_bin n).priority .c_odd := by
      have := lt_trans (prio_lp3_lt_l3 n m m) (prio_l3_lt_r_2_odd n m)
      dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at this ⊢; omega
    refine ⟨?_, ?_⟩
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .c .c_odd (by rintro ⟨⟩) hp_lt
      rw [hstep]; exact htop
    · apply hitsPortal_of_step glob n b s hvalid (.lp3 m) .c (by rintro ⟨⟩)
        (by dsimp [G_bin, priority_bin] at hp_lt ⊢; omega)
      rw [hstep]; exact hport
  | v + 1, hv => by
    let m : Fin (3 * n - 1) := ⟨v + 1, hv⟩
    have hm0 : m.val ≠ 0 := by dsimp [m]; omega
    have hce : chooseEdge1 glob n b s (.lp3 m) = true := by
      dsimp [chooseEdge1]; rw [if_neg (by omega)]; exact decide_eq_true (by dsimp [m]; omega)
    have hstep := step_lp3_pos_true glob n b s m hm0 hce
    rcases hitsWithTop_lp3_not_close_zero_aux glob n b s hvalid hnot_close hs0 v (by omega) with
      ⟨htop, hport⟩
    have hp_lt : (G_bin n).priority (.lp3 m) < (G_bin n).priority .c_odd := by
      have := lt_trans (prio_lp3_lt_l3 n m m) (prio_l3_lt_r_2_odd n m)
      dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at this ⊢; omega
    refine ⟨?_, ?_⟩
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .c .c_odd (by rintro ⟨⟩) hp_lt
      rw [hstep]; exact htop
    · apply hitsPortal_of_step glob n b s hvalid (.lp3 m) .c (by rintro ⟨⟩)
        (by dsimp [G_bin, priority_bin] at hp_lt ⊢; omega)
      rw [hstep]; exact hport

lemma hitsWithTop_lp3_not_close_pos_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hs1 : 1 ≤ s) :
    ∀ (v : ℕ) (hv : v < 3 * n - 1),
      HitsWithTop glob n b s (.lp3 ⟨v, hv⟩) .c
        (.b ⟨3 * min v ((s - 1) / 3) + 1, by omega⟩) ∧
      HitsPortal glob n b s (.lp3 ⟨v, hv⟩) .c
  | 0, hv => by
    let m : Fin (3 * n - 1) := ⟨0, hv⟩
    have hstep := step_lp3_zero glob n b s m rfl
    rcases hitsWithTop_l3_not_close_le glob n b s hvalid m hnot_close (by dsimp [m]; omega) with
      ⟨htop, hport⟩
    let k : Fin (3 * (3 * n - 1)) := ⟨1, by omega⟩
    have hp_b : (G_bin n).priority (.lp3 m) < (G_bin n).priority (.b k) :=
      lt_trans (prio_lp3_lt_l3 n m m) (lt_trans (prio_l3_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
    refine ⟨?_, ?_⟩
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .c (.b k) (by rintro ⟨⟩) hp_b
      rw [hstep]; exact htop
    · apply hitsPortal_of_step glob n b s hvalid (.lp3 m) .c (by rintro ⟨⟩)
        (lt_trans hp_b (priority_b_lt_c n k))
      rw [hstep]; exact hport
  | v + 1, hv => by
    let m : Fin (3 * n - 1) := ⟨v + 1, hv⟩
    have hm0 : m.val ≠ 0 := by dsimp [m]; omega
    by_cases hlt : s < 3 * (v + 1) + 1
    · have hce : chooseEdge1 glob n b s (.lp3 m) = true := by
        dsimp [chooseEdge1]; rw [if_neg (by omega)]; exact decide_eq_true hlt
      have hstep := step_lp3_pos_true glob n b s m hm0 hce
      rcases hitsWithTop_lp3_not_close_pos_aux glob n b s hvalid hnot_close hs1 v (by omega) with
        ⟨htop, hport⟩
      let k : Fin (3 * (3 * n - 1)) := ⟨3 * min (v + 1) ((s - 1) / 3) + 1, by omega⟩
      have hkeq : k = ⟨3 * min v ((s - 1) / 3) + 1, by omega⟩ := by ext; dsimp [k]; omega
      have hp_b : (G_bin n).priority (.lp3 m) < (G_bin n).priority (.b k) :=
        lt_trans (prio_lp3_lt_l3 n m m) (lt_trans (prio_l3_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
      refine ⟨?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .c (.b k) (by rintro ⟨⟩) hp_b
        rw [hstep, hkeq]; exact htop
      · apply hitsPortal_of_step glob n b s hvalid (.lp3 m) .c (by rintro ⟨⟩)
          (lt_trans hp_b (priority_b_lt_c n k))
        rw [hstep]; exact hport
    · have hce : chooseEdge1 glob n b s (.lp3 m) = false := by
        dsimp [chooseEdge1]; rw [if_neg (by omega)]; exact decide_eq_false hlt
      have hstep := step_lp3_pos_false glob n b s m hm0 hce
      rcases hitsWithTop_l3_not_close_le glob n b s hvalid m hnot_close
        (by rw [if_neg hm0]; dsimp [m]; omega) with ⟨htop, hport⟩
      let k : Fin (3 * (3 * n - 1)) := ⟨3 * min (v + 1) ((s - 1) / 3) + 1, by omega⟩
      have hkeq : k = ⟨3 * m.val + 1, by have := m.isLt; omega⟩ := by ext; dsimp [k, m]; omega
      have hp_b : (G_bin n).priority (.lp3 m) < (G_bin n).priority (.b k) :=
        lt_trans (prio_lp3_lt_l3 n m m) (lt_trans (prio_l3_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
      refine ⟨?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .c (.b k) (by rintro ⟨⟩) hp_b
        rw [hstep, hkeq]; exact htop
      · apply hitsPortal_of_step glob n b s hvalid (.lp3 m) .c (by rintro ⟨⟩)
          (lt_trans hp_b (priority_b_lt_c n k))
        rw [hstep]; exact hport

lemma hitsWithTop_lp2_not_close_lt_two_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hs2 : s < 2) :
    ∀ (v : ℕ) (hv : v < 3 * n - 1),
      HitsWithTop glob n b s (.lp2 ⟨v, hv⟩) .c .c_odd ∧
      HitsPortal glob n b s (.lp2 ⟨v, hv⟩) .c
  | 0, hv => by
    let m : Fin (3 * n - 1) := ⟨0, hv⟩
    have hstep := step_lp2_zero glob n b s m rfl
    rcases hitsWithTop_l2_not_close_gt glob n b s hvalid m hnot_close (by dsimp [m]; omega) with
      ⟨htop, hport⟩
    have hp_lt : (G_bin n).priority (.lp2 m) < (G_bin n).priority .c_odd := by
      have := lt_trans (prio_lp2_lt_l2 n m m) (prio_l2_lt_r_2_odd n m)
      dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at this ⊢; omega
    refine ⟨?_, ?_⟩
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .c .c_odd (by rintro ⟨⟩) hp_lt
      rw [hstep]; exact htop
    · apply hitsPortal_of_step glob n b s hvalid (.lp2 m) .c (by rintro ⟨⟩)
        (by dsimp [G_bin, priority_bin] at hp_lt ⊢; omega)
      rw [hstep]; exact hport
  | v + 1, hv => by
    let m : Fin (3 * n - 1) := ⟨v + 1, hv⟩
    have hm0 : m.val ≠ 0 := by dsimp [m]; omega
    have hce : chooseEdge1 glob n b s (.lp2 m) = true := by
      dsimp [chooseEdge1]
      rw [if_neg (by omega), if_neg (by omega)]
      exact decide_eq_true (by dsimp [m]; omega)
    have hstep := step_lp2_pos_true glob n b s m hm0 hce
    rcases hitsWithTop_lp2_not_close_lt_two_aux glob n b s hvalid hnot_close hs2 v (by omega) with
      ⟨htop, hport⟩
    have hp_lt : (G_bin n).priority (.lp2 m) < (G_bin n).priority .c_odd := by
      have := lt_trans (prio_lp2_lt_l2 n m m) (prio_l2_lt_r_2_odd n m)
      dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at this ⊢; omega
    refine ⟨?_, ?_⟩
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .c .c_odd (by rintro ⟨⟩) hp_lt
      rw [hstep]; exact htop
    · apply hitsPortal_of_step glob n b s hvalid (.lp2 m) .c (by rintro ⟨⟩)
        (by dsimp [G_bin, priority_bin] at hp_lt ⊢; omega)
      rw [hstep]; exact hport

lemma hitsWithTop_lp2_not_close_ge_two_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hs2 : 2 ≤ s) :
    ∀ (v : ℕ) (hv : v < 3 * n - 1),
      HitsWithTop glob n b s (.lp2 ⟨v, hv⟩) .c
        (.b ⟨3 * min v ((s - 2) / 3) + 2, by omega⟩) ∧
      HitsPortal glob n b s (.lp2 ⟨v, hv⟩) .c
  | 0, hv => by
    let m : Fin (3 * n - 1) := ⟨0, hv⟩
    have hstep := step_lp2_zero glob n b s m rfl
    rcases hitsWithTop_l2_not_close_le glob n b s hvalid m hnot_close (by dsimp [m]; omega) with
      ⟨htop, hport⟩
    let k : Fin (3 * (3 * n - 1)) := ⟨2, by omega⟩
    have hp_b : (G_bin n).priority (.lp2 m) < (G_bin n).priority (.b k) :=
      lt_trans (prio_lp2_lt_l2 n m m) (lt_trans (prio_l2_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
    refine ⟨?_, ?_⟩
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .c (.b k) (by rintro ⟨⟩) hp_b
      rw [hstep]; exact htop
    · apply hitsPortal_of_step glob n b s hvalid (.lp2 m) .c (by rintro ⟨⟩)
        (lt_trans hp_b (priority_b_lt_c n k))
      rw [hstep]; exact hport
  | v + 1, hv => by
    let m : Fin (3 * n - 1) := ⟨v + 1, hv⟩
    have hm0 : m.val ≠ 0 := by dsimp [m]; omega
    by_cases hlt : s < 3 * (v + 1) + 2
    · have hce : chooseEdge1 glob n b s (.lp2 m) = true := by
        dsimp [chooseEdge1]
        rw [if_neg (by omega), if_neg (by omega)]
        exact decide_eq_true hlt
      have hstep := step_lp2_pos_true glob n b s m hm0 hce
      rcases hitsWithTop_lp2_not_close_ge_two_aux glob n b s hvalid hnot_close hs2 v (by omega) with
        ⟨htop, hport⟩
      let k : Fin (3 * (3 * n - 1)) := ⟨3 * min (v + 1) ((s - 2) / 3) + 2, by omega⟩
      have hkeq : k = ⟨3 * min v ((s - 2) / 3) + 2, by omega⟩ := by ext; dsimp [k]; omega
      have hp_b : (G_bin n).priority (.lp2 m) < (G_bin n).priority (.b k) :=
        lt_trans (prio_lp2_lt_l2 n m m) (lt_trans (prio_l2_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
      refine ⟨?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .c (.b k) (by rintro ⟨⟩) hp_b
        rw [hstep, hkeq]; exact htop
      · apply hitsPortal_of_step glob n b s hvalid (.lp2 m) .c (by rintro ⟨⟩)
          (lt_trans hp_b (priority_b_lt_c n k))
        rw [hstep]; exact hport
    · have hce : chooseEdge1 glob n b s (.lp2 m) = false := by
        dsimp [chooseEdge1]
        rw [if_neg (by omega), if_neg (by omega)]
        exact decide_eq_false hlt
      have hstep := step_lp2_pos_false glob n b s m hm0 hce
      rcases hitsWithTop_l2_not_close_le glob n b s hvalid m hnot_close
        (by rw [if_neg hm0]; dsimp [m]; omega) with ⟨htop, hport⟩
      let k : Fin (3 * (3 * n - 1)) := ⟨3 * min (v + 1) ((s - 2) / 3) + 2, by omega⟩
      have hkeq : k = ⟨3 * m.val + 2, by have := m.isLt; omega⟩ := by ext; dsimp [k, m]; omega
      have hp_b : (G_bin n).priority (.lp2 m) < (G_bin n).priority (.b k) :=
        lt_trans (prio_lp2_lt_l2 n m m) (lt_trans (prio_l2_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
      refine ⟨?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .c (.b k) (by rintro ⟨⟩) hp_b
        rw [hstep, hkeq]; exact htop
      · apply hitsPortal_of_step glob n b s hvalid (.lp2 m) .c (by rintro ⟨⟩)
          (lt_trans hp_b (priority_b_lt_c n k))
        rw [hstep]; exact hport

lemma hitsWithTop_lp1_s_eq_close_add_two_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hs2 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 2) :
    ∀ (v : ℕ) (hv : v < 3 * n - 1), 1 ≤ v →
      HitsWithTop glob n b s (.lp1 ⟨v, hv⟩) .r_a (.b ⟨3 * min v (s / 3), by omega⟩) ∧
      HitsWithTop glob n b s (.lp1 ⟨v, hv⟩) .r .r_a ∧
      HitsPortal glob n b s (.lp1 ⟨v, hv⟩) .r
  | 0, _, hv1 => by omega
  | v + 1, hv, _ => by
    have hn := hvalid.1
    have hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) := ⟨hs2.1, Or.inl hs2.2⟩
    let m : Fin (3 * n - 1) := ⟨v + 1, hv⟩
    have hm0 : m.val ≠ 0 := by dsimp [m]; omega
    by_cases hlt : s < 3 * (v + 1)
    · have hv1 : 1 ≤ v := by have := hs2.2; unfold S_close0 at this; omega
      have hce : chooseEdge1 glob n b s (.lp1 m) = true := by
        have := hs2.2; dsimp [chooseEdge1]
        rw [if_neg (by omega)]
        dsimp [m]
        split_ifs <;> (unfold S_close0 at *; exact decide_eq_true (by omega))
      have hstep := step_lp1_pos_true glob n b s m hm0 hce
      rcases hitsWithTop_lp1_s_eq_close_add_two_aux glob n b s hvalid hs2 v (by omega) hv1 with
        ⟨htop_a, htop_r, hport_r⟩
      let k : Fin (3 * (3 * n - 1)) := ⟨3 * min (v + 1) (s / 3), by omega⟩
      have hkeq : k = ⟨3 * min v (s / 3), by omega⟩ := by ext; dsimp [k]; omega
      have hp_b : (G_bin n).priority (.lp1 m) < (G_bin n).priority (.b k) :=
        lt_trans (prio_lp1_lt_l1 n m m) (lt_trans (prio_l1_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
      have hp_ra : (G_bin n).priority (.lp1 m) < (G_bin n).priority .r_a :=
        lt_trans hp_b (priority_b_lt_r_a n k)
      have hp_c : (G_bin n).priority (.lp1 m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin] at hp_ra ⊢; omega
      refine ⟨?_, ?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp1 m) .r_a (.b k) (by rintro ⟨⟩) hp_b
        rw [hstep, hkeq]; exact htop_a
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp1 m) .r .r_a (by rintro ⟨⟩) hp_ra
        rw [hstep]; exact htop_r
      · apply hitsPortal_of_step glob n b s hvalid (.lp1 m) .r (by rintro ⟨⟩) hp_c
        rw [hstep]; exact hport_r
    · have hce : chooseEdge1 glob n b s (.lp1 m) = false := by
        have := hs2.2; dsimp [chooseEdge1]
        rw [if_neg (by omega)]
        dsimp [m]
        split_ifs <;> (unfold S_close0 at *; exact decide_eq_false (by omega))
      have hstep := step_lp1_pos_false glob n b s m hm0 hce
      have hl_ce : chooseEdge1 glob n b s (.l1 m) = true := by
        have := hs2.2; dsimp [chooseEdge1, m]
        split_ifs <;> (unfold S_close0 at *; first | rfl | omega | exact decide_eq_true (by omega))
      rcases hitsWithTop_l1_close_true glob n b s hvalid m hm0 hclose hl_ce with
        ⟨htop_a, htop_r, hport_r⟩
      let k : Fin (3 * (3 * n - 1)) := ⟨3 * min (v + 1) (s / 3), by omega⟩
      have hkeq : k = ⟨3 * m.val, by have := m.isLt; omega⟩ := by ext; dsimp [k, m]; omega
      have hp_b : (G_bin n).priority (.lp1 m) < (G_bin n).priority (.b k) :=
        lt_trans (prio_lp1_lt_l1 n m m) (lt_trans (prio_l1_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
      have hp_ra : (G_bin n).priority (.lp1 m) < (G_bin n).priority .r_a :=
        lt_trans hp_b (priority_b_lt_r_a n k)
      have hp_c : (G_bin n).priority (.lp1 m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin] at hp_ra ⊢; omega
      refine ⟨?_, ?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp1 m) .r_a (.b k) (by rintro ⟨⟩) hp_b
        rw [hstep, hkeq]; exact htop_a
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp1 m) .r .r_a (by rintro ⟨⟩) hp_ra
        rw [hstep]; exact htop_r
      · apply hitsPortal_of_step glob n b s hvalid (.lp1 m) .r (by rintro ⟨⟩) hp_c
        rw [hstep]; exact hport_r

lemma hitsWithTop_lp3_s_eq_close_add_two_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hs2 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 2) :
    ∀ (v : ℕ) (hv : v < 3 * n - 1),
      HitsWithTop glob n b s (.lp3 ⟨v, hv⟩) .r_a (.b ⟨3 * min v ((s - 1) / 3) + 1, by omega⟩) ∧
      HitsWithTop glob n b s (.lp3 ⟨v, hv⟩) .r .r_a ∧
      HitsPortal glob n b s (.lp3 ⟨v, hv⟩) .r
  | 0, hv => by
    have hn := hvalid.1
    have hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) := ⟨hs2.1, Or.inl hs2.2⟩
    let m : Fin (3 * n - 1) := ⟨0, hv⟩
    have hstep := step_lp3_zero glob n b s m rfl
    have hl_ce : chooseEdge1 glob n b s (.l3 m) = true := by
      have := hs2.2; dsimp [chooseEdge1, m]
      split_ifs <;> (unfold S_close0 at *; first | rfl | omega | exact decide_eq_true (by omega))
    rcases hitsWithTop_l3_close_true glob n b s hvalid m hclose hl_ce with
      ⟨htop_a, htop_r, hport_r⟩
    let k : Fin (3 * (3 * n - 1)) := ⟨1, by omega⟩
    have hp_b : (G_bin n).priority (.lp3 m) < (G_bin n).priority (.b k) :=
      lt_trans (prio_lp3_lt_l3 n m m) (lt_trans (prio_l3_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
    have hp_ra : (G_bin n).priority (.lp3 m) < (G_bin n).priority .r_a :=
      lt_trans hp_b (priority_b_lt_r_a n k)
    have hp_c : (G_bin n).priority (.lp3 m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin] at hp_ra ⊢; omega
    refine ⟨?_, ?_, ?_⟩
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r_a (.b k) (by rintro ⟨⟩) hp_b
      rw [hstep]; exact htop_a
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r .r_a (by rintro ⟨⟩) hp_ra
      rw [hstep]; exact htop_r
    · apply hitsPortal_of_step glob n b s hvalid (.lp3 m) .r (by rintro ⟨⟩) hp_c
      rw [hstep]; exact hport_r
  | v + 1, hv => by
    have hn := hvalid.1
    have hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) := ⟨hs2.1, Or.inl hs2.2⟩
    let m : Fin (3 * n - 1) := ⟨v + 1, hv⟩
    have hm0 : m.val ≠ 0 := by dsimp [m]; omega
    by_cases hlt : s < 3 * (v + 1) + 1
    · have hce : chooseEdge1 glob n b s (.lp3 m) = true := by
        dsimp [chooseEdge1]; rw [if_neg (by omega)]; exact decide_eq_true hlt
      have hstep := step_lp3_pos_true glob n b s m hm0 hce
      rcases hitsWithTop_lp3_s_eq_close_add_two_aux glob n b s hvalid hs2 v (by omega) with
        ⟨htop_a, htop_r, hport_r⟩
      let k : Fin (3 * (3 * n - 1)) := ⟨3 * min (v + 1) ((s - 1) / 3) + 1, by omega⟩
      have hkeq : k = ⟨3 * min v ((s - 1) / 3) + 1, by omega⟩ := by ext; dsimp [k]; omega
      have hp_b : (G_bin n).priority (.lp3 m) < (G_bin n).priority (.b k) :=
        lt_trans (prio_lp3_lt_l3 n m m) (lt_trans (prio_l3_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
      have hp_ra : (G_bin n).priority (.lp3 m) < (G_bin n).priority .r_a :=
        lt_trans hp_b (priority_b_lt_r_a n k)
      have hp_c : (G_bin n).priority (.lp3 m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin] at hp_ra ⊢; omega
      refine ⟨?_, ?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r_a (.b k) (by rintro ⟨⟩) hp_b
        rw [hstep, hkeq]; exact htop_a
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r .r_a (by rintro ⟨⟩) hp_ra
        rw [hstep]; exact htop_r
      · apply hitsPortal_of_step glob n b s hvalid (.lp3 m) .r (by rintro ⟨⟩) hp_c
        rw [hstep]; exact hport_r
    · have hce : chooseEdge1 glob n b s (.lp3 m) = false := by
        dsimp [chooseEdge1]; rw [if_neg (by omega)]; exact decide_eq_false hlt
      have hstep := step_lp3_pos_false glob n b s m hm0 hce
      have hl_ce : chooseEdge1 glob n b s (.l3 m) = true := by
        have := hs2.2; dsimp [chooseEdge1, m]
        split_ifs <;> (unfold S_close0 at *; first | rfl | omega | exact decide_eq_true (by omega))
      rcases hitsWithTop_l3_close_true glob n b s hvalid m hclose hl_ce with
        ⟨htop_a, htop_r, hport_r⟩
      let k : Fin (3 * (3 * n - 1)) := ⟨3 * min (v + 1) ((s - 1) / 3) + 1, by omega⟩
      have hkeq : k = ⟨3 * m.val + 1, by have := m.isLt; omega⟩ := by ext; dsimp [k, m]; omega
      have hp_b : (G_bin n).priority (.lp3 m) < (G_bin n).priority (.b k) :=
        lt_trans (prio_lp3_lt_l3 n m m) (lt_trans (prio_l3_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
      have hp_ra : (G_bin n).priority (.lp3 m) < (G_bin n).priority .r_a :=
        lt_trans hp_b (priority_b_lt_r_a n k)
      have hp_c : (G_bin n).priority (.lp3 m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin] at hp_ra ⊢; omega
      refine ⟨?_, ?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r_a (.b k) (by rintro ⟨⟩) hp_b
        rw [hstep, hkeq]; exact htop_a
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r .r_a (by rintro ⟨⟩) hp_ra
        rw [hstep]; exact htop_r
      · apply hitsPortal_of_step glob n b s hvalid (.lp3 m) .r (by rintro ⟨⟩) hp_c
        rw [hstep]; exact hport_r

lemma hitsWithTop_lp2_s_eq_close_add_two_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hs2 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 2) :
    ∀ (v : ℕ) (hv : v < 3 * n - 1),
      HitsWithTop glob n b s (.lp2 ⟨v, hv⟩) .r_a (.b ⟨3 * min v ((s - 2) / 3) + 2, by omega⟩) ∧
      HitsWithTop glob n b s (.lp2 ⟨v, hv⟩) .r .r_a ∧
      HitsPortal glob n b s (.lp2 ⟨v, hv⟩) .r
  | 0, hv => by
    have hn := hvalid.1
    have hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) := ⟨hs2.1, Or.inl hs2.2⟩
    let m : Fin (3 * n - 1) := ⟨0, hv⟩
    have hstep := step_lp2_zero glob n b s m rfl
    have hl_ce : chooseEdge1 glob n b s (.l2 m) = true := by
      have := hs2.2; dsimp [chooseEdge1, m]
      split_ifs <;> (unfold S_close0 at *; first | rfl | omega | exact decide_eq_true (by omega))
    rcases hitsWithTop_l2_close_true glob n b s hvalid m hclose hl_ce with
      ⟨htop_a, htop_r, hport_r⟩
    let k : Fin (3 * (3 * n - 1)) := ⟨2, by omega⟩
    have hp_b : (G_bin n).priority (.lp2 m) < (G_bin n).priority (.b k) :=
      lt_trans (prio_lp2_lt_l2 n m m) (lt_trans (prio_l2_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
    have hp_ra : (G_bin n).priority (.lp2 m) < (G_bin n).priority .r_a :=
      lt_trans hp_b (priority_b_lt_r_a n k)
    have hp_c : (G_bin n).priority (.lp2 m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin] at hp_ra ⊢; omega
    refine ⟨?_, ?_, ?_⟩
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r_a (.b k) (by rintro ⟨⟩) hp_b
      rw [hstep]; exact htop_a
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r .r_a (by rintro ⟨⟩) hp_ra
      rw [hstep]; exact htop_r
    · apply hitsPortal_of_step glob n b s hvalid (.lp2 m) .r (by rintro ⟨⟩) hp_c
      rw [hstep]; exact hport_r
  | v + 1, hv => by
    have hn := hvalid.1
    have hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) := ⟨hs2.1, Or.inl hs2.2⟩
    let m : Fin (3 * n - 1) := ⟨v + 1, hv⟩
    have hm0 : m.val ≠ 0 := by dsimp [m]; omega
    by_cases hlt : s < 3 * (v + 1) + 2
    · have hce : chooseEdge1 glob n b s (.lp2 m) = true := by
        have := hs2.2; dsimp [chooseEdge1]
        rw [if_neg (by omega)]
        dsimp [m]
        split_ifs <;> (unfold S_close0 at *; exact decide_eq_true (by omega))
      have hstep := step_lp2_pos_true glob n b s m hm0 hce
      rcases hitsWithTop_lp2_s_eq_close_add_two_aux glob n b s hvalid hs2 v (by omega) with
        ⟨htop_a, htop_r, hport_r⟩
      let k : Fin (3 * (3 * n - 1)) := ⟨3 * min (v + 1) ((s - 2) / 3) + 2, by omega⟩
      have hkeq : k = ⟨3 * min v ((s - 2) / 3) + 2, by omega⟩ := by ext; dsimp [k]; omega
      have hp_b : (G_bin n).priority (.lp2 m) < (G_bin n).priority (.b k) :=
        lt_trans (prio_lp2_lt_l2 n m m) (lt_trans (prio_l2_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
      have hp_ra : (G_bin n).priority (.lp2 m) < (G_bin n).priority .r_a :=
        lt_trans hp_b (priority_b_lt_r_a n k)
      have hp_c : (G_bin n).priority (.lp2 m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin] at hp_ra ⊢; omega
      refine ⟨?_, ?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r_a (.b k) (by rintro ⟨⟩) hp_b
        rw [hstep, hkeq]; exact htop_a
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r .r_a (by rintro ⟨⟩) hp_ra
        rw [hstep]; exact htop_r
      · apply hitsPortal_of_step glob n b s hvalid (.lp2 m) .r (by rintro ⟨⟩) hp_c
        rw [hstep]; exact hport_r
    · have hce : chooseEdge1 glob n b s (.lp2 m) = false := by
        have := hs2.2; dsimp [chooseEdge1]
        rw [if_neg (by omega)]
        dsimp [m]
        split_ifs <;> (unfold S_close0 at *; exact decide_eq_false (by omega))
      have hstep := step_lp2_pos_false glob n b s m hm0 hce
      have hl_ce : chooseEdge1 glob n b s (.l2 m) = true := by
        have := hs2.2; dsimp [chooseEdge1, m]
        split_ifs <;> (unfold S_close0 at *; first | rfl | omega | exact decide_eq_true (by omega))
      rcases hitsWithTop_l2_close_true glob n b s hvalid m hclose hl_ce with
        ⟨htop_a, htop_r, hport_r⟩
      let k : Fin (3 * (3 * n - 1)) := ⟨3 * min (v + 1) ((s - 2) / 3) + 2, by omega⟩
      have hkeq : k = ⟨3 * m.val + 2, by have := m.isLt; omega⟩ := by ext; dsimp [k, m]; omega
      have hp_b : (G_bin n).priority (.lp2 m) < (G_bin n).priority (.b k) :=
        lt_trans (prio_lp2_lt_l2 n m m) (lt_trans (prio_l2_lt_r_2_odd n m) (prio_r_2_odd_lt_b n k))
      have hp_ra : (G_bin n).priority (.lp2 m) < (G_bin n).priority .r_a :=
        lt_trans hp_b (priority_b_lt_r_a n k)
      have hp_c : (G_bin n).priority (.lp2 m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin] at hp_ra ⊢; omega
      refine ⟨?_, ?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r_a (.b k) (by rintro ⟨⟩) hp_b
        rw [hstep, hkeq]; exact htop_a
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r .r_a (by rintro ⟨⟩) hp_ra
        rw [hstep]; exact htop_r
      · apply hitsPortal_of_step glob n b s hvalid (.lp2 m) .r (by rintro ⟨⟩) hp_c
        rw [hstep]; exact hport_r

def lp13Stop (glob : Bool) (n b v : ℕ) : ℕ :=
  if glob then min v ((S_close0 n b + 1) / 3) else v

def lp2Stop (glob : Bool) (n b v : ℕ) : ℕ :=
  if glob then min v ((S_close0 n b - 1) / 3) else v

lemma lp13Stop_lt (glob : Bool) (n b v : ℕ) (hv : v < 3 * n - 1) :
    lp13Stop glob n b v < 3 * n - 1 := by
  unfold lp13Stop; split_ifs <;> omega

lemma lp2Stop_lt (glob : Bool) (n b v : ℕ) (hv : v < 3 * n - 1) :
    lp2Stop glob n b v < 3 * n - 1 := by
  unfold lp2Stop; split_ifs <;> omega

lemma hitsWithTop_lp1_s_eq_close_add_three_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3) :
    ∀ (v : ℕ) (hv : v < 3 * n - 1), 1 ≤ v →
      HitsWithTop glob n b s (.lp1 ⟨v, hv⟩) .r_2_odd
        (.l1 ⟨lp13Stop glob n b v, lp13Stop_lt glob n b v hv⟩) ∧
      HitsWithTop glob n b s (.lp1 ⟨v, hv⟩) .r_2 .r_2_odd ∧
      HitsWithTop glob n b s (.lp1 ⟨v, hv⟩) .r .r_2 ∧
      HitsPortal glob n b s (.lp1 ⟨v, hv⟩) .r
  | 0, _, hv1 => by omega
  | v + 1, hv, _ => by
    have hn := hvalid.1
    let m : Fin (3 * n - 1) := ⟨v + 1, hv⟩
    have hm0 : m.val ≠ 0 := by dsimp [m]; omega
    by_cases hce : chooseEdge1 glob n b s (.lp1 m) = true
    · have hgt : glob = true ∧ S_close0 n b + 1 < 3 * (v + 1) := by
        dsimp [chooseEdge1] at hce
        rw [if_pos hs3] at hce
        dsimp [m] at hce
        cases glob <;> simp_all
      have hv1 : 1 ≤ v := by have := hgt.2; unfold S_close0 at this; omega
      have hstop : lp13Stop glob n b (v + 1) = lp13Stop glob n b v := by
        rcases hgt with ⟨rfl, hgt2⟩; unfold lp13Stop S_close0 at *; simp; omega
      have hstep := step_lp1_pos_true glob n b s m hm0 hce
      rcases hitsWithTop_lp1_s_eq_close_add_three_aux glob n b s hvalid hs3 v (by omega) hv1 with
        ⟨htop_o, htop_2, htop_r, hport_r⟩
      let m' : Fin (3 * n - 1) := ⟨lp13Stop glob n b (v + 1), lp13Stop_lt glob n b (v + 1) hv⟩
      have hmeq : m' = ⟨lp13Stop glob n b v, lp13Stop_lt glob n b v (by omega)⟩ := by ext; exact hstop
      have hp_l : (G_bin n).priority (.lp1 m) < (G_bin n).priority (.l1 m') := prio_lp1_lt_l1 n m m'
      have hp_o : (G_bin n).priority (.lp1 m) < (G_bin n).priority .r_2_odd :=
        lt_trans hp_l (prio_l1_lt_r_2_odd n m')
      have hp_2 : (G_bin n).priority (.lp1 m) < (G_bin n).priority .r_2 := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_o ⊢; omega
      have hp_c : (G_bin n).priority (.lp1 m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin] at hp_2 ⊢; omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp1 m) .r_2_odd (.l1 m') (by rintro ⟨⟩) hp_l
        rw [hstep, hmeq]; exact htop_o
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp1 m) .r_2 .r_2_odd (by rintro ⟨⟩) hp_o
        rw [hstep]; exact htop_2
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp1 m) .r .r_2 (by rintro ⟨⟩) hp_2
        rw [hstep]; exact htop_r
      · apply hitsPortal_of_step glob n b s hvalid (.lp1 m) .r (by rintro ⟨⟩) hp_c
        rw [hstep]; exact hport_r
    · have hce' : chooseEdge1 glob n b s (.lp1 m) = false := Bool.eq_false_iff.mpr hce
      have hstop : lp13Stop glob n b (v + 1) = v + 1 := by
        dsimp [chooseEdge1] at hce'
        rw [if_pos hs3] at hce'
        dsimp [m] at hce'
        unfold lp13Stop S_close0 at *; (cases glob <;> simp_all); omega
      have hstep := step_lp1_pos_false glob n b s m hm0 hce'
      rcases hitsWithTop_l1_s_eq_close_add_three glob n b s hvalid m hm0 hs3 with
        ⟨htop_o, htop_2, htop_r, hport_r⟩
      let m' : Fin (3 * n - 1) := ⟨lp13Stop glob n b (v + 1), lp13Stop_lt glob n b (v + 1) hv⟩
      have hmeq : m' = m := by ext; exact hstop
      have hp_l : (G_bin n).priority (.lp1 m) < (G_bin n).priority (.l1 m') := prio_lp1_lt_l1 n m m'
      have hp_o : (G_bin n).priority (.lp1 m) < (G_bin n).priority .r_2_odd :=
        lt_trans hp_l (prio_l1_lt_r_2_odd n m')
      have hp_2 : (G_bin n).priority (.lp1 m) < (G_bin n).priority .r_2 := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_o ⊢; omega
      have hp_c : (G_bin n).priority (.lp1 m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin] at hp_2 ⊢; omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp1 m) .r_2_odd (.l1 m') (by rintro ⟨⟩) hp_l
        rw [hstep, hmeq]; exact htop_o
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp1 m) .r_2 .r_2_odd (by rintro ⟨⟩) hp_o
        rw [hstep]; exact htop_2
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp1 m) .r .r_2 (by rintro ⟨⟩) hp_2
        rw [hstep]; exact htop_r
      · apply hitsPortal_of_step glob n b s hvalid (.lp1 m) .r (by rintro ⟨⟩) hp_c
        rw [hstep]; exact hport_r

lemma hitsWithTop_lp3_s_eq_close_add_three_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3) :
    ∀ (v : ℕ) (hv : v < 3 * n - 1),
      HitsWithTop glob n b s (.lp3 ⟨v, hv⟩) .r_2
        (.l3 ⟨lp13Stop glob n b v, lp13Stop_lt glob n b v hv⟩) ∧
      HitsWithTop glob n b s (.lp3 ⟨v, hv⟩) .r .r_2 ∧
      HitsPortal glob n b s (.lp3 ⟨v, hv⟩) .r
  | 0, hv => by
    let m : Fin (3 * n - 1) := ⟨0, hv⟩
    have hstop : lp13Stop glob n b 0 = 0 := by unfold lp13Stop; split_ifs <;> omega
    have hstep := step_lp3_zero glob n b s m rfl
    rcases hitsWithTop_l3_s_eq_close_add_three glob n b s hvalid m hs3 with
      ⟨htop_2, htop_r, hport_r⟩
    let m' : Fin (3 * n - 1) := ⟨lp13Stop glob n b 0, lp13Stop_lt glob n b 0 hv⟩
    have hmeq : m' = m := by ext; exact hstop
    have hp_l : (G_bin n).priority (.lp3 m) < (G_bin n).priority (.l3 m') := prio_lp3_lt_l3 n m m'
    have hp_o : (G_bin n).priority (.lp3 m) < (G_bin n).priority .r_2_odd :=
      lt_trans hp_l (prio_l3_lt_r_2_odd n m')
    have hp_2 : (G_bin n).priority (.lp3 m) < (G_bin n).priority .r_2 := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_o ⊢; omega
    have hp_c : (G_bin n).priority (.lp3 m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin] at hp_2 ⊢; omega
    refine ⟨?_, ?_, ?_⟩
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r_2 (.l3 m') (by rintro ⟨⟩) hp_l
      rw [hstep, hmeq]; exact htop_2
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r .r_2 (by rintro ⟨⟩) hp_2
      rw [hstep]; exact htop_r
    · apply hitsPortal_of_step glob n b s hvalid (.lp3 m) .r (by rintro ⟨⟩) hp_c
      rw [hstep]; exact hport_r
  | v + 1, hv => by
    let m : Fin (3 * n - 1) := ⟨v + 1, hv⟩
    have hm0 : m.val ≠ 0 := by dsimp [m]; omega
    by_cases hce : chooseEdge1 glob n b s (.lp3 m) = true
    · have hgt : glob = true ∧ S_close0 n b + 2 < 3 * (v + 1) + 1 := by
        dsimp [chooseEdge1] at hce
        rw [if_pos hs3] at hce
        dsimp [m] at hce
        cases glob <;> simp_all
      have hstop : lp13Stop glob n b (v + 1) = lp13Stop glob n b v := by
        rcases hgt with ⟨rfl, hgt2⟩; unfold lp13Stop S_close0 at *; simp; omega
      have hstep := step_lp3_pos_true glob n b s m hm0 hce
      rcases hitsWithTop_lp3_s_eq_close_add_three_aux glob n b s hvalid hs3 v (by omega) with
        ⟨htop_2, htop_r, hport_r⟩
      let m' : Fin (3 * n - 1) := ⟨lp13Stop glob n b (v + 1), lp13Stop_lt glob n b (v + 1) hv⟩
      have hmeq : m' = ⟨lp13Stop glob n b v, lp13Stop_lt glob n b v (by omega)⟩ := by ext; exact hstop
      have hp_l : (G_bin n).priority (.lp3 m) < (G_bin n).priority (.l3 m') := prio_lp3_lt_l3 n m m'
      have hp_o : (G_bin n).priority (.lp3 m) < (G_bin n).priority .r_2_odd :=
        lt_trans hp_l (prio_l3_lt_r_2_odd n m')
      have hp_2 : (G_bin n).priority (.lp3 m) < (G_bin n).priority .r_2 := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_o ⊢; omega
      have hp_c : (G_bin n).priority (.lp3 m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin] at hp_2 ⊢; omega
      refine ⟨?_, ?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r_2 (.l3 m') (by rintro ⟨⟩) hp_l
        rw [hstep, hmeq]; exact htop_2
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r .r_2 (by rintro ⟨⟩) hp_2
        rw [hstep]; exact htop_r
      · apply hitsPortal_of_step glob n b s hvalid (.lp3 m) .r (by rintro ⟨⟩) hp_c
        rw [hstep]; exact hport_r
    · have hce' : chooseEdge1 glob n b s (.lp3 m) = false := Bool.eq_false_iff.mpr hce
      have hstop : lp13Stop glob n b (v + 1) = v + 1 := by
        dsimp [chooseEdge1] at hce'
        rw [if_pos hs3] at hce'
        dsimp [m] at hce'
        unfold lp13Stop S_close0 at *; (cases glob <;> simp_all); omega
      have hstep := step_lp3_pos_false glob n b s m hm0 hce'
      rcases hitsWithTop_l3_s_eq_close_add_three glob n b s hvalid m hs3 with
        ⟨htop_2, htop_r, hport_r⟩
      let m' : Fin (3 * n - 1) := ⟨lp13Stop glob n b (v + 1), lp13Stop_lt glob n b (v + 1) hv⟩
      have hmeq : m' = m := by ext; exact hstop
      have hp_l : (G_bin n).priority (.lp3 m) < (G_bin n).priority (.l3 m') := prio_lp3_lt_l3 n m m'
      have hp_o : (G_bin n).priority (.lp3 m) < (G_bin n).priority .r_2_odd :=
        lt_trans hp_l (prio_l3_lt_r_2_odd n m')
      have hp_2 : (G_bin n).priority (.lp3 m) < (G_bin n).priority .r_2 := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_o ⊢; omega
      have hp_c : (G_bin n).priority (.lp3 m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin] at hp_2 ⊢; omega
      refine ⟨?_, ?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r_2 (.l3 m') (by rintro ⟨⟩) hp_l
        rw [hstep, hmeq]; exact htop_2
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r .r_2 (by rintro ⟨⟩) hp_2
        rw [hstep]; exact htop_r
      · apply hitsPortal_of_step glob n b s hvalid (.lp3 m) .r (by rintro ⟨⟩) hp_c
        rw [hstep]; exact hport_r

lemma hitsWithTop_lp2_s_eq_close_add_three_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3) :
    ∀ (v : ℕ) (hv : v < 3 * n - 1),
      HitsWithTop glob n b s (.lp2 ⟨v, hv⟩) .r_2
        (.l2 ⟨lp2Stop glob n b v, lp2Stop_lt glob n b v hv⟩) ∧
      HitsWithTop glob n b s (.lp2 ⟨v, hv⟩) .r .r_2 ∧
      HitsPortal glob n b s (.lp2 ⟨v, hv⟩) .r
  | 0, hv => by
    let m : Fin (3 * n - 1) := ⟨0, hv⟩
    have hstop : lp2Stop glob n b 0 = 0 := by unfold lp2Stop; split_ifs <;> omega
    have hstep := step_lp2_zero glob n b s m rfl
    rcases hitsWithTop_l2_s_eq_close_add_three glob n b s hvalid m hs3 with
      ⟨htop_2, htop_r, hport_r⟩
    let m' : Fin (3 * n - 1) := ⟨lp2Stop glob n b 0, lp2Stop_lt glob n b 0 hv⟩
    have hmeq : m' = m := by ext; exact hstop
    have hp_l : (G_bin n).priority (.lp2 m) < (G_bin n).priority (.l2 m') := prio_lp2_lt_l2 n m m'
    have hp_o : (G_bin n).priority (.lp2 m) < (G_bin n).priority .r_2_odd :=
      lt_trans hp_l (prio_l2_lt_r_2_odd n m')
    have hp_2 : (G_bin n).priority (.lp2 m) < (G_bin n).priority .r_2 := by
      dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_o ⊢; omega
    have hp_c : (G_bin n).priority (.lp2 m) < (G_bin n).priority .c := by
      dsimp [G_bin, priority_bin] at hp_2 ⊢; omega
    refine ⟨?_, ?_, ?_⟩
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r_2 (.l2 m') (by rintro ⟨⟩) hp_l
      rw [hstep, hmeq]; exact htop_2
    · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r .r_2 (by rintro ⟨⟩) hp_2
      rw [hstep]; exact htop_r
    · apply hitsPortal_of_step glob n b s hvalid (.lp2 m) .r (by rintro ⟨⟩) hp_c
      rw [hstep]; exact hport_r
  | v + 1, hv => by
    let m : Fin (3 * n - 1) := ⟨v + 1, hv⟩
    have hm0 : m.val ≠ 0 := by dsimp [m]; omega
    by_cases hce : chooseEdge1 glob n b s (.lp2 m) = true
    · have hgt : glob = true ∧ S_close0 n b + 1 < 3 * (v + 1) + 2 := by
        dsimp [chooseEdge1] at hce
        rw [if_pos hs3] at hce
        dsimp [m] at hce
        cases glob <;> simp_all
      have hstop : lp2Stop glob n b (v + 1) = lp2Stop glob n b v := by
        rcases hgt with ⟨rfl, hgt2⟩; unfold lp2Stop S_close0 at *; simp; omega
      have hstep := step_lp2_pos_true glob n b s m hm0 hce
      rcases hitsWithTop_lp2_s_eq_close_add_three_aux glob n b s hvalid hs3 v (by omega) with
        ⟨htop_2, htop_r, hport_r⟩
      let m' : Fin (3 * n - 1) := ⟨lp2Stop glob n b (v + 1), lp2Stop_lt glob n b (v + 1) hv⟩
      have hmeq : m' = ⟨lp2Stop glob n b v, lp2Stop_lt glob n b v (by omega)⟩ := by ext; exact hstop
      have hp_l : (G_bin n).priority (.lp2 m) < (G_bin n).priority (.l2 m') := prio_lp2_lt_l2 n m m'
      have hp_o : (G_bin n).priority (.lp2 m) < (G_bin n).priority .r_2_odd :=
        lt_trans hp_l (prio_l2_lt_r_2_odd n m')
      have hp_2 : (G_bin n).priority (.lp2 m) < (G_bin n).priority .r_2 := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_o ⊢; omega
      have hp_c : (G_bin n).priority (.lp2 m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin] at hp_2 ⊢; omega
      refine ⟨?_, ?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r_2 (.l2 m') (by rintro ⟨⟩) hp_l
        rw [hstep, hmeq]; exact htop_2
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r .r_2 (by rintro ⟨⟩) hp_2
        rw [hstep]; exact htop_r
      · apply hitsPortal_of_step glob n b s hvalid (.lp2 m) .r (by rintro ⟨⟩) hp_c
        rw [hstep]; exact hport_r
    · have hce' : chooseEdge1 glob n b s (.lp2 m) = false := Bool.eq_false_iff.mpr hce
      have hstop : lp2Stop glob n b (v + 1) = v + 1 := by
        dsimp [chooseEdge1] at hce'
        rw [if_pos hs3] at hce'
        dsimp [m] at hce'
        unfold lp2Stop S_close0 at *; (cases glob <;> simp_all); omega
      have hstep := step_lp2_pos_false glob n b s m hm0 hce'
      rcases hitsWithTop_l2_s_eq_close_add_three glob n b s hvalid m hs3 with
        ⟨htop_2, htop_r, hport_r⟩
      let m' : Fin (3 * n - 1) := ⟨lp2Stop glob n b (v + 1), lp2Stop_lt glob n b (v + 1) hv⟩
      have hmeq : m' = m := by ext; exact hstop
      have hp_l : (G_bin n).priority (.lp2 m) < (G_bin n).priority (.l2 m') := prio_lp2_lt_l2 n m m'
      have hp_o : (G_bin n).priority (.lp2 m) < (G_bin n).priority .r_2_odd :=
        lt_trans hp_l (prio_l2_lt_r_2_odd n m')
      have hp_2 : (G_bin n).priority (.lp2 m) < (G_bin n).priority .r_2 := by
        dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin] at hp_o ⊢; omega
      have hp_c : (G_bin n).priority (.lp2 m) < (G_bin n).priority .c := by
        dsimp [G_bin, priority_bin] at hp_2 ⊢; omega
      refine ⟨?_, ?_, ?_⟩
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r_2 (.l2 m') (by rintro ⟨⟩) hp_l
        rw [hstep, hmeq]; exact htop_2
      · apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r .r_2 (by rintro ⟨⟩) hp_2
        rw [hstep]; exact htop_r
      · apply hitsPortal_of_step glob n b s hvalid (.lp2 m) .r (by rintro ⟨⟩) hp_c
        rw [hstep]; exact hport_r

lemma hitsWithTop_l3_not_close_gt_r2 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hgt : s < (if m.val = 0 then 1 else 3 * m.val)) :
    HitsWithTop glob n b s (.l3 m) .r_2 (.l3 m) := by
  have hce : chooseEdge1 glob n b s (.l3 m) = false := by
    dsimp [chooseEdge1]
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases hm0 : m.val = 0
    · rw [if_pos hm0, if_neg (by omega)]; rw [if_pos hm0] at hgt; exact decide_eq_false (by omega)
    · rw [if_neg hm0, if_neg (by omega)]; rw [if_neg hm0] at hgt; exact decide_eq_false (by omega)
  have hstep := step_l3_false glob n b s m hce
  exact hitsWithTop_of_step_eq glob n b s hvalid (.l3 m) .r_2 (by rintro ⟨⟩) hstep

lemma hitsWithTop_l2_not_close_gt_r2 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (m : Fin (3 * n - 1))
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hgt : s < (if m.val = 0 then 2 else 3 * m.val + 1)) :
    HitsWithTop glob n b s (.l2 m) .r_2 (.l2 m) := by
  have hce : chooseEdge1 glob n b s (.l2 m) = false := by
    dsimp [chooseEdge1]
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases hm0 : m.val = 0
    · rw [if_pos hm0, if_neg (by omega)]; rw [if_pos hm0] at hgt; exact decide_eq_false (by omega)
    · rw [if_neg hm0, if_neg (by omega)]; rw [if_neg hm0] at hgt; exact decide_eq_false (by omega)
  have hstep := step_l2_false glob n b s m hce
  exact hitsWithTop_of_step_eq glob n b s hvalid (.l2 m) .r_2 (by rintro ⟨⟩) hstep

lemma hitsWithTop_lp3_not_close_zero_r2_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hs0 : s = 0) :
    ∀ (v : ℕ) (hv : v < 3 * n - 1),
      HitsWithTop glob n b s (.lp3 ⟨v, hv⟩) .r_2 (.l3 ⟨0, by omega⟩)
  | 0, hv => by
    let m : Fin (3 * n - 1) := ⟨0, hv⟩
    have hstep := step_lp3_zero glob n b s m rfl
    have htop := hitsWithTop_l3_not_close_gt_r2 glob n b s hvalid m hnot_close (by dsimp [m]; omega)
    have hp_l := prio_lp3_lt_l3 n m m
    apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r_2 (.l3 m) (by rintro ⟨⟩) hp_l
    rw [hstep]; exact htop
  | v + 1, hv => by
    let m : Fin (3 * n - 1) := ⟨v + 1, hv⟩
    let m0 : Fin (3 * n - 1) := ⟨0, by omega⟩
    have hm0 : m.val ≠ 0 := by dsimp [m]; omega
    have hce : chooseEdge1 glob n b s (.lp3 m) = true := by
      dsimp [chooseEdge1]; rw [if_neg (by omega)]; exact decide_eq_true (by dsimp [m]; omega)
    have hstep := step_lp3_pos_true glob n b s m hm0 hce
    have htop := hitsWithTop_lp3_not_close_zero_r2_aux glob n b s hvalid hnot_close hs0 v (by omega)
    have hp_l := prio_lp3_lt_l3 n m m0
    apply hitsWithTop_of_step_lt glob n b s hvalid (.lp3 m) .r_2 (.l3 m0) (by rintro ⟨⟩) hp_l
    rw [hstep]; exact htop

lemma hitsWithTop_lp2_not_close_lt_two_r2_aux (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)))
    (hs2 : s < 2) :
    ∀ (v : ℕ) (hv : v < 3 * n - 1),
      HitsWithTop glob n b s (.lp2 ⟨v, hv⟩) .r_2 (.l2 ⟨0, by omega⟩)
  | 0, hv => by
    let m : Fin (3 * n - 1) := ⟨0, hv⟩
    have hstep := step_lp2_zero glob n b s m rfl
    have htop := hitsWithTop_l2_not_close_gt_r2 glob n b s hvalid m hnot_close (by dsimp [m]; omega)
    have hp_l := prio_lp2_lt_l2 n m m
    apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r_2 (.l2 m) (by rintro ⟨⟩) hp_l
    rw [hstep]; exact htop
  | v + 1, hv => by
    let m : Fin (3 * n - 1) := ⟨v + 1, hv⟩
    let m0 : Fin (3 * n - 1) := ⟨0, by omega⟩
    have hm0 : m.val ≠ 0 := by dsimp [m]; omega
    have hce : chooseEdge1 glob n b s (.lp2 m) = true := by
      dsimp [chooseEdge1]
      rw [if_neg (by omega), if_neg (by omega)]
      exact decide_eq_true (by dsimp [m]; omega)
    have hstep := step_lp2_pos_true glob n b s m hm0 hce
    have htop := hitsWithTop_lp2_not_close_lt_two_r2_aux glob n b s hvalid hnot_close hs2 v (by omega)
    have hp_l := prio_lp2_lt_l2 n m m0
    apply hitsWithTop_of_step_lt glob n b s hvalid (.lp2 m) .r_2 (.l2 m0) (by rintro ⟨⟩) hp_l
    rw [hstep]; exact htop

/-! ### Part 6: `BestEdgeProp` for `.lp1`, `.lp3`, `.lp2` -/

theorem bestEdge_lp1 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (hportal : PortalOrderProp glob n b s) (m : Fin (3 * n - 1)) :
    BestEdgeProp glob n b s (.lp1 m) := by
  by_cases hm0 : m.val = 0
  · intro hown; dsimp [G_bin, owner_bin] at hown; rw [if_pos hm0] at hown; cases hown
  · intro _ _
    let m_prev : Fin (3 * n - 1) := ⟨m.val - 1, by have := m.isLt; omega⟩
    have he0 : edge0 n (.lp1 m) = .l1 m := rfl
    have he1 : edge1 n (.lp1 m) = .lp1 m_prev := by dsimp [edge1]; exact dif_neg hm0
    by_cases hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
    · have hbe : bestEdge1 n b s (.lp1 m) = true := by
        unfold bestEdge1 nextPair
        rw [if_neg (by omega), if_pos hs3]
        dsimp [chooseEdge1]
        rw [if_neg hm0, if_neg (by unfold S_close0; omega), if_neg (by simp)]
        exact decide_eq_true (by omega)
      unfold bestEdge worstEdge
      rw [if_pos hbe, if_pos hbe, he0, he1]
      by_cases hm1 : m.val = 1
      · have h_l1_r := (hitsWithTop_l1_s_eq_close_add_three glob n b s hvalid m hm0 hs3).2.2.2
        have h_lp_c := (hitsWithTop_lp1_zero_c glob n b s hvalid m_prev (by dsimp [m_prev]; omega)).2
        unfold PortalOrderProp at hportal
        rw [if_neg (by omega)] at hportal
        exact hportal (.l1 m) (.lp1 m_prev) h_l1_r h_lp_c
      · have hl_top := (hitsWithTop_l1_s_eq_close_add_three glob n b s hvalid m hm0 hs3).1
        have hlp_top := (hitsWithTop_lp1_s_eq_close_add_three_aux glob n b s hvalid hs3
          (m.val - 1) m_prev.isLt (by omega)).1
        apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hl_top hlp_top
        · apply prio_l1_anti
          dsimp [lp13Stop]; split_ifs <;> omega
        · exact prio_l1_even n _
    · by_cases hs2 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 2
      · have hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) := ⟨hs2.1, Or.inl hs2.2⟩
        have hbe : bestEdge1 n b s (.lp1 m) = false := by
          unfold bestEdge1 nextPair
          rw [if_neg (by omega), if_neg (by omega)]
          dsimp [chooseEdge1]
          rw [if_neg hm0, if_pos ⟨hs2.1, by omega⟩]
        unfold bestEdge worstEdge
        rw [hbe, he0, he1]
        by_cases hm1 : m.val = 1
        · have h_lp_c := (hitsWithTop_lp1_zero_c glob n b s hvalid m_prev (by dsimp [m_prev]; omega)).2
          have h_l1_r : HitsPortal glob n b s (.l1 m) .r := by
            by_cases hl_ce : chooseEdge1 glob n b s (.l1 m) = true
            · exact (hitsWithTop_l1_close_true glob n b s hvalid m hm0 hclose hl_ce).2.2
            · exact (hitsWithTop_l1_close_false glob n b s hvalid m hm0 hclose (Bool.eq_false_iff.mpr hl_ce)).2
          unfold PortalOrderProp at hportal
          rw [if_pos ⟨hs2.1, Or.inr hs2.2⟩] at hportal
          exact hportal (.lp1 m_prev) (.l1 m) h_lp_c h_l1_r
        · rcases hitsWithTop_lp1_s_eq_close_add_two_aux glob n b s hvalid hs2
            (m.val - 1) m_prev.isLt (by omega) with ⟨htop_a, htop_r, _⟩
          by_cases hl_ce : chooseEdge1 glob n b s (.l1 m) = true
          · rcases hitsWithTop_l1_close_true glob n b s hvalid m hm0 hclose hl_ce with ⟨hl_a, _, _⟩
            apply predVal_lt_of_hitsWithTop_even glob n b s hvalid htop_a hl_a
            · apply priority_b_strictMono; dsimp; omega
            · exact prio_b_even n _
          · rcases hitsWithTop_l1_close_false glob n b s hvalid m hm0 hclose (Bool.eq_false_iff.mpr hl_ce) with
              ⟨hl_r, _⟩
            apply predVal_lt_of_hitsWithTop_even glob n b s hvalid htop_r hl_r
            · dsimp [G_bin, priority_bin]; omega
            · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin, baseL_bin]; omega
      · have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
          rintro ⟨hb, h2 | h3⟩
          · exact hs2 ⟨hb, h2⟩
          · exact hs3 ⟨hb, h3⟩
        have hbe_iff : bestEdge1 n b s (.lp1 m) = decide (s + 1 < 3 * m.val) := by
          have hm := m.isLt
          unfold bestEdge1 nextPair
          by_cases hterm : b = 2 ^ n - 1 ∧ s = 9 * n - 4
          · rw [if_pos hterm]
            dsimp [chooseEdge1]
            rw [if_neg hm0, if_neg (by omega), if_neg (by simp)]
            rw [decide_eq_false (by omega), decide_eq_false (by omega)]
          · rw [if_neg hterm, if_neg (by omega)]
            dsimp [chooseEdge1]
            rw [if_neg hm0, if_neg (by omega), if_neg (by simp)]
        by_cases hlt : s + 1 < 3 * m.val
        · have hbe : bestEdge1 n b s (.lp1 m) = true := by rw [hbe_iff, decide_eq_true_eq]; exact hlt
          unfold bestEdge worstEdge
          rw [if_pos hbe, if_pos hbe, he0, he1]
          have hl_top := (hitsWithTop_l1_not_close_gt glob n b s hvalid m hnot_close hlt).1
          have hlp_top := (hitsWithTop_lp1_not_close glob n b s hvalid m_prev hnot_close).1
          apply predVal_lt_of_hitsWithTop_odd glob n b s hvalid hl_top hlp_top
          · exact prio_b_lt_c_odd n _
          · exact prio_c_odd_odd n
        · have hbe : bestEdge1 n b s (.lp1 m) = false := by rw [hbe_iff, decide_eq_false_iff_not]; exact hlt
          unfold bestEdge worstEdge
          rw [hbe, he0, he1]
          have hl_top := (hitsWithTop_l1_not_close_le glob n b s hvalid m hnot_close (by omega)).1
          have hlp_top := (hitsWithTop_lp1_not_close glob n b s hvalid m_prev hnot_close).1
          apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hlp_top hl_top
          · apply priority_b_strictMono; dsimp [m_prev]; omega
          · exact prio_b_even n _

theorem bestEdge_lp3 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (_hportal : PortalOrderProp glob n b s) (m : Fin (3 * n - 1)) :
    BestEdgeProp glob n b s (.lp3 m) := by
  by_cases hm0 : m.val = 0
  · intro hown; dsimp [G_bin, owner_bin] at hown; rw [if_pos hm0] at hown; cases hown
  · intro _ _
    let m_prev : Fin (3 * n - 1) := ⟨m.val - 1, by have := m.isLt; omega⟩
    have he0 : edge0 n (.lp3 m) = .l3 m := rfl
    have he1 : edge1 n (.lp3 m) = .lp3 m_prev := by dsimp [edge1]; exact dif_neg hm0
    by_cases hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
    · have hbe : bestEdge1 n b s (.lp3 m) = true := by
        unfold bestEdge1 nextPair
        rw [if_neg (by omega), if_pos hs3]
        dsimp [chooseEdge1]
        rw [if_neg hm0, if_neg (by unfold S_close0; omega)]
        exact decide_eq_true (by omega)
      unfold bestEdge worstEdge
      rw [if_pos hbe, if_pos hbe, he0, he1]
      have hl_top := (hitsWithTop_l3_s_eq_close_add_three glob n b s hvalid m hs3).1
      have hlp_top := (hitsWithTop_lp3_s_eq_close_add_three_aux glob n b s hvalid hs3
        (m.val - 1) m_prev.isLt).1
      apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hl_top hlp_top
      · apply prio_l3_anti
        dsimp [lp13Stop]; split_ifs <;> omega
      · exact prio_l3_even n _
    · by_cases hs2 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 2
      · have hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) := ⟨hs2.1, Or.inl hs2.2⟩
        have hbe : bestEdge1 n b s (.lp3 m) = false := by
          unfold bestEdge1 nextPair
          rw [if_neg (by omega), if_neg (by omega)]
          dsimp [chooseEdge1]
          rw [if_neg hm0, if_pos ⟨hs2.1, by omega⟩]
        unfold bestEdge worstEdge
        rw [hbe, he0, he1]
        rcases hitsWithTop_lp3_s_eq_close_add_two_aux glob n b s hvalid hs2
          (m.val - 1) m_prev.isLt with ⟨htop_a, htop_r, _⟩
        by_cases hl_ce : chooseEdge1 glob n b s (.l3 m) = true
        · rcases hitsWithTop_l3_close_true glob n b s hvalid m hclose hl_ce with ⟨hl_a, _, _⟩
          apply predVal_lt_of_hitsWithTop_even glob n b s hvalid htop_a hl_a
          · apply priority_b_strictMono; dsimp; omega
          · exact prio_b_even n _
        · rcases hitsWithTop_l3_close_false glob n b s hvalid m hclose (Bool.eq_false_iff.mpr hl_ce) with
            ⟨hl_r, _⟩
          apply predVal_lt_of_hitsWithTop_even glob n b s hvalid htop_r hl_r
          · dsimp [G_bin, priority_bin]; omega
          · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin, baseL_bin]; omega
      · have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
          rintro ⟨hb, h2 | h3⟩
          · exact hs2 ⟨hb, h2⟩
          · exact hs3 ⟨hb, h3⟩
        have hbe_iff : bestEdge1 n b s (.lp3 m) = decide (s + 1 < 3 * m.val + 1) := by
          have hm := m.isLt
          unfold bestEdge1 nextPair
          by_cases hterm : b = 2 ^ n - 1 ∧ s = 9 * n - 4
          · rw [if_pos hterm]
            dsimp [chooseEdge1]
            rw [if_neg hm0, if_neg (by omega)]
            rw [decide_eq_false (by omega), decide_eq_false (by omega)]
          · rw [if_neg hterm, if_neg (by omega)]
            dsimp [chooseEdge1]
            rw [if_neg hm0, if_neg (by omega)]
        by_cases hlt : s + 1 < 3 * m.val + 1
        · have hbe : bestEdge1 n b s (.lp3 m) = true := by rw [hbe_iff, decide_eq_true_eq]; exact hlt
          unfold bestEdge worstEdge
          rw [if_pos hbe, if_pos hbe, he0, he1]
          by_cases hs0 : s = 0
          · have hl_top := hitsWithTop_l3_not_close_gt_r2 glob n b s hvalid m hnot_close
              (by rw [if_neg hm0]; omega)
            have hlp_top := hitsWithTop_lp3_not_close_zero_r2_aux glob n b s hvalid hnot_close hs0
              (m.val - 1) m_prev.isLt
            apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hl_top hlp_top
            · apply prio_l3_anti; dsimp; omega
            · exact prio_l3_even n _
          · have hl_top := (hitsWithTop_l3_not_close_gt glob n b s hvalid m hnot_close
              (by rw [if_neg hm0]; omega)).1
            have hlp_top := (hitsWithTop_lp3_not_close_pos_aux glob n b s hvalid hnot_close (by omega)
              (m.val - 1) m_prev.isLt).1
            apply predVal_lt_of_hitsWithTop_odd glob n b s hvalid hl_top hlp_top
            · exact prio_b_lt_c_odd n _
            · exact prio_c_odd_odd n
        · have hbe : bestEdge1 n b s (.lp3 m) = false := by rw [hbe_iff, decide_eq_false_iff_not]; exact hlt
          unfold bestEdge worstEdge
          rw [hbe, he0, he1]
          have hl_top := (hitsWithTop_l3_not_close_le glob n b s hvalid m hnot_close
            (by rw [if_neg hm0]; omega)).1
          have hlp_top := (hitsWithTop_lp3_not_close_pos_aux glob n b s hvalid hnot_close (by omega)
            (m.val - 1) m_prev.isLt).1
          apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hlp_top hl_top
          · apply priority_b_strictMono; dsimp; omega
          · exact prio_b_even n _

theorem bestEdge_lp2 (glob : Bool) (n b s : ℕ) (hvalid : ValidState n b s)
    (_hportal : PortalOrderProp glob n b s) (m : Fin (3 * n - 1)) :
    BestEdgeProp glob n b s (.lp2 m) := by
  by_cases hm0 : m.val = 0
  · intro hown; dsimp [G_bin, owner_bin] at hown; rw [if_pos hm0] at hown; cases hown
  · intro _ _
    let m_prev : Fin (3 * n - 1) := ⟨m.val - 1, by have := m.isLt; omega⟩
    have he0 : edge0 n (.lp2 m) = .l2 m := rfl
    have he1 : edge1 n (.lp2 m) = .lp2 m_prev := by dsimp [edge1]; exact dif_neg hm0
    by_cases hs3 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 3
    · have hbe : bestEdge1 n b s (.lp2 m) = true := by
        unfold bestEdge1 nextPair
        rw [if_neg (by omega), if_pos hs3]
        dsimp [chooseEdge1]
        rw [if_neg hm0, if_neg (by unfold S_close0; omega), if_neg (by simp)]
        exact decide_eq_true (by omega)
      unfold bestEdge worstEdge
      rw [if_pos hbe, if_pos hbe, he0, he1]
      have hl_top := (hitsWithTop_l2_s_eq_close_add_three glob n b s hvalid m hs3).1
      have hlp_top := (hitsWithTop_lp2_s_eq_close_add_three_aux glob n b s hvalid hs3
        (m.val - 1) m_prev.isLt).1
      apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hl_top hlp_top
      · apply prio_l2_anti
        dsimp [lp2Stop]; split_ifs <;> omega
      · exact prio_l2_even n _
    · by_cases hs2 : b < 2 ^ n - 1 ∧ s = S_close0 n b + 2
      · have hclose : b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3) := ⟨hs2.1, Or.inl hs2.2⟩
        have hbe : bestEdge1 n b s (.lp2 m) = false := by
          unfold bestEdge1 nextPair
          rw [if_neg (by omega), if_neg (by omega)]
          dsimp [chooseEdge1]
          rw [if_neg hm0, if_pos ⟨hs2.1, by omega⟩]
        unfold bestEdge worstEdge
        rw [hbe, he0, he1]
        rcases hitsWithTop_lp2_s_eq_close_add_two_aux glob n b s hvalid hs2
          (m.val - 1) m_prev.isLt with ⟨htop_a, htop_r, _⟩
        by_cases hl_ce : chooseEdge1 glob n b s (.l2 m) = true
        · rcases hitsWithTop_l2_close_true glob n b s hvalid m hclose hl_ce with ⟨hl_a, _, _⟩
          apply predVal_lt_of_hitsWithTop_even glob n b s hvalid htop_a hl_a
          · apply priority_b_strictMono; dsimp; omega
          · exact prio_b_even n _
        · rcases hitsWithTop_l2_close_false glob n b s hvalid m hclose (Bool.eq_false_iff.mpr hl_ce) with
            ⟨hl_r, _⟩
          apply predVal_lt_of_hitsWithTop_even glob n b s hvalid htop_r hl_r
          · dsimp [G_bin, priority_bin]; omega
          · dsimp [G_bin, priority_bin, top_bin, shift_bin, Na_bin, M_bin, baseL_bin]; omega
      · have hnot_close : ¬(b < 2 ^ n - 1 ∧ (s = S_close0 n b + 2 ∨ s = S_close0 n b + 3)) := by
          rintro ⟨hb, h2 | h3⟩
          · exact hs2 ⟨hb, h2⟩
          · exact hs3 ⟨hb, h3⟩
        have hbe_iff : bestEdge1 n b s (.lp2 m) = decide (s + 1 < 3 * m.val + 2) := by
          have hm := m.isLt
          unfold bestEdge1 nextPair
          by_cases hterm : b = 2 ^ n - 1 ∧ s = 9 * n - 4
          · rw [if_pos hterm]
            dsimp [chooseEdge1]
            rw [if_neg hm0, if_neg (by omega), if_neg (by simp)]
            rw [decide_eq_false (by omega), decide_eq_false (by omega)]
          · rw [if_neg hterm, if_neg (by omega)]
            dsimp [chooseEdge1]
            rw [if_neg hm0, if_neg (by omega), if_neg (by simp)]
        by_cases hlt : s + 1 < 3 * m.val + 2
        · have hbe : bestEdge1 n b s (.lp2 m) = true := by rw [hbe_iff, decide_eq_true_eq]; exact hlt
          unfold bestEdge worstEdge
          rw [if_pos hbe, if_pos hbe, he0, he1]
          by_cases hs_lt2 : s < 2
          · have hl_top := hitsWithTop_l2_not_close_gt_r2 glob n b s hvalid m hnot_close
              (by rw [if_neg hm0]; omega)
            have hlp_top := hitsWithTop_lp2_not_close_lt_two_r2_aux glob n b s hvalid hnot_close hs_lt2
              (m.val - 1) m_prev.isLt
            apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hl_top hlp_top
            · apply prio_l2_anti; dsimp; omega
            · exact prio_l2_even n _
          · have hl_top := (hitsWithTop_l2_not_close_gt glob n b s hvalid m hnot_close
              (by rw [if_neg hm0]; omega)).1
            have hlp_top := (hitsWithTop_lp2_not_close_ge_two_aux glob n b s hvalid hnot_close (by omega)
              (m.val - 1) m_prev.isLt).1
            apply predVal_lt_of_hitsWithTop_odd glob n b s hvalid hl_top hlp_top
            · exact prio_b_lt_c_odd n _
            · exact prio_c_odd_odd n
        · have hbe : bestEdge1 n b s (.lp2 m) = false := by rw [hbe_iff, decide_eq_false_iff_not]; exact hlt
          unfold bestEdge worstEdge
          rw [hbe, he0, he1]
          have hl_top := (hitsWithTop_l2_not_close_le glob n b s hvalid m hnot_close
            (by rw [if_neg hm0]; omega)).1
          have hlp_top := (hitsWithTop_lp2_not_close_ge_two_aux glob n b s hvalid hnot_close (by omega)
            (m.val - 1) m_prev.isLt).1
          apply predVal_lt_of_hitsWithTop_even glob n b s hvalid hlp_top hl_top
          · apply priority_b_strictMono; dsimp; omega
          · exact prio_b_even n _

end FriedmannParity


