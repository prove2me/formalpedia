-- Prove2me | solution 1 for A166944Research.a166944_target_of_two_caps
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-15T06:25:33.315042+00:00
-- url     : https://prove2.me/submissions/e3cce0c1-4349-4e45-a993-a8f7427e7fe5

import Definitions.Def_a166944_record_core
import Definitions.Def_a166944_moving_horizon

/-!
Self-contained solution for the platform target
`A166944Research.a166944_target_of_travel`.

`TwinPrimeTravelBoundFrom 45895573` unfolds to the hypothesis the target states,
and the proof is `record_index_and_twin_prime_of_twin_travel_bound_from_45895573`
applied to the record, taking the second component. Helper lemmas from the source
project are inlined below in dependency order -- not source order, which matters
because Lean rejects forward references.
-/

open A166944Research

namespace A166944Research

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

def B (n : Nat) : Nat := a n - (2 * n - 2)

theorem a_pos : ∀ n : Nat, 0 < n → 0 < a n := by
  intro n
  induction n with
  | zero =>
      intro h
      cases h
  | succ n ih =>
      cases n with
      | zero => simp [a]
      | succ n =>
          intro _
          simp only [a]
          split <;> exact Nat.add_pos_left (ih (Nat.zero_lt_succ n)) _

theorem index_le_a : ∀ n : Nat, n ≤ a n := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      cases n with
      | zero => simp [a]
      | succ n =>
          rw [a]
          split
          · have hg : 1 ≤ Nat.gcd (n + 2) (a (n + 1)) :=
              Nat.succ_le_of_lt
                (Nat.gcd_pos_of_pos_right _ (a_pos (n + 1) (Nat.zero_lt_succ n)))
            exact Nat.le_trans (Nat.succ_le_succ ih)
              (Nat.add_le_add_left hg _)
          · have hg : 1 ≤ Nat.gcd n (a (n + 1)) :=
              Nat.succ_le_of_lt
                (Nat.gcd_pos_of_pos_right _ (a_pos (n + 1) (Nat.zero_lt_succ n)))
            exact Nat.le_trans (Nat.succ_le_succ ih)
              (Nat.add_le_add_left hg _)

theorem a_add_one_le_add_two (n : Nat) : a (n + 1) ≤ a (n + 2) := by
  simp only [a]
  split <;> exact Nat.le_add_right _ _

theorem a_le_succ (n : Nat) : a n ≤ a (n + 1) := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => simpa using a_add_one_le_add_two n

theorem a_add_d_succ {k : Nat} :
    a k + d (k + 1) = a (k + 1) := by
  have hsub : d (k + 1) = a (k + 1) - a k := by simp [d]
  rw [hsub]
  simpa [Nat.add_comm] using Nat.sub_add_cancel (a_le_succ k)

theorem gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one {m n : Nat}
    (h : m % 2 = 1 ∨ n % 2 = 1) : Nat.gcd m n % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one (Nat.gcd m n) with hg | hg
  · exfalso
    have h2g : 2 ∣ Nat.gcd m n := Nat.dvd_of_mod_eq_zero hg
    rcases h with hm | hn
    · have h2m : 2 ∣ m := Nat.dvd_trans h2g (Nat.gcd_dvd_left m n)
      have hm0 : m % 2 = 0 := Nat.mod_eq_zero_of_dvd h2m
      have : (0 : Nat) = 1 := hm0.symm.trans hm
      cases this
    · have h2n : 2 ∣ n := Nat.dvd_trans h2g (Nat.gcd_dvd_right m n)
      have hn0 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h2n
      have : (0 : Nat) = 1 := hn0.symm.trans hn
      cases this
  · exact hg

theorem a_add_two_mod_two (n : Nat) :
    a (n + 2) % 2 = (n + 2) % 2 := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
      change a (n + 3) % 2 = (n + 3) % 2
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · have hidx : (n + 3) % 2 ≠ 0 := by simp [Nat.add_mod, hn]
        have hprev : a (n + 2) % 2 = 0 := by
          calc
            a (n + 2) % 2 = (n + 2) % 2 := ih
            _ = 0 := by simp [hn]
        have hg : Nat.gcd (n + 1) (a (n + 2)) % 2 = 1 :=
          gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one
            (Or.inl (by simp [Nat.add_mod, hn]))
        rw [a]
        rw [if_neg hidx, Nat.add_mod]
        simp [hprev, hg, Nat.add_mod, hn]
      · have hidx : (n + 3) % 2 = 0 := by simp [Nat.add_mod, hn]
        have hprev : a (n + 2) % 2 = 1 := by
          calc
            a (n + 2) % 2 = (n + 2) % 2 := ih
            _ = 1 := by simp [hn]
        have hg : Nat.gcd (n + 3) (a (n + 2)) % 2 = 1 :=
          gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one
            (Or.inr hprev)
        rw [a]
        rw [if_pos hidx, Nat.add_mod]
        simp [hprev, hg, Nat.add_mod, hn]

theorem a_mod_two_of_two_le {n : Nat} (hn : 2 ≤ n) :
    a n % 2 = n % 2 := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using a_add_two_mod_two k

theorem d_add_two (n : Nat) :
    d (n + 2) = if (n + 2) % 2 = 0 then
      Nat.gcd (n + 2) (a (n + 1))
    else Nat.gcd n (a (n + 1)) := by
  simp only [d, a]
  split <;> simp_all

theorem d_add_two_pos (n : Nat) : 0 < d (n + 2) := by
  rw [d_add_two]
  split <;> exact Nat.gcd_pos_of_pos_right _ (a_pos (n + 1) (Nat.zero_lt_succ n))

theorem one_le_d_succ (n : Nat) : 1 ≤ d (n + 1) := by
  cases n with
  | zero => simp [d, a]
  | succ n => exact Nat.succ_le_of_lt (d_add_two_pos n)

theorem a_succ_ge_add_one {k : Nat} :
    a k + 1 ≤ a (k + 1) := by
  calc
    a k + 1 ≤ a k + d (k + 1) :=
      Nat.add_le_add_left (one_le_d_succ k) _
    _ = a (k + 1) := a_add_d_succ

theorem d_add_two_of_odd (n : Nat) (h : (n + 2) % 2 ≠ 0) :
    d (n + 2) = Nat.gcd n (a (n + 1)) := by
  have h' : n % 2 ≠ 0 := by simpa using h
  simpa [h'] using d_add_two n

theorem a_lower_step {k : Nat} (hk : 2 ≤ k)
    (hbound : 2 * k ≤ a k + 2) :
    2 * (k + 1) ≤ a (k + 1) + 2 := by
  rcases Nat.eq_or_lt_of_le hbound with heq | hlt
  · have hk2 : 2 ≤ 2 * k := by
      exact Nat.le_trans (by simp) (Nat.mul_le_mul_left 2 hk)
    have ha : a k = 2 * k - 2 := by
      exact (Nat.sub_eq_iff_eq_add hk2).2 heq |>.symm
    have ha2 : a k = 2 * (k - 1) := by
      calc
        a k = 2 * k - 2 := ha
        _ = 2 * (k - 1) := by
          rw [Nat.mul_sub_left_distrib]
    have hak0 : a k % 2 = 0 := by
      have hmod := congrArg (fun x : Nat => x % 2) heq
      simpa [Nat.mul_mod, Nat.add_mod] using hmod.symm
    have hk0 : k % 2 = 0 := by
      calc
        k % 2 = a k % 2 := (a_mod_two_of_two_le hk).symm
        _ = 0 := hak0
    have hk3 : 3 ≤ k := by
      have hne2 : ¬ k = 2 := by
        intro hk2eq
        subst k
        simp [a] at heq
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hk (by
        intro h
        exact hne2 h.symm))
    have hkminus : 2 ≤ k - 1 :=
      Nat.le_sub_of_add_le (by simpa using hk3)
    have hidx : (k - 1) + 2 = k + 1 := by
      calc
        (k - 1) + 2 = (k - 1) + 1 + 1 := by simp [Nat.add_assoc]
        _ = k + 1 := by
          rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
    have hne : (k + 1) % 2 ≠ 0 := by simp [Nat.add_mod, hk0]
    have hne' : ((k - 1) + 2) % 2 ≠ 0 := by simpa [hidx] using hne
    have hdk : d (k + 1) = k - 1 := by
      calc
        d (k + 1) = d ((k - 1) + 2) := by rw [hidx]
        _ = Nat.gcd (k - 1) (a ((k - 1) + 1)) :=
          d_add_two_of_odd (k - 1) hne'
        _ = Nat.gcd (k - 1) (a k) := by
          rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
        _ = k - 1 := by
          rw [ha2]
          simpa using (Nat.gcd_mul_right 1 (k - 1) 2)
    have hd2 : 2 ≤ d (k + 1) := by simpa [hdk] using hkminus
    calc
      2 * (k + 1) = 2 * k + 2 := by simp [Nat.mul_add]
      _ = (a k + 2) + 2 := by rw [heq]
      _ ≤ (a k + d (k + 1)) + 2 := by
        exact Nat.add_le_add_right (Nat.add_le_add_left hd2 (a k)) 2
      _ = a (k + 1) + 2 := by rw [a_add_d_succ]
  · have hnext : 2 * k + 1 ≤ a k + 2 := Nat.succ_le_of_lt hlt
    have hstep : a k + 1 ≤ a (k + 1) := a_succ_ge_add_one
    calc
      2 * (k + 1) = 2 * k + 2 := by simp [Nat.mul_add]
      _ = (2 * k + 1) + 1 := by simp [Nat.add_assoc]
      _ ≤ (a k + 2) + 1 := Nat.add_le_add_right hnext 1
      _ = (a k + 1) + 2 := by simp [Nat.add_assoc, Nat.add_left_comm]
      _ ≤ a (k + 1) + 2 := Nat.add_le_add_right hstep 2

theorem two_mul_le_a_add_two {k : Nat} (hk : 2 ≤ k) :
    2 * k ≤ a k + 2 := by
  obtain ⟨t, rfl⟩ := Nat.le.dest hk
  clear hk
  induction t with
  | zero => simp [a]
  | succ t ih =>
      have ht : 2 ≤ 2 + t := Nat.le_add_right 2 t
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (a_lower_step ht ih)

theorem two_mul_sub_two_le_a {k : Nat} (hk : 2 ≤ k) :
    2 * k - 2 ≤ a k := by
  exact (Nat.sub_le_iff_le_add).2 (two_mul_le_a_add_two hk)

theorem B_add_index_eq_D_add_two {n : Nat} (hn : 2 ≤ n) :
    B n + n = D n + 2 := by
  have hbase : 2 * n - 2 ≤ a n := two_mul_sub_two_le_a hn
  have hBsum : B n + (2 * n - 2) = a n := Nat.sub_add_cancel hbase
  have hDsum : D n + n = a n := Nat.sub_add_cancel (index_le_a n)
  have hsplit : 2 * n - 2 = n + (n - 2) := by
    have hnn : 2 ≤ n + n := Nat.le_trans hn (Nat.le_add_right n n)
    have hnn' : 2 ≤ 2 * n := by simpa only [Nat.two_mul] using hnn
    apply (Nat.sub_eq_iff_eq_add hnn').2
    calc
      2 * n = n + n := by simp [Nat.succ_mul, Nat.add_comm]
      _ = n + ((n - 2) + 2) := by rw [Nat.sub_add_cancel hn]
      _ = n + (n - 2) + 2 := by simp [Nat.add_assoc]
  have hleft : B n + n + (n - 2) = D n + n := by
    calc
      B n + n + (n - 2) = B n + (2 * n - 2) := by
        rw [hsplit]
        simp [Nat.add_assoc]
      _ = a n := hBsum
      _ = D n + n := hDsum.symm
  have hright : D n + n = (D n + 2) + (n - 2) := by
    calc
      D n + n = D n + ((n - 2) + 2) := by rw [Nat.sub_add_cancel hn]
      _ = (D n + 2) + (n - 2) := by simp [Nat.add_assoc, Nat.add_comm]
  apply Nat.add_right_cancel
  calc
    (B n + n) + (n - 2) = D n + n := hleft
    _ = (D n + 2) + (n - 2) := hright

theorem base_eq_two_mul_pred (k : Nat) :
    2 * k - 2 = 2 * (k - 1) := by
  rw [Nat.mul_sub_left_distrib]

theorem B_mod_two_of_two_le {k : Nat} (hk : 2 ≤ k) :
    B k % 2 = k % 2 := by
  have hbase : 2 * k - 2 ≤ a k := two_mul_sub_two_le_a hk
  have hsum : B k + (2 * k - 2) = a k := Nat.sub_add_cancel hbase
  have hbase_mod : (2 * k - 2) % 2 = 0 := by
    rw [base_eq_two_mul_pred k]
    simp [Nat.mul_mod]
  calc
    B k % 2 = (B k + (2 * k - 2)) % 2 := by
      rw [Nat.add_mod, hbase_mod]
      simp
    _ = a k % 2 := by rw [hsum]
    _ = k % 2 := a_mod_two_of_two_le hk

theorem excess_succ_add_two {k : Nat} (hk : 2 ≤ k) :
    B (k + 1) + 2 = B k + d (k + 1) := by
  simp only [B]
  have hbase : 2 * k - 2 ≤ a k := two_mul_sub_two_le_a hk
  have hnext : 2 * (k + 1) - 2 ≤ a (k + 1) :=
    (Nat.sub_le_iff_le_add).2
      (two_mul_le_a_add_two (Nat.le_trans hk (Nat.le_succ k)))
  have hnext0 : 2 * k ≤ a (k + 1) := by
    simpa [Nat.mul_add] using hnext
  have hk2 : 2 ≤ 2 * k := by
    exact Nat.le_trans (by simp) (Nat.mul_le_mul_left 2 hk)
  have hshift : a (k + 1) - 2 * k + 2 =
      a (k + 1) - (2 * k - 2) := by
    have h := Nat.sub_add_sub_cancel hnext0
      (Nat.sub_le (2 * k) 2)
    simpa [Nat.sub_sub_self hk2] using h
  have hsum : (a k - (2 * k - 2)) + d (k + 1) =
      a (k + 1) - (2 * k - 2) := by
    have h := Nat.sub_add_sub_cancel (a_le_succ k) hbase
    calc
      (a k - (2 * k - 2)) + d (k + 1) =
          d (k + 1) + (a k - (2 * k - 2)) := Nat.add_comm _ _
      _ = (a (k + 1) - a k) + (a k - (2 * k - 2)) := by
        rw [d]
        simp
      _ = a (k + 1) - (2 * k - 2) := h
  calc
    a (k + 1) - (2 * (k + 1) - 2) + 2 =
        a (k + 1) - 2 * k + 2 := by simp [Nat.mul_add]
    _ = a (k + 1) - (2 * k - 2) := hshift
    _ = (a k - (2 * k - 2)) + d (k + 1) := hsum.symm

theorem d_add_two_mod_two_eq_one {n : Nat} (hn : 1 ≤ n) :
    d (n + 2) % 2 = 1 := by
  rw [d_add_two]
  rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
  · have hprev : a (n + 1) % 2 = 1 := by
      calc
        a (n + 1) % 2 = (n + 1) % 2 :=
          a_mod_two_of_two_le (Nat.succ_le_succ hn)
        _ = 1 := by simp [Nat.add_mod, hn0]
    have hg : Nat.gcd (n + 2) (a (n + 1)) % 2 = 1 :=
      gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one (Or.inr hprev)
    simp [hn0, hg]
  · have hg : Nat.gcd n (a (n + 1)) % 2 = 1 :=
      gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one (Or.inl hn1)
    simp [hn1, hg]

theorem d_mod_two_eq_one_of_three_le {n : Nat} (hn : 3 ≤ n) :
    d n % 2 = 1 := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    d_add_two_mod_two_eq_one hk

theorem d_add_two_of_even (n : Nat) (h : (n + 2) % 2 = 0) :
    d (n + 2) = Nat.gcd (n + 2) (a (n + 1)) := by
  simpa [h] using d_add_two n

theorem d_succ_eq_gcd_small_residual {k : Nat} (hk : 2 ≤ k)
    (hk1 : k % 2 = 1) (hB : B k ≤ 4) :
    d (k + 1) = Nat.gcd (k + 1) (4 - B k) := by
  have hidx : (k - 1) + 2 = k + 1 := by
    calc
      (k - 1) + 2 = (k - 1) + 1 + 1 := by simp [Nat.add_assoc]
      _ = k + 1 := by
        rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
  have hprev : (k - 1) + 1 = k := by
    rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
  have heven : (k + 1) % 2 = 0 := by
    simp [Nat.add_mod, hk1]
  have heven' : ((k - 1) + 2) % 2 = 0 := by
    simpa [hidx] using heven
  have hsum : B k + (2 * k - 2) = a k :=
    Nat.sub_add_cancel (two_mul_sub_two_le_a hk)
  have hk2 : 2 ≤ 2 * k := by
    exact Nat.le_trans (by simp) (Nat.mul_le_mul_left 2 hk)
  have hbase4 : (2 * k - 2) + 4 = 2 * k + 2 := by
    calc
      (2 * k - 2) + 4 = (2 * k - 2) + 2 + 2 := by simp [Nat.add_assoc]
      _ = 2 * k + 2 := by rw [Nat.sub_add_cancel hk2]
  have hBsum : B k + (4 - B k) = 4 := Nat.add_sub_cancel' hB
  have ha : a k + (4 - B k) = 2 * (k + 1) := by
    calc
      a k + (4 - B k) = (B k + (2 * k - 2)) + (4 - B k) := by
        rw [hsum]
      _ = (2 * k - 2) + (B k + (4 - B k)) := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = (2 * k - 2) + 4 := by rw [hBsum]
      _ = 2 * k + 2 := hbase4
      _ = 2 * (k + 1) := by simp [Nat.mul_add]
  have hkplus : 2 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  have hfour : 4 ≤ 2 * (k + 1) := by
    calc
      4 = 2 * 2 := by simp
      _ ≤ 2 * (k + 1) := Nat.mul_le_mul_left 2 hkplus
  have hrespos : 4 - B k ≤ 2 * (k + 1) :=
    Nat.le_trans (Nat.sub_le _ _) hfour
  have hasub : a k = 2 * (k + 1) - (4 - B k) := by
    exact (Nat.sub_eq_iff_eq_add hrespos).2 ha.symm |>.symm
  calc
    d (k + 1) = d ((k - 1) + 2) := by rw [hidx]
    _ = Nat.gcd ((k - 1) + 2) (a ((k - 1) + 1)) :=
      d_add_two_of_even (k - 1) heven'
    _ = Nat.gcd (k + 1) (a k) := by rw [hidx, hprev]
    _ = Nat.gcd (k + 1) (2 * (k + 1) - (4 - B k)) := by rw [hasub]
    _ = Nat.gcd (k + 1) (4 - B k) := by
      have hmul : 4 - B k ≤ (k + 1) * 2 := by
        simpa [Nat.mul_comm] using hrespos
      simpa [Nat.mul_comm] using (Nat.gcd_mul_left_sub_right (m := k + 1)
        (n := 4 - B k) (k := 2) hmul)

theorem one_or_three_le_of_mod_two_eq_one {c : Nat} (hc : c % 2 = 1) :
    c = 1 ∨ 3 ≤ c := by
  cases c with
  | zero => simp at hc
  | succ c =>
      cases c with
      | zero => exact Or.inl rfl
      | succ c =>
          cases c with
          | zero => simp at hc
          | succ c =>
              right
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (Nat.le_add_right 3 c)

theorem odd_small_residual_classification {k : Nat} (hk : 2 ≤ k)
    (hk1 : k % 2 = 1) (hB : B k < 4) :
    (B k = 1 ∧ (d (k + 1) = 1 ∨ d (k + 1) = 3)) ∨
      (B k = 3 ∧ d (k + 1) = 1) := by
  have hBmod : B k % 2 = 1 := by
    calc
      B k % 2 = k % 2 := B_mod_two_of_two_le hk
      _ = 1 := hk1
  rcases one_or_three_le_of_mod_two_eq_one hBmod with hB1 | hB3
  · left
    refine ⟨hB1, ?_⟩
    have hd : d (k + 1) = Nat.gcd (k + 1) 3 := by
      calc
        d (k + 1) = Nat.gcd (k + 1) (4 - B k) :=
          d_succ_eq_gcd_small_residual hk hk1 (Nat.le_of_lt hB)
        _ = Nat.gcd (k + 1) 3 := by rw [hB1]
    have hdiv : d (k + 1) ∣ 3 := by
      rw [hd]
      exact Nat.gcd_dvd_right _ _
    have hle : d (k + 1) ≤ 3 := Nat.le_of_dvd (by simp) hdiv
    rcases one_or_three_le_of_mod_two_eq_one
      (d_mod_two_eq_one_of_three_le (Nat.succ_le_succ hk)) with
      hd1 | hd3
    · exact Or.inl hd1
    · exact Or.inr (Nat.le_antisymm hle hd3)
  · right
    refine ⟨?_, ?_⟩
    · exact Nat.le_antisymm (Nat.le_of_lt_succ hB) hB3
    calc
      d (k + 1) = Nat.gcd (k + 1) (4 - B k) :=
        d_succ_eq_gcd_small_residual hk hk1 (Nat.le_of_lt hB)
      _ = 1 := by
        rw [Nat.le_antisymm (Nat.le_of_lt_succ hB) hB3]
        simp

theorem B_one_transition {k : Nat} (hk : 2 ≤ k) (hk1 : k % 2 = 1)
    (hB : B k = 1) :
    (d (k + 1) = 1 ∧ B (k + 1) = 0) ∨
      (d (k + 1) = 3 ∧ B (k + 1) = 2) := by
  have hsmall : B k < 4 := by simpa [hB]
  rcases odd_small_residual_classification hk hk1 hsmall with
    ⟨hB1, hd1 | hd3⟩ | ⟨hB3, hd1⟩
  · left
    refine ⟨hd1, ?_⟩
    have hstep := excess_succ_add_two hk
    have hnext : B (k + 1) + 2 = 0 + 2 := by
      calc
        B (k + 1) + 2 = B k + d (k + 1) := hstep
        _ = 1 + 1 := by rw [hB, hd1]
        _ = 0 + 2 := by simp
    exact Nat.add_right_cancel hnext
  · right
    refine ⟨hd3, ?_⟩
    have hstep := excess_succ_add_two hk
    have hnext : B (k + 1) + 2 = 2 + 2 := by
      calc
        B (k + 1) + 2 = B k + d (k + 1) := hstep
        _ = 1 + 3 := by rw [hB, hd3]
        _ = 2 + 2 := by simp
    exact Nat.add_right_cancel hnext
  · have : (3 : Nat) = 1 := by rw [← hB3, hB]
    cases this

theorem d_succ_eq_gcd_even_residual {k : Nat} (hk : 2 ≤ k)
    (hk0 : k % 2 = 0) :
    d (k + 1) = Nat.gcd (k - 1) (B k) := by
  have hidx : (k - 1) + 2 = k + 1 := by
    calc
      (k - 1) + 2 = (k - 1) + 1 + 1 := by simp [Nat.add_assoc]
      _ = k + 1 := by
        rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
  have hprev : (k - 1) + 1 = k := by
    rw [Nat.sub_add_cancel (Nat.le_trans (by simp) hk)]
  have hne : (k + 1) % 2 ≠ 0 := by
    simp [Nat.add_mod, hk0]
  have hne' : ((k - 1) + 2) % 2 ≠ 0 := by
    simpa [hidx] using hne
  have hsum : B k + (2 * k - 2) = a k :=
    Nat.sub_add_cancel (two_mul_sub_two_le_a hk)
  have ha : a k = B k + 2 * (k - 1) := by
    calc
      a k = B k + (2 * k - 2) := hsum.symm
      _ = B k + 2 * (k - 1) := by rw [base_eq_two_mul_pred k]
  calc
    d (k + 1) = d ((k - 1) + 2) := by rw [hidx]
    _ = Nat.gcd (k - 1) (a ((k - 1) + 1)) :=
      d_add_two_of_odd (k - 1) hne'
    _ = Nat.gcd (k - 1) (a k) := by rw [hprev]
    _ = Nat.gcd (k - 1) (B k + 2 * (k - 1)) := by rw [ha]
    _ = Nat.gcd (k - 1) (B k) := by
      simpa using (Nat.gcd_add_mul_right_right (k - 1) (B k) 2)

theorem quotient_mod_two_of_left_odd {R q : Nat} (hR : R % 2 = 1) :
    q % 2 = (R * q) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
  · simp [Nat.mul_mod, hR, hq0]
  · simp [Nat.mul_mod, hR, hq1]

theorem two_le_of_pos_of_mod_two_eq_zero {c : Nat} (hcpos : 0 < c)
    (hc : c % 2 = 0) : 2 ≤ c := by
  cases c with
  | zero => simp at hcpos
  | succ c =>
      cases c with
      | zero => simp at hc
      | succ c =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.le_add_right 2 c)

theorem even_residual_structure {k : Nat} (hk : 2 ≤ k)
    (hk0 : k % 2 = 0) :
    ∃ t : Nat, B k = d (k + 1) * t ∧ t % 2 = 0 ∧
      (B k = 0 ∨ 2 * d (k + 1) ≤ B k) := by
  have hidentity := d_succ_eq_gcd_even_residual hk hk0
  have hdvd : d (k + 1) ∣ B k := by
    rw [hidentity]
    exact Nat.gcd_dvd_right _ _
  rcases hdvd with ⟨t, ht⟩
  have hk3 : 3 ≤ k + 1 := by
    simpa using Nat.add_le_add_right hk 1
  have hdodd : d (k + 1) % 2 = 1 :=
    d_mod_two_eq_one_of_three_le hk3
  have htmod : t % 2 = 0 := by
    calc
      t % 2 = (d (k + 1) * t) % 2 :=
        quotient_mod_two_of_left_odd hdodd
      _ = B k % 2 := by rw [ht]
      _ = k % 2 := B_mod_two_of_two_le hk
      _ = 0 := hk0
  by_cases hzero : B k = 0
  · exact ⟨t, ht, htmod, Or.inl hzero⟩
  · refine ⟨t, ht, htmod, Or.inr ?_⟩
    have htne : t ≠ 0 := by
      intro ht0
      apply hzero
      simpa [ht0] using ht
    have htpos : 0 < t := Nat.pos_of_ne_zero htne
    have ht2 : 2 ≤ t := two_le_of_pos_of_mod_two_eq_zero htpos htmod
    calc
      2 * d (k + 1) = d (k + 1) * 2 := by simp [Nat.mul_comm]
      _ ≤ d (k + 1) * t := Nat.mul_le_mul_left _ ht2
      _ = B k := ht.symm

theorem d_pos_of_two_le {n : Nat} (hn : 2 ≤ n) : 0 < d n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using d_add_two_pos k

theorem one_le_d_of_two_le {n : Nat} (hn : 2 ≤ n) : 1 ≤ d n := by
  exact Nat.succ_le_of_lt (d_pos_of_two_le hn)

theorem B_two_transition {k : Nat} (hk : 2 ≤ k) (hB : B k = 2) :
    d (k + 1) = 1 ∧ B (k + 1) = 1 := by
  have hk0 : k % 2 = 0 := by
    calc
      k % 2 = B k % 2 := (B_mod_two_of_two_le hk).symm
      _ = 2 % 2 := by rw [hB]
      _ = 0 := by simp
  rcases even_residual_structure hk hk0 with
    ⟨t, ht, htmod, hzero | hbound⟩
  · simp [hB] at hzero
  · have hdle : d (k + 1) ≤ 1 := by
      have hbound' : 2 * d (k + 1) ≤ 2 := by simpa [hB] using hbound
      exact Nat.le_of_mul_le_mul_left hbound' (by simp : 0 < 2)
    have hdpos : 1 ≤ d (k + 1) :=
      one_le_d_of_two_le (Nat.le_trans hk (Nat.le_succ k))
    have hd : d (k + 1) = 1 := Nat.le_antisymm hdle hdpos
    have hstep := excess_succ_add_two hk
    have hnext : B (k + 1) + 2 = 1 + 2 := by
      calc
        B (k + 1) + 2 = B k + d (k + 1) := hstep
        _ = 2 + 1 := by rw [hB, hd]
        _ = 1 + 2 := by simp
    exact ⟨hd, Nat.add_right_cancel hnext⟩

theorem B_zero_transition {k : Nat} (hk : 2 ≤ k) (hB : B k = 0) :
    d (k + 1) = k - 1 ∧ B (k + 1) + 2 = k - 1 := by
  have hk0 : k % 2 = 0 := by
    calc
      k % 2 = B k % 2 := (B_mod_two_of_two_le hk).symm
      _ = 0 % 2 := by rw [hB]
      _ = 0 := by simp
  have hd : d (k + 1) = k - 1 := by
    calc
      d (k + 1) = Nat.gcd (k - 1) (B k) :=
        d_succ_eq_gcd_even_residual hk hk0
      _ = Nat.gcd (k - 1) 0 := by rw [hB]
      _ = k - 1 := by simp
  have hstep := excess_succ_add_two hk
  have hnext : B (k + 1) + 2 = k - 1 := by
    calc
      B (k + 1) + 2 = B k + d (k + 1) := hstep
      _ = k - 1 := by rw [hB, hd]; simp
  exact ⟨hd, hnext⟩

theorem D_succ_add_one_eq_add_d (n : Nat) :
    D (n + 1) + 1 = D n + d (n + 1) := by
  simp only [D, d]
  have hindex : n ≤ a n := index_le_a n
  have hnext : n + 1 ≤ a (n + 1) := index_le_a (n + 1)
  have hstep : a n ≤ a (n + 1) := a_le_succ n
  calc
    a (n + 1) - (n + 1) + 1 =
        a (n + 1) - (n + 1) + ((n + 1) - n) := by simp
    _ = a (n + 1) - n :=
      Nat.sub_add_sub_cancel hnext (Nat.le_add_right n 1)
    _ = (a n - n) + (a (n + 1) - a n) := by
      calc
        a (n + 1) - n = (a (n + 1) - a n) + (a n - n) :=
          (Nat.sub_add_sub_cancel hstep hindex).symm
        _ = (a n - n) + (a (n + 1) - a n) := Nat.add_comm _ _

theorem D_succ_eq_add_d_sub_one (n : Nat) :
    D (n + 1) = D n + d (n + 1) - 1 := by
  simpa using congrArg (fun x : Nat => x - 1) (D_succ_add_one_eq_add_d n)

theorem D_succ_eq_D_add_d_sub_one (n : Nat) :
    D (n + 1) = D n + (d (n + 1) - 1) := by
  rw [D_succ_eq_add_d_sub_one n]
  exact Nat.add_sub_assoc (one_le_d_succ n) (D n)

theorem D_add_two_le_succ_of_two_le {n : Nat} (hn : 2 ≤ n)
    (h : 1 < d (n + 1)) : D n + 2 ≤ D (n + 1) := by
  have hn3 : 3 ≤ n + 1 := by
    exact Nat.succ_le_succ hn
  have hdodd : d (n + 1) % 2 = 1 := by
    simpa [Nat.add_assoc] using d_mod_two_eq_one_of_three_le hn3
  have hd3 : 3 ≤ d (n + 1) := by
    rcases one_or_three_le_of_mod_two_eq_one hdodd with hd1 | hd3
    · have : (1 : Nat) < 1 := by simpa [hd1] using h
      exact False.elim (Nat.lt_irrefl 1 this)
    · exact hd3
  have hdsub : 2 ≤ d (n + 1) - 1 := by
    apply Nat.le_sub_of_add_le
    simpa using hd3
  rw [D_succ_eq_D_add_d_sub_one]
  exact Nat.add_le_add_left hdsub (D n)

theorem D_eq_self_of_fundamental {m : Nat} (hm : 2 ≤ m)
    (hfund : B m = 2) : D m = m := by
  have h := B_add_index_eq_D_add_two hm
  rw [hfund] at h
  have hcancel : 2 + m = 2 + D m := by
    calc
      2 + m = D m + 2 := h
      _ = 2 + D m := by simp [Nat.add_comm]
  exact (Nat.add_left_cancel hcancel).symm

theorem D_le_succ (n : Nat) : D n ≤ D (n + 1) := by
  have hle : D n + 1 ≤ D n + d (n + 1) :=
    Nat.add_le_add_left (one_le_d_succ n) (D n)
  have hle' : D n + 1 ≤ D (n + 1) + 1 :=
    Nat.le_trans hle (Nat.le_of_eq (D_succ_add_one_eq_add_d n).symm)
  exact Nat.le_of_succ_le_succ hle'

theorem D_le_of_le {m n : Nat} (hmn : m ≤ n) : D m ≤ D n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hmn
  clear hmn
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      exact Nat.le_trans ih (by simpa [Nat.add_assoc] using D_le_succ (m + k))

theorem D_mod_two_eq_zero_of_two_le {n : Nat} (hn : 2 ≤ n) :
    D n % 2 = 0 := by
  have hsum : D n + n = a n :=
    Nat.sub_add_cancel (index_le_a n)
  rcases Nat.mod_two_eq_zero_or_one (D n) with hzero | hone
  · exact hzero
  · have hsum_mod : (D n + n) % 2 = n % 2 := by
      rw [hsum]
      exact a_mod_two_of_two_le hn
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · simp [Nat.add_mod, hone, hn0] at hsum_mod
    · simp [Nat.add_mod, hone, hn1] at hsum_mod

theorem d_eq_if_gcd_of_two_le {n : Nat} (hn : 2 ≤ n) :
    d n = if n % 2 = 0 then
      Nat.gcd n (a (n - 1))
    else Nat.gcd (n - 2) (a (n - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using d_add_two k

theorem constant_D_event_map {r C : Nat} (hr : 2 ≤ r)
    (hD : D (r - 1) = C) :
    d r = if r % 2 = 0 then Nat.gcd r (C - 1)
      else Nat.gcd (r - 2) (C + 1) := by
  have hr1 : 1 ≤ r := Nat.le_trans (by simp) hr
  have hs : 1 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hrs : r - 1 + 1 = r := Nat.sub_add_cancel hr1
  have ha : a (r - 1) = C + (r - 1) := by
    calc
      a (r - 1) = D (r - 1) + (r - 1) :=
        (Nat.sub_add_cancel (index_le_a (r - 1))).symm
      _ = C + (r - 1) := by rw [hD]
  have hC : 1 ≤ C := by
    rw [← hD]
    calc
      1 = D 1 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  by_cases heven : r % 2 = 0
  · rw [if_pos heven, d_eq_if_gcd_of_two_le hr, if_pos heven, ha]
    have hsum : C + (r - 1) = (C - 1) + r := by
      calc
        C + (r - 1) = ((C - 1) + 1) + (r - 1) := by
          rw [Nat.sub_add_cancel hC]
        _ = (C - 1) + ((r - 1) + 1) := by
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ = (C - 1) + r := by rw [hrs]
    rw [hsum]
    simpa [Nat.add_assoc] using
      (Nat.gcd_add_mul_right_right r (C - 1) 1)
  · rw [if_neg heven, d_eq_if_gcd_of_two_le hr, if_neg heven, ha]
    have hpred : r - 1 = (r - 2) + 1 := by
      apply (Nat.sub_eq_iff_eq_add hr1).2
      calc
        r = (r - 2) + 2 := (Nat.sub_add_cancel hr).symm
        _ = ((r - 2) + 1) + 1 := by simp [Nat.add_assoc]
    have hsum : C + (r - 1) = (C + 1) + (r - 2) := by
      rw [hpred]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hsum]
    simpa [Nat.add_assoc] using
      (Nat.gcd_add_mul_right_right (r - 2) (C + 1) 1)

theorem constant_D_event_map_succ {s C : Nat} (hs : 1 ≤ s)
    (hD : D s = C) :
    d (s + 1) = if (s + 1) % 2 = 0 then Nat.gcd (s + 1) (C - 1)
      else Nat.gcd (s - 1) (C + 1) := by
  have hr : 2 ≤ s + 1 := Nat.succ_le_succ hs
  have hpred : s + 1 - 1 = s := Nat.add_sub_cancel s 1
  have hpred2 : s + 1 - 2 = s - 1 := by
    cases s with
    | zero => simp at hs
    | succ s => simp [Nat.add_assoc]
  simpa [hpred, hpred2] using constant_D_event_map hr (by simpa [hpred] using hD)

private theorem add_le_next_multiple {e x H : Nat}
    (hlt : x < H) (hx : e ∣ x) (hH : e ∣ H) :
    x + e ≤ H := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hH
  have huv := Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left hlt)
  simpa [Nat.mul_add] using Nat.mul_le_mul_left e huv

/-- A single increment cannot cross an even multiple of its value. -/
theorem D_succ_le_even_multiple {n H : Nat} (hn : 2 ≤ n)
    (hHeven : H % 2 = 0) (hbound : D n ≤ H) (hdiv : d (n + 1) ∣ H) :
    D (n + 1) ≤ H := by
  have hupdate := D_succ_add_one_eq_add_d n
  have hepos := one_le_d_succ n
  by_cases he : d (n + 1) = 1
  · omega
  have hmap := constant_D_event_map_succ (show 1 ≤ n by omega) (rfl : D n = D n)
  by_cases hpar : (n + 1) % 2 = 0
  · rw [if_pos hpar] at hmap
    have hfactor : d (n + 1) ∣ D n - 1 := hmap.symm ▸ Nat.gcd_dvd_right _ _
    have hDtwo : 2 ≤ D n := Nat.le_trans (by decide : 2 ≤ D 2) (D_le_of_le hn)
    have hnext := add_le_next_multiple (by omega : D n - 1 < H) hfactor hdiv
    omega
  · rw [if_neg hpar] at hmap
    have hfactor : d (n + 1) ∣ D n + 1 := hmap.symm ▸ Nat.gcd_dvd_right _ _
    have hstrict : D n < H := by
      by_cases hEq : D n = H
      · have hone := Nat.dvd_sub hfactor (hEq.symm ▸ hdiv)
        have hunit : d (n + 1) ∣ 1 := by simpa using hone
        exact False.elim (he (Nat.eq_one_of_dvd_one hunit))
      · omega
    have hDeven := D_mod_two_eq_zero_of_two_le hn
    have hnext := add_le_next_multiple (by omega : D n + 1 < H) hfactor hdiv
    omega

/-- A common even multiple of the increments on an interval bounds the
horizon throughout that interval once it bounds the initial horizon. -/
theorem D_le_even_multiple_of_interval {s n H : Nat} (hs : 2 ≤ s) (hsn : s ≤ n)
    (hHeven : H % 2 = 0) (hstart : D s ≤ H)
    (hdiv : ∀ j : Nat, s < j → j ≤ n → d j ∣ H) :
    D n ≤ H := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hsn
  induction k with
  | zero => simpa using hstart
  | succ k ih =>
      have hk := ih (by omega : s ≤ s + k) (fun j hsj hj => hdiv j hsj (by omega))
      have hnext := D_succ_le_even_multiple (n := s + k) (by omega) hHeven hk
        (hdiv (s + k + 1) (by omega) (by omega))
      simpa [Nat.add_assoc] using hnext

/-- The least common multiple of 2 and the positive odd integers at most
the increment cap. Increments from index 3 onward are all odd. -/
def recordHorizonBound : Nat → Nat
  | 0 => 2
  | m + 1 =>
      if (m + 1) % 2 = 1 then Nat.lcm (m + 1) (recordHorizonBound m)
      else recordHorizonBound m

private theorem recordHorizonBound_dvd_succ (M : Nat) :
    recordHorizonBound M ∣ recordHorizonBound (M + 1) := by
  by_cases h : (M + 1) % 2 = 1
  · simpa [recordHorizonBound, h] using Nat.dvd_lcm_right (M + 1) (recordHorizonBound M)
  · simp [recordHorizonBound, h]

theorem odd_dvd_recordHorizonBound {e M : Nat} (he : e % 2 = 1) (hcap : e ≤ M) :
    e ∣ recordHorizonBound M := by
  induction M with
  | zero => omega
  | succ M ih =>
      by_cases h : e = M + 1
      · subst e
        simpa [recordHorizonBound, he] using Nat.dvd_lcm_left (M + 1) (recordHorizonBound M)
      · exact Nat.dvd_trans (ih (by omega)) (recordHorizonBound_dvd_succ M)

theorem recordHorizonBound_pos_even (M : Nat) :
    0 < recordHorizonBound M ∧ 2 ∣ recordHorizonBound M := by
  induction M with
  | zero => decide
  | succ M ih =>
      refine ⟨?_, Nat.dvd_trans ih.2 (recordHorizonBound_dvd_succ M)⟩
      by_cases h : (M + 1) % 2 = 1
      · simpa [recordHorizonBound, h] using
          Nat.lcm_pos (Nat.zero_lt_succ M) ih.1
      · simpa [recordHorizonBound, h] using ih.1

theorem D_le_recordHorizonBound_of_cap {M n : Nat} (hn : 2 ≤ n)
    (hcap : ∀ j : Nat, 2 ≤ j → j ≤ n → d j ≤ M) :
    D n ≤ recordHorizonBound M := by
  have hH := recordHorizonBound_pos_even M
  have hstart : D 2 ≤ recordHorizonBound M := by
    have htwo := Nat.le_of_dvd hH.1 hH.2
    exact Nat.le_trans (by decide : D 2 ≤ 2) htwo
  exact D_le_even_multiple_of_interval (by decide : 2 ≤ 2) hn
    (Nat.mod_eq_zero_of_dvd hH.2) hstart
    (fun j hj hle =>
      odd_dvd_recordHorizonBound (d_mod_two_eq_one_of_three_le (by omega))
        (hcap j (by omega) hle))

theorem D_succ_eq_self_iff_d_succ_eq_one (n : Nat) :
    D (n + 1) = D n ↔ d (n + 1) = 1 := by
  constructor
  · intro h
    have h' := D_succ_add_one_eq_add_d n
    rw [h] at h'
    exact (Nat.add_left_cancel h').symm
  · intro h
    have h' := D_succ_add_one_eq_add_d n
    rw [h] at h'
    exact Nat.succ.inj h'

/-- A candidate last nontrivial increment before `m`; this is only a predicate.
Existence is proved separately when the endpoint and earlier increment permit it.
-/
def IsLastNontrivialBefore (rho m : Nat) : Prop :=
  2 ≤ rho ∧ rho < m ∧ 1 < d rho ∧
    ∀ j : Nat, rho < j → j ≤ m → d j = 1

/-- For a number at least two, this is the proper-divisor condition for
primality. It keeps the replay checker on the recurrence-side imports. -/
abbrev NoProperFactor (N : Nat) : Prop :=
  ∀ f : Fin N, 2 ≤ f.val → ¬ f.val ∣ N

abbrev NoSmallFactor (N root : Nat) : Prop :=
  ∀ f : Fin (root + 1), 2 ≤ f.val → ¬ f.val ∣ N

/-- Every strict record greater than five through the given index has
its canonical position and both twin candidates have no proper factors. -/
def RecordsVerifiedThrough (N : Nat) : Prop :=
  ∀ {R n : Nat}, 5 < R → 2 ≤ n → n ≤ N → d n = R →
    (∀ j : Nat, 2 ≤ j → j < n → d j < R) →
    n = R + 2 ∧ NoProperFactor (R - 2) ∧ NoProperFactor R

/-- The two caps, bundled so the induction can carry one hypothesis. -/
def TwinPrimeTwoCapBoundFrom (lower : Nat) : Prop :=
  (∀ {M sf Cf p : Nat}, lower ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → Cf ≤ 3 * M + 4) ∧
  (∀ {M sf Cf p : Nat}, lower ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 4 * sf ≤ 7 * M - 1)

theorem attained_previous_maximum_extend {P s : Nat}
    (hs : 2 ≤ s) (hP : IsAttainedPreviousMaximum P (s - 1))
    (hnew : P < d s) : IsAttainedPreviousMaximum (d s) s := by
  refine ⟨?_, ⟨s, hs, Nat.le_refl s, rfl⟩⟩
  intro j hj2 hjs
  by_cases hpred : j ≤ s - 1
  · exact Nat.le_trans (hP.1 j hj2 hpred) (Nat.le_of_lt hnew)
  · rcases Nat.lt_or_ge j s with hlt | hge
    · exact False.elim (hpred (Nat.le_sub_of_add_le (Nat.succ_le_of_lt hlt)))
    · have heq : j = s := Nat.le_antisymm hjs hge
      simpa [heq]

theorem attained_previous_maximum_exists (k : Nat) (hk : 2 ≤ k) :
    ∃ M : Nat, IsAttainedPreviousMaximum M k := by
  obtain ⟨j, rfl⟩ := Nat.le.dest hk
  clear hk
  induction j with
  | zero =>
      refine ⟨d 2, ?_, ⟨2, by decide, by decide, rfl⟩⟩
      intro i hi2 hi
      have heq : i = 2 := by omega
      simp [heq]
  | succ j ih =>
      obtain ⟨M, hM⟩ := ih
      have hindex : 2 + (j + 1) - 1 = 2 + j := by omega
      by_cases hnew : M < d (2 + (j + 1))
      · exact ⟨_, attained_previous_maximum_extend (by omega)
          (by simpa only [hindex] using hM) hnew⟩
      · obtain ⟨r, hr, hrj, hdr⟩ := hM.2
        refine ⟨M, ?_, ⟨r, hr, by omega, hdr⟩⟩
        intro i hi2 hi
        by_cases h : i ≤ 2 + j
        · exact hM.1 i hi2 h
        · have heq : i = 2 + (j + 1) := by omega
          rw [heq]
          omega

theorem attained_previous_maximum_first_occurrence {P k : Nat}
    (hP : IsAttainedPreviousMaximum P k) :
    ∃ r : Nat, 2 ≤ r ∧ r ≤ k ∧ d r = P ∧
      ∀ j : Nat, 2 ≤ j → j < r → d j < P := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      rcases hP.2 with ⟨r, hr2, hrk, hdr⟩
      by_cases hprev : ∃ j : Nat, 2 ≤ j ∧ j < k ∧ d j = P
      · rcases hprev with ⟨j, hj2, hjk, hdj⟩
        have hPj : IsAttainedPreviousMaximum P j := by
          refine ⟨?_, ⟨j, hj2, Nat.le_refl j, hdj⟩⟩
          intro i hi2 hij
          have hjk' : j ≤ k := Nat.le_of_lt hjk
          exact hP.1 i hi2 (Nat.le_trans hij hjk')
        rcases ih j hjk hPj with ⟨s, hs2, hsj, hsd, hsprior⟩
        exact ⟨s, hs2, Nat.le_trans hsj (Nat.le_of_lt hjk), hsd, hsprior⟩
      · have hr_eq : r = k := by
          apply Nat.le_antisymm hrk
          exact Nat.le_of_not_gt (fun hkr => hprev ⟨r, hr2, hkr, hdr⟩)
        refine ⟨k, ?_, Nat.le_refl k, ?_, ?_⟩
        · simpa [hr_eq] using hr2
        · simpa [hr_eq] using hdr
        · intro j hj2 hjk
          have hjle := hP.1 j hj2 (Nat.le_of_lt hjk)
          have hneq : d j ≠ P := by
            intro hdj
            exact hprev ⟨j, hj2, hjk, hdj⟩
          exact Nat.lt_of_le_of_ne hjle hneq

theorem a_le_three_mul (n : Nat) : a n ≤ 3 * n := by
  induction n with
  | zero => decide
  | succ n ih =>
      by_cases hn : 2 ≤ n
      · have hprev : n + 1 - 1 = n := by omega
        have hmap := d_eq_if_gcd_of_two_le (show 2 ≤ n + 1 by omega)
        rw [hprev] at hmap
        have hstep := a_add_d_succ (k := n)
        by_cases hpar : (n + 1) % 2 = 0
        · rw [if_pos hpar] at hmap
          have hnDiv : d (n + 1) ∣ n + 1 := hmap.symm ▸ Nat.gcd_dvd_left _ _
          have haDiv : d (n + 1) ∣ a n := hmap.symm ▸ Nat.gcd_dvd_right _ _
          have hdiv := Nat.dvd_sub (Nat.dvd_mul_left_of_dvd hnDiv 3) haDiv
          have hbound := Nat.le_of_dvd (by omega : 0 < 3 * (n + 1) - a n) hdiv
          omega
        · rw [if_neg hpar, show n + 1 - 2 = n - 1 by omega] at hmap
          have hnDiv : d (n + 1) ∣ n - 1 := hmap.symm ▸ Nat.gcd_dvd_left _ _
          have haDiv : d (n + 1) ∣ a n := hmap.symm ▸ Nat.gcd_dvd_right _ _
          have hthree := Nat.dvd_mul_left_of_dvd hnDiv 3
          have hparity := a_mod_two_of_two_le hn
          have hneq : a n ≠ 3 * (n - 1) := by omega
          by_cases hlt : a n < 3 * (n - 1)
          · have hbound := Nat.le_of_dvd (by omega : 0 < 3 * (n - 1) - a n)
              (Nat.dvd_sub hthree haDiv)
            omega
          · have hbound := Nat.le_of_dvd (by omega : 0 < a n - 3 * (n - 1))
              (Nat.dvd_sub haDiv hthree)
            omega
      · have hcases : n = 0 ∨ n = 1 := by omega
        rcases hcases with rfl | rfl <;> decide

theorem canonical_record_fundamental_predecessor {M : Nat}
    (hM5 : 5 < M) (hModd : M % 2 = 1)
    (ha : a (M + 1) = 2 * M) (hdp : d (M + 2) = M)
    (hBcanon : B (M + 2) + 2 = M) :
    B (M - 1) = 2 ∧ B M = 1 ∧ B (M + 1) = 0 ∧
      d (M + 1) = 1 ∧ d M = 1 ∧ d (M + 2) = M ∧
      B (M + 2) + 2 = M := by
  have hM2 : 2 ≤ M := by omega
  have hM3 : 3 ≤ M := by omega
  have hMminus2 : 2 ≤ M - 1 := by omega
  have hidx : M - 1 + 1 = M := by omega
  have hBsucc : B (M + 1) = 0 := by
    simp only [B]
    rw [ha]
    omega
  have hstepM := excess_succ_add_two hM2
  rw [hBsucc] at hstepM
  have hBMmod := B_mod_two_of_two_le hM2
  have hdnextpos : 1 ≤ d (M + 1) :=
    one_le_d_of_two_le (by omega)
  have hdnextmod := d_mod_two_eq_one_of_three_le (by omega : 3 ≤ M + 1)
  have hBM : B M = 1 := by omega
  have hdnext : d (M + 1) = 1 := by omega
  have hstepMminus := excess_succ_add_two hMminus2
  rw [hidx, hBM] at hstepMminus
  have hBminusmod := B_mod_two_of_two_le hMminus2
  have hdMpos : 1 ≤ d M := one_le_d_of_two_le hM2
  have hdMmod := d_mod_two_eq_one_of_three_le hM3
  have hBminus : B (M - 1) = 2 := by
    by_cases hzero : B (M - 1) = 0
    · have hzero' := B_zero_transition hMminus2 hzero
      rw [hidx] at hzero'
      omega
    · have hpos : 1 ≤ B (M - 1) := Nat.one_le_iff_ne_zero.mpr hzero
      omega
  have hdM : d M = 1 := by omega
  exact ⟨hBminus, hBM, hBsucc, hdnext, hdM, hdp, hBcanon⟩

/-- The canonical index alone forces the usual coordinates and a preceding
fundamental point. -/
theorem canonical_increment_coordinates {R : Nat} (hR : 5 < R)
    (hd : d (R + 2) = R) :
    a (R + 1) = 2 * R ∧ D (R + 2) = 2 * R - 2 ∧ B (R - 1) = 2 := by
  have hodd : R % 2 = 1 := hd ▸ d_mod_two_eq_one_of_three_le (by omega : 3 ≤ R + 2)
  have hmap := d_add_two_of_odd R (by omega : (R + 2) % 2 ≠ 0)
  have hdiv : R ∣ a (R + 1) := by
    have hg := Nat.gcd_dvd_right R (a (R + 1))
    rwa [← hmap, hd] at hg
  obtain ⟨u, hu⟩ := hdiv
  have hapar := a_mod_two_of_two_le (by omega : 2 ≤ R + 1)
  have hupar : u % 2 = 0 := by
    rw [quotient_mod_two_of_left_odd hodd, ← hu, hapar]
    omega
  have halo := two_mul_le_a_add_two (by omega : 2 ≤ R + 1)
  have hahi := a_le_three_mul (R + 1)
  have huhi : u < 4 := by
    by_cases h : u < 4
    · exact h
    have hmul := Nat.mul_le_mul_left R (by omega : 4 ≤ u)
    omega
  have hupos : u ≠ 0 := by
    intro hzero
    rw [hzero, Nat.mul_zero] at hu
    omega
  have ha : a (R + 1) = 2 * R := by
    rw [hu, show u = 2 by omega, Nat.mul_comm]
  have haRecord : a (R + 2) = 3 * R := by
    have hstep : a (R + 1) + d (R + 2) = a (R + 2) := a_add_d_succ
    omega
  have hD : D (R + 2) = 2 * R - 2 := by simp [D, haRecord]; omega
  have hB : B (R + 2) + 2 = R := by simp [B, haRecord]; omega
  exact ⟨ha, hD, (canonical_record_fundamental_predecessor hR hodd ha hd hB).1⟩

theorem exists_last_nontrivial_before {m : Nat} (hm : d m = 1)
    (hex : ∃ q : Nat, 2 ≤ q ∧ q < m ∧ 1 < d q) :
    ∃ rho : Nat, IsLastNontrivialBefore rho m := by
  revert hm hex
  induction m with
  | zero =>
      intro _ hex
      rcases hex with ⟨q, _, hq, _⟩
      exact False.elim (Nat.not_lt_zero q hq)
  | succ m ih =>
      intro hm hex
      by_cases hmone : d m = 1
      · by_cases hpred : ∃ q : Nat, 2 ≤ q ∧ q < m ∧ 1 < d q
        · rcases ih hmone hpred with ⟨rho, hrho⟩
          rcases hrho with ⟨hrho2, hlt, hlarge, htail⟩
          refine ⟨rho, hrho2, Nat.lt_trans hlt (Nat.lt_succ_self m), hlarge, ?_⟩
          intro j hj hjle
          rcases Nat.lt_or_eq_of_le hjle with hjlt | hjeq
          · exact htail j hj (Nat.le_of_lt_succ hjlt)
          · simpa [hjeq] using hm
        · rcases hex with ⟨q, hq2, hqle, hqd⟩
          have hqle' : q ≤ m := Nat.le_of_lt_succ hqle
          have hqm : q = m := by
            rcases Nat.lt_or_eq_of_le hqle' with hqmt | hqeq
            · exact False.elim (hpred ⟨q, hq2, hqmt, hqd⟩)
            · exact hqeq
          subst q
          refine ⟨m, hq2, Nat.lt_succ_self m, hqd, ?_⟩
          intro j hj hjle
          rcases Nat.lt_or_eq_of_le hjle with hjlt | hjeq
          · have hjm : j ≤ m := Nat.le_of_lt_succ hjlt
            exact False.elim ((Nat.not_lt_of_ge hjm) hj)
          · simpa [hjeq] using hm
      · rcases hex with ⟨q, hq2, hqle, _⟩
        have hqle' : q ≤ m := Nat.le_of_lt_succ hqle
        have hm2 : 2 ≤ m := Nat.le_trans hq2 hqle'
        have hdmpos : 1 ≤ d m := one_le_d_of_two_le hm2
        have hdmgt : 1 < d m :=
          Nat.lt_of_le_of_ne hdmpos (fun h => hmone h.symm)
        refine ⟨m, hm2, Nat.lt_succ_self m, hdmgt, ?_⟩
        intro j hj hjle
        rcases Nat.lt_or_eq_of_le hjle with hjlt | hjeq
        · have hjm : j ≤ m := Nat.le_of_lt_succ hjlt
          exact False.elim ((Nat.not_lt_of_ge hjm) hj)
        · simpa [hjeq] using hm

theorem one_interval_const_D_B {l t : Nat} (hl : 2 ≤ l)
    (hone : ∀ j : Nat, l < j → j ≤ l + t → d j = 1) :
    D (l + t) = D l ∧ B (l + t) + t = B l := by
  induction t with
  | zero => simp
  | succ t iht =>
      have hlt : l < l + t + 1 :=
        Nat.lt_succ_of_le (Nat.le_add_right l t)
      have hle : l + t + 1 ≤ l + Nat.succ t := by simp [Nat.add_assoc]
      have hd : d (l + t + 1) = 1 := hone _ hlt hle
      have hone' : ∀ j : Nat, l < j → j ≤ l + t → d j = 1 := by
        intro j hj hjt
        exact hone j hj (Nat.le_trans hjt (Nat.le_add_right (l + t) 1))
      have ih := iht hone'
      have hltwo : 2 ≤ l + t :=
        Nat.le_trans hl (Nat.le_add_right l t)
      have hstep := excess_succ_add_two hltwo
      have hBstep : B (l + t + 1) + 1 = B (l + t) := by
        have hcancel : B (l + t + 1) + 1 + 1 = B (l + t) + 1 := by
          calc
            B (l + t + 1) + 1 + 1 = B (l + t + 1) + 2 := by
              simp [Nat.add_assoc]
            _ = B (l + t) + d (l + t + 1) := hstep
            _ = B (l + t) + 1 := by rw [hd]
        exact Nat.add_right_cancel hcancel
      have hDstep : D (l + t + 1) = D (l + t) :=
        (D_succ_eq_self_iff_d_succ_eq_one (l + t)).2 hd
      constructor
      · calc
          D (l + Nat.succ t) = D (l + t + 1) := by simp [Nat.add_assoc]
          _ = D (l + t) := hDstep
          _ = D l := ih.1
      · calc
          B (l + Nat.succ t) + Nat.succ t =
              B (l + t + 1) + (t + 1) := by simp [Nat.add_assoc]
          _ = (B (l + t + 1) + 1) + t := by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          _ = B (l + t) + t := by rw [hBstep]
          _ = B l := ih.2

theorem first_later_event_D_eq {n C r : Nat} (hn : 2 ≤ n)
    (hC : D n = C) (hnr : n < r)
    (hfirst : ∀ j : Nat, n < j → j < r → d j = 1) :
    D (r - 1) = C := by
  have hle : n ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using Nat.succ_le_of_lt hnr
  obtain ⟨t, ht⟩ := Nat.le.dest hle
  have hr1 : 1 ≤ r := by
    have hn1 : 1 ≤ n := Nat.le_trans (by simp) hn
    exact Nat.le_trans hn1 (Nat.le_of_lt hnr)
  have hone : ∀ j : Nat, n < j → j ≤ n + t → d j = 1 := by
    intro j hnj hjt
    apply hfirst j hnj
    have hjpred : j ≤ r - 1 := by
      exact Nat.le_trans hjt (Nat.le_of_eq ht)
    apply Nat.lt_of_succ_le
    calc
      j + 1 ≤ (r - 1) + 1 := Nat.add_le_add_right hjpred 1
      _ = r := Nat.sub_add_cancel hr1
  have htail := one_interval_const_D_B hn hone
  rw [ht] at htail
  exact htail.1.trans hC

private theorem early_fundamental_mod_six :
    ∀ m : Fin 14, 6 ≤ m.val → B m.val = 2 → m.val % 6 = 0 := by
  decide

private theorem fundamental_last_event_gap {m rho : Nat} (hm : 14 ≤ m)
    (hfund : B m = 2) (hLast : IsLastNontrivialBefore rho m) :
    5 ≤ m - rho := by
  obtain ⟨hρ2, hρm, hEvent, hunit⟩ := hLast
  have hDm := D_eq_self_of_fundamental (by omega : 2 ≤ m) hfund
  have hmeven : m % 2 = 0 := hDm ▸ D_mod_two_eq_zero_of_two_le (by omega)
  have htail := first_later_event_D_eq (r := m + 1) hρ2 (rfl : D rho = D rho)
    (by omega) (fun j hj hjm => hunit j hj (by omega))
  have hDρ : D rho = m := by simpa [hDm] using htail.symm
  have hρ3 : 3 ≤ rho := by
    by_cases h : rho = 2
    · rw [h, show D 2 = 2 by decide] at hDρ
      omega
    · omega
  have hDprev : 2 ≤ D (rho - 1) :=
    Nat.le_trans (by decide : 2 ≤ D 2) (D_le_of_le (by omega))
  have heodd := d_mod_two_eq_one_of_three_le hρ3
  have he3 : 3 ≤ d rho := by omega
  have hupdate := D_succ_add_one_eq_add_d (rho - 1)
  rw [show rho - 1 + 1 = rho by omega, hDρ] at hupdate
  have hmap := constant_D_event_map (by omega : 2 ≤ rho) (rfl : D (rho - 1) = D (rho - 1))
  by_cases hgap : 5 ≤ m - rho
  · exact hgap
  by_cases hpar : rho % 2 = 0
  · rw [if_pos hpar] at hmap
    have hrDiv : d rho ∣ rho := hmap.symm ▸ Nat.gcd_dvd_left _ _
    have hprevDiv : d rho ∣ D (rho - 1) - 1 := hmap.symm ▸ Nat.gcd_dvd_right _ _
    have hmDiv : d rho ∣ m := by
      rw [show m = (D (rho - 1) - 1) + d rho by omega]
      exact Nat.dvd_add hprevDiv (Nat.dvd_refl _)
    obtain ⟨q, hq⟩ := Nat.dvd_sub hmDiv hrDiv
    have hqeven : q % 2 = 0 := by
      rw [quotient_mod_two_of_left_odd heodd, ← hq]
      omega
    have hqpos : q ≠ 0 := by
      intro hzero
      rw [hzero, Nat.mul_zero] at hq
      omega
    have hmul := Nat.mul_le_mul he3 (by omega : 2 ≤ q)
    omega
  · rw [if_neg hpar] at hmap
    have hrDiv : d rho ∣ rho - 2 := hmap.symm ▸ Nat.gcd_dvd_left _ _
    have hprevDiv : d rho ∣ D (rho - 1) + 1 := hmap.symm ▸ Nat.gcd_dvd_right _ _
    have hmDiv : d rho ∣ m + 2 := by
      rw [show m + 2 = (D (rho - 1) + 1) + d rho by omega]
      exact Nat.dvd_add hprevDiv (Nat.dvd_refl _)
    obtain ⟨q, hq⟩ := Nat.dvd_sub hmDiv hrDiv
    rw [show m + 2 - (rho - 2) = m - rho + 4 by omega] at hq
    have hqodd : q % 2 = 1 := by
      rw [quotient_mod_two_of_left_odd heodd, ← hq]
      omega
    have hqone : q = 1 := by
      by_cases h : q = 1
      · exact h
      have hmul := Nat.mul_le_mul he3 (by omega : 3 ≤ q)
      omega
    rw [hqone, Nat.mul_one] at hq
    have hprev : D (rho - 1) = rho - 3 := by omega
    rw [hprev, show rho - 3 + 1 = rho - 2 by omega, Nat.gcd_self] at hmap
    omega

/-- Every fundamental point of the actual recurrence from 6 onward is
divisible by 6. -/
theorem fundamental_point_mod_six {m : Nat} (hm : 6 ≤ m) (hfund : B m = 2) :
    m % 6 = 0 := by
  by_cases hsmall : m < 14
  · exact early_fundamental_mod_six ⟨m, hsmall⟩ hm hfund
  have hDm := D_eq_self_of_fundamental (by omega : 2 ≤ m) hfund
  have hmeven : m % 2 = 0 := hDm ▸ D_mod_two_eq_zero_of_two_le (by omega)
  by_cases hdm : d m = 1
  · obtain ⟨rho, hLast⟩ := exists_last_nontrivial_before hdm
      ⟨2, by decide, by omega, by decide⟩
    have hgap := fundamental_last_event_gap (by omega) hfund hLast
    obtain ⟨hρ2, hρm, _, hunit⟩ := hLast
    have htail := first_later_event_D_eq (r := m + 1) hρ2 (rfl : D rho = D rho)
      (by omega) (fun j hj hjm => hunit j hj (by omega))
    have hDρ : D rho = m := by simpa [hDm] using htail.symm
    have hnotOne : m % 3 ≠ 1 := by
      intro hmod
      have hD := first_later_event_D_eq (r := m - 4) hρ2 hDρ
        (by omega) (fun j hj hjm => hunit j hj (by omega))
      have hmap := constant_D_event_map (by omega : 2 ≤ m - 4) hD
      rw [if_pos (by omega), hunit (m - 4) (by omega) (by omega)] at hmap
      have hdiv := Nat.gcd_eq_one_iff.mp hmap.symm 3
        (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega))
      omega
    have hnotTwo : m % 3 ≠ 2 := by
      intro hmod
      have hD := first_later_event_D_eq (r := m - 3) hρ2 hDρ
        (by omega) (fun j hj hjm => hunit j hj (by omega))
      have hmap := constant_D_event_map (by omega : 2 ≤ m - 3) hD
      rw [if_neg (by omega), hunit (m - 3) (by omega) (by omega)] at hmap
      have hdiv := Nat.gcd_eq_one_iff.mp hmap.symm 3
        (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero (by omega))
      omega
    omega
  · have hstep := excess_succ_add_two (k := m - 1) (by omega)
    rw [show m - 1 + 1 = m by omega, hfund] at hstep
    have hdodd := d_mod_two_eq_one_of_three_le (by omega : 3 ≤ m)
    have hdthree : d m = 3 := by omega
    have hmap := d_eq_if_gcd_of_two_le (by omega : 2 ≤ m)
    rw [if_pos hmeven, hdthree] at hmap
    have hdiv : 3 ∣ m := hmap.symm ▸ Nat.gcd_dvd_left _ _
    have hmod := Nat.mod_eq_zero_of_dvd hdiv
    omega

theorem fundamental_reset {m : Nat} (hm : 2 ≤ m) (hfund : B m = 2) :
    (d (m + 1) = 1 ∧ d (m + 2) = 1 ∧ B (m + 2) = 0 ∧
      d (m + 3) = m + 1 ∧ B (m + 3) + 2 = m + 1) ∨
    (d (m + 1) = 1 ∧ d (m + 2) = 3 ∧ B (m + 2) = 2 ∧
      d (m + 3) = 1 ∧ d (m + 4) = 1 ∧ B (m + 4) = 0 ∧
      d (m + 5) = m + 3 ∧ B (m + 5) + 2 = m + 3) := by
  have hfirst := B_two_transition hm hfund
  have hm0 : m % 2 = 0 := by
    calc
      m % 2 = B m % 2 := (B_mod_two_of_two_le hm).symm
      _ = 2 % 2 := by rw [hfund]
      _ = 0 := by simp
  have hm1 : (m + 1) % 2 = 1 := by simp [Nat.add_mod, hm0]
  rcases B_one_transition (Nat.le_trans hm (by simp)) hm1 hfirst.2 with hcase | hcase
  · rcases hcase with ⟨hd2, hB2⟩
    have hzero := B_zero_transition (k := m + 2) (by omega) hB2
    left
    exact ⟨hfirst.1, hd2, hB2, hzero.1, by simpa using hzero.2⟩
  · rcases hcase with ⟨hd2, hB2⟩
    have htwo := B_two_transition (k := m + 2) (by omega) hB2
    have hm3 : (m + 3) % 2 = 1 := by simp [Nat.add_mod, hm0]
    rcases B_one_transition (k := m + 3) (by omega) hm3 htwo.2 with hcase' | hcase'
    · rcases hcase' with ⟨hd4, hB4⟩
      have hzero := B_zero_transition (k := m + 4) (by omega) hB4
      right
      exact ⟨hfirst.1, hd2, hB2, htwo.1, hd4, hB4,
        hzero.1, by simpa using hzero.2⟩
    · rcases hcase' with ⟨hd4, hB4⟩
      have hmap1 := d_succ_eq_gcd_small_residual (k := m + 1)
        (by omega) hm1 (by simpa [hfirst.2])
      have hmap2 := d_succ_eq_gcd_small_residual (k := m + 3)
        (by omega) hm3 (by simpa [htwo.2])
      have hmap1' : d (m + 2) = Nat.gcd (m + 2) 3 := by
        simpa [hfirst.2] using hmap1
      have hmap2' : d (m + 4) = Nat.gcd (m + 4) 3 := by
        simpa [htwo.2] using hmap2
      have hdiv1 : 3 ∣ m + 2 := by
        have hg := Nat.gcd_dvd_left (m + 2) 3
        rw [← hmap1', hd2] at hg
        exact hg
      have hdiv2 : 3 ∣ m + 4 := by
        have hg := Nat.gcd_dvd_left (m + 4) 3
        rw [← hmap2', hd4] at hg
        exact hg
      rcases hdiv1 with ⟨q1, hq1⟩
      rcases hdiv2 with ⟨q2, hq2⟩
      omega

/-- A large fundamental point always resets after three indices. -/
theorem fundamental_reset_at_three {m : Nat} (hm : 6 ≤ m) (hfund : B m = 2) :
    d (m + 1) = 1 ∧ d (m + 2) = 1 ∧ d (m + 3) = m + 1 := by
  rcases fundamental_reset (by omega : 2 ≤ m) hfund with h | h
  · exact ⟨h.1, h.2.1, h.2.2.2.1⟩
  · have hmod := fundamental_point_mod_six hm hfund
    have hmap := d_eq_if_gcd_of_two_le (by omega : 2 ≤ m + 2)
    rw [if_pos (by omega), h.2.1] at hmap
    have hdiv : 3 ∣ m + 2 := hmap.symm ▸ Nat.gcd_dvd_left _ _
    have hbad := Nat.mod_eq_zero_of_dvd hdiv
    omega

theorem moving_horizon_no_event_telescope {s C : Nat}
    (hs : IsMovingHorizonState s C)
    (hno : ∀ j : Nat, s < j → j ≤ C → d j = 1) :
    D C = C ∧ B C + (C - s) = B s := by
  rcases hs with ⟨hs2, hDs, hsc⟩
  have hsle : s ≤ C := Nat.le_of_lt hsc
  have hsum : s + (C - s) = C := by
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel hsle
  have hone : ∀ j : Nat, s < j → j ≤ s + (C - s) → d j = 1 := by
    intro j hsj hj
    apply hno j hsj
    rw [hsum] at hj
    exact hj
  have htail := one_interval_const_D_B hs2 hone
  constructor
  · calc
      D C = D (s + (C - s)) := congrArg D hsum.symm
      _ = D s := htail.1
      _ = C := hDs
  · calc
      B C + (C - s) = B (s + (C - s)) + (C - s) := by rw [hsum]
      _ = B s := htail.2

/-- A quiet return at a horizon of at least the starting canonical
horizon determines the next strict record. -/
theorem canonical_quiet_return_next_record {M sf finish : Nat}
    (hM : 5 < M) (hF : 2 * M - 2 ≤ finish)
    (hstate : IsMovingHorizonState sf finish) (hfmax : IsAttainedPreviousMaximum M sf)
    (hquiet : ∀ j : Nat, sf < j → j ≤ finish → d j = 1) :
    M < finish + 1 ∧ IsAttainedPreviousMaximum M (finish + 2) ∧
      d (finish + 3) = finish + 1 ∧ D (finish + 2) = finish := by
  have hsf := hstate.2.2
  have hD := (moving_horizon_no_event_telescope hstate hquiet).1
  have hB := B_add_index_eq_D_add_two (by omega : 2 ≤ finish)
  have hfund : B finish = 2 := by omega
  obtain ⟨hd1, hd2, hd3⟩ := fundamental_reset_at_three (by omega) hfund
  have hD1 := (D_succ_eq_self_iff_d_succ_eq_one finish).2 hd1
  have hD2 := (D_succ_eq_self_iff_d_succ_eq_one (finish + 1)).2 hd2
  obtain ⟨i, hi2, his, hdi⟩ := hfmax.2
  refine ⟨by omega, ⟨?_, ⟨i, hi2, by omega, hdi⟩⟩, hd3, hD2.trans (hD1.trans hD)⟩
  intro j hj2 hj
  by_cases hs : j ≤ sf
  · exact hfmax.1 j hj2 hs
  · by_cases hle : j ≤ finish
    · rw [hquiet j (by omega) hle]
      omega
    · have hcases : j = finish + 1 ∨ j = finish + 2 := by omega
      rcases hcases with heq | heq
      · rw [heq, hd1]
        omega
      · rw [heq, hd2]
        omega

theorem first_later_nontrivial_of_exists {n C : Nat} (hn : 2 ≤ n)
    (hex : ∃ j : Nat, n < j ∧ j ≤ C ∧ 1 < d j) :
    ∃ r : Nat, n < r ∧ r ≤ C ∧ 1 < d r ∧
      ∀ j : Nat, n < j → j < r → d j = 1 := by
  induction C using Nat.strongRecOn with
  | ind C ih =>
      rcases hex with ⟨r, hnr, hrC, hdr⟩
      by_cases hprev : ∃ j : Nat, n < j ∧ j < C ∧ 1 < d j
      · rcases hprev with ⟨j, hnj, hjC, hdj⟩
        have hexj : ∃ q : Nat, n < q ∧ q ≤ j ∧ 1 < d q :=
          ⟨j, hnj, Nat.le_refl j, hdj⟩
        rcases ih j hjC hexj with ⟨s, hns, hsj, hds, hprior⟩
        exact ⟨s, hns, Nat.le_trans hsj (Nat.le_of_lt hjC), hds, hprior⟩
      · have hr_eq : r = C := by
          apply Nat.le_antisymm hrC
          exact Nat.le_of_not_gt (fun hrc => hprev ⟨r, hnr, hrc, hdr⟩)
        refine ⟨C, ?_, Nat.le_refl C, ?_, ?_⟩
        · simpa [hr_eq] using hnr
        · simpa [hr_eq] using hdr
        · intro j hnj hjC
          by_cases heq : d j = 1
          · exact heq
          · have hj2 : 2 ≤ j := Nat.le_trans hn (Nat.le_of_lt hnj)
            have hdpos : 1 ≤ d j := one_le_d_of_two_le hj2
            have hdgt : 1 < d j :=
              Nat.lt_of_le_of_ne hdpos (fun h => heq h.symm)
            exact False.elim (hprev ⟨j, hnj, hjC, hdgt⟩)

theorem first_later_nontrivial_dichotomy {n C : Nat} (hn : 2 ≤ n) :
    (∀ j : Nat, n < j → j ≤ C → d j = 1) ∨
      ∃ r : Nat, n < r ∧ r ≤ C ∧ 1 < d r ∧
        ∀ j : Nat, n < j → j < r → d j = 1 := by
  by_cases hex : ∃ j : Nat, n < j ∧ j ≤ C ∧ 1 < d j
  · exact Or.inr (first_later_nontrivial_of_exists hn hex)
  · left
    intro j hnj hjC
    by_cases heq : d j = 1
    · exact heq
    · have hj2 : 2 ≤ j := Nat.le_trans hn (Nat.le_of_lt hnj)
      have hdpos : 1 ≤ d j := one_le_d_of_two_le hj2
      have hdgt : 1 < d j :=
        Nat.lt_of_le_of_ne hdpos (fun h => heq h.symm)
      exact False.elim (hex ⟨j, hnj, hjC, hdgt⟩)

theorem moving_horizon_step_of_exists {s C : Nat}
    (hs : IsMovingHorizonState s C)
    (hex : ∃ j : Nat, s < j ∧ j ≤ C ∧ 1 < d j) :
    ∃ r C', IsMovingHorizonStep s C r C' := by
  rcases first_later_nontrivial_of_exists hs.1 hex with
    ⟨r, hsr, hrC, hdr, hfirst⟩
  have hDrpred : D (r - 1) = C :=
    first_later_event_D_eq hs.1 hs.2.1 hsr hfirst
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hs.1) (Nat.succ_le_of_lt hsr)
  have hrpred : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr3
  have hrsucc : r - 1 + 1 = r :=
    Nat.sub_add_cancel (Nat.le_trans (by simp) hr3)
  have hdr' : 1 < d (r - 1 + 1) := by
    rw [hrsucc]
    exact hdr
  have hgrowth : C + 2 ≤ D r := by
    have h := D_add_two_le_succ_of_two_le hrpred hdr'
    rw [hrsucc, hDrpred] at h
    exact h
  have hr2 : 2 ≤ r := Nat.le_trans hs.1 (Nat.le_of_lt hsr)
  have hrC' : r < D r := by
    calc
      r ≤ C := hrC
      _ < C + 2 := by simp
      _ ≤ D r := hgrowth
  refine ⟨r, D r, ?_⟩
  exact ⟨hs, hsr, hrC, hdr, hfirst, hDrpred, rfl, hgrowth,
    ⟨hr2, rfl, hrC'⟩⟩

theorem moving_horizon_dichotomy {s C : Nat}
    (hs : IsMovingHorizonState s C) :
    (∀ j : Nat, s < j → j ≤ C → d j = 1) ∨
      ∃ r C', IsMovingHorizonStep s C r C' := by
  rcases first_later_nontrivial_dichotomy hs.1 with hno | hex
  · exact Or.inl hno
  · rcases hex with ⟨r, hsr, hrC, hdr, _⟩
    exact Or.inr (moving_horizon_step_of_exists hs ⟨r, hsr, hrC, hdr⟩)

theorem moving_horizon_max_transfer {P s r : Nat}
    (hP : IsAttainedPreviousMaximum P s) (hsr : s < r)
    (hdr : 1 < d r)
    (hfirst : ∀ j : Nat, s < j → j < r → d j = 1) :
    (d r ≤ P ∧ IsAttainedPreviousMaximum P r) ∨
      (P < d r ∧ IsAttainedPreviousMaximum (d r) r) := by
  by_cases hle : d r ≤ P
  · left
    refine ⟨hle, ?_⟩
    rcases hP.2 with ⟨q, hq2, hqs, hdq⟩
    refine ⟨?_, ⟨q, hq2, Nat.le_trans hqs (Nat.le_of_lt hsr), hdq⟩⟩
    intro j hj2 hjr
    by_cases hjs : j ≤ s
    · exact hP.1 j hj2 hjs
    · have hsj : s < j := Nat.lt_of_not_ge hjs
      rcases Nat.lt_or_eq_of_le hjr with hjlt | hjeq
      · rw [hfirst j hsj hjlt]
        have hPpos : 1 ≤ P := by
          rw [← hdq]
          exact one_le_d_of_two_le hq2
        exact hPpos
      · simpa [hjeq] using hle
  · right
    have hgt : P < d r := Nat.lt_of_not_ge hle
    have hr2 : 2 ≤ r := by
      rcases hP.2 with ⟨q, hq2, hqs, _⟩
      exact Nat.le_trans hq2 (Nat.le_trans hqs (Nat.le_of_lt hsr))
    refine ⟨hgt, ?_⟩
    refine ⟨?_, ⟨r, hr2, Nat.le_refl r, rfl⟩⟩
    intro j hj2 hjr
    by_cases hjs : j ≤ s
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hP.1 j hj2 hjs) hgt)
    · have hsj : s < j := Nat.lt_of_not_ge hjs
      rcases Nat.lt_or_eq_of_le hjr with hjlt | hjeq
      · rw [hfirst j hsj hjlt]
        exact Nat.le_of_lt hdr
      · simpa [hjeq]

/-- An actual moving horizon with an attained maximum follows a finite
sequence of old events. Its exit is a fundamental point at the horizon or
a new record inside the horizon. -/
theorem capped_moving_horizon_eventual_exit {M s C : Nat}
    (hstate : IsMovingHorizonState s C) (hP : IsAttainedPreviousMaximum M s) :
    ∃ sf Cf p : Nat, HasMovingHorizonPathTo s C sf Cf p ∧
      IsAttainedPreviousMaximum M sf ∧
      ((B Cf = 2 ∧ ∀ j : Nat, sf < j → j ≤ Cf → d j = 1) ∨
        ∃ r C' : Nat, IsMovingHorizonStep sf Cf r C' ∧ M < d r) := by
  let H := recordHorizonBound M
  have aux (budget : Nat) : ∀ s C : Nat, H - C = budget →
      IsMovingHorizonState s C → IsAttainedPreviousMaximum M s →
      ∃ sf Cf p : Nat, HasMovingHorizonPathTo s C sf Cf p ∧
        IsAttainedPreviousMaximum M sf ∧
        ((B Cf = 2 ∧ ∀ j : Nat, sf < j → j ≤ Cf → d j = 1) ∨
          ∃ r C' : Nat, IsMovingHorizonStep sf Cf r C' ∧ M < d r) := by
    induction budget using Nat.strongRecOn with
    | ind budget ih =>
        intro s C hbudget hs hPs
        rcases moving_horizon_dichotomy hs with hno | ⟨r, C', hstep⟩
        · have hDc := (moving_horizon_no_event_telescope hs hno).1
          have hBc := B_add_index_eq_D_add_two (by have := hs.1; have := hs.2.2; omega : 2 ≤ C)
          exact ⟨s, C, 0, ⟨rfl, rfl, hs⟩, hPs, Or.inl ⟨by omega, hno⟩⟩
        · rcases hstep with ⟨hs', hsr, hrC, hdr, hunit, hDr, hC', hgrowth, hr⟩
          rcases moving_horizon_max_transfer hPs hsr hdr hunit with hOld | hNew
          · have hbound := D_le_recordHorizonBound_of_cap hr.1 hOld.2.1
            have hCbound : C' ≤ H := by rw [hC']; exact hbound
            have hlt : H - C' < budget := by omega
            obtain ⟨sf, Cf, p, hpath, hPsf, hexit⟩ :=
              ih (H - C') hlt r C' rfl hr hOld.2
            exact ⟨sf, Cf, p + 1,
              ⟨hs, r, C', ⟨hs', hsr, hrC, hdr, hunit, hDr, hC', hgrowth, hr⟩, hpath⟩,
              hPsf, hexit⟩
          · exact ⟨s, C, 0, ⟨rfl, rfl, hs⟩, hPs,
              Or.inr ⟨r, C', ⟨hs', hsr, hrC, hdr, hunit, hDr, hC', hgrowth, hr⟩, hNew.1⟩⟩
  exact aux (H - C) s C rfl hstate hP

theorem attained_previous_maximum_record {P k : Nat}
    (hP : IsAttainedPreviousMaximum P k) :
    ∃ r : Nat, 2 ≤ r ∧ r ≤ k ∧ d r = P ∧ IsDifferenceRecord P := by
  rcases attained_previous_maximum_first_occurrence hP with
    ⟨r, hr2, hrk, hdr, hprior⟩
  exact ⟨r, hr2, hrk, hdr, ⟨r, hr2, hdr, hprior⟩⟩

theorem record_value_mod_two_eq_one {R : Nat} (hR : 5 < R)
    (hrec : IsDifferenceRecord R) : R % 2 = 1 := by
  rcases hrec with ⟨w, hw2, hwd, _⟩
  have hw3 : 3 ≤ w := by
    obtain ⟨k, rfl⟩ := Nat.le.dest hw2
    cases k with
    | zero =>
        exfalso
        rw [← hwd] at hR
        simpa [d, a] using hR
    | succ k =>
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (Nat.le_add_right 3 k)
  rw [← hwd]
  exact d_mod_two_eq_one_of_three_le hw3

theorem attained_previous_maximum_value_mod_two_eq_one {P k : Nat}
    (hP : IsAttainedPreviousMaximum P k) (hP5 : 5 < P) :
    P % 2 = 1 := by
  rcases attained_previous_maximum_record hP with
    ⟨r, hr2, _, hdr, hrec⟩
  exact record_value_mod_two_eq_one hP5 hrec

theorem constant_D_event_even_not_dvd_of_le {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (heven : r % 2 = 0)
    (hle : r ≤ C) (hnontriv : 1 < d r) :
    ¬ (C - 1) ∣ r := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hCmod : C % 2 = 0 := by
    rw [← hD]
    exact D_mod_two_eq_zero_of_two_le hs
  have hC2 : 2 ≤ C := by
    rw [← hD]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  have hCpos : 0 < C - 1 :=
    Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by simp) hC2)
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_pos heven] at hmap
  have hdvd : d r ∣ C - 1 := by
    rw [hmap]
    exact Nat.gcd_dvd_right _ _
  have hdle : d r ≤ C - 1 := Nat.le_of_dvd hCpos hdvd
  have hd2 : 2 ≤ d r := Nat.succ_le_of_lt hnontriv
  have hq2 : 2 ≤ C - 1 := Nat.le_trans hd2 hdle
  have hqodd : (C - 1) % 2 = 1 := by
    have hCstep : C - 1 + 1 = C :=
      Nat.sub_add_cancel (Nat.le_trans (by simp) hC2)
    rcases Nat.mod_two_eq_zero_or_one (C - 1) with hq0 | hq1
    · have hbad : C % 2 = 1 := by
        calc
          C % 2 = ((C - 1) + 1) % 2 := by rw [hCstep]
          _ = 1 := by simp [Nat.add_mod, hq0]
      simp [hCmod] at hbad
    · exact hq1
  intro hdiv
  have hqle : C - 1 ≤ r :=
    Nat.le_of_dvd (Nat.lt_of_lt_of_le (by simp) hr) hdiv
  have hupper : r ≤ (C - 1) + 1 := by
    calc
      r ≤ C := hle
      _ = (C - 1) + 1 :=
        (Nat.sub_add_cancel (Nat.le_trans (by simp) hC2)).symm
  rcases Nat.lt_or_eq_of_le hqle with hlt | heq
  · have hreq : r = (C - 1) + 1 :=
      Nat.le_antisymm hupper (Nat.succ_le_of_lt hlt)
    have hone : C - 1 ∣ 1 := by
      have hsub := Nat.dvd_sub hdiv (Nat.dvd_refl (C - 1))
      rw [hreq] at hsub
      simpa [Nat.add_sub_cancel_left] using hsub
    have hqone : C - 1 = 1 := Nat.eq_one_of_dvd_one hone
    have : (2 : Nat) ≤ 1 := by simpa [hqone] using hq2
    simp at this
  · have hbad : (1 : Nat) = 0 := by
      calc
        1 = (C - 1) % 2 := hqodd.symm
        _ = r % 2 := by rw [heq]
        _ = 0 := heven
    cases hbad

theorem constant_D_event_even_proper_iff {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (heven : r % 2 = 0) :
    d r < C - 1 ↔ ¬ (C - 1) ∣ r := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hC2 : 2 ≤ C := by
    rw [← hD]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  have hqpos : 0 < C - 1 := by
    exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by simp) hC2)
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_pos heven] at hmap
  rw [hmap]
  constructor
  · intro hlt hdiv
    rw [Nat.gcd_eq_right hdiv] at hlt
    exact False.elim (Nat.lt_irrefl _ hlt)
  · intro hnot
    apply Nat.lt_of_le_of_ne (Nat.gcd_le_right r hqpos)
    intro heq
    apply hnot
    exact (Nat.gcd_eq_right_iff_dvd).1 heq

theorem three_mul_le_of_odd_dvd_odd_of_proper {x q : Nat}
    (hxodd : x % 2 = 1) (hqodd : q % 2 = 1)
    (hdiv : x ∣ q) (hproper : x < q) :
    3 * x ≤ q := by
  rcases hdiv with ⟨t, ht⟩
  have htodd : t % 2 = 1 := by
    calc
      t % 2 = (x * t) % 2 := quotient_mod_two_of_left_odd hxodd
      _ = q % 2 := by rw [ht]
      _ = 1 := hqodd
  rcases one_or_three_le_of_mod_two_eq_one htodd with ht1 | ht3
  · have heq : q = x := by
      calc
        q = x * t := ht
        _ = x := by rw [ht1]; simp
    have : x < x := by simpa [heq] using hproper
    exact False.elim (Nat.lt_irrefl x this)
  · calc
      3 * x = x * 3 := by simp [Nat.mul_comm]
      _ ≤ x * t := Nat.mul_le_mul_left x ht3
      _ = q := ht.symm

theorem constant_D_event_even_size_bound {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (heven : r % 2 = 0)
    (hproper : d r < C - 1) :
    3 * d r ≤ C - 1 := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hCmod : C % 2 = 0 := by
    rw [← hD]
    exact D_mod_two_eq_zero_of_two_le hs
  have hC2 : 2 ≤ C := by
    rw [← hD]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D (r - 1) := D_le_of_le hs
  have hdmod : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr
  have hCstep : C - 1 + 1 = C :=
    Nat.sub_add_cancel (Nat.le_trans (by simp) hC2)
  have hqmod : (C - 1) % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (C - 1) with hq0 | hq1
    · have hbad : C % 2 = 1 := by
        calc
          C % 2 = ((C - 1) + 1) % 2 := by rw [hCstep]
          _ = 1 := by simp [Nat.add_mod, hq0]
      simp [hCmod] at hbad
    · exact hq1
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_pos heven] at hmap
  have hdiv : d r ∣ C - 1 := by
    rw [hmap]
    exact Nat.gcd_dvd_right _ _
  exact three_mul_le_of_odd_dvd_odd_of_proper hdmod hqmod hdiv hproper

theorem constant_D_event_even_size_bound_of_le {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (heven : r % 2 = 0)
    (hle : r ≤ C) (hnontriv : 1 < d r) :
    3 * d r ≤ C - 1 := by
  apply constant_D_event_even_size_bound hr hD heven
  exact (constant_D_event_even_proper_iff hr hD heven).2
    (constant_D_event_even_not_dvd_of_le hr hD heven hle hnontriv)

theorem constant_D_event_odd_not_dvd_of_le {r C : Nat} (hr : 3 ≤ r)
    (hle : r ≤ C) :
    ¬ (C + 1) ∣ r - 2 := by
  intro hdiv
  have hr2 : 0 < r - 2 :=
    Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by simp) hr)
  have hqle : C + 1 ≤ r - 2 := Nat.le_of_dvd hr2 hdiv
  have hbad : C + 1 ≤ C :=
    Nat.le_trans hqle (Nat.le_trans (Nat.sub_le r 2) hle)
  exact (Nat.not_succ_le_self C) hbad

theorem constant_D_event_odd_proper_iff {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (hodd : r % 2 ≠ 0) :
    d r < C + 1 ↔ ¬ (C + 1) ∣ r - 2 := by
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_neg hodd] at hmap
  rw [hmap]
  constructor
  · intro hlt hdiv
    rw [Nat.gcd_eq_right hdiv] at hlt
    exact False.elim (Nat.lt_irrefl _ hlt)
  · intro hnot
    apply Nat.lt_of_le_of_ne (Nat.gcd_le_right (r - 2) (by simp))
    intro heq
    apply hnot
    exact (Nat.gcd_eq_right_iff_dvd).1 heq

theorem constant_D_event_odd_size_bound {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (hodd : r % 2 ≠ 0)
    (hproper : d r < C + 1) :
    3 * d r ≤ C + 1 := by
  have hs : 2 ≤ r - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_assoc] using hr
  have hCmod : C % 2 = 0 := by
    rw [← hD]
    exact D_mod_two_eq_zero_of_two_le hs
  have hdmod : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr
  have hqmod : (C + 1) % 2 = 1 := by simp [Nat.add_mod, hCmod]
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr) hD
  rw [if_neg hodd] at hmap
  have hdiv : d r ∣ C + 1 := by
    rw [hmap]
    exact Nat.gcd_dvd_right _ _
  exact three_mul_le_of_odd_dvd_odd_of_proper hdmod hqmod hdiv hproper

theorem constant_D_event_odd_size_bound_of_le {r C : Nat} (hr : 3 ≤ r)
    (hD : D (r - 1) = C) (hodd : r % 2 ≠ 0)
    (hle : r ≤ C) :
    3 * d r ≤ C + 1 := by
  apply constant_D_event_odd_size_bound hr hD hodd
  exact (constant_D_event_odd_proper_iff hr hD hodd).2
    (constant_D_event_odd_not_dvd_of_le hr hle)

/-- An escape inside the horizon can only happen once the horizon
exceeds three times the previous maximum by at least five. -/
theorem moving_horizon_new_record_horizon_lower_bound {M s C r C' : Nat}
    (hM : 5 < M) (hP : IsAttainedPreviousMaximum M s)
    (hstep : IsMovingHorizonStep s C r C') (hnew : M < d r) :
    3 * M + 5 ≤ C := by
  obtain ⟨hs, hsr, hrC, hdr, _, hD, _, _, _⟩ := hstep
  have hr3 : 3 ≤ r := by have := hs.1; omega
  have hModd := attained_previous_maximum_value_mod_two_eq_one hP hM
  have hdodd := d_mod_two_eq_one_of_three_le hr3
  by_cases hpar : r % 2 = 0
  · have hsize := constant_D_event_even_size_bound_of_le hr3 hD hpar hrC hdr
    omega
  · have hsize := constant_D_event_odd_size_bound_of_le hr3 hD hpar hrC
    omega

theorem moving_horizon_path_endpoint {s C sf Cf q : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf q) :
    IsMovingHorizonState sf Cf := by
  induction q generalizing s C with
  | zero =>
      rcases hpath with ⟨hsf, hCf, hstate⟩
      simpa [hsf, hCf] using hstate
  | succ q ih =>
      rcases hpath with ⟨_, r, C', _, htail⟩
      exact ih htail

theorem moving_horizon_step_update {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    C' = C + (d r - 1) := by
  rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, hC', _, _⟩
  have hr1 : 1 ≤ r := Nat.le_trans (by simp) (Nat.le_trans hs.1 (Nat.le_of_lt hsr))
  have hrsucc : r - 1 + 1 = r := Nat.sub_add_cancel hr1
  have hDstep : D r = C + (d r - 1) := by
    have h := D_succ_eq_D_add_d_sub_one (r - 1)
    rw [hrsucc, hDr] at h
    exact h
  exact hC'.trans hDstep

theorem moving_horizon_step_event_ge_three
    {s C r C' : Nat} (hstep : IsMovingHorizonStep s C r C') :
    3 ≤ d r := by
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hstep.1.1)
      (Nat.succ_le_of_lt hstep.2.1)
  have hdodd : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr3
  rcases one_or_three_le_of_mod_two_eq_one hdodd with hd1 | hd3
  · have hbad : (1 : Nat) < 1 := by simpa [hd1] using hstep.2.2.2.1
    exact False.elim (Nat.lt_irrefl 1 hbad)
  · exact hd3

theorem moving_horizon_first_hit_map {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 ∧ d r = Nat.gcd r (C - 1) ∧ 1 < d r ∧
        (∀ j : Nat, s < j → j < r →
          (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
          (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1))) ∨
      (r % 2 = 1 ∧ d r = Nat.gcd (r - 2) (C + 1) ∧ 1 < d r ∧
        (∀ j : Nat, s < j → j < r →
          (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
          (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1))) := by
  rcases hstep with ⟨hs, hsr, hrC, hdr, hfirst, hDr, hC', hgrowth, hrstate⟩
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hs.1) (Nat.succ_le_of_lt hsr)
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
  have hunit : ∀ j : Nat, s < j → j < r →
      (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
      (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1) := by
    intro j hsj hjr
    have hj2 : 2 ≤ j := Nat.le_trans hs.1 (Nat.le_of_lt hsj)
    have hfirstj : ∀ l : Nat, s < l → l < j → d l = 1 := by
      intro l hsl hlj
      exact hfirst l hsl (Nat.lt_trans hlj hjr)
    have hDj : D (j - 1) = C :=
      first_later_event_D_eq hs.1 hs.2.1 hsj hfirstj
    have hjmap := constant_D_event_map hj2 hDj
    have hdj : d j = 1 := hfirst j hsj hjr
    constructor
    · intro hevenj
      rw [if_pos hevenj] at hjmap
      rw [hjmap] at hdj
      exact hdj
    · intro hoddj
      have hjne : j % 2 ≠ 0 := by simp [hoddj]
      rw [if_neg hjne] at hjmap
      rw [hjmap] at hdj
      exact hdj
  by_cases heven : r % 2 = 0
  · left
    rw [if_pos heven] at hmap
    exact ⟨heven, hmap, hdr, hunit⟩
  · right
    have hodd : r % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one r with hzero | hone
      · exact False.elim (heven hzero)
      · exact hone
    rw [if_neg heven] at hmap
    exact ⟨hodd, hmap, hdr, hunit⟩

private theorem moving_horizon_unit_gcd {s C r C' j : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hsj : s < j) (hjr : j < r) :
    (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
      (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1) := by
  rcases moving_horizon_first_hit_map hstep with h | h
  · exact h.2.2.2 j hsj hjr
  · exact h.2.2.2 j hsj hjr

private theorem next_multiple_with_parity {s v parity : Nat}
    (hv : 0 < v) (hvodd : v % 2 = 1) (hparity : parity < 2) :
    ∃ j : Nat, s < j ∧ j ≤ s + 2 * v ∧ v ∣ j ∧ j % 2 = parity := by
  let k := s / v + 1
  have hquot := Nat.div_add_mod s v
  have hrem := Nat.mod_lt s hv
  have hk : v * k = v * (s / v) + v := by simp [k, Nat.mul_add]
  by_cases hp : k % 2 = parity
  · refine ⟨v * k, by omega, by omega, ⟨k, rfl⟩, ?_⟩
    simp [Nat.mul_mod, hvodd, hp, Nat.mod_eq_of_lt hparity]
  · have hp' : (k + 1) % 2 = parity := by omega
    have hnext : v * (k + 1) = v * k + v := by simp [Nat.mul_add]
    refine ⟨v * (k + 1), by omega, by omega, ⟨k + 1, rfl⟩, ?_⟩
    simp [Nat.mul_mod, hvodd, hp', Nat.mod_eq_of_lt hparity]

private theorem odd_factor {v w : Nat} (hodd : w % 2 = 1) (hv : v ∣ w) :
    v % 2 = 1 := by
  obtain ⟨k, rfl⟩ := hv
  rw [Nat.mul_mod] at hodd
  by_cases hzero : v % 2 = 0
  · simp [hzero] at hodd
  · omega

/-- Any nonunit divisor of the even-event horizon term bounds the first gap. -/
theorem moving_horizon_gap_le_twice_even_factor {s C r C' v : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hv : 1 < v) (hdiv : v ∣ C - 1) :
    r - s ≤ 2 * v := by
  have hC : C % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
  have hCpos : 0 < C := Nat.zero_lt_of_lt hstep.1.2.2
  have hvodd := odd_factor (by omega : (C - 1) % 2 = 1) hdiv
  obtain ⟨j, hsj, hj, hvj, hpar⟩ :=
    next_multiple_with_parity (s := s) (parity := 0) (by omega : 0 < v) hvodd (by decide)
  by_cases h : r - s ≤ 2 * v
  · exact h
  · have hunit := (moving_horizon_unit_gcd hstep hsj (by omega)).1 hpar
    have hvone := Nat.gcd_eq_one_iff.mp hunit v hvj hdiv
    omega

/-- Any nonunit divisor of the odd-event horizon term bounds the first gap. -/
theorem moving_horizon_gap_le_twice_odd_factor {s C r C' v : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hv : 1 < v) (hdiv : v ∣ C + 1) :
    r - s ≤ 2 * v := by
  have hC : C % 2 = 0 := hstep.1.2.1 ▸ D_mod_two_eq_zero_of_two_le hstep.1.1
  have hvodd := odd_factor (by omega : (C + 1) % 2 = 1) hdiv
  obtain ⟨j, hsj, hj, hvj, hpar⟩ :=
    next_multiple_with_parity (s := s - 2) (parity := 1) (by omega : 0 < v) hvodd (by decide)
  have hs : 2 ≤ s := hstep.1.1
  by_cases h : r - s ≤ 2 * v
  · exact h
  · have hunit := (moving_horizon_unit_gcd hstep (j := j + 2) (by omega) (by omega)).2
      (by omega)
    have hvone := Nat.gcd_eq_one_iff.mp hunit v (by simpa using hvj) hdiv
    omega

theorem moving_horizon_step_event_package {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r % 2 = 0 ∧ d r ∣ C - 1 ∧ d r < C - 1 ∧ 3 * d r ≤ C - 1) ∨
      (r % 2 = 1 ∧ d r ∣ C + 1 ∧ d r < C + 1 ∧ 3 * d r ≤ C + 1) := by
  rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, _, _, _⟩
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hs.1) (Nat.succ_le_of_lt hsr)
  by_cases heven : r % 2 = 0
  · left
    have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
    rw [if_pos heven] at hmap
    have hdiv : d r ∣ C - 1 := by
      rw [hmap]
      exact Nat.gcd_dvd_right _ _
    have hproper : d r < C - 1 :=
      (constant_D_event_even_proper_iff hr3 hDr heven).2
        (constant_D_event_even_not_dvd_of_le hr3 hDr heven hrC hdr)
    have hbound : 3 * d r ≤ C - 1 :=
      constant_D_event_even_size_bound_of_le hr3 hDr heven hrC hdr
    exact ⟨heven, hdiv, hproper, hbound⟩
  · right
    have hodd : r % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one r with hzero | hone
      · exact False.elim (heven hzero)
      · exact hone
    have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
    rw [if_neg heven] at hmap
    have hdiv : d r ∣ C + 1 := by
      rw [hmap]
      exact Nat.gcd_dvd_right _ _
    have hproper : d r < C + 1 :=
      (constant_D_event_odd_proper_iff hr3 hDr heven).2
        (constant_D_event_odd_not_dvd_of_le hr3 hrC)
    have hbound : 3 * d r ≤ C + 1 :=
      constant_D_event_odd_size_bound_of_le hr3 hDr heven hrC
    exact ⟨hodd, hdiv, hproper, hbound⟩

theorem moving_horizon_step_gap_le_twice_increment_factor {s C r C' f : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hf : 1 < f) (hdiv : f ∣ d r) :
    r - s ≤ 2 * f := by
  rcases moving_horizon_step_event_package hstep with ⟨_, hd, _, _⟩ | ⟨_, hd, _, _⟩
  · exact moving_horizon_gap_le_twice_even_factor hstep hf (Nat.dvd_trans hdiv hd)
  · exact moving_horizon_gap_le_twice_odd_factor hstep hf (Nat.dvd_trans hdiv hd)

theorem moving_horizon_step_gap_le_twice_increment {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') : r - s ≤ 2 * d r :=
  moving_horizon_step_gap_le_twice_increment_factor hstep hstep.2.2.2.1 (Nat.dvd_refl _)

private theorem moving_horizon_step_gap_le_three_growth {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') : r - s ≤ 3 * (C' - C) := by
  have he3 := moving_horizon_step_event_ge_three hstep
  have hup := moving_horizon_step_update hstep
  have hgap := moving_horizon_step_gap_le_twice_increment hstep
  omega

/-- A first-hit path travels at most three indices per unit of horizon growth. -/
theorem moving_horizon_path_gap_le_three_growth {s C sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf p) :
    s ≤ sf ∧ C ≤ Cf ∧ sf - s ≤ 3 * (Cf - C) := by
  induction p generalizing s C with
  | zero =>
      obtain ⟨rfl, rfl, _⟩ := hpath
      omega
  | succ p ih =>
      obtain ⟨_, r, C', hstep, htail⟩ := hpath
      obtain ⟨hrf, hCf, htailgap⟩ := ih htail
      have hsr := hstep.2.1
      have hup := moving_horizon_step_update hstep
      have hgap := moving_horizon_step_gap_le_three_growth hstep
      omega

private theorem gcd_eq_one_of_no_small_factor {N j root : Nat}
    (hj : 0 < j) (hlt : j < N) (hcheck : NoSmallFactor N root)
    (hroot : N < (root + 1) * (root + 1)) : Nat.gcd j N = 1 := by
  let g := Nat.gcd j N
  have hdivj : g ∣ j := Nat.gcd_dvd_left _ _
  have hdivN : g ∣ N := Nat.gcd_dvd_right _ _
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hj
  have hgle := Nat.le_of_dvd hj hdivj
  by_cases h : g = 1
  · exact h
  · have hg2 : 2 ≤ g := by omega
    by_cases hsmall : g ≤ root
    · exact False.elim ((hcheck ⟨g, by omega⟩ hg2) hdivN)
    · obtain ⟨q, hq⟩ := hdivN
      have hq2 : 2 ≤ q := by
        by_cases hq' : 2 ≤ q
        · exact hq'
        · have hm := Nat.mul_le_mul_left g (show q ≤ 1 by omega)
          rw [← hq, Nat.mul_one] at hm
          omega
      by_cases hsmall' : q ≤ root
      · have hdivq : q ∣ N := ⟨g, by simpa [Nat.mul_comm] using hq⟩
        exact False.elim ((hcheck ⟨q, by omega⟩ hq2) hdivq)
      · have hm := Nat.mul_le_mul (show root + 1 ≤ g by omega) (show root + 1 ≤ q by omega)
        omega

theorem no_proper_factor_of_no_small_factor {N root : Nat}
    (hcheck : NoSmallFactor N root) (hroot : N < (root + 1) * (root + 1)) : NoProperFactor N := by
  intro f hf hdiv
  have h := gcd_eq_one_of_no_small_factor (by omega : 0 < f.val) f.isLt hcheck hroot
  have hdvd := Nat.dvd_gcd (Nat.dvd_refl f.val) hdiv
  rw [h] at hdvd
  have := Nat.eq_one_of_dvd_one hdvd
  omega

private theorem quiet_return_no_small_factors {s C root : Nat}
    (hstate : IsMovingHorizonState s C)
    (hquiet : ∀ j : Nat, s < j → j ≤ C → d j = 1)
    (hlong : 2 * root < C - s) :
    NoSmallFactor (C - 1) root ∧ NoSmallFactor (C + 1) root := by
  have hs := hstate.1
  have hsc := hstate.2.2
  have hCe : C % 2 = 0 := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hs
  have hgcd (j : Nat) (hsj : s < j) (hjC : j ≤ C) :
      (j % 2 = 0 → Nat.gcd j (C - 1) = 1) ∧
        (j % 2 = 1 → Nat.gcd (j - 2) (C + 1) = 1) := by
    have hD := first_later_event_D_eq hs hstate.2.1 hsj
      (fun i hsi hij => hquiet i hsi (by omega))
    have hmap := constant_D_event_map (by omega : 2 ≤ j) hD
    rw [hquiet j hsj hjC] at hmap
    constructor
    · intro h
      simpa only [h, if_pos] using hmap.symm
    · intro h
      simpa only [h, Nat.one_ne_zero, if_false] using hmap.symm
  constructor
  · intro f hf hdiv
    have hfle := f.isLt
    have hfodd : f.val % 2 = 1 := by
      by_cases h : f.val % 2 = 0
      · have h2 : 2 ∣ f.val := Nat.dvd_of_mod_eq_zero h
        have := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h2 hdiv)
        omega
      · omega
    let j := C - 1 - f.val
    have hsj : s < j := by omega
    have hjC : j ≤ C := by omega
    have hpar : j % 2 = 0 := by omega
    have hjdiv : f.val ∣ j := Nat.dvd_sub hdiv (Nat.dvd_refl _)
    have hcontra := Nat.dvd_gcd hjdiv hdiv
    rw [(hgcd j hsj hjC).1 hpar] at hcontra
    have := Nat.eq_one_of_dvd_one hcontra
    omega
  · intro f hf hdiv
    have hfle := f.isLt
    let j := C + 3 - 2 * f.val
    have hsj : s < j := by omega
    have hjC : j ≤ C := by omega
    have hpar : j % 2 = 1 := by omega
    have hsub : j - 2 = C + 1 - 2 * f.val := by omega
    have hjdiv : f.val ∣ j - 2 := by
      rw [hsub]
      exact Nat.dvd_sub hdiv (Nat.dvd_mul_left_of_dvd (Nat.dvd_refl f.val) 2)
    have hcontra := Nat.dvd_gcd hjdiv hdiv
    rw [(hgcd j hsj hjC).2 hpar] at hcontra
    have := Nat.eq_one_of_dvd_one hcontra
    omega

theorem quiet_return_no_proper_factors {s C : Nat}
    (hstate : IsMovingHorizonState s C)
    (hquiet : ∀ j : Nat, s < j → j ≤ C → d j = 1)
    (hlong : 2 * Nat.sqrt (C + 1) < C - s) :
    NoProperFactor (C - 1) ∧ NoProperFactor (C + 1) := by
  obtain ⟨hlo, hhi⟩ := quiet_return_no_small_factors hstate hquiet hlong
  have hroot : C + 1 < (Nat.sqrt (C + 1) + 1) * (Nat.sqrt (C + 1) + 1) :=
    Nat.lt_succ_sqrt (C + 1)
  exact ⟨no_proper_factor_of_no_small_factor hlo (by omega),
    no_proper_factor_of_no_small_factor hhi hroot⟩

/-- E13a: the exact threshold, `4*s ≤ 7*M - 1`.  **COMPILES.** -/
private theorem b_tight {M s C : Nat} (hM : 968 ≤ M) (h : 4 * s ≤ 7 * M - 1)
    (hlo : 2 * M - 2 ≤ C) (hhi : C ≤ 3 * M + 4) : 2 * Nat.sqrt (C + 1) < C - s := by
  let q := Nat.sqrt (C + 1); let b := M / 8
  have hb : 121 ≤ b := by omega
  have hb2 := Nat.mul_le_mul_right b hb
  have hq2 : q * q ≤ C + 1 := Nat.sqrt_le _
  have hqb : q < b := by
    by_cases hq : q < b
    · exact hq
    · have hsq := Nat.mul_le_mul (show b ≤ q by omega) (show b ≤ q by omega)
      omega
  change 2 * q < C - s; omega

/-- The quiet gap at the tight threshold `4*s ≤ 7*M-1`. -/
private theorem quiet_gap_tight {M s C : Nat}
    (hM : 968 ≤ M) (h4 : 4 * s ≤ 7 * M - 1)
    (hlo : 2 * M - 2 ≤ C) (hhi : C ≤ 3 * M + 4) :
    2 * Nat.sqrt (C + 1) < C - s :=
  b_tight hM h4 hlo hhi

/-- **THE DECOMPOSED GATE.**  `canonical_next_record_factors_of_short_travel`
with the parent replaced by two strictly weaker, separately-stated caps. -/
theorem canonical_next_record_factors_of_two_caps_tight {M : Nat}
    (hM : 968 ≤ M) (hcanon : d (M + 2) = M)
    (hmax : IsAttainedPreviousMaximum M (M + 2))
    (hA : ∀ {sf Cf p : Nat},
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → Cf ≤ 3 * M + 4)
    (hB : ∀ {sf Cf p : Nat},
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 4 * sf ≤ 7 * M - 1) :
    ∃ C : Nat, M < C + 1 ∧ IsAttainedPreviousMaximum M (C + 2) ∧
      d (C + 3) = C + 1 ∧ NoProperFactor (C - 1) ∧ NoProperFactor (C + 1) := by
  have hM5 : 5 < M := by omega
  have hstart : IsMovingHorizonState (M + 2) (2 * M - 2) :=
    ⟨by omega, (canonical_increment_coordinates hM5 hcanon).2.1, by omega⟩
  obtain ⟨sf, Cf, p, hpath, hfmax, hexit⟩ := capped_moving_horizon_eventual_exit hstart hmax
  have hstate := moving_horizon_path_endpoint hpath
  have hhi := hA hpath hfmax
  have h4sf := hB hpath hfmax
  have hlo := (moving_horizon_path_gap_le_three_growth hpath).2.1
  rcases hexit with ⟨_, hquiet⟩ | ⟨r, C', hstep, hnew⟩
  · obtain ⟨hgt, hpre, hd, _⟩ := canonical_quiet_return_next_record hM5 hlo hstate hfmax hquiet
    obtain ⟨hminus, hplus⟩ := quiet_return_no_proper_factors hstate hquiet
      (quiet_gap_tight hM h4sf hlo hhi)
    exact ⟨Cf, hgt, hpre, hd, hminus, hplus⟩
  · have hlow := moving_horizon_new_record_horizon_lower_bound hM5 hfmax hstep hnew
    omega

private def replayGcd (j C : Nat) : Nat :=
  if j % 2 = 0 then Nat.gcd j (C - 1) else Nat.gcd (j - 2) (C + 1)

private def replayQuietCheck (s C r : Nat) : Bool :=
  (List.range (r - s - 1)).all (fun i => replayGcd (s + i + 1) C == 1)

/-- Check that the supplied hits give an old-event path ending at the
supplied horizon. The indices in the open gaps are checked separately. -/
def recordReplayCheck (M s C : Nat) (hits : List Nat) (finish : Nat) : Bool :=
  match hits with
  | [] => C == finish
  | r :: rest =>
      let e := replayGcd r C
      (decide (s < r ∧ r ≤ C ∧ 1 < e ∧ e ≤ M) && replayQuietCheck s C r) &&
      recordReplayCheck M r (C + e - 1) rest finish

private def noSmallFactorCheck (N root : Nat) : Bool :=
  (List.range (root - 1)).all (fun i => N % (i + 2) != 0)

/-- Check the two horizon terms using only divisors up to their square
roots. This avoids iterating over the long final quiet tail. -/
def recordReturnCheck (C root : Nat) : Bool :=
  (decide (C + 1 < (root + 1) * (root + 1)) && noSmallFactorCheck (C - 1) root) &&
    noSmallFactorCheck (C + 1) root

/-- Each certificate segment supplies a terminal horizon and the indices
of its nonunit increments. The terminal horizon fixes the next record. -/
def recordPrefixCheck (M final : Nat) (segments : List (Nat × Nat × List Nat)) : Bool :=
  match segments with
  | [] => M == final
  | (finish, root, hits) :: rest =>
      (recordReplayCheck M (M + 2) (2 * M - 2) hits finish && recordReturnCheck finish root) &&
      recordPrefixCheck (finish + 1) final rest

theorem moving_horizon_path_index_le {s C sf Cf q : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf q) : s ≤ sf := by
  induction q generalizing s C with
  | zero =>
      rcases hpath with ⟨hsf, _, _⟩
      omega
  | succ q ih =>
      rcases hpath with ⟨_, r, C', hstep, htail⟩
      have hrest := ih htail
      have hsr : s < r := hstep.2.1
      omega

private theorem replay_unit_interval {s C t : Nat} (hs : 2 ≤ s) (hD : D s = C)
    (hquiet : ∀ j : Nat, s < j → j ≤ t → replayGcd j C = 1) :
    ∀ j : Nat, s < j → j ≤ t → d j = 1 := by
  rcases first_later_nontrivial_dichotomy (C := t) hs with h | ⟨r, hsr, hrt, hdr, hfirst⟩
  · exact h
  · have hprev := first_later_event_D_eq hs hD hsr hfirst
    have hmap : d r = replayGcd r C := constant_D_event_map (by omega) hprev
    rw [hmap, hquiet r hsr hrt] at hdr
    omega

private theorem checked_replay_step {s C r : Nat} (hstate : IsMovingHorizonState s C)
    (hsr : s < r) (hrC : r ≤ C) (he : 1 < replayGcd r C)
    (hquiet : ∀ j : Nat, s < j → j < r → replayGcd j C = 1) :
    IsMovingHorizonStep s C r (C + replayGcd r C - 1) ∧ d r = replayGcd r C := by
  have hgcd (j : Nat) (hsj : s < j) (hjr : j ≤ r - 1) : replayGcd j C = 1 := by
    exact hquiet j hsj (by omega)
  have hunit := replay_unit_interval hstate.1 hstate.2.1 hgcd
  have hfirst (j : Nat) (hsj : s < j) (hjr : j < r) : d j = 1 :=
    hunit j hsj (by omega)
  have hDprev := first_later_event_D_eq hstate.1 hstate.2.1 hsr hfirst
  have hr3 : 3 ≤ r := by have := hstate.1; omega
  have hd : d r = replayGcd r C := constant_D_event_map (by omega) hDprev
  have hDstep := D_succ_add_one_eq_add_d (r - 1)
  rw [show r - 1 + 1 = r by omega, hDprev, hd] at hDstep
  have hD : D r = C + replayGcd r C - 1 := by omega
  have hodd := d_mod_two_eq_one_of_three_le hr3
  have hgrowth : C + 2 ≤ C + replayGcd r C - 1 := by omega
  exact ⟨⟨hstate, hsr, hrC, by omega, hfirst, hDprev, hD.symm, hgrowth,
    ⟨by omega, hD, by omega⟩⟩, hd⟩

private theorem replayQuietCheck_sound {s C r : Nat} (h : replayQuietCheck s C r = true) :
    ∀ j : Nat, s < j → j < r → replayGcd j C = 1 := by
  intro j hsj hjr
  have hi : j - s - 1 ∈ List.range (r - s - 1) := List.mem_range.2 (by omega)
  have htest := (List.all_eq_true.mp h) (j - s - 1) hi
  change (replayGcd (s + (j - s - 1) + 1) C == 1) = true at htest
  simpa only [show s + (j - s - 1) + 1 = j by omega, beq_iff_eq] using htest

/-- The checked list determines the exact endpoint, including an empty
list whose endpoint is the starting index. -/
theorem recordReplayCheck_sound_last {M s C finish : Nat} (hits : List Nat)
    (hstate : IsMovingHorizonState s C) (hmax : IsAttainedPreviousMaximum M s)
    (hcheck : recordReplayCheck M s C hits finish = true) :
    HasMovingHorizonPathTo s C (hits.getLastD s) finish hits.length ∧
      IsAttainedPreviousMaximum M (hits.getLastD s) := by
  induction hits generalizing s C with
  | nil =>
      have hfinish : C = finish := by simpa [recordReplayCheck] using hcheck
      subst finish
      exact ⟨⟨rfl, rfl, hstate⟩, hmax⟩
  | cons r rest ih =>
      simp only [recordReplayCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      obtain ⟨⟨⟨hsr, hrC, he, hcap⟩, hquiet⟩, hrest⟩ := hcheck
      obtain ⟨hstep, hd⟩ := checked_replay_step hstate hsr hrC he (replayQuietCheck_sound hquiet)
      have hmax' : IsAttainedPreviousMaximum M r := by
        rcases moving_horizon_max_transfer hmax hsr hstep.2.2.2.1 hstep.2.2.2.2.1 with h | h
        · exact h.2
        · have := h.1
          omega
      obtain ⟨hpath, hfmax⟩ := ih hstep.2.2.2.2.2.2.2.2 hmax' hrest
      rw [List.getLastD_cons]
      exact ⟨⟨hstate, r, C + replayGcd r C - 1, hstep, hpath⟩, hfmax⟩

theorem recordReplayCheck_sound {M s C finish : Nat} (hits : List Nat)
    (hstate : IsMovingHorizonState s C) (hmax : IsAttainedPreviousMaximum M s)
    (hcheck : recordReplayCheck M s C hits finish = true) :
    ∃ sf : Nat, HasMovingHorizonPathTo s C sf finish hits.length ∧
      IsAttainedPreviousMaximum M sf :=
  ⟨hits.getLastD s, recordReplayCheck_sound_last hits hstate hmax hcheck⟩

private theorem noSmallFactorCheck_sound {N root : Nat} (h : noSmallFactorCheck N root = true) :
    NoSmallFactor N root := by
  intro f hf hdiv
  have hfle := f.isLt
  have hi : f.val - 2 ∈ List.range (root - 1) := List.mem_range.2 (by omega)
  have htest := (List.all_eq_true.mp h) (f.val - 2) hi
  change (N % (f.val - 2 + 2) != 0) = true at htest
  simp [show f.val - 2 + 2 = f.val by omega, Nat.mod_eq_zero_of_dvd hdiv] at htest

private theorem recordReturnCheck_conditions {C root : Nat} (h : recordReturnCheck C root = true) :
    C + 1 < (root + 1) * (root + 1) ∧ NoSmallFactor (C - 1) root ∧ NoSmallFactor (C + 1) root := by
  simp only [recordReturnCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, noSmallFactorCheck_sound h.1.2, noSmallFactorCheck_sound h.2⟩

private theorem recordReturnCheck_sound {s C root : Nat} (hstate : IsMovingHorizonState s C)
    (hcheck : recordReturnCheck C root = true) :
    ∀ j : Nat, s < j → j ≤ C → d j = 1 := by
  have hterms := recordReturnCheck_conditions hcheck
  have hCe : C % 2 = 0 := hstate.2.1 ▸ D_mod_two_eq_zero_of_two_le hstate.1
  have hs2 := hstate.1
  apply replay_unit_interval hs2 hstate.2.1
  intro j hsj hjC
  unfold replayGcd
  by_cases hj : j % 2 = 0
  · rw [if_pos hj]
    by_cases heq : j = C
    · subst j
      have hg := Nat.dvd_sub (Nat.gcd_dvd_left C (C - 1)) (Nat.gcd_dvd_right C (C - 1))
      rw [show C - (C - 1) = 1 by omega] at hg
      exact Nat.eq_one_of_dvd_one hg
    · exact gcd_eq_one_of_no_small_factor (by omega) (by omega) hterms.2.1 (by omega)
  · rw [if_neg hj]
    exact gcd_eq_one_of_no_small_factor (by omega) (by omega) hterms.2.2 hterms.1

/-- An accepted replay and return check determine the next strict
record and bound every preceding increment by the old record. -/
theorem canonical_replay_next_record {M finish root : Nat} (hits : List Nat)
    (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hmax : IsAttainedPreviousMaximum M (M + 2))
    (hcheck : recordReplayCheck M (M + 2) (2 * M - 2) hits finish = true)
    (hreturn : recordReturnCheck finish root = true) :
    M < finish + 1 ∧ IsAttainedPreviousMaximum M (finish + 2) ∧
      d (finish + 3) = finish + 1 ∧ D (finish + 2) = finish := by
  have hstart : IsMovingHorizonState (M + 2) (2 * M - 2) :=
    ⟨by omega, (canonical_increment_coordinates hM hcanon).2.1, by omega⟩
  obtain ⟨sf, hpath, hfmax⟩ := recordReplayCheck_sound hits hstart hmax hcheck
  have hstate := moving_horizon_path_endpoint hpath
  have hF := D_le_of_le (moving_horizon_path_index_le hpath)
  rw [hstart.2.1, hstate.2.1] at hF
  exact canonical_quiet_return_next_record hM hF hstate hfmax (recordReturnCheck_sound hstate hreturn)

theorem recordReturnCheck_factor_free {C root : Nat} (hcheck : recordReturnCheck C root = true) :
    NoProperFactor (C - 1) ∧ NoProperFactor (C + 1) := by
  have h := recordReturnCheck_conditions hcheck
  exact ⟨no_proper_factor_of_no_small_factor h.2.1 (by omega),
    no_proper_factor_of_no_small_factor h.2.2 h.1⟩

private theorem replay_new_maximum {M finish : Nat} (hnew : M < finish + 1)
    (hpre : IsAttainedPreviousMaximum M (finish + 2)) (hcanon : d (finish + 3) = finish + 1) :
    IsAttainedPreviousMaximum (finish + 1) (finish + 3) := by
  have hnew' : M < d (finish + 2 + 1) := by rwa [show finish + 2 + 1 = finish + 3 by omega, hcanon]
  have h := attained_previous_maximum_extend (by omega) hpre hnew'
  simpa only [show finish + 2 + 1 = finish + 3 by omega, hcanon] using h

theorem recordPrefixCheck_sound {M final : Nat} (segments : List (Nat × Nat × List Nat))
    (hM : 5 < M) (hcanon : d (M + 2) = M) (hmax : IsAttainedPreviousMaximum M (M + 2))
    (hprefix : RecordsVerifiedThrough (M + 2))
    (hcheck : recordPrefixCheck M final segments = true) :
    d (final + 2) = final ∧ IsAttainedPreviousMaximum final (final + 2) ∧
      RecordsVerifiedThrough (final + 2) := by
  induction segments generalizing M with
  | nil =>
      have h : M = final := by simpa [recordPrefixCheck] using hcheck
      subst final
      exact ⟨hcanon, hmax, hprefix⟩
  | cons segment rest ih =>
      obtain ⟨finish, root, hits⟩ := segment
      simp only [recordPrefixCheck, Bool.and_eq_true] at hcheck
      obtain ⟨⟨hreplay, hreturn⟩, hrest⟩ := hcheck
      obtain ⟨hnew, hpre, hcanon', _⟩ := canonical_replay_next_record
        hits hM hcanon hmax hreplay hreturn
      have hmax' := replay_new_maximum hnew hpre hcanon'
      have hprefix' : RecordsVerifiedThrough (finish + 3) := by
        intro R n hR hn hnf hdn hprior
        by_cases h : n ≤ M + 2
        · exact hprefix hR hn h hdn hprior
        · by_cases heq : n = finish + 3
          · have hR' : R = finish + 1 := by rw [heq, hcanon'] at hdn; omega
            obtain ⟨hlo, hhi⟩ := recordReturnCheck_factor_free hreturn
            rw [hR', show finish + 1 - 2 = finish - 1 by omega]
            exact ⟨by omega, hlo, hhi⟩
          · have hcap := hpre.1 n hn (by omega)
            have hbig := hprior (M + 2) (by omega) (by omega)
            omega
      exact ih (by omega) hcanon' hmax' hprefix' hrest

private theorem seven_record_verified :
    ∀ n : Fin 10, 5 < d n.val → n.val = d n.val + 2 ∧
      NoProperFactor (d n.val - 2) ∧ NoProperFactor (d n.val) := by decide

theorem recordPrefixCheck_sound_from_seven {final : Nat} (segments : List (Nat × Nat × List Nat))
    (hcheck : recordPrefixCheck 7 final segments = true) :
    d (final + 2) = final ∧ IsAttainedPreviousMaximum final (final + 2) ∧
      RecordsVerifiedThrough (final + 2) := by
  have hcanon : d 9 = 7 := by decide
  have hcap : ∀ j : Fin 10, 2 ≤ j.val → d j.val ≤ 7 := by decide
  have hmax : IsAttainedPreviousMaximum 7 9 :=
    ⟨fun j hj hj9 => hcap ⟨j, by omega⟩ hj, ⟨9, by decide, by decide, hcanon⟩⟩
  have hprefix : RecordsVerifiedThrough 9 := by
    intro R n hR _ hn hdn _
    have h := seven_record_verified ⟨n, by omega⟩ (by simpa only [hdn] using hR)
    simpa only [hdn] using h
  exact recordPrefixCheck_sound segments (by decide) hcanon hmax hprefix hcheck

private def verifiedSegments : List (Nat × Nat × List Nat) := [
  (12, 3, []),
  (42, 6, [17, 18, 20, 24]),
  (138, 11, [47, 48, 51, 60, 66, 79]),
  (312, 17, [150, 156]),
  (660, 25, [317, 318, 340, 342, 343, 348]),
  (1320, 36, []),
  (2658, 51, [1326, 1339]),
  (5418, 73, [
    2667, 2674, 2675, 2676, 2680, 2682, 2705, 2706,
    2710, 2711, 2712
  ]),
  (10890, 104, [
    5430, 5436, 5441, 5455, 5460, 5466, 5474, 5491,
    5496
  ]),
  (22038, 148, [
    10904, 10908, 10910, 10914, 10983, 10990, 10991, 10992,
    11007, 11013, 11041
  ]),
  (44382, 210, [
    22050, 22066, 22068, 22294, 22297, 22302, 22307, 22308,
    22321, 22326, 22357, 22362, 22386
  ]),
  (88800, 297, [44387, 44388, 44390, 44394, 44396, 44400, 44403]),
  (177840, 421, [
    88808, 88810, 88811, 88812, 88817, 88818, 88826, 88830,
    88849, 88854, 88868, 88877, 88878, 89050, 89052, 89076
  ]),
  (355722, 596, [177861, 177870, 177876]),
  (713832, 844, [
    355727, 355728, 355747, 355796, 355800, 355807, 355810, 355811,
    355812, 355817, 355818, 355861, 355866, 355887, 355894, 355897,
    355902, 355903, 355910, 355913, 355914, 355948, 355950, 355964,
    356024, 356028, 356044, 356048, 356241, 356250, 356267, 356268,
    356624, 356628, 356631, 356640, 356646, 356857, 356862, 356873,
    356874, 356883, 356890, 356892, 356902, 356918, 356922, 356930,
    356934, 357004, 357006, 357007, 357011, 357016, 357021, 357038,
    357042
  ]),
  (1427748, 1194, [
    713837, 713838, 713841, 713849, 713850, 713857, 713862, 713868,
    713870, 713874, 713888
  ]),
  (2860770, 1691, [
    1427760, 1427766, 1427769, 1427776, 1427934, 1427944, 1427945, 1427946,
    1427950, 1427952, 1427960, 1427964, 1427967, 1428085, 1428090, 1428096,
    1428097, 1428102, 1428112, 1428117, 1428120, 1428130, 1428131, 1428132,
    1428135, 1428137, 1428138, 1428140, 1428144, 1428672, 1428677, 1428678,
    1428680, 1428684, 1428699, 1428709, 1428745, 1428750, 1429314, 1429473,
    1429481, 1429482, 1429512, 1429517, 1429518, 1429521, 1429530, 1429536,
    1429549, 1429552, 1429553, 1429554, 1429573, 1429578, 1430854, 1430856,
    1430857, 1430858, 1430862, 1430876, 1430877, 1430879, 1430880, 1430890,
    1430892, 1430928, 1430930, 1430934, 1430940, 1430983, 1431003, 1431006
  ]),
  (5725452, 2392, [
    2860783, 2860790, 2860794, 2860814, 2860818, 2860827, 2860830, 2860840,
    2860844, 2860848, 2860850, 2860854, 2860866, 2860903, 2860907, 2860913,
    2860914, 2860920, 2860926, 2860927, 2860930, 2860932, 2860940, 2860944,
    2860946, 2860950, 2860957, 2860962, 2860994, 2860998, 2861003, 2861004,
    2861007, 2861041, 2861046, 2861075, 2861076, 2861078, 2861080, 2861081,
    2861082, 2861087, 2861088, 2861091, 2861100, 2861110, 2861120, 2861124,
    2861133, 2861134, 2861136, 2861140, 2861142, 2861152, 2861155, 2861160,
    2861166, 2862610, 2862612, 2862618, 2862622, 2862624, 2862630, 2862631,
    2862636, 2862672, 2862678, 2862693, 2862730, 2863565, 2863567, 2863578,
    2863599, 2863602, 2863614, 2863686, 2863692, 2863695, 2863697, 2863698,
    2863707, 2863742, 2863746, 2863750, 2863751
  ]),
  (11461140, 3385, [
    5725457, 5725458, 5725460, 5725464, 5725469, 5725470, 5725477, 5725481,
    5725482, 5725496, 5725497, 5725500, 5725510, 5725520, 5725524, 5725529,
    5725530, 5725576, 5725590, 5725619, 5725620, 5725641, 5725650, 5727376,
    5727378, 5727570, 5728718, 5728720, 5728721, 5728722, 5728727, 5728728,
    5728764, 5730952, 5730960, 5730966, 5730970, 5730972, 5731025, 5731035,
    5731040, 5731044, 5731057, 5731062, 5731067, 5731068, 5731076, 5731184,
    5731262, 5731266, 5731267, 5731272, 5731280, 5731284, 5731316, 5731317,
    5731319, 5731320, 5731334, 5731352, 5731356, 5731360, 5731362, 5731371,
    5731380, 5731386, 5731404, 5731409, 5731410, 5731417, 5731418, 5731422,
    5731430, 5731434, 5731437, 5731567, 5731572, 5731577, 5731578, 5731580,
    5731584, 5731774, 5731776, 5731793, 5731794, 5731797, 5731800, 5731805,
    5731810, 5731812, 5732763, 5732782, 5732784, 5732790, 5732796, 5732897,
    5732898, 5732907, 5732910, 5732914, 5732916, 5732929
  ]),
  (22933440, 4788, [
    11461246, 11461247, 11461248, 11461250, 11461254, 11461268, 11461357, 11461361,
    11461366, 11461568, 11461608, 11461610, 11461613, 11461614, 11461617, 11461619,
    11461620, 11461636, 11461638, 11461647, 11461650, 11461740, 11461753, 11461760,
    11461764, 11463115, 11463120, 11463125, 11463190, 11463221, 11463222, 11463244,
    11464811, 11464849, 11464851, 11464854, 11464877, 11464881, 11464882, 11464883,
    11464884, 11464894, 11464982, 11464986, 11464990, 11464992, 11465358, 11465365,
    11465367, 11465368, 11465369, 11465370, 11465381, 11465412, 11465413, 11465418,
    11465427, 11465430, 11465431, 11465436, 11465479, 11465583, 11465586, 11465592,
    11465599, 11465747, 11465762, 11465766, 11465778, 11465805, 11465807, 11465813,
    11465814, 11465870, 11465874, 11465875, 11465885, 11465888, 11465890, 11465892,
    11465897, 11465900, 11465904, 11465941, 11465953, 11465973, 11465976, 11466057,
    11466060, 11466078, 11466080, 11466083, 11466084, 11466104, 11466114, 11466120,
    11466121, 11466127, 11466132, 11466225, 11466228, 11466233, 11466246, 11466252,
    11466265, 11466266, 11466395, 11466397, 11466402, 11466548, 11466550, 11466552,
    11466572, 11466577, 11466582, 11466589, 11466594, 11466597, 11466719, 11466724,
    11466730, 11466732, 11466800, 11466804, 11466810, 11466816, 11466821, 11466840,
    11466847, 11466852, 11466863, 11466870, 11466876, 11466897, 11466900, 11466933,
    11466941, 11466942, 11467074, 11467091, 11467095, 11467098, 11467146, 11467154,
    11467157, 11467160, 11467161, 11467163, 11467164, 11467167, 11467170, 11467176,
    11467192, 11467194, 11467196, 11467238, 11467240, 11467242, 11467247, 11467248,
    11467318, 11467320, 11467326, 11467337, 11467338, 11467347, 11467350, 11467354,
    11467356, 11467357, 11467358, 11467876, 11467880, 11467884, 11467894, 11467896,
    11467899, 11467900, 11467902, 11467908, 11467913, 11467920, 11467926, 11467930,
    11467932, 11467941, 11467944, 11467962, 11467968, 11467984, 11467986, 11468540,
    11468574, 11468580, 11468613, 11468616, 11468653, 11468658, 11468669, 11468687,
    11468690, 11468694, 11468702, 11468710, 11468712
  ])
]

private theorem verifiedSegments_accepted :
    recordPrefixCheck 7 22933441 verifiedSegments = true := by
  simp only [verifiedSegments, recordPrefixCheck, Bool.and_eq_true]
  repeat' (first | apply And.intro | decide)

private theorem verified_prefix_result :
    d 22933443 = 22933441 ∧ IsAttainedPreviousMaximum 22933441 22933443 ∧
      RecordsVerifiedThrough 22933443 :=
  recordPrefixCheck_sound_from_seven verifiedSegments verifiedSegments_accepted

theorem last_verified_prefix_maximum : IsAttainedPreviousMaximum 22933441 22933443 :=
  verified_prefix_result.2.1

theorem last_verified_record_value : d 22933443 = 22933441 :=
  verified_prefix_result.1

theorem prime_of_no_proper_factor {N : Nat} (hN : 2 ≤ N)
    (hfree : NoProperFactor N) : N.Prime :=
  Nat.prime_def_lt'.2 ⟨hN, fun f hf hlt => hfree ⟨f, hlt⟩ hf⟩

theorem records_verified_through_22933443 : RecordsVerifiedThrough 22933443 :=
  verified_prefix_result.2.2

/-- The bound can be stated by record value, with no assumption on
its index. A later strict record already has to exceed the last one. -/
theorem record_index_and_factors_of_le_22933441 {R n : Nat}
    (hR : 5 < R) (hbound : R ≤ 22933441) (hn : 2 ≤ n) (hd : d n = R)
    (hprior : ∀ j : Nat, 2 ≤ j → j < n → d j < R) :
    n = R + 2 ∧ NoProperFactor (R - 2) ∧ NoProperFactor R := by
  have hindex : n ≤ 22933443 := by
    by_cases h : n ≤ 22933443
    · exact h
    · have hlast := hprior 22933443 (by decide) (by omega)
      rw [last_verified_record_value] at hlast
      omega
  exact records_verified_through_22933443 hR hn hindex hd hprior

/-- The A166944 twin-primality statement for every strict record greater
than five and at most the last verified record value. -/
theorem target_for_records_le_22933441 {R : Nat}
    (hR : 5 < R) (hbound : R ≤ 22933441) (hrecord : IsDifferenceRecord R) :
    IsGreaterTwinPrime R := by
  obtain ⟨n, hn, hd, hprior⟩ := hrecord
  obtain ⟨_, hminus, hplus⟩ := record_index_and_factors_of_le_22933441 hR hbound hn hd hprior
  exact ⟨prime_of_no_proper_factor (by omega) hplus, prime_of_no_proper_factor (by omega) hminus⟩

/-- **The index theorem from the two caps.**  The same induction as the
travel-bound version, with the consumer replaced by its decomposed form. -/
theorem record_index_and_twin_prime_of_two_caps_from_22933441
    (hcaps : TwinPrimeTwoCapBoundFrom 22933441) :
    ∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2 ∧ IsGreaterTwinPrime R := by
  intro R n
  induction n using Nat.strongRecOn generalizing R with
  | ind n ih =>
    intro hR hn hd hprior
    by_cases h : R ≤ 22933441
    · exact ⟨(record_index_and_factors_of_le_22933441 hR h hn hd hprior).1,
        target_for_records_le_22933441 hR h ⟨n, hn, hd, hprior⟩⟩
    · have hnLarge : 22933443 < n := by
        by_cases hle : n ≤ 22933443
        · have hcap := last_verified_prefix_maximum.1 n hn hle
          omega
        · omega
      obtain ⟨M, hmax⟩ := attained_previous_maximum_exists (n - 1) (by omega)
      have hM : 22933441 ≤ M := by
        have hcap := hmax.1 22933443 (by decide) (by omega)
        simpa only [last_verified_record_value] using hcap
      obtain ⟨m, hm, hmn, hdm, hMprior⟩ := attained_previous_maximum_first_occurrence hmax
      obtain ⟨hmi, hMtwin⟩ := ih m (by omega) (by omega : 5 < M) hm hdm hMprior
      have hMcanon : d (M + 2) = M := by rwa [← hmi]
      have hstartMax : IsAttainedPreviousMaximum M (M + 2) :=
        ⟨fun j hj hjM => hmax.1 j hj (by omega), ⟨M + 2, by omega, Nat.le_refl _, hMcanon⟩⟩
      have hMlt : M < R := by simpa only [hdm] using hprior m hm (by omega)
      obtain ⟨C, hnew, hpre, hdnew, hminus, hplus⟩ :=
        canonical_next_record_factors_of_two_caps_tight (by omega) hMcanon hstartMax
          (fun hpath hp => hcaps.1 (by omega) hMtwin hMcanon hpath hp)
          (fun hpath hp => hcaps.2 (by omega) hMtwin hMcanon hpath hp)
      have heq : n = C + 3 := by
        rcases Nat.lt_trichotomy n (C + 3) with hlt | heq | hgt
        · have hcap := hpre.1 n hn (by omega)
          omega
        · exact heq
        · have hcap := hmax.1 (C + 3) (by omega) (by omega)
          omega
      have hR' : R = C + 1 := by rw [heq, hdnew] at hd; omega
      refine ⟨by omega, ?_⟩
      change R.Prime ∧ (R - 2).Prime
      rw [hR', show C + 1 - 2 = C - 1 by omega]
      exact ⟨prime_of_no_proper_factor (by omega) hplus, prime_of_no_proper_factor (by omega) hminus⟩

/-- A bound on the index of the last old event bounds the horizon. -/
theorem canonical_horizon_bound_of_short_travel {M sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (htravel : 2 * (sf - (M + 2)) ≤ M) : Cf ≤ 3 * M + 4 := by
  have hD := (moving_horizon_path_endpoint hpath).2.1
  have hsf := moving_horizon_path_index_le hpath
  have ha := a_le_three_mul sf
  have hsum : D sf + sf = a sf := Nat.sub_add_cancel (index_le_a _)
  omega

theorem moving_horizon_path_index_lt {s C sf Cf q : Nat} (hq : 1 ≤ q)
    (hpath : HasMovingHorizonPathTo s C sf Cf q) : s < sf := by
  cases q with
  | zero => omega
  | succ q =>
      rcases hpath with ⟨_, r, C', hstep, htail⟩
      have hrest := moving_horizon_path_index_le htail
      have hsr : s < r := hstep.2.1
      omega

theorem moving_horizon_path_last_step {s C sf Cf q : Nat}
    (hpath : HasMovingHorizonPathTo s C sf Cf q) (hstart : s < sf) :
    ∃ sp Cp q₀, HasMovingHorizonPathTo s C sp Cp q₀ ∧
      IsMovingHorizonStep sp Cp sf Cf := by
  induction q generalizing s C sf Cf with
  | zero =>
      rcases hpath with ⟨hsf, _, _⟩
      omega
  | succ q ih =>
      rcases hpath with ⟨hstate, r, C', hstep, htail⟩
      cases q with
      | zero =>
          rcases htail with ⟨hrf, hCf, _⟩
          subst sf
          subst Cf
          exact ⟨s, C, 0, ⟨rfl, rfl, hstate⟩, hstep⟩
      | succ q =>
          have hrlt : r < sf := moving_horizon_path_index_lt (by omega) htail
          rcases ih htail hrlt with ⟨sp, Cp, q₀, hprefix, hlast⟩
          exact ⟨sp, Cp, q₀ + 1,
            ⟨hstate, r, C', hstep, hprefix⟩, hlast⟩

/-- A complete checked replay bounds travel on every capped prefix,
not just on the path supplied to the checker. -/
theorem canonical_replay_travel_bound {M finish root : Nat} (hits : List Nat)
    (hM : 5 < M) (hcanon : d (M + 2) = M)
    (hmax : IsAttainedPreviousMaximum M (M + 2))
    (hcheck : recordReplayCheck M (M + 2) (2 * M - 2) hits finish = true)
    (hreturn : recordReturnCheck finish root = true)
    (hlast : 2 * (hits.getLastD (M + 2) - (M + 2)) ≤ M) :
    ∀ {sf Cf p : Nat}, HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 2 * (sf - (M + 2)) ≤ M := by
  let last := hits.getLastD (M + 2)
  have hstart : IsMovingHorizonState (M + 2) (2 * M - 2) :=
    ⟨by omega, (canonical_increment_coordinates hM hcanon).2.1, by omega⟩
  obtain ⟨hreplay, hmaxLast⟩ := recordReplayCheck_sound_last hits hstart hmax hcheck
  have hstate := moving_horizon_path_endpoint hreplay
  have hstartLast : M + 2 ≤ last := moving_horizon_path_index_le hreplay
  have hF := D_le_of_le hstartLast
  have hDlast : D last = finish := hstate.2.1
  rw [hstart.2.1, hDlast] at hF
  have hquiet := recordReturnCheck_sound hstate hreturn
  obtain ⟨hnew, _, hd, hD⟩ := canonical_quiet_return_next_record hM hF hstate hmaxLast hquiet
  intro sf Cf p hpath hmaxSf
  have hsfFinish : sf ≤ finish + 2 := by
    by_cases h : sf ≤ finish + 2
    · exact h
    · have hcap := hmaxSf.1 (finish + 3) (by omega) (by omega)
      omega
  have hsfLast : sf ≤ last := by
    by_cases h : sf ≤ last
    · exact h
    · obtain ⟨sp, Cp, q, _, hstep⟩ := moving_horizon_path_last_step hpath (by omega)
      have hnonunit := hstep.2.2.2.1
      have hlo := D_le_of_le (by omega : last ≤ sf - 1)
      have hmid := D_le_of_le (by omega : sf - 1 ≤ sf)
      have hhi := D_le_of_le hsfFinish
      rw [hDlast] at hlo
      rw [hD] at hhi
      have heq : D sf = D (sf - 1) := by omega
      have hunit : d sf = 1 := by
        have hindex : sf - 1 + 1 = sf := by omega
        have h := (D_succ_eq_self_iff_d_succ_eq_one (sf - 1)).1 (by rwa [hindex])
        simpa only [hindex] using h
      omega
  change 2 * (last - (M + 2)) ≤ M at hlast
  omega

private def extensionHits : List Nat := [
    22933560, 22933591, 22933597, 22933602, 22933605, 22933623, 22933631, 22933632,
    22933647, 22933653, 22933664, 22933668, 22933698, 22933700, 22933704, 22938265,
    22938268, 22938269, 22938270, 22938363, 22938365, 22938367, 22938372, 22938579,
    22938580, 22938581, 22938582, 22938586, 22938587, 22938593, 22938594, 22939304,
    22939308, 22939309, 22939314, 22939317, 22939320, 22939326, 22939329, 22939336,
    22939340, 22939344, 22940147, 22940148, 22940150, 22940154, 22940160, 22940166,
    22940179, 22940182, 22940183, 22940184, 22940187, 22940190, 22940203, 22940204,
    22940207, 22940208, 22940213, 22940220, 22940226, 22940227, 22940232, 22940246,
    22940250, 22940256, 22940258, 22940262, 22940267, 22940268, 22940295, 22940298,
    22940309, 22941260, 22941264, 22941567, 22941678, 22941680, 22941684, 22941697,
    22941707, 22941708, 22941736, 22941738, 22941740, 22941744, 22941758, 22941776,
    22941778, 22941789, 22941792, 22941847, 22941852, 22941855, 22941856, 22941858,
    22942900, 22942901, 22942910, 22942914, 22942960, 22942962, 22942971, 22942977,
    22942980, 22943093, 22943097, 22943100, 22943102, 22943109, 22943110, 22943111,
    22943112, 22943117, 22943118, 22943140, 22943142, 22943144, 22943147, 22943149,
    22943154, 22943157, 22943160, 22943295, 22943298, 22943615, 22943616, 22943620,
    22943622, 22943627, 22943628, 22943630, 22943634, 22943640, 22943659, 22943662,
    22943664, 22943690, 22943694, 22943914, 22943916, 22943939, 22943951, 22944107,
    22944108, 22945432, 22945463, 22945464, 22945470, 22945476, 22945494, 22945496,
    22945512, 22945518, 22945538, 22945542, 22945770, 22945777, 22945785, 22945787,
    22945788, 22945793, 22945794, 22945803, 22945806, 22945813, 22945820, 22945824,
    22945852, 22945854, 22945859, 22945860, 22945980, 22945986, 22946049, 22946056,
    22946058, 22946067, 22946070, 22946077, 22946082, 22946172, 22946177, 22946178,
    22946187, 22946190, 22946191, 22946200, 22946202, 22946211, 22946217, 22946219,
    22946220, 22946245, 22947464, 22947468, 22947587, 22947588, 22947590, 22947594,
    22947626, 22947630, 22947633, 22947678, 22947680, 22947684, 22947775, 22947782,
    22947786
  ]

private theorem extensionReplay_accepted :
    recordReplayCheck 22933441 (22933441 + 2) (2 * 22933441 - 2) extensionHits 45895572 = true := by
  decide

private theorem extensionReturn_accepted : recordReturnCheck 45895572 6774 = true := by decide

theorem canonical_travel_bound_at_22933441 {sf Cf p : Nat}
    (hpath : HasMovingHorizonPathTo (22933441 + 2) (2 * 22933441 - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum 22933441 sf) :
    2 * (sf - (22933441 + 2)) ≤ 22933441 :=
  canonical_replay_travel_bound extensionHits (by decide) last_verified_record_value
    last_verified_prefix_maximum extensionReplay_accepted extensionReturn_accepted (by decide) hpath hmax

private theorem extension_next_record :
    22933441 < 45895573 ∧ IsAttainedPreviousMaximum 22933441 45895574 ∧
      d 45895575 = 45895573 ∧ D 45895574 = 45895572 :=
  canonical_replay_next_record extensionHits (by decide) last_verified_record_value
    last_verified_prefix_maximum extensionReplay_accepted extensionReturn_accepted

/-- There is no intervening canonical record value, and all capped
prefixes at the lower endpoint satisfy the travel bound. -/
theorem canonical_travel_bound_on_verified_extension {M sf Cf p : Nat}
    (hM : 22933441 ≤ M) (hupper : M < 45895573) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum M sf) :
    2 * (sf - (M + 2)) ≤ M := by
  have hcap := extension_next_record.2.1.1 (M + 2) (by omega) (by omega)
  have hEq : M = 22933441 := by omega
  subst M
  exact canonical_travel_bound_at_22933441 hpath hmax

/-- **The caps hold below the platform threshold.**  Between `22933441` and
`45895573` the explicit replay certificate gives the travel bound, and each cap is
a consequence of it. -/
theorem two_cap_below_platform_threshold {M sf Cf p : Nat}
    (hM : 22933441 ≤ M) (hupper : M < 45895573) (hcanon : d (M + 2) = M)
    (hpath : HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p)
    (hmax : IsAttainedPreviousMaximum M sf) :
    Cf ≤ 3 * M + 4 ∧ 4 * sf ≤ 7 * M - 1 := by
  have hshort := canonical_travel_bound_on_verified_extension hM hupper hcanon hpath hmax
  have hsf : M + 2 ≤ sf := by
    have := moving_horizon_path_index_le hpath
    omega
  constructor
  · exact canonical_horizon_bound_of_short_travel hpath hshort
  · omega

/-- **The platform threshold version.**  Caps stated at `45895573` give the target;
below that threshold the certificate supplies them, above it the hypotheses do. -/
theorem a166944_target_of_two_caps_at_platform_threshold
    (hA : ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → Cf ≤ 3 * M + 4)
    (hB : ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 4 * sf ≤ 7 * M - 1) :
    ∀ R : Nat, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R := by
  -- Assemble the threshold-22933441 pair the induction consumes.
  have hcaps : TwinPrimeTwoCapBoundFrom 22933441 := by
    constructor
    · intro M sf Cf p hM htwin hcanon hpath hmax
      by_cases h : M < 45895573
      · exact (two_cap_below_platform_threshold (by omega) h hcanon hpath hmax).1
      · exact hA (by omega) htwin hcanon hpath hmax
    · intro M sf Cf p hM htwin hcanon hpath hmax
      by_cases h : M < 45895573
      · exact (two_cap_below_platform_threshold (by omega) h hcanon hpath hmax).2
      · exact hB (by omega) htwin hcanon hpath hmax
  intro R hR hrecord
  obtain ⟨n, hn, hd, hprior⟩ := hrecord
  exact (record_index_and_twin_prime_of_two_caps_from_22933441
    hcaps hR hn hd hprior).2

end A166944Research

open A166944Research in
theorem solution
    (hA : ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → Cf ≤ 3 * M + 4)
    (hB : ∀ {M sf Cf p : Nat}, 45895573 ≤ M → IsGreaterTwinPrime M → d (M + 2) = M →
      HasMovingHorizonPathTo (M + 2) (2 * M - 2) sf Cf p →
      IsAttainedPreviousMaximum M sf → 4 * sf ≤ 7 * M - 1) :
    ∀ R : Nat, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R :=
  a166944_target_of_two_caps_at_platform_threshold hA hB
