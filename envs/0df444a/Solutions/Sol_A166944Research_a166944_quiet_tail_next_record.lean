-- Prove2me | solution 1 for A166944Research.a166944_quiet_tail_next_record
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-20T03:28:18.546869+00:00
-- url     : https://prove2.me/submissions/d3129ded-2b6b-47bf-b26d-c18b446aba55

import Definitions.Def_a166944_moving_horizon

open A166944Research

namespace A166944Research.NextRecordProof

private def B (n : Nat) : Nat := a n - (2 * n - 2)

private theorem a_pos : ∀ n : Nat, 0 < n → 0 < a n := by
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

private theorem index_le_a : ∀ n : Nat, n ≤ a n := by
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

private theorem a_add_one_le_add_two (n : Nat) : a (n + 1) ≤ a (n + 2) := by
  simp only [a]
  split <;> exact Nat.le_add_right _ _

private theorem a_le_succ (n : Nat) : a n ≤ a (n + 1) := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => simpa using a_add_one_le_add_two n

private theorem a_add_d_succ {k : Nat} :
    a k + d (k + 1) = a (k + 1) := by
  have hsub : d (k + 1) = a (k + 1) - a k := by simp [d]
  rw [hsub]
  simpa [Nat.add_comm] using Nat.sub_add_cancel (a_le_succ k)

private theorem gcd_mod_two_eq_one_of_left_or_right_mod_two_eq_one {m n : Nat}
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

private theorem a_add_two_mod_two (n : Nat) :
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

private theorem a_mod_two_of_two_le {n : Nat} (hn : 2 ≤ n) :
    a n % 2 = n % 2 := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using a_add_two_mod_two k

private theorem d_add_two (n : Nat) :
    d (n + 2) = if (n + 2) % 2 = 0 then
      Nat.gcd (n + 2) (a (n + 1))
    else Nat.gcd n (a (n + 1)) := by
  simp only [d, a]
  split <;> simp_all

private theorem d_add_two_pos (n : Nat) : 0 < d (n + 2) := by
  rw [d_add_two]
  split <;> exact Nat.gcd_pos_of_pos_right _ (a_pos (n + 1) (Nat.zero_lt_succ n))

private theorem one_le_d_succ (n : Nat) : 1 ≤ d (n + 1) := by
  cases n with
  | zero => simp [d, a]
  | succ n => exact Nat.succ_le_of_lt (d_add_two_pos n)

private theorem a_succ_ge_add_one {k : Nat} :
    a k + 1 ≤ a (k + 1) := by
  calc
    a k + 1 ≤ a k + d (k + 1) :=
      Nat.add_le_add_left (one_le_d_succ k) _
    _ = a (k + 1) := a_add_d_succ

private theorem d_add_two_of_odd (n : Nat) (h : (n + 2) % 2 ≠ 0) :
    d (n + 2) = Nat.gcd n (a (n + 1)) := by
  have h' : n % 2 ≠ 0 := by simpa using h
  simpa [h'] using d_add_two n

private theorem a_lower_step {k : Nat} (hk : 2 ≤ k)
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

private theorem two_mul_le_a_add_two {k : Nat} (hk : 2 ≤ k) :
    2 * k ≤ a k + 2 := by
  obtain ⟨t, rfl⟩ := Nat.le.dest hk
  clear hk
  induction t with
  | zero => simp [a]
  | succ t ih =>
      have ht : 2 ≤ 2 + t := Nat.le_add_right 2 t
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (a_lower_step ht ih)

private theorem two_mul_sub_two_le_a {k : Nat} (hk : 2 ≤ k) :
    2 * k - 2 ≤ a k := by
  exact (Nat.sub_le_iff_le_add).2 (two_mul_le_a_add_two hk)

private theorem B_add_index_eq_D_add_two {n : Nat} (hn : 2 ≤ n) :
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

private theorem base_eq_two_mul_pred (k : Nat) :
    2 * k - 2 = 2 * (k - 1) := by
  rw [Nat.mul_sub_left_distrib]

private theorem B_mod_two_of_two_le {k : Nat} (hk : 2 ≤ k) :
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

private theorem excess_succ_add_two {k : Nat} (hk : 2 ≤ k) :
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

private theorem d_add_two_mod_two_eq_one {n : Nat} (hn : 1 ≤ n) :
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

private theorem d_mod_two_eq_one_of_three_le {n : Nat} (hn : 3 ≤ n) :
    d n % 2 = 1 := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    d_add_two_mod_two_eq_one hk

private theorem d_add_two_of_even (n : Nat) (h : (n + 2) % 2 = 0) :
    d (n + 2) = Nat.gcd (n + 2) (a (n + 1)) := by
  simpa [h] using d_add_two n

private theorem d_succ_eq_gcd_small_residual {k : Nat} (hk : 2 ≤ k)
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

private theorem one_or_three_le_of_mod_two_eq_one {c : Nat} (hc : c % 2 = 1) :
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

private theorem odd_small_residual_classification {k : Nat} (hk : 2 ≤ k)
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

private theorem B_one_transition {k : Nat} (hk : 2 ≤ k) (hk1 : k % 2 = 1)
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

private theorem d_succ_eq_gcd_even_residual {k : Nat} (hk : 2 ≤ k)
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

private theorem quotient_mod_two_of_left_odd {R q : Nat} (hR : R % 2 = 1) :
    q % 2 = (R * q) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
  · simp [Nat.mul_mod, hR, hq0]
  · simp [Nat.mul_mod, hR, hq1]

private theorem two_le_of_pos_of_mod_two_eq_zero {c : Nat} (hcpos : 0 < c)
    (hc : c % 2 = 0) : 2 ≤ c := by
  cases c with
  | zero => simp at hcpos
  | succ c =>
      cases c with
      | zero => simp at hc
      | succ c =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Nat.le_add_right 2 c)

private theorem even_residual_structure {k : Nat} (hk : 2 ≤ k)
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

private theorem d_pos_of_two_le {n : Nat} (hn : 2 ≤ n) : 0 < d n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using d_add_two_pos k

private theorem one_le_d_of_two_le {n : Nat} (hn : 2 ≤ n) : 1 ≤ d n := by
  exact Nat.succ_le_of_lt (d_pos_of_two_le hn)

private theorem B_two_transition {k : Nat} (hk : 2 ≤ k) (hB : B k = 2) :
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

private theorem B_zero_transition {k : Nat} (hk : 2 ≤ k) (hB : B k = 0) :
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

private theorem D_succ_add_one_eq_add_d (n : Nat) :
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

private theorem D_eq_self_of_fundamental {m : Nat} (hm : 2 ≤ m)
    (hfund : B m = 2) : D m = m := by
  have h := B_add_index_eq_D_add_two hm
  rw [hfund] at h
  have hcancel : 2 + m = 2 + D m := by
    calc
      2 + m = D m + 2 := h
      _ = 2 + D m := by simp [Nat.add_comm]
  exact (Nat.add_left_cancel hcancel).symm

private theorem D_le_succ (n : Nat) : D n ≤ D (n + 1) := by
  have hle : D n + 1 ≤ D n + d (n + 1) :=
    Nat.add_le_add_left (one_le_d_succ n) (D n)
  have hle' : D n + 1 ≤ D (n + 1) + 1 :=
    Nat.le_trans hle (Nat.le_of_eq (D_succ_add_one_eq_add_d n).symm)
  exact Nat.le_of_succ_le_succ hle'

private theorem D_le_of_le {m n : Nat} (hmn : m ≤ n) : D m ≤ D n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hmn
  clear hmn
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      exact Nat.le_trans ih (by simpa [Nat.add_assoc] using D_le_succ (m + k))

private theorem D_mod_two_eq_zero_of_two_le {n : Nat} (hn : 2 ≤ n) :
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

private theorem d_eq_if_gcd_of_two_le {n : Nat} (hn : 2 ≤ n) :
    d n = if n % 2 = 0 then
      Nat.gcd n (a (n - 1))
    else Nat.gcd (n - 2) (a (n - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using d_add_two k

private theorem constant_D_event_map {r C : Nat} (hr : 2 ≤ r)
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

private theorem D_succ_eq_self_iff_d_succ_eq_one (n : Nat) :
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

private def IsLastNontrivialBefore (rho m : Nat) : Prop :=
  2 ≤ rho ∧ rho < m ∧ 1 < d rho ∧
    ∀ j : Nat, rho < j → j ≤ m → d j = 1

private theorem exists_last_nontrivial_before {m : Nat} (hm : d m = 1)
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

private theorem one_interval_const_D_B {l t : Nat} (hl : 2 ≤ l)
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

private theorem first_later_event_D_eq {n C r : Nat} (hn : 2 ≤ n)
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

private theorem fundamental_point_mod_six {m : Nat} (hm : 6 ≤ m) (hfund : B m = 2) :
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

private theorem fundamental_reset {m : Nat} (hm : 2 ≤ m) (hfund : B m = 2) :
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

private theorem fundamental_reset_at_three {m : Nat} (hm : 6 ≤ m) (hfund : B m = 2) :
    d (m + 1) = 1 ∧ d (m + 2) = 1 ∧ d (m + 3) = m + 1 := by
  rcases fundamental_reset (by omega : 2 ≤ m) hfund with h | h
  · exact ⟨h.1, h.2.1, h.2.2.2.1⟩
  · have hmod := fundamental_point_mod_six hm hfund
    have hmap := d_eq_if_gcd_of_two_le (by omega : 2 ≤ m + 2)
    rw [if_pos (by omega), h.2.1] at hmap
    have hdiv : 3 ∣ m + 2 := hmap.symm ▸ Nat.gcd_dvd_left _ _
    have hbad := Nat.mod_eq_zero_of_dvd hdiv
    omega

private theorem moving_horizon_no_event_telescope {s C : Nat}
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

private theorem canonical_quiet_return_next_record {M sf finish : Nat}
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

end A166944Research.NextRecordProof

open A166944Research

theorem solution {M sf Cf : Nat}
    (hM : 968 ≤ M) (hF : 2 * M - 2 ≤ Cf)
    (hstate : IsMovingHorizonState sf Cf) (hfmax : IsAttainedPreviousMaximum M sf)
    (hquiet : ∀ j : Nat, sf < j → j ≤ Cf → d j = 1) :
    M < Cf + 1 ∧ IsAttainedPreviousMaximum M (Cf + 2) ∧ d (Cf + 3) = Cf + 1 := by
  obtain ⟨hgt, hmax, hd, _⟩ := NextRecordProof.canonical_quiet_return_next_record (by omega : 5 < M) hF hstate hfmax hquiet
  exact ⟨hgt, hmax, hd⟩
