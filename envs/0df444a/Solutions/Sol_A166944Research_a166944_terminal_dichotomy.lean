-- Prove2me | solution 1 for A166944Research.a166944_terminal_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-20T03:28:26.682922+00:00
-- url     : https://prove2.me/submissions/139fd9db-a7ca-41fc-bd7b-310112c70689

import Definitions.Def_a166944_moving_horizon
import Definitions.Def_a166944_B

open A166944Research

namespace A166944Research.TerminalDichotomyProof

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

private theorem d_pos_of_two_le {n : Nat} (hn : 2 ≤ n) : 0 < d n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using d_add_two_pos k

private theorem one_le_d_of_two_le {n : Nat} (hn : 2 ≤ n) : 1 ≤ d n := by
  exact Nat.succ_le_of_lt (d_pos_of_two_le hn)

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

private theorem D_succ_eq_add_d_sub_one (n : Nat) :
    D (n + 1) = D n + d (n + 1) - 1 := by
  simpa using congrArg (fun x : Nat => x - 1) (D_succ_add_one_eq_add_d n)

private theorem D_succ_eq_D_add_d_sub_one (n : Nat) :
    D (n + 1) = D n + (d (n + 1) - 1) := by
  rw [D_succ_eq_add_d_sub_one n]
  exact Nat.add_sub_assoc (one_le_d_succ n) (D n)

private theorem D_add_two_le_succ_of_two_le {n : Nat} (hn : 2 ≤ n)
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

private theorem constant_D_event_map_succ {s C : Nat} (hs : 1 ≤ s)
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

private theorem D_succ_le_even_multiple {n H : Nat} (hn : 2 ≤ n)
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

private theorem D_le_even_multiple_of_interval {s n H : Nat} (hs : 2 ≤ s) (hsn : s ≤ n)
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

private def recordHorizonBound : Nat → Nat
  | 0 => 2
  | m + 1 =>
      if (m + 1) % 2 = 1 then Nat.lcm (m + 1) (recordHorizonBound m)
      else recordHorizonBound m

private theorem recordHorizonBound_dvd_succ (M : Nat) :
    recordHorizonBound M ∣ recordHorizonBound (M + 1) := by
  by_cases h : (M + 1) % 2 = 1
  · simpa [recordHorizonBound, h] using Nat.dvd_lcm_right (M + 1) (recordHorizonBound M)
  · simp [recordHorizonBound, h]

private theorem odd_dvd_recordHorizonBound {e M : Nat} (he : e % 2 = 1) (hcap : e ≤ M) :
    e ∣ recordHorizonBound M := by
  induction M with
  | zero => omega
  | succ M ih =>
      by_cases h : e = M + 1
      · subst e
        simpa [recordHorizonBound, he] using Nat.dvd_lcm_left (M + 1) (recordHorizonBound M)
      · exact Nat.dvd_trans (ih (by omega)) (recordHorizonBound_dvd_succ M)

private theorem recordHorizonBound_pos_even (M : Nat) :
    0 < recordHorizonBound M ∧ 2 ∣ recordHorizonBound M := by
  induction M with
  | zero => decide
  | succ M ih =>
      refine ⟨?_, Nat.dvd_trans ih.2 (recordHorizonBound_dvd_succ M)⟩
      by_cases h : (M + 1) % 2 = 1
      · simpa [recordHorizonBound, h] using
          Nat.lcm_pos (Nat.zero_lt_succ M) ih.1
      · simpa [recordHorizonBound, h] using ih.1

private theorem D_le_recordHorizonBound_of_cap {M n : Nat} (hn : 2 ≤ n)
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

private theorem first_later_nontrivial_of_exists {n C : Nat} (hn : 2 ≤ n)
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

private theorem first_later_nontrivial_dichotomy {n C : Nat} (hn : 2 ≤ n) :
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

private theorem moving_horizon_step_of_exists {s C : Nat}
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

private theorem moving_horizon_dichotomy {s C : Nat}
    (hs : IsMovingHorizonState s C) :
    (∀ j : Nat, s < j → j ≤ C → d j = 1) ∨
      ∃ r C', IsMovingHorizonStep s C r C' := by
  rcases first_later_nontrivial_dichotomy hs.1 with hno | hex
  · exact Or.inl hno
  · rcases hex with ⟨r, hsr, hrC, hdr, _⟩
    exact Or.inr (moving_horizon_step_of_exists hs ⟨r, hsr, hrC, hdr⟩)

private theorem moving_horizon_max_transfer {P s r : Nat}
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

private theorem capped_moving_horizon_eventual_exit {M s C : Nat}
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

end A166944Research.TerminalDichotomyProof

open A166944Research

theorem solution {M s C : Nat}
    (hstate : IsMovingHorizonState s C) (hP : IsAttainedPreviousMaximum M s) :
    ∃ sf Cf p : Nat, HasMovingHorizonPathTo s C sf Cf p ∧
      IsAttainedPreviousMaximum M sf ∧
      ((B Cf = 2 ∧ ∀ j : Nat, sf < j → j ≤ Cf → d j = 1) ∨
        ∃ r C' : Nat, IsMovingHorizonStep sf Cf r C' ∧ M < d r) := by
  exact TerminalDichotomyProof.capped_moving_horizon_eventual_exit hstate hP
