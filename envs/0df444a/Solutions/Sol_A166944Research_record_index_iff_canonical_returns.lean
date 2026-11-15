-- Prove2me | solution 1 for A166944Research.record_index_iff_canonical_returns
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-14T23:15:01.518966+00:00
-- url     : https://prove2.me/submissions/3e52eca0-a83d-4fc8-be95-4dcd64fb38e0

import Definitions.Def_a166944_canonical

/-!
Self-contained solution for the platform target
`A166944Research.record_index_iff_canonical_returns`.
Helper lemmas inlined in dependency order (skeleton subtraction).
-/

open A166944Research

namespace A166944Research

theorem base_eq_two_mul_pred (k : Nat) :
    2 * k - 2 = 2 * (k - 1) := by
  rw [Nat.mul_sub_left_distrib]

theorem quotient_mod_two_of_left_odd {R q : Nat} (hR : R % 2 = 1) :
    q % 2 = (R * q) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
  · simp [Nat.mul_mod, hR, hq0]
  · simp [Nat.mul_mod, hR, hq1]

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

theorem a_add_one_le_add_two (n : Nat) : a (n + 1) ≤ a (n + 2) := by
  simp only [a]
  split <;> exact Nat.le_add_right _ _

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

private theorem early_fundamental_mod_six :
    ∀ m : Fin 14, 6 ≤ m.val → B m.val = 2 → m.val % 6 = 0 := by
  decide

private theorem early_large_increment_index :
    ∀ n : Fin 10, 5 < d n.val → n.val = d n.val + 2 := by
  decide

theorem d_add_two (n : Nat) :
    d (n + 2) = if (n + 2) % 2 = 0 then
      Nat.gcd (n + 2) (a (n + 1))
    else Nat.gcd n (a (n + 1)) := by
  simp only [d, a]
  split <;> simp_all

theorem a_le_succ (n : Nat) : a n ≤ a (n + 1) := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => simpa using a_add_one_le_add_two n

theorem a_mod_two_of_two_le {n : Nat} (hn : 2 ≤ n) :
    a n % 2 = n % 2 := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using a_add_two_mod_two k

theorem d_add_two_of_even (n : Nat) (h : (n + 2) % 2 = 0) :
    d (n + 2) = Nat.gcd (n + 2) (a (n + 1)) := by
  simpa [h] using d_add_two n

theorem d_eq_if_gcd_of_two_le {n : Nat} (hn : 2 ≤ n) :
    d n = if n % 2 = 0 then
      Nat.gcd n (a (n - 1))
    else Nat.gcd (n - 2) (a (n - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using d_add_two k

theorem d_add_two_of_odd (n : Nat) (h : (n + 2) % 2 ≠ 0) :
    d (n + 2) = Nat.gcd n (a (n + 1)) := by
  have h' : n % 2 ≠ 0 := by simpa using h
  simpa [h'] using d_add_two n

theorem d_add_two_pos (n : Nat) : 0 < d (n + 2) := by
  rw [d_add_two]
  split <;> exact Nat.gcd_pos_of_pos_right _ (a_pos (n + 1) (Nat.zero_lt_succ n))

theorem critical_actual_next_difference_record_prior {k M : Nat}
    (hP : IsAttainedPreviousMaximum M k) (hnew : M < d (k + 1)) :
    ∀ j : Nat, 2 ≤ j → j < k + 1 → d j < d (k + 1) := by
  intro j hj2 hjlt
  have hjk : j ≤ k := by omega
  exact Nat.lt_of_le_of_lt (hP.1 j hj2 hjk) hnew

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

theorem a_add_d_succ {k : Nat} :
    a k + d (k + 1) = a (k + 1) := by
  have hsub : d (k + 1) = a (k + 1) - a k := by simp [d]
  rw [hsub]
  simpa [Nat.add_comm] using Nat.sub_add_cancel (a_le_succ k)

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

theorem one_le_d_succ (n : Nat) : 1 ≤ d (n + 1) := by
  cases n with
  | zero => simp [d, a]
  | succ n => exact Nat.succ_le_of_lt (d_add_two_pos n)

theorem d_pos_of_two_le {n : Nat} (hn : 2 ≤ n) : 0 < d n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using d_add_two_pos k

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

theorem d_mod_two_eq_one_of_three_le {n : Nat} (hn : 3 ≤ n) :
    d n % 2 = 1 := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    d_add_two_mod_two_eq_one hk

theorem D_le_succ (n : Nat) : D n ≤ D (n + 1) := by
  have hle : D n + 1 ≤ D n + d (n + 1) :=
    Nat.add_le_add_left (one_le_d_succ n) (D n)
  have hle' : D n + 1 ≤ D (n + 1) + 1 :=
    Nat.le_trans hle (Nat.le_of_eq (D_succ_add_one_eq_add_d n).symm)
  exact Nat.le_of_succ_le_succ hle'

theorem a_succ_ge_add_one {k : Nat} :
    a k + 1 ≤ a (k + 1) := by
  calc
    a k + 1 ≤ a k + d (k + 1) :=
      Nat.add_le_add_left (one_le_d_succ k) _
    _ = a (k + 1) := a_add_d_succ

theorem one_le_d_of_two_le {n : Nat} (hn : 2 ≤ n) : 1 ≤ d n := by
  exact Nat.succ_le_of_lt (d_pos_of_two_le hn)

theorem D_le_of_le {m n : Nat} (hmn : m ≤ n) : D m ≤ D n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hmn
  clear hmn
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      exact Nat.le_trans ih (by simpa [Nat.add_assoc] using D_le_succ (m + k))

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

theorem B_eq_two_iff_a_eq_two_mul {k : Nat} (hk : 2 ≤ k) :
    B k = 2 ↔ a k = 2 * k := by
  have hbase : 2 * k - 2 ≤ a k := two_mul_sub_two_le_a hk
  have hsum : B k + (2 * k - 2) = a k := Nat.sub_add_cancel hbase
  have hk2 : 2 ≤ 2 * k := by
    exact Nat.le_trans (by simp) (Nat.mul_le_mul_left 2 hk)
  constructor
  · intro hB
    calc
      a k = B k + (2 * k - 2) := hsum.symm
      _ = 2 + (2 * k - 2) := by rw [hB]
      _ = (2 * k - 2) + 2 := by simp [Nat.add_comm]
      _ = 2 * k := Nat.sub_add_cancel hk2
  · intro ha
    change a k - (2 * k - 2) = 2
    rw [ha]
    have hbase' : 2 * k - 2 ≤ 2 * k := Nat.sub_le _ _
    apply (Nat.sub_eq_iff_eq_add hbase').2
    calc
      2 * k = (2 * k - 2) + 2 := (Nat.sub_add_cancel hk2).symm
      _ = 2 + (2 * k - 2) := by simp [Nat.add_comm]

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

theorem D_eq_self_of_fundamental {m : Nat} (hm : 2 ≤ m)
    (hfund : B m = 2) : D m = m := by
  have h := B_add_index_eq_D_add_two hm
  rw [hfund] at h
  have hcancel : 2 + m = 2 + D m := by
    calc
      2 + m = D m + 2 := h
      _ = 2 + D m := by simp [Nat.add_comm]
  exact (Nat.add_left_cancel hcancel).symm

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

/-- From a canonical previous record, the next strict record is canonical
exactly when a fundamental point occurs between the two records. -/
theorem next_record_index_iff_fundamental {M k : Nat} (hM : 5 < M)
    (hcanonical : d (M + 2) = M)
    (hP : IsAttainedPreviousMaximum M k) (hnew : M < d (k + 1)) :
    k + 1 = d (k + 1) + 2 ↔
      ∃ m : Nat, M + 2 ≤ m ∧ m < k + 1 ∧ B m = 2 := by
  have ⟨haM, hDM, _⟩ := canonical_increment_coordinates hM hcanonical
  constructor
  · intro hidx
    have hR : 5 < d (k + 1) := by omega
    have hcanon : d (d (k + 1) + 2) = d (k + 1) := congrArg d hidx.symm
    have hB := (canonical_increment_coordinates hR hcanon).2.2
    have hModd : M % 2 = 1 := hcanonical ▸ d_mod_two_eq_one_of_three_le (by omega : 3 ≤ M + 2)
    have hRodd := d_mod_two_eq_one_of_three_le (by omega : 3 ≤ k + 1)
    have hRgap : M + 2 ≤ d (k + 1) := by omega
    have hneq : d (k + 1) ≠ M + 2 := by
      intro heq
      rw [heq, show M + 2 - 1 = M + 1 by omega] at hB
      have ha := (B_eq_two_iff_a_eq_two_mul (by omega : 2 ≤ M + 1)).1 hB
      omega
    exact ⟨d (k + 1) - 1, by omega, by omega, hB⟩
  · rintro ⟨m, hm, hmk, hfund⟩
    have hm2 : 2 ≤ m := by omega
    have hD := D_le_of_le hm
    rw [hDM, D_eq_self_of_fundamental hm2 hfund] at hD
    obtain ⟨hd1, hd2, hd3⟩ := fundamental_reset_at_three (by omega) hfund
    have hlater : k + 1 ≤ m + 3 := by
      by_cases h : k + 1 ≤ m + 3
      · exact h
      have hcap := hP.1 (m + 3) (by omega) (by omega)
      omega
    have heq : k + 1 = m + 3 := by
      by_cases h : k + 1 = m + 3
      · exact h
      rcases (show k + 1 = m + 1 ∨ k + 1 = m + 2 by omega) with h | h
      · rw [h, hd1] at hnew; omega
      · rw [h, hd2] at hnew; omega
    rw [heq, hd3]

/-- The full record-index theorem is equivalent to proving a fundamental
return between a canonical record and its next strict record. -/
theorem record_index_iff_canonical_returns :
    (∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2) ↔
    (∀ {M k : Nat}, 5 < M → M + 2 ≤ k → d (M + 2) = M →
      IsAttainedPreviousMaximum M k → M < d (k + 1) →
      ∃ m : Nat, M + 2 ≤ m ∧ m < k + 1 ∧ B m = 2) := by
  constructor
  · intro hIndex M k hM hk hcanon hP hnew
    have hnext := hIndex (by omega : 5 < d (k + 1)) (by omega : 2 ≤ k + 1) rfl
      (critical_actual_next_difference_record_prior hP hnew)
    exact (next_record_index_iff_fundamental hM hcanon hP hnew).1 hnext
  · intro hReturn R n
    induction n using Nat.strongRecOn generalizing R with
    | ind n ih =>
        intro hR hn hd hprior
        by_cases hsmall : n ≤ 9
        · have h := early_large_increment_index ⟨n, by omega⟩ (by change 5 < d n; omega)
          change n = d n + 2 at h
          omega
        · let k := n - 1
          have hk : 9 ≤ k := by omega
          have hkn : k + 1 = n := by omega
          obtain ⟨M, hP⟩ := attained_previous_maximum_exists k (by omega)
          have hM : 5 < M := by
            have h := hP.1 9 (by decide) hk
            rw [show d 9 = 7 by decide] at h
            omega
          obtain ⟨p, hp, hpk, hdp, hpPrior⟩ := attained_previous_maximum_first_occurrence hP
          have hpEq := ih p (by omega) hM hp hdp hpPrior
          have hMcanon : d (M + 2) = M := by rwa [← hpEq]
          have hnew : M < d (k + 1) := by
            rw [hkn, hd, ← hdp]
            exact hprior p hp (by omega)
          have hfund := hReturn hM (by omega : M + 2 ≤ k) hMcanon hP hnew
          have hEq := (next_record_index_iff_fundamental hM hMcanon hP hnew).2 hfund
          simpa only [hkn, hd] using hEq

end A166944Research

open A166944Research in
theorem solution :
    (∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2) ↔
    (∀ {M k : Nat}, 5 < M → M + 2 ≤ k → d (M + 2) = M →
      IsAttainedPreviousMaximum M k → M < d (k + 1) →
      ∃ m : Nat, M + 2 ≤ m ∧ m < k + 1 ∧ B m = 2) :=
  record_index_iff_canonical_returns
