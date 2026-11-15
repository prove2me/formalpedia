-- Prove2me | solution 1 for A166944Research.band_exit_gap_le_half_record_v2
-- status  : ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-15T03:12:15.907552+00:00
-- url     : https://prove2.me/submissions/37b07107-836b-4912-8425-ed4a25524181

import Definitions.Def_a166944_record_core
import Definitions.Def_a166944_moving_horizon

/-!
Self-contained solution for the band-structure target
`A166944Research.band_exit_gap_le_half_record`.

A canonical replay can leave the capped band `C - s <= M` and come back: the
replay from the record `M = 43` visits `(48,90)` with room `42`, then `(51,96)`
with room `45 > 43`, then `(60,100)` with room `40`. So the tail of a replay
cannot be packaged as a single in-band suffix without an argument about the
excursion.

The statements below fix the shape of such an excursion. The key step is
`two_mul_increment_le_room_next`, which contains no gap term and therefore
composes: an exit has room rising, hence `e >= g + 2`, hence the gap is at most
half the record.

Helper lemmas from the source project are inlined below in dependency order --
not source order, which matters because Lean rejects forward references.
-/

open A166944Research

namespace A166944Research

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

theorem a_add_one_le_add_two (n : Nat) : a (n + 1) ≤ a (n + 2) := by
  simp only [a]
  split <;> exact Nat.le_add_right _ _

theorem a_le_succ (n : Nat) : a n ≤ a (n + 1) := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => simpa using a_add_one_le_add_two n

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

theorem D_succ_eq_add_d_sub_one (n : Nat) :
    D (n + 1) = D n + d (n + 1) - 1 := by
  simpa using congrArg (fun x : Nat => x - 1) (D_succ_add_one_eq_add_d n)

theorem D_succ_eq_D_add_d_sub_one (n : Nat) :
    D (n + 1) = D n + (d (n + 1) - 1) := by
  rw [D_succ_eq_add_d_sub_one n]
  exact Nat.add_sub_assoc (one_le_d_succ n) (D n)

theorem moving_horizon_slack_transition {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (C' - r) + (r - s) = (C - s) + (d r - 1) := by
  rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, hC', _, _⟩
  have hr1 : 1 ≤ r :=
    Nat.le_trans (by simp) (Nat.le_trans hs.1 (Nat.le_of_lt hsr))
  have hrsucc : r - 1 + 1 = r := Nat.sub_add_cancel hr1
  have hDstep : D r = C + (d r - 1) := by
    have h := D_succ_eq_D_add_d_sub_one (r - 1)
    rw [hrsucc, hDr] at h
    exact h
  have hsle : s ≤ r := Nat.le_of_lt hsr
  calc
    (C' - r) + (r - s) = (C + (d r - 1) - r) + (r - s) := by
      rw [hC', hDstep]
    _ = ((C - r) + (d r - 1)) + (r - s) := by
      rw [Nat.sub_add_comm hrC]
    _ = (C - r + (r - s)) + (d r - 1) := by
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ = (C - s) + (d r - 1) := by
      rw [Nat.sub_add_sub_cancel hrC hsle]

/-- **A band exit forces the event to exceed the gap by at least two.**

This is the mechanism behind `BandReentry`. The state is in the band, `room <= M`, and
the next state is out of it, `M < room'`; then the room rose, so the transition
identity forces `e >= g + 2`, and in particular `room' > room`. Leaving the band is a
*gain* in room -- which is exactly why the replay can come back, and why no
monotonicity argument in the opposite direction can work. -/
theorem band_exit_increment_ge_gap_add_two {M s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hin : C - s ≤ M) (hout : M < C' - r) :
    (r - s) + 2 ≤ d r := by
  have htrans := moving_horizon_slack_transition hstep
  have hlt : C - s < C' - r := Nat.lt_of_le_of_lt hin hout
  have hsr : s < r := hstep.2.1
  omega

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

theorem d_pos_of_two_le {n : Nat} (hn : 2 ≤ n) : 0 < d n := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hn
  simpa [Nat.add_comm] using d_add_two_pos k

theorem one_le_d_of_two_le {n : Nat} (hn : 2 ≤ n) : 1 ≤ d n := by
  exact Nat.succ_le_of_lt (d_pos_of_two_le hn)

theorem quotient_mod_two_of_left_odd {R q : Nat} (hR : R % 2 = 1) :
    q % 2 = (R * q) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
  · simp [Nat.mul_mod, hR, hq0]
  · simp [Nat.mul_mod, hR, hq1]

theorem moving_horizon_even_quotient_normal_form {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (heven : r % 2 = 0) :
    ∃ q : Nat, C - s = (r - s) + 1 + d r * q ∧ q % 2 = 1 ∧
      1 ≤ q ∧ C' - r = d r * (q + 1) := by
  have htransition := moving_horizon_slack_transition hstep
  rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, hC', _, _⟩
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hs.1) (Nat.succ_le_of_lt hsr)
  have hC2 : 2 ≤ C := by
    rw [← hs.2.1]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D s := D_le_of_le hs.1
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
  rw [if_pos heven] at hmap
  have hdivr : d r ∣ r := by
    rw [hmap]
    exact Nat.gcd_dvd_left _ _
  have hdivC : d r ∣ C - 1 := by
    rw [hmap]
    exact Nat.gcd_dvd_right _ _
  have hrne : r ≠ C := by
    intro hreq
    have hdvdC : d r ∣ C := by simpa [hreq] using hdivr
    have hdvd1 : d r ∣ 1 := by
      have hsub := Nat.dvd_sub hdvdC hdivC
      rw [Nat.sub_sub_self (Nat.le_trans (by simp) hC2)] at hsub
      exact hsub
    have hdone : d r = 1 := Nat.eq_one_of_dvd_one hdvd1
    have : (1 : Nat) < 1 := by simpa [hdone] using hdr
    exact Nat.lt_irrefl 1 this
  have hrlt : r < C := Nat.lt_of_le_of_ne hrC (fun h => hrne h)
  have hrle : r ≤ C - 1 := by
    apply Nat.le_sub_of_add_le
    exact Nat.succ_le_of_lt hrlt
  have hdivdiff : d r ∣ (C - 1) - r := Nat.dvd_sub hdivC hdivr
  rcases hdivdiff with ⟨q, hq⟩
  have hCminus : C - 1 = r + d r * q := by
    calc
      C - 1 = ((C - 1) - r) + r := (Nat.sub_add_cancel hrle).symm
      _ = d r * q + r := by rw [hq]
      _ = r + d r * q := Nat.add_comm _ _
  have hCpos : 1 ≤ C := Nat.le_trans (by simp) hC2
  have hCeq : C = r + d r * q + 1 := by
    calc
      C = (C - 1) + 1 := (Nat.sub_add_cancel hCpos).symm
      _ = (r + d r * q) + 1 := by rw [hCminus]
  have hrsum : (r - s) + s = r := Nat.sub_add_cancel (Nat.le_of_lt hsr)
  have hL : C - s = (r - s) + 1 + d r * q := by
    apply (Nat.sub_eq_iff_eq_add (Nat.le_trans (Nat.le_of_lt hsr) hrC)).2
    calc
      C = r + d r * q + 1 := hCeq
      _ = ((r - s) + 1 + d r * q) + s := by
        calc
          r + d r * q + 1 = r + 1 + d r * q := by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          _ = (r - s) + s + 1 + d r * q := by rw [hrsum]
          _ = ((r - s) + 1 + d r * q) + s := by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hdodd : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr3
  have hCmod : C % 2 = 0 := by
    rw [← hs.2.1]
    exact D_mod_two_eq_zero_of_two_le hs.1
  have hCminusmod : (C - 1) % 2 = 1 := by
    have hCstep : C - 1 + 1 = C := Nat.sub_add_cancel hCpos
    rcases Nat.mod_two_eq_zero_or_one (C - 1) with hzero | hone
    · have hbad : C % 2 = 1 := by
        calc
          C % 2 = ((C - 1) + 1) % 2 := by rw [hCstep]
          _ = 1 := by simp [Nat.add_mod, hzero]
      simp [hCmod] at hbad
    · exact hone
  have hqmod : q % 2 = 1 := by
    calc
      q % 2 = (d r * q) % 2 := quotient_mod_two_of_left_odd hdodd
      _ = (r + d r * q) % 2 := by simp [Nat.add_mod, heven]
      _ = (C - 1) % 2 := by rw [← hCminus]
      _ = 1 := hCminusmod
  have hq1 : 1 ≤ q := by
    cases q with
    | zero => simp at hqmod
    | succ q => exact Nat.succ_le_succ (Nat.zero_le q)
  have hepos : 1 ≤ d r := one_le_d_of_two_le (Nat.le_trans hs.1 (Nat.le_of_lt hsr))
  have hcancel : (C' - r) + (r - s) =
      (d r * (q + 1)) + (r - s) := by
    calc
      (C' - r) + (r - s) = (C - s) + (d r - 1) := htransition
      _ = ((r - s) + 1 + d r * q) + (d r - 1) := by rw [hL]
      _ = (r - s) + ((d r - 1) + 1) + d r * q := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = (r - s) + d r + d r * q := by rw [Nat.sub_add_cancel hepos]
      _ = d r * (q + 1) + (r - s) := by
        simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hL' : C' - r = d r * (q + 1) := by
    apply Nat.add_right_cancel hcancel
  exact ⟨q, hL, hqmod, hq1, hL'⟩

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

theorem moving_horizon_odd_quotient_normal_form {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') (hodd : r % 2 = 1) :
    ∃ q : Nat, C - s + 3 = (r - s) + d r * q ∧ q % 2 = 0 ∧
      2 ≤ q ∧ C' - r + 4 = d r * (q + 1) := by
  have htransition := moving_horizon_slack_transition hstep
  rcases hstep with ⟨hs, hsr, hrC, hdr, _, hDr, hC', _, _⟩
  have hr3 : 3 ≤ r := by
    exact Nat.le_trans (Nat.succ_le_succ hs.1) (Nat.succ_le_of_lt hsr)
  have hC2 : 2 ≤ C := by
    rw [← hs.2.1]
    calc
      2 = D 2 := by simp [D, a]
      _ ≤ D s := D_le_of_le hs.1
  have hmap := constant_D_event_map (Nat.le_trans (by simp) hr3) hDr
  have hne : r % 2 ≠ 0 := by simp [hodd]
  rw [if_neg hne] at hmap
  have hdivr : d r ∣ r - 2 := by
    rw [hmap]
    exact Nat.gcd_dvd_left _ _
  have hdivC : d r ∣ C + 1 := by
    rw [hmap]
    exact Nat.gcd_dvd_right _ _
  have hr2 : 2 ≤ r := Nat.le_trans hs.1 (Nat.le_of_lt hsr)
  have hqarg : r - 2 ≤ C + 1 :=
    Nat.le_trans (Nat.sub_le r 2) (Nat.le_trans hrC (by simp))
  have hdivdiff : d r ∣ (C + 1) - (r - 2) := Nat.dvd_sub hdivC hdivr
  rcases hdivdiff with ⟨q, hq⟩
  have hCplus : C + 1 = (r - 2) + d r * q := by
    calc
      C + 1 = ((C + 1) - (r - 2)) + (r - 2) :=
        (Nat.sub_add_cancel hqarg).symm
      _ = d r * q + (r - 2) := by rw [hq]
      _ = (r - 2) + d r * q := Nat.add_comm _ _
  have hCplus3 : C + 3 = r + d r * q := by
    calc
      C + 3 = (C + 1) + 2 := by simp [Nat.add_assoc]
      _ = ((r - 2) + d r * q) + 2 := by rw [hCplus]
      _ = (r - 2) + 2 + d r * q := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = r + d r * q := by rw [Nat.sub_add_cancel hr2]
  have hrsum : (r - s) + s = r := Nat.sub_add_cancel (Nat.le_of_lt hsr)
  have hsle : s ≤ C := Nat.le_trans (Nat.le_of_lt hsr) hrC
  have hL : C - s + 3 = (r - s) + d r * q := by
    apply Nat.add_right_cancel
    calc
      (C - s + 3) + s = (C - s) + s + 3 := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = C + 3 := by rw [Nat.sub_add_cancel hsle]
      _ = r + d r * q := hCplus3
      _ = (r - s) + s + d r * q := by rw [hrsum]
      _ = ((r - s) + d r * q) + s := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hdodd : d r % 2 = 1 := d_mod_two_eq_one_of_three_le hr3
  have hCmod : C % 2 = 0 := by
    rw [← hs.2.1]
    exact D_mod_two_eq_zero_of_two_le hs.1
  have hCplusmod : (C + 1) % 2 = 1 := by
    simp [Nat.add_mod, hCmod]
  have hrminusmod : (r - 2) % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (r - 2) with hzero | hone
    · have hbad : r % 2 = 0 := by
        calc
          r % 2 = ((r - 2) + 2) % 2 := by
            rw [Nat.sub_add_cancel hr2]
          _ = 0 := by simp [Nat.add_mod, hzero]
      simp [hodd] at hbad
    · exact hone
  have hqmod : q % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one q with hq0 | hq1
    · exact hq0
    · have hbad : (1 : Nat) = 0 := by
        calc
          1 = (C + 1) % 2 := hCplusmod.symm
          _ = ((r - 2) + d r * q) % 2 := by rw [hCplus]
          _ = 0 := by simp [Nat.add_mod, hrminusmod, Nat.mul_mod, hdodd, hq1]
      cases hbad
  have hqne : q ≠ 0 := by
    intro hq0
    have heq : C + 1 = r - 2 := by simpa [hq0] using hCplus
    have hlt : r - 2 < C + 1 :=
      Nat.lt_of_le_of_lt (Nat.sub_le r 2)
        (Nat.lt_of_le_of_lt hrC (Nat.lt_succ_self C))
    have : r - 2 < r - 2 := by simpa [heq] using hlt
    exact Nat.lt_irrefl _ this
  have hqpos : 0 < q := by
    cases q with
    | zero => exact False.elim (hqne rfl)
    | succ q => exact Nat.zero_lt_succ q
  have hq2 : 2 ≤ q := two_le_of_pos_of_mod_two_eq_zero hqpos hqmod
  have hepos : 1 ≤ d r := one_le_d_of_two_le (Nat.le_trans hs.1 (Nat.le_of_lt hsr))
  have hfour : d r - 1 + 4 = 3 + ((d r - 1) + 1) := by
    calc
      d r - 1 + 4 = (d r - 1 + 1) + 3 := by
        simp [Nat.add_assoc]
      _ = d r + 3 := by rw [Nat.sub_add_cancel hepos]
      _ = 3 + ((d r - 1) + 1) := by
        rw [Nat.sub_add_cancel hepos]
        simp [Nat.add_comm]
  have hcancel : (C' - r + 4) + (r - s) =
      (d r * (q + 1)) + (r - s) := by
    calc
      (C' - r + 4) + (r - s) = (C' - r) + (r - s) + 4 := by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = (C - s) + (d r - 1) + 4 := by rw [htransition]
      _ = (C - s) + (3 + ((d r - 1) + 1)) := by
        rw [Nat.add_assoc, hfour]
      _ = (C - s + 3) + ((d r - 1) + 1) := by
        simp [Nat.add_assoc]
      _ = ((r - s) + d r * q) + ((d r - 1) + 1) := by rw [hL]
      _ = (r - s) + d r + d r * q := by
        rw [Nat.sub_add_cancel hepos]
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = d r * (q + 1) + (r - s) := by
        simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hL' : C' - r + 4 = d r * (q + 1) := Nat.add_right_cancel hcancel
  exact ⟨q, hL, hqmod, hq2, hL'⟩

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

/-- **The room left after a step is at least twice the event minus two.**

Even case: `C' - r = e * (q + 1)` with `q >= 1`, so `C' - r >= 2 * e`.
Odd case: `C' - r + 4 = e * (q + 1)` with `q >= 2`, so `C' - r + 4 >= 3 * e`, and
`3 * e - 4 >= 2 * e - 2` because `e >= 2`.

Neither case uses the gap, which is why this form composes along a path. -/
theorem two_mul_increment_le_room_next {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    2 * d r ≤ (C' - r) + 2 := by
  by_cases heven : r % 2 = 0
  · obtain ⟨q, _, _, hq1, hlast⟩ :=
      moving_horizon_even_quotient_normal_form hstep heven
    have hmul : d r * 2 ≤ d r * (q + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  · have hodd : r % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one r with hzero | hone
      · exact absurd hzero heven
      · exact hone
    obtain ⟨q, _, _, hq2, hlast⟩ :=
      moving_horizon_odd_quotient_normal_form hstep hodd
    have hmul : d r * 3 ≤ d r * (q + 1) := Nat.mul_le_mul_left _ (by omega)
    have he2 : 2 ≤ d r := by
      have := moving_horizon_step_event_ge_three hstep
      omega
    omega

/-- **The room plus one covers the gap plus the event.**  Equivalently the gap is at
most the room minus the event plus one, so a large event *forces* a short gap. -/
theorem gap_add_increment_le_room_add_one {s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C') :
    (r - s) + d r ≤ (C - s) + 1 := by
  have htrans := moving_horizon_slack_transition hstep
  have hmain := two_mul_increment_le_room_next hstep
  have hsr : s < r := hstep.2.1
  omega

/-- **At a band exit the gap is at most half the record.**  Combining
`in_band_exit_forces` (`e >= g + 2`) with `gap_le_room_sub_increment_add_one`
(`g <= room - e + 1`) and `room <= M`. -/
theorem band_exit_gap_le_half_record {M s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hin : C - s ≤ M) (hout : M < C' - r) :
    2 * (r - s) + 1 ≤ M := by
  have hinc := band_exit_increment_ge_gap_add_two hstep hin hout
  -- Additive route: the room form avoids inverting the truncated subtraction.
  have hroomform := gap_add_increment_le_room_add_one hstep
  omega

end A166944Research

open A166944Research in
/-- The target, with the binder order of the source declaration preserved so the
two types are syntactically identical: `{M s C r C'}` first, then the hypotheses
in the order `hstep`, `hin`, `hout`. -/
theorem solution {M s C r C' : Nat}
    (hstep : IsMovingHorizonStep s C r C')
    (hin : C - s ≤ M) (hout : M < C' - r) :
    2 * (r - s) + 1 ≤ M :=
  band_exit_gap_le_half_record hstep hin hout
