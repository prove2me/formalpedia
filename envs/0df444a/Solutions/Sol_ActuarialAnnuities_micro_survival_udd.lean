-- Prove2me | solution 1 for ActuarialAnnuities.micro_survival_udd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T07:22:33.322227+00:00
-- url     : https://prove2.me/submissions/c9bc14aa-8091-490b-b960-4c702bce9fe3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bUDD
import Definitions.Def_actuarial_bUDDMicroSurvival
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAnnuities

theorem solution (h m q : ℕ) (p : ℕ → ℝ)
    (hm : 0 < m) (hq : q < h*m) :
    bUDDMicroSurvival h m p q =
      bUDD (bSurvival h p (q/m))
        (bSurvival h p (q/m+1)) (((q % m : ℕ) : ℝ)/(m : ℝ)) := by
  classical
  let w : ℕ → ℝ := bUDDMicroMass h m p
  let j : ℕ := q/m
  let r : ℕ := q%m
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hj : j < h := by
    dsimp [j]
    exact (Nat.div_lt_iff_lt_mul hm).2 hq
  have hr : r < m := Nat.mod_lt q hm
  have hqsplit : q = j*m+r := by
    calc
      q = q%m + m*(q/m) := (Nat.mod_add_div q m).symm
      _ = j*m+r := by dsimp [j,r]; ring
  have hblock (i v : ℕ) (hi : i < h) (hv : v ≤ m) :
      (∑ t ∈ Finset.range v, w (i*m+t)) =
        (v : ℝ)*p i/(m : ℝ) := by
    have heach (t : ℕ) (ht : t < v) :
        w (i*m+t) = p i/(m : ℝ) := by
      have hit : t < m := lt_of_lt_of_le ht hv
      have hisucc : i+1 ≤ h := Nat.succ_le_of_lt hi
      have himul : (i+1)*m ≤ h*m :=
        Nat.mul_le_mul_right m hisucc
      have hiindex : i*m+t < (i+1)*m := by
        rw [Nat.succ_mul]
        omega
      have hindex : i*m+t < h*m := lt_of_lt_of_le hiindex himul
      have hdiv : (i*m+t)/m = i := by
        rw [show i*m+t = m*i+t by ring]
        rw [Nat.mul_add_div hm]
        simp [Nat.div_eq_of_lt hit]
      simp [w, bUDDMicroMass, hindex, hdiv]
    calc
      (∑ t ∈ Finset.range v, w (i*m+t)) =
          ∑ t ∈ Finset.range v, (p i/(m : ℝ)) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact heach t (Finset.mem_range.mp ht)
      _ = (v : ℝ)*p i/(m : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hprefix : ∀ i : ℕ, i ≤ h →
      (∑ t ∈ Finset.range (i*m), w t) =
        ∑ t ∈ Finset.range i, p t := by
    intro i
    induction i with
    | zero =>
      intro _
      simp
    | succ i ih =>
      intro hi
      have hlt : i < h := Nat.lt_of_succ_le hi
      have hb := hblock i m hlt (le_refl m)
      have hmblock : (m : ℝ)*p i/(m : ℝ) = p i := by
        field_simp [hm0]
      calc
        (∑ t ∈ Finset.range ((i+1)*m), w t) =
            (∑ t ∈ Finset.range (i*m), w t) +
            (∑ t ∈ Finset.range m, w (i*m+t)) := by
          conv_lhs =>
            rw [show (i+1)*m = i*m+m by ring, Finset.sum_range_add]
        _ = (∑ t ∈ Finset.range i, p t) + p i := by
          rw [ih (Nat.le_of_lt hlt), hb, hmblock]
        _ = ∑ t ∈ Finset.range (i+1), p t := by
          rw [Finset.sum_range_succ]
  have htotal :
      (∑ t ∈ Finset.range (h*m+1), w t) =
        ∑ t ∈ Finset.range (h+1), p t := by
    have he : w (h*m) = p h := by simp [w,bUDDMicroMass]
    rw [Finset.sum_range_succ, hprefix h (le_refl h), he,
        Finset.sum_range_succ]
  have hprefixq :
      (∑ t ∈ Finset.range q, w t) =
      (∑ t ∈ Finset.range j, p t) +
        (r : ℝ)*p j/(m : ℝ) := by
    conv_lhs => rw [hqsplit, Finset.sum_range_add]
    rw [hprefix j (Nat.le_of_lt hj), hblock j r hj (Nat.le_of_lt hr)]
  have hsurv (N t : ℕ) (u : ℕ → ℝ) (ht : t ≤ N) :
      bSurvival N u t =
        (∑ k ∈ Finset.range (N+1), u k) -
        (∑ k ∈ Finset.range t, u k) := by
    unfold bSurvival
    have hhead :
        (∑ k ∈ Finset.range t, u k * bAlive k t) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hnot : ¬t ≤ k := Nat.not_le_of_gt (Finset.mem_range.mp hk)
      simp [bAlive, hnot]
    have htail :
        (∑ k ∈ Finset.range (N+1-t),
          u (t+k)*bAlive (t+k) t) =
        (∑ k ∈ Finset.range (N+1-t), u (t+k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [bAlive, Nat.le_add_right]
    have hsum :
        (∑ k ∈ Finset.range (N+1), u k) =
        (∑ k ∈ Finset.range t, u k) +
        (∑ k ∈ Finset.range (N+1-t), u (t+k)) := by
      conv_lhs =>
        rw [show N+1=t+(N+1-t) by omega, Finset.sum_range_add]
    calc
      (∑ k ∈ Finset.range (N+1), u k*bAlive k t) =
          (∑ k ∈ Finset.range t, u k*bAlive k t) +
          (∑ k ∈ Finset.range (N+1-t),
            u (t+k)*bAlive (t+k) t) := by
        conv_lhs =>
          rw [show N+1=t+(N+1-t) by omega, Finset.sum_range_add]
      _ = (∑ k ∈ Finset.range (N+1-t), u (t+k)) := by
        rw [hhead, htail, zero_add]
      _ = (∑ k ∈ Finset.range (N+1), u k) -
          (∑ k ∈ Finset.range t, u k) := by
        rw [hsum]
        ring
  have hsMicro : bUDDMicroSurvival h m p q =
      (∑ k ∈ Finset.range (h+1), p k) -
      ((∑ k ∈ Finset.range j, p k) +
        (r : ℝ)*p j/(m : ℝ)) := by
    unfold bUDDMicroSurvival
    simpa only [w] using
      (hsurv (h*m) q w (Nat.le_of_lt hq)).trans
      (by rw [htotal, hprefixq])
  have hsMacro := hsurv h j p (Nat.le_of_lt hj)
  have hsNext := hsurv h (j+1) p (Nat.succ_le_of_lt hj)
  unfold bUDD
  have hprefix_next :
      (∑ k ∈ Finset.range (j+1), p k) =
        (∑ k ∈ Finset.range j, p k) + p j :=
      Finset.sum_range_succ p j
  rw [hsMicro, hsMacro, hsNext, hprefix_next]
  ring
