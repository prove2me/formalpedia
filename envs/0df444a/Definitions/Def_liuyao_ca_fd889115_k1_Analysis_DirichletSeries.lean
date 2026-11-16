-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_DirichletSeries
-- name    : liuyao_ca_fd889115_k1_Analysis_DirichletSeries
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:54:54.414259+00:00
-- url     : https://prove2.me/theorems/940a86f4-8d0f-494d-8b3f-6a4ff16d65a8
-- title:
--   Computable analysis · DirichletSeries · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/DirichletSeries.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTC

set_option autoImplicit true

/-!
# Dirichlet series

Computable Dirichlet-series style algorithms: zeta values, Dirichlet
L-functions, and the Dirichlet beta value behind Leibniz pi.
-/

namespace ComputableAnalysis

namespace DirichletSeries

def zetaTwoTerm (k : Nat) : Rat :=
  let m : Rat := ((k + 1 : Nat) : Rat)
  1 / (m * m)

/-- The finite partial sum `sum_{k=1}^n 1/k^2`. -/
def zetaTwoPartial : Nat -> Rat
  | 0 => 0
  | n + 1 => zetaTwoPartial n + zetaTwoTerm n

theorem zetaTwoPartial_succ (n : Nat) :
    zetaTwoPartial (n + 1) = zetaTwoPartial n + zetaTwoTerm n := by
  rfl

theorem zetaTwoTerm_nonneg (k : Nat) : 0 <= zetaTwoTerm k := by
  unfold zetaTwoTerm
  let m : Rat := ((k + 1 : Nat) : Rat)
  have hmpos : 0 < m := by
    dsimp [m]
    exact (Rat.natCast_pos).2 (Nat.succ_pos k)
  exact Rat.le_of_lt (by
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 (Rat.mul_pos hmpos hmpos))

theorem zetaTwoTerm_pos (k : Nat) : 0 < zetaTwoTerm k := by
  unfold zetaTwoTerm
  let m : Rat := ((k + 1 : Nat) : Rat)
  have hmpos : 0 < m := by
    dsimp [m]
    exact (Rat.natCast_pos).2 (Nat.succ_pos k)
  rw [Rat.div_def, Rat.one_mul]
  exact (Rat.inv_pos).2 (Rat.mul_pos hmpos hmpos)

theorem zetaTwoPartial_nonneg (n : Nat) :
    0 <= zetaTwoPartial n := by
  induction n with
  | zero => simp [zetaTwoPartial]
  | succ n ih =>
      rw [zetaTwoPartial_succ]
      exact Rat.add_nonneg ih (zetaTwoTerm_nonneg n)

theorem zetaTwoPartial_le_succ (n : Nat) :
    zetaTwoPartial n <= zetaTwoPartial (n + 1) := by
  change zetaTwoPartial n <= zetaTwoPartial n + zetaTwoTerm n
  grind [zetaTwoTerm_nonneg n]

theorem zetaTwoPartial_lt_succ (n : Nat) :
    zetaTwoPartial n < zetaTwoPartial (n + 1) := by
  change zetaTwoPartial n < zetaTwoPartial n + zetaTwoTerm n
  have h : zetaTwoPartial n + 0 <
      zetaTwoPartial n + zetaTwoTerm n :=
    (Rat.add_lt_add_left).2 (zetaTwoTerm_pos n)
  grind

theorem zetaTwoPartial_le_of_le {n m : Nat} :
    n <= m -> zetaTwoPartial n <= zetaTwoPartial m := by
  intro h
  induction h with
  | refl => exact Rat.le_refl
  | step _ ih =>
      exact Rat.le_trans ih (zetaTwoPartial_le_succ _)

/-- A finite tail after the first `n` terms:
`sum_{j=0}^{count-1} 1/(n+j+1)^2`. -/
def zetaTwoFiniteTail (n : Nat) : Nat -> Rat
  | 0 => 0
  | count + 1 => zetaTwoFiniteTail n count + zetaTwoTerm (n + count)

theorem zetaTwoFiniteTail_succ (n count : Nat) :
    zetaTwoFiniteTail n (count + 1) =
      zetaTwoFiniteTail n count + zetaTwoTerm (n + count) := by
  rfl

/-- Finite tails concatenate exactly at the shifted starting index.  This is
the blockwise accounting law used when several finite error budgets are
combined. -/
theorem zetaTwoFiniteTail_add (n count extra : Nat) :
    zetaTwoFiniteTail n (count + extra) =
      zetaTwoFiniteTail n count +
        zetaTwoFiniteTail (n + count) extra := by
  induction extra with
  | zero => grind [zetaTwoFiniteTail]
  | succ extra ih =>
      have hcount : count + (extra + 1) = (count + extra) + 1 := by omega
      rw [hcount, zetaTwoFiniteTail_succ]
      rw [ih]
      have hshift : n + (count + extra) = (n + count) + extra := by omega
      rw [hshift, zetaTwoFiniteTail_succ]
      grind [Rat.add_assoc]

theorem zetaTwoFiniteTail_nonneg (n count : Nat) :
    0 <= zetaTwoFiniteTail n count := by
  induction count with
  | zero => simp [zetaTwoFiniteTail]
  | succ count ih =>
      rw [zetaTwoFiniteTail_succ]
      exact Rat.add_nonneg ih (zetaTwoTerm_nonneg (n + count))

theorem zetaTwoFiniteTail_pos (n count : Nat) (hcount : 0 < count) :
    0 < zetaTwoFiniteTail n count := by
  cases count with
  | zero => omega
  | succ count =>
      rw [zetaTwoFiniteTail_succ]
      have hterm := zetaTwoTerm_pos (n + count)
      have htail := zetaTwoFiniteTail_nonneg n count
      grind

private theorem rat_add_le_add {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d := by
  grind

/-- One term of the zeta tail is bounded by the corresponding telescoping
difference:

`1/(m+1)^2 <= 1/m - 1/(m+1)`.
-/
theorem zetaTwoTerm_le_telescopeStep (m : Nat) (hm : 0 < m) :
    zetaTwoTerm m <=
      1 / (m : Rat) - 1 / ((m + 1 : Nat) : Rat) := by
  unfold zetaTwoTerm
  let M : Rat := (m : Rat)
  let S : Rat := ((m + 1 : Nat) : Rat)
  have hMpos : 0 < M := by
    dsimp [M]
    exact (Rat.natCast_pos).2 hm
  have hSpos : 0 < S := by
    dsimp [S]
    exact (Rat.natCast_pos).2 (Nat.succ_pos m)
  have hMne : M ≠0 := Rat.ne_of_gt hMpos
  have hSne : S ≠0 := Rat.ne_of_gt hSpos
  have hSSne : S * S ≠0 := by
    exact Rat.ne_of_gt (Rat.mul_pos hSpos hSpos)
  have hMleS : M <= S := by
    dsimp [M, S]
    exact_mod_cast (Nat.le_succ m)
  apply Rat.le_of_mul_le_mul_right (c := (S * S) * M)
  · calc
      (1 / (S * S)) * ((S * S) * M) = M := by
        rw [Rat.div_def]
        have hcancel : (S * S) * (S * S)⁻¹= 1 :=
          Rat.mul_inv_cancel (S * S) hSSne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= S := hMleS
      _ = (1 / M - 1 / S) * ((S * S) * M) := by
        rw [Rat.div_def, Rat.div_def]
        have hMcancel : M * M⁻¹= 1 := Rat.mul_inv_cancel M hMne
        have hScancel : S * S⁻¹= 1 := Rat.mul_inv_cancel S hSne
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
          Rat.mul_assoc, Rat.mul_comm]
  · exact Rat.mul_pos (Rat.mul_pos hSpos hSpos) hMpos

def telescopingTailBound (n : Nat) (count : Nat) : Rat :=
  1 / (n : Rat) - 1 / ((n + count : Nat) : Rat)

private theorem telescopingTailBound_step (n : Nat) (count : Nat) :
    telescopingTailBound n count +
      (1 / ((n + count : Nat) : Rat) -
        1 / (((n + count) + 1 : Nat) : Rat)) =
      telescopingTailBound n (count + 1) := by
  unfold telescopingTailBound
  have hnat : n + (count + 1) = (n + count) + 1 := by omega
  rw [hnat]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- Finite telescoping proof of the zeta(2) tail estimate:

`sum_{j=0}^{count-1} 1/(n+j+1)^2 <= 1/n - 1/(n+count)`.
-/
theorem zetaTwoFiniteTail_le_telescoping
    (n : Nat) (hn : 0 < n) (count : Nat) :
    zetaTwoFiniteTail n count <= telescopingTailBound n count := by
  induction count with
  | zero =>
      unfold zetaTwoFiniteTail telescopingTailBound
      grind [Rat.sub_eq_add_neg]
  | succ count ih =>
      unfold zetaTwoFiniteTail
      have hstep :
          zetaTwoTerm (n + count) <=
            1 / ((n + count : Nat) : Rat) -
              1 / (((n + count) + 1 : Nat) : Rat) :=
        zetaTwoTerm_le_telescopeStep (n + count) (Nat.add_pos_left hn count)
      calc
        zetaTwoFiniteTail n count + zetaTwoTerm (n + count)
            <= telescopingTailBound n count +
                (1 / ((n + count : Nat) : Rat) -
                  1 / (((n + count) + 1 : Nat) : Rat)) :=
              rat_add_le_add ih hstep
        _ = telescopingTailBound n (count + 1) :=
              telescopingTailBound_step n count

/-- The finite tail estimate in the coarser form used by the interval
algorithm. -/
theorem zetaTwoFiniteTail_le_tailBound (n : Nat) (hn : 0 < n) (count : Nat) :
    zetaTwoFiniteTail n count <= 1 / (n : Rat) := by
  have htel := zetaTwoFiniteTail_le_telescoping n hn count
  have hdenpos : 0 < ((n + count : Nat) : Rat) := by
    exact (Rat.natCast_pos).2 (Nat.add_pos_left hn count)
  have hnonneg : 0 <= 1 / ((n + count : Nat) : Rat) :=
    Rat.le_of_lt (by
      rw [Rat.div_def, Rat.one_mul]
      exact (Rat.inv_pos).2 hdenpos)
  exact Rat.le_trans htel (by
    unfold telescopingTailBound
    grind [Rat.sub_eq_add_neg])

theorem zetaTwoFiniteTail_lt_one_div
    (n : Nat) (hn : 0 < n) (count : Nat) (hcount : 0 < count) :
    zetaTwoFiniteTail n count < 1 / (n : Rat) := by
  have hbound := zetaTwoFiniteTail_le_telescoping n hn count
  have hsumpos : 0 < n + count := by omega
  have htailpos : 0 < 1 / ((n + count : Nat) : Rat) := by
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 hsumpos)
  unfold telescopingTailBound at hbound
  grind

/-- The endpoint padding used by the Basel-series interval algorithm.

This is part of the raw algorithm's definition.  The finite telescoping
lemmas above explain why this is the traditional tail padding, but validity
of the raw real only uses the interval order, nesting, and width shrinking
proved below. -/
def zetaTwoTailBound (n : Nat) : Rat :=
  if n = 0 then 2 else 1 / (n : Rat)

def zetaTwoUpper (n : Nat) : Rat :=
  zetaTwoPartial n + zetaTwoTailBound n

theorem zetaTwoUpper_succ_le (n : Nat) (hn : 0 < n) :
    zetaTwoUpper (n + 1) <= zetaTwoUpper n := by
  unfold zetaTwoUpper zetaTwoTailBound
  rw [if_neg (Nat.succ_ne_zero n)]
  rw [if_neg (Nat.ne_of_gt hn)]
  change zetaTwoPartial n + zetaTwoTerm n +
      1 / ((n + 1 : Nat) : Rat) <=
    zetaTwoPartial n + 1 / (n : Rat)
  have hstep := zetaTwoTerm_le_telescopeStep n hn
  have hwithPartial :
      zetaTwoPartial n + zetaTwoTerm n <=
        zetaTwoPartial n +
          (1 / (n : Rat) - 1 / ((n + 1 : Nat) : Rat)) :=
    rat_add_le_add (by exact Rat.le_refl) hstep
  calc
    zetaTwoPartial n + zetaTwoTerm n +
        1 / ((n + 1 : Nat) : Rat)
        <= zetaTwoPartial n +
            (1 / (n : Rat) - 1 / ((n + 1 : Nat) : Rat)) +
              1 / ((n + 1 : Nat) : Rat) :=
          rat_add_le_add hwithPartial (by exact Rat.le_refl)
    _ = zetaTwoPartial n + 1 / (n : Rat) := by
          grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem zetaTwoUpper_le_of_le {n m : Nat}
    (hn : 0 < n) (h : n <= m) :
    zetaTwoUpper m <= zetaTwoUpper n := by
  induction h with
  | refl => exact Rat.le_refl
  | step h ih =>
      have hmpos : 0 < _ := Nat.lt_of_lt_of_le hn h
      exact Rat.le_trans (zetaTwoUpper_succ_le _ hmpos) ih

/-- Every finite reciprocal-square partial sum stays below the initial
stage-one padded endpoint.  This is a global finite bound for the Basel
certificate, not an assertion of the infinite sum. -/
theorem zetaTwoPartial_le_two (n : Nat) :
    zetaTwoPartial n ≤ 2 := by
  by_cases hn0 : n = 0
  · simp [hn0, zetaTwoPartial]
    decide +kernel
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hpartial_upper : zetaTwoPartial n ≤ zetaTwoUpper n := by
      unfold zetaTwoUpper zetaTwoTailBound
      simp [hn0]
      have htail_pos : 0 < 1 / (n : Rat) := one_div_nat_pos hn
      have htail_nonneg : 0 ≤ 1 / (n : Rat) := Rat.le_of_lt htail_pos
      simpa only [Rat.add_zero] using (Rat.add_le_add_left (a := (0 : Rat))
        (b := 1 / (n : Rat)) (c := zetaTwoPartial n)).2 htail_nonneg
    have hupper : zetaTwoUpper n ≤ zetaTwoUpper 1 :=
      zetaTwoUpper_le_of_le (by omega : 0 < (1 : Nat)) hn
    have hstage_one : zetaTwoUpper 1 = 2 := by
      decide +kernel
    calc
      zetaTwoPartial n ≤ zetaTwoUpper n := hpartial_upper
      _ ≤ zetaTwoUpper 1 := hupper
      _ = 2 := hstage_one

/-- Computable interval for `zeta(2)` at stage `n`.

The lower endpoint is the first `n` terms.  The upper endpoint adds the
elementary rational tail bound `1/n`.
-/
def zetaTwoInterval (n : Nat) : QInterval :=
  let s := zetaTwoPartial n
  { lo := s, hi := s + zetaTwoTailBound n }

theorem zetaTwoInterval_width (n : Nat) :
    (zetaTwoInterval n).width = zetaTwoTailBound n := by
  unfold zetaTwoInterval QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem zetaTwoInterval_width_nonneg (n : Nat) :
    0 <= (zetaTwoInterval n).width := by
  rw [zetaTwoInterval_width]
  unfold zetaTwoTailBound
  by_cases hn0 : n = 0
  · simp [hn0]
    decide +kernel
  · simp [hn0]
    exact Rat.le_of_lt (by
      rw [Rat.div_def, Rat.one_mul]
      exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn0)))

theorem zetaTwoInterval_width_pos (n : Nat) (hn : 0 < n) :
    0 < (zetaTwoInterval n).width := by
  rw [zetaTwoInterval_width]
  unfold zetaTwoTailBound
  simp [Nat.ne_of_gt hn]
  exact one_div_nat_pos hn

theorem zetaTwoInterval_lo_nonneg (n : Nat) :
    0 <= (zetaTwoInterval n).lo := by
  change 0 <= zetaTwoPartial n
  exact zetaTwoPartial_nonneg n

theorem zetaTwoInterval_hi_pos (n : Nat) :
    0 < (zetaTwoInterval n).hi := by
  change 0 < zetaTwoPartial n + zetaTwoTailBound n
  by_cases hn0 : n = 0
  · simp [hn0, zetaTwoPartial, zetaTwoTailBound]
    decide +kernel
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have htail : 0 < zetaTwoTailBound n := by
      unfold zetaTwoTailBound
      simp [hn0]
      exact one_div_nat_pos hn
    grind [zetaTwoPartial_nonneg n]

theorem zetaTwoInterval_width_le_one_div (n : Nat) (hn : 0 < n) :
    (zetaTwoInterval n).width <= 1 / (n : Rat) := by
  rw [zetaTwoInterval_width]
  unfold zetaTwoTailBound
  simp [Nat.ne_of_gt hn]

theorem zetaTwoInterval_ordered (n : Nat) :
    (zetaTwoInterval n).lo <= (zetaTwoInterval n).hi := by
  have h := zetaTwoInterval_width_nonneg n
  unfold QInterval.width at h
  grind [Rat.sub_eq_add_neg]

theorem zetaTwoInterval_nested (n m : Nat) (hnm : n <= m) :
    (zetaTwoInterval n).lo <= (zetaTwoInterval m).lo /\
      (zetaTwoInterval m).lo <= (zetaTwoInterval m).hi /\
      (zetaTwoInterval m).hi <= (zetaTwoInterval n).hi := by
  constructor
  · change zetaTwoPartial n <= zetaTwoPartial m
    exact zetaTwoPartial_le_of_le hnm
  · constructor
    · exact zetaTwoInterval_ordered m
    · change zetaTwoUpper m <= zetaTwoUpper n
      by_cases hn0 : n = 0
      · by_cases hm0 : m = 0
        · simp [hn0, hm0, zetaTwoUpper, zetaTwoTailBound]
        · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          calc
            zetaTwoUpper m <= zetaTwoUpper 1 :=
              zetaTwoUpper_le_of_le (by omega : 0 < (1 : Nat)) hmpos
            _ = zetaTwoUpper n := by
              rw [hn0]
              decide +kernel
      · exact zetaTwoUpper_le_of_le (Nat.pos_of_ne_zero hn0) hnm

/-- Every later finite partial sum is enclosed by the earlier interval's
upper endpoint.  The proof exposes the finite decomposition into the first
`n` terms and the next `count` terms, then applies the explicit telescoping
tail bound.  This is a finite convergence certificate; it does not identify
the raw value with `pi^2 / 6`. -/
theorem zetaTwoPartial_add_finiteTail_le_interval_hi
    (n count : Nat) (hn : 0 < n) :
    zetaTwoPartial (n + count) <= (zetaTwoInterval n).hi := by
  have hsplit :
    zetaTwoPartial (n + count) =
        zetaTwoPartial n + zetaTwoFiniteTail n count := by
    induction count with
    | zero => simp [zetaTwoFiniteTail, Rat.add_zero]
    | succ count ih =>
        rw [show n + (count + 1) = (n + count) + 1 by omega]
        rw [zetaTwoPartial_succ, ih, zetaTwoFiniteTail_succ]
        grind [Rat.add_assoc]
  rw [hsplit]
  change zetaTwoPartial n + zetaTwoFiniteTail n count <=
    zetaTwoPartial n + zetaTwoTailBound n
  rw [show zetaTwoTailBound n = 1 / (n : Rat) by
    simp [zetaTwoTailBound, Nat.ne_of_gt hn]]
  exact (Rat.add_le_add_left).2
    (zetaTwoFiniteTail_le_tailBound n hn count)

/-- A nonempty finite tail lies strictly below the interval's padded upper
endpoint.  This is the strict finite counterpart of
`zetaTwoPartial_add_finiteTail_le_interval_hi`; it does not use a completed
zeta value. -/
theorem zetaTwoPartial_add_nonempty_finiteTail_lt_interval_hi
    (n count : Nat) (hn : 0 < n) (hcount : 0 < count) :
    zetaTwoPartial (n + count) < (zetaTwoInterval n).hi := by
  have hsplit :
      zetaTwoPartial (n + count) =
        zetaTwoPartial n + zetaTwoFiniteTail n count := by
    clear hcount
    induction count with
    | zero => simp [zetaTwoFiniteTail, Rat.add_zero]
    | succ count ih =>
        rw [show n + (count + 1) = (n + count) + 1 by omega]
        rw [zetaTwoPartial_succ, ih, zetaTwoFiniteTail_succ]
        grind [Rat.add_assoc]
  rw [hsplit]
  change zetaTwoPartial n + zetaTwoFiniteTail n count <
    zetaTwoPartial n + zetaTwoTailBound n
  rw [show zetaTwoTailBound n = 1 / (n : Rat) by
    simp [zetaTwoTailBound, Nat.ne_of_gt hn]]
  exact (Rat.add_lt_add_left).2
    (zetaTwoFiniteTail_lt_one_div n hn count hcount)

/-- A checked finite endpoint certificate for the Basel target.

The stage-1000 interval contains the rational decimal `1.644934`.  This is
only a finite comparison with a proposed target interval; it does not identify
the raw zeta value with `pi^2 / 6`.
-/
theorem zetaTwoInterval_contains_basel_decimal_1000 :
    (zetaTwoInterval 1000).lo <= (822467 : Rat) / 500000 /\
      (822467 : Rat) / 500000 <= (zetaTwoInterval 1000).hi := by
  decide +kernel

theorem zetaTwoInterval_later_inside_stage_10000 {m : Nat}
    (hm : 10000 <= m) :
    (zetaTwoInterval 10000).lo <= (zetaTwoInterval m).lo /\
      (zetaTwoInterval m).hi <= (zetaTwoInterval 10000).hi := by
  have hnested := zetaTwoInterval_nested 10000 m hm
  exact ⟨hnested.1, hnested.2.2⟩

theorem zetaTwoPartial_later_inside_stage_10000 {m : Nat}
    (hm : 10000 <= m) :
    (zetaTwoInterval 10000).lo <= zetaTwoPartial m /\
      zetaTwoPartial m <= (zetaTwoInterval 10000).hi := by
  have hpartial_lo : zetaTwoPartial 10000 <= zetaTwoPartial m :=
    zetaTwoPartial_le_of_le hm
  have hpartial_hi : zetaTwoPartial m <= (zetaTwoInterval m).hi := by
    change (zetaTwoInterval m).lo <= (zetaTwoInterval m).hi
    exact zetaTwoInterval_ordered m
  have hnested := zetaTwoInterval_later_inside_stage_10000 hm
  constructor
  · exact hpartial_lo
  · exact Rat.le_trans hpartial_hi hnested.2

private theorem one_div_nat_le_one_div_nat_of_le
    {a b : Nat} (ha : 0 < a) (hab : a <= b) :
    1 / (b : Rat) <= 1 / (a : Rat) := by
  let A : Rat := (a : Rat)
  let B : Rat := (b : Rat)
  have hApos : 0 < A := by
    dsimp [A]
    exact (Rat.natCast_pos).2 ha
  have hBpos : 0 < B := by
    dsimp [B]
    exact (Rat.natCast_pos).2 (Nat.lt_of_lt_of_le ha hab)
  have hAne : A ≠0 := Rat.ne_of_gt hApos
  have hBne : B ≠0 := Rat.ne_of_gt hBpos
  have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
  have hAleB : A <= B := by
    dsimp [A, B]
    exact_mod_cast hab
  apply Rat.le_of_mul_le_mul_right (c := A * B)
  · calc
      (1 / B) * (A * B) = A := by
        rw [Rat.div_def]
        have hcancel : B * B⁻¹= 1 := Rat.mul_inv_cancel B hBne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= B := hAleB
      _ = (1 / A) * (A * B) := by
        rw [Rat.div_def]
        have hcancel : A * A⁻¹= 1 := Rat.mul_inv_cancel A hAne
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hABpos

/-- An explicit denominator/stage budget turns the finite Basel interval width
into a prescribed rational error bound.  The hypothesis
`eps.den + 1 <= n` is a natural-number certificate: at stage `n`, the
interval width is at most `eps`.  This is an endpoint/width estimate for the
finite evaluator only; it does not assert a completed zeta sum or identify it
with `pi^2 / 6`.
-/
theorem zetaTwoInterval_width_le_of_denominator_budget {n : Nat} {eps : Rat}
    (heps : 0 < eps) (hbudget : eps.den + 1 <= n) :
    (zetaTwoInterval n).width <= eps := by
  have hbase : 0 < eps.den + 1 := Nat.succ_pos eps.den
  have hn : 0 < n := Nat.lt_of_lt_of_le hbase hbudget
  calc
    (zetaTwoInterval n).width <= 1 / (n : Rat) :=
      zetaTwoInterval_width_le_one_div n hn
    _ <= 1 / (((eps.den + 1 : Nat) : Rat)) :=
      one_div_nat_le_one_div_nat_of_le hbase hbudget
    _ <= eps := FTC.one_div_den_succ_le_of_pos heps

/-- The denominator budget has an executable stage-selector form.  For every
positive rational tolerance, the finite reciprocal-square interval algorithm
returns a natural stage whose width is below that tolerance; no completed
zeta value is introduced. -/
theorem zetaTwoInterval_reaches_of_positive_tolerance (eps : QPos) :
    ∃ n : Nat, (zetaTwoInterval n).width <= eps.val := by
  refine ⟨eps.val.den + 1, ?_⟩
  exact zetaTwoInterval_width_le_of_denominator_budget
    eps.property (Nat.le_refl (eps.val.den + 1))

/-- A supplied rational target interval can be used as a finite comparison
anchor for all later zeta-two stages.  The endpoint hypothesis says that the
target contains the stage-`n` interval; nesting transports that comparison to
stage `m`, while the denominator budget gives the requested finite width
bound.  This is only a comparison of rational interval evaluators and makes
no claim about a completed zeta value or the Basel identity. -/
theorem zetaTwoInterval_later_contained_in_target_of_budget
    (target : QInterval) {n m : Nat} {eps : Rat}
    (heps : 0 < eps) (hbudget : eps.den + 1 <= n) (hnm : n <= m)
    (htarget : target.ContainsInterval (zetaTwoInterval n)) :
    target.ContainsInterval (zetaTwoInterval m) /\
      (zetaTwoInterval m).width <= eps := by
  have htarget_stage := zetaTwoInterval_nested n m hnm
  have hmBudget : eps.den + 1 <= m := Nat.le_trans hbudget hnm
  constructor
  · unfold QInterval.ContainsInterval at htarget ⊢
    constructor
    · exact Rat.le_trans htarget.1 htarget_stage.1
    · exact Rat.le_trans htarget_stage.2.2 htarget.2
  · exact zetaTwoInterval_width_le_of_denominator_budget heps hmBudget

/-- Every later finite partial sum lies inside a supplied rational target
interval anchored at an earlier Basel-series stage.  This is the endpoint
form of the interval propagation certificate: the lower endpoint comes from
monotonicity of the partial sums, while the upper endpoint comes from the
telescoping tail enclosure and the target's upper endpoint.  The same
denominator budget records the width of the later rational interval. -/
theorem zetaTwoPartial_later_in_target_of_budget
    (target : QInterval) {n m : Nat} {eps : Rat}
    (heps : 0 < eps) (hbudget : eps.den + 1 <= n) (hnm : n <= m)
    (htarget : target.ContainsInterval (zetaTwoInterval n)) :
    target.lo <= zetaTwoPartial m /\
      zetaTwoPartial m <= target.hi /\
      (zetaTwoInterval m).width <= eps := by
  have htarget_stage := zetaTwoInterval_nested n m hnm
  have hmBudget : eps.den + 1 <= m := Nat.le_trans hbudget hnm
  have hwidth := zetaTwoInterval_width_le_of_denominator_budget heps hmBudget
  have hordered := zetaTwoInterval_ordered m
  have hpartial_hi : zetaTwoPartial m <= (zetaTwoInterval m).hi := by
    change (zetaTwoInterval m).lo <= (zetaTwoInterval m).hi
    exact hordered
  constructor
  · exact Rat.le_trans htarget.1 htarget_stage.1
  · constructor
    · exact Rat.le_trans hpartial_hi
        (Rat.le_trans htarget_stage.2.2 htarget.2)
    · exact hwidth

theorem zetaTwoWidthsShrinkToZero :
    RealCompute.WidthsShrinkToZero zetaTwoInterval := by
  intro eps
  let N : Nat := eps.val.den + 1
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  exact ⟨N, by
    intro n hn
    rw [zetaTwoInterval_width]
    unfold zetaTwoTailBound
    rw [if_neg (Nat.ne_of_gt (Nat.lt_of_lt_of_le hNpos hn))]
    have hsmallN : 1 / (N : Rat) <= eps.val := by
      dsimp [N]
      exact FTC.one_div_den_succ_le_of_pos eps.property
    exact Rat.le_trans
      (one_div_nat_le_one_div_nat_of_le (a := N) (b := n) hNpos hn)
      hsmallN⟩
theorem zetaTwoRaw_validCompute :
    RealCompute.ValidCompute zetaTwoInterval := by
  constructor
  · exact zetaTwoInterval_width_nonneg
  · constructor
    · exact zetaTwoInterval_nested
    · exact zetaTwoWidthsShrinkToZero

/-- Raw zeta(2) algorithm. -/
def zetaTwoRaw : RealCompute where
  compute := zetaTwoInterval
  rate := .power
    1 1 1 (by omega)
    (by
      intro n hn
      rw [zetaTwoInterval_width]
      unfold zetaTwoTailBound
      rw [if_neg (by omega : n ≠ 0)]
      rw [Rat.pow_one]
      exact Rat.le_refl)

/-!
## Integer-exponent zeta values

For every natural exponent `p >= 2`, the same interval trick works:

`sum_{k=1}^n 1/k^p <= zeta(p) <= sum_{k=1}^n 1/k^p + 1/n`.

The padding is intentionally coarse but very robust.  Since
`1/k^p <= 1/k^2` for `p >= 2`, the Basel telescoping estimate certifies
nesting for the whole integer-exponent family.
-/

def zetaNatTerm (p : Nat) (k : Nat) : Rat :=
  let m : Rat := ((k + 1 : Nat) : Rat)
  1 / (m ^ p)

def zetaNatPartial (p : Nat) : Nat -> Rat
  | 0 => 0
  | n + 1 => zetaNatPartial p n + zetaNatTerm p n

/-! The same finite-tail accumulator used for `zeta(2)`, now exposed for
every fixed natural exponent. -/
def zetaNatFiniteTail (p n : Nat) : Nat -> Rat
  | 0 => 0
  | count + 1 =>
      zetaNatFiniteTail p n count + zetaNatTerm p (n + count)

theorem zetaNatFiniteTail_succ (p n count : Nat) :
    zetaNatFiniteTail p n (count + 1) =
      zetaNatFiniteTail p n count + zetaNatTerm p (n + count) := by
  rfl

theorem zetaNatPartial_add_finiteTail_eq (p n count : Nat) :
    zetaNatPartial p (n + count) =
      zetaNatPartial p n + zetaNatFiniteTail p n count := by
  induction count with
  | zero => simp [zetaNatFiniteTail, Rat.add_zero]
  | succ count ih =>
      rw [show n + (count + 1) = (n + count) + 1 by omega]
      rw [show zetaNatPartial p ((n + count) + 1) =
        zetaNatPartial p (n + count) + zetaNatTerm p (n + count) by rfl]
      rw [ih, zetaNatFiniteTail_succ]
      grind [Rat.add_assoc]

def zetaNatTailBound (n : Nat) : Rat :=
  if n = 0 then 2 else 1 / (n : Rat)

def zetaNatUpper (p : Nat) (n : Nat) : Rat :=
  zetaNatPartial p n + zetaNatTailBound n

def zetaNatInterval (p : Nat) (n : Nat) : QInterval :=
  { lo := zetaNatPartial p n, hi := zetaNatUpper p n }

private theorem rat_pow_add (q : Rat) (m n : Nat) :
    q ^ (m + n) = q ^ m * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show m + (n + 1) = m + n + 1 by omega]
      rw [Rat.pow_succ, ih, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem one_le_pow_of_one_le {q : Rat}
    (hq : 1 <= q) (n : Nat) :
    1 <= q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Rat.pow_succ]
      have hq_nonneg : 0 <= q := by grind
      have hpow_nonneg : 0 <= q ^ n := Rat.pow_nonneg hq_nonneg
      have hleft : q ^ n * 1 <= q ^ n * q :=
        Rat.mul_le_mul_of_nonneg_left hq hpow_nonneg
      have hone : 1 <= q ^ n * 1 := by simpa using ih
      exact Rat.le_trans hone hleft

private theorem rat_pow_two_le_pow_of_two_le {q : Rat}
    (hq : 1 <= q) {p : Nat} (hp : 2 <= p) :
    q ^ 2 <= q ^ p := by
  have hrewrite : p = 2 + (p - 2) := by omega
  rw [hrewrite, rat_pow_add]
  have hq_nonneg : 0 <= q := by grind
  have hq2_nonneg : 0 <= q ^ 2 := Rat.pow_nonneg hq_nonneg
  have htail : 1 <= q ^ (p - 2) := one_le_pow_of_one_le hq _
  calc
    q ^ 2 = q ^ 2 * 1 := by rw [Rat.mul_one]
    _ <= q ^ 2 * q ^ (p - 2) :=
      Rat.mul_le_mul_of_nonneg_left htail hq2_nonneg

private theorem one_div_le_one_div_of_pos_of_le
    {a b : Rat} (ha : 0 < a) (hab : a <= b) :
    1 / b <= 1 / a := by
  have hb : 0 < b := by grind
  have hane : a ≠0 := Rat.ne_of_gt ha
  have hbne : b ≠0 := Rat.ne_of_gt hb
  have hprod : 0 < a * b := Rat.mul_pos ha hb
  apply Rat.le_of_mul_le_mul_right (c := a * b)
  · calc
      (1 / b) * (a * b) = a := by
        rw [Rat.div_def]
        have hcancel : b * b⁻¹= 1 := Rat.mul_inv_cancel b hbne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= b := hab
      _ = (1 / a) * (a * b) := by
        rw [Rat.div_def]
        have hcancel : a * a⁻¹= 1 := Rat.mul_inv_cancel a hane
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hprod

theorem zetaTwoTerm_antitone {n m : Nat} (hnm : n <= m) :
    zetaTwoTerm m <= zetaTwoTerm n := by
  unfold zetaTwoTerm
  let a : Rat := ((n + 1 : Nat) : Rat)
  let b : Rat := ((m + 1 : Nat) : Rat)
  have ha : 0 < a := by
    dsimp [a]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hb : 0 < b := by
    dsimp [b]
    exact (Rat.natCast_pos).2 (Nat.succ_pos m)
  have hab : a <= b := by
    dsimp [a, b]
    exact_mod_cast (Nat.add_le_add_right hnm 1)
  have hsq : a * a <= b * b := by
    calc
      a * a <= b * a :=
        Rat.mul_le_mul_of_nonneg_right hab (Rat.le_of_lt ha)
      _ <= b * b :=
        Rat.mul_le_mul_of_nonneg_left hab (Rat.le_of_lt hb)
  exact one_div_le_one_div_of_pos_of_le (Rat.mul_pos ha ha) hsq

/-- A finite rectangular certificate for a zeta(2) block.

Every term in the block beginning after `n` is no larger than the first
term, so the whole finite block is bounded by `count` copies of that first
term.  This is a reusable rational block estimate; it uses only finite
induction and order, with no limiting or completeness principle. -/
theorem zetaTwoFiniteTail_le_firstTerm_block
    (n count : Nat) :
    zetaTwoFiniteTail n count <= (count : Rat) * zetaTwoTerm n := by
  induction count with
  | zero => simp [zetaTwoFiniteTail]
  | succ count ih =>
      rw [zetaTwoFiniteTail_succ]
      have hterm := zetaTwoTerm_antitone (n := n) (m := n + count)
        (Nat.le_add_right n count)
      have hcount : (count : Rat) * zetaTwoTerm n + zetaTwoTerm n =
          ((count + 1 : Nat) : Rat) * zetaTwoTerm n := by
        rw [Rat.natCast_add]
        simp [Rat.add_mul]
      calc
        zetaTwoFiniteTail n count + zetaTwoTerm (n + count)
            <= (count : Rat) * zetaTwoTerm n + zetaTwoTerm n :=
              rat_add_le_add ih hterm
        _ = ((count + 1 : Nat) : Rat) * zetaTwoTerm n := hcount

theorem zetaNatTerm_nonneg (p k : Nat) :
    0 <= zetaNatTerm p k := by
  unfold zetaNatTerm
  let m : Rat := ((k + 1 : Nat) : Rat)
  have hmpos : 0 < m := by
    dsimp [m]
    exact (Rat.natCast_pos).2 (Nat.succ_pos k)
  exact Rat.le_of_lt (by
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 (Rat.pow_pos hmpos))

theorem zetaNatTerm_le_zetaTwoTerm
    (p k : Nat) (hp : 2 <= p) :
    zetaNatTerm p k <= zetaTwoTerm k := by
  unfold zetaNatTerm zetaTwoTerm
  let m : Rat := ((k + 1 : Nat) : Rat)
  have hmpos : 0 < m := by
    dsimp [m]
    exact (Rat.natCast_pos).2 (Nat.succ_pos k)
  have hmone : 1 <= m := by
    dsimp [m]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hpow : m ^ 2 <= m ^ p := rat_pow_two_le_pow_of_two_le hmone hp
  have hm2 : m ^ 2 = m * m := by
    rw [show (2 : Nat) = 1 + 1 by omega]
    rw [Rat.pow_succ]
    simp [Rat.pow_succ, Rat.mul_comm]
  change 1 / (m ^ p) <= 1 / (m * m)
  rw [←hm2]
  exact one_div_le_one_div_of_pos_of_le
    (Rat.pow_pos hmpos) hpow

theorem zetaNatFiniteTail_le_zetaTwoFiniteTail
    (p n count : Nat) (hp : 2 <= p) :
    zetaNatFiniteTail p n count <= zetaTwoFiniteTail n count := by
  induction count with
  | zero => simp [zetaNatFiniteTail, zetaTwoFiniteTail]
  | succ count ih =>
      rw [zetaNatFiniteTail_succ, zetaTwoFiniteTail_succ]
      exact rat_add_le_add ih
        (zetaNatTerm_le_zetaTwoTerm p (n + count) hp)

theorem zetaNatFiniteTail_le_tailBound
    (p n count : Nat) (hp : 2 <= p) (hn : 0 < n) :
    zetaNatFiniteTail p n count <= 1 / (n : Rat) := by
  exact Rat.le_trans
    (zetaNatFiniteTail_le_zetaTwoFiniteTail p n count hp)
    (zetaTwoFiniteTail_le_tailBound n hn count)

theorem zetaNatPartial_add_finiteTail_le_interval_hi
    (p n count : Nat) (hp : 2 <= p) (hn : 0 < n) :
    zetaNatPartial p (n + count) <= (zetaNatInterval p n).hi := by
  rw [zetaNatPartial_add_finiteTail_eq]
  change zetaNatPartial p n + zetaNatFiniteTail p n count <=
    zetaNatPartial p n + zetaNatTailBound n
  rw [show zetaNatTailBound n = 1 / (n : Rat) by
    simp [zetaNatTailBound, Nat.ne_of_gt hn]]
  exact (Rat.add_le_add_left).2
    (zetaNatFiniteTail_le_tailBound p n count hp hn)

theorem zetaNatPartial_le_succ (p n : Nat) :
    zetaNatPartial p n <= zetaNatPartial p (n + 1) := by
  change zetaNatPartial p n <=
    zetaNatPartial p n + zetaNatTerm p n
  grind [zetaNatTerm_nonneg p n]

theorem zetaNatPartial_le_of_le (p : Nat) {n m : Nat} :
    n <= m -> zetaNatPartial p n <= zetaNatPartial p m := by
  intro h
  induction h with
  | refl => exact Rat.le_refl
  | step _ ih =>
      exact Rat.le_trans ih (zetaNatPartial_le_succ p _)

theorem zetaNatInterval_contains_partial_add_finiteTail
    (p n count : Nat) (hp : 2 <= p) (hn : 0 < n) :
    (zetaNatInterval p n).lo <= zetaNatPartial p (n + count) /\
      zetaNatPartial p (n + count) <= (zetaNatInterval p n).hi := by
  constructor
  · change zetaNatPartial p n <= zetaNatPartial p (n + count)
    exact zetaNatPartial_le_of_le p (Nat.le_add_right n count)
  · exact zetaNatPartial_add_finiteTail_le_interval_hi p n count hp hn

theorem zetaNatUpper_succ_le
    (p n : Nat) (hp : 2 <= p) (hn : 0 < n) :
    zetaNatUpper p (n + 1) <= zetaNatUpper p n := by
  unfold zetaNatUpper zetaNatTailBound
  rw [if_neg (Nat.succ_ne_zero n)]
  rw [if_neg (Nat.ne_of_gt hn)]
  change zetaNatPartial p n + zetaNatTerm p n +
      1 / ((n + 1 : Nat) : Rat) <=
    zetaNatPartial p n + 1 / (n : Rat)
  have hstepTwo := zetaTwoTerm_le_telescopeStep n hn
  have hterm : zetaNatTerm p n <=
      1 / (n : Rat) - 1 / ((n + 1 : Nat) : Rat) :=
    Rat.le_trans (zetaNatTerm_le_zetaTwoTerm p n hp) hstepTwo
  have hwithPartial :
      zetaNatPartial p n + zetaNatTerm p n <=
        zetaNatPartial p n +
          (1 / (n : Rat) - 1 / ((n + 1 : Nat) : Rat)) :=
    rat_add_le_add (by exact Rat.le_refl) hterm
  calc
    zetaNatPartial p n + zetaNatTerm p n +
        1 / ((n + 1 : Nat) : Rat)
        <= zetaNatPartial p n +
            (1 / (n : Rat) - 1 / ((n + 1 : Nat) : Rat)) +
              1 / ((n + 1 : Nat) : Rat) :=
          rat_add_le_add hwithPartial (by exact Rat.le_refl)
    _ = zetaNatPartial p n + 1 / (n : Rat) := by
          grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem zetaNatUpper_le_of_le
    (p : Nat) (hp : 2 <= p) {n m : Nat}
    (hn : 0 < n) (h : n <= m) :
    zetaNatUpper p m <= zetaNatUpper p n := by
  induction h with
  | refl => exact Rat.le_refl
  | step h ih =>
      have hmpos : 0 < _ := Nat.lt_of_lt_of_le hn h
      exact Rat.le_trans (zetaNatUpper_succ_le p _ hp hmpos) ih

theorem zetaNatInterval_width (p : Nat) (n : Nat) :
    (zetaNatInterval p n).width = zetaNatTailBound n := by
  unfold zetaNatInterval zetaNatUpper QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem zetaNatInterval_width_nonneg (p : Nat) (n : Nat) :
    0 <= (zetaNatInterval p n).width := by
  rw [zetaNatInterval_width]
  unfold zetaNatTailBound
  by_cases hn0 : n = 0
  · simp [hn0]
    decide +kernel
  · simp [hn0]
    exact Rat.le_of_lt (by
      rw [Rat.div_def, Rat.one_mul]
      exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.pos_of_ne_zero hn0)))

theorem zetaNatInterval_ordered (p : Nat) (n : Nat) :
    (zetaNatInterval p n).lo <= (zetaNatInterval p n).hi := by
  have h := zetaNatInterval_width_nonneg p n
  unfold QInterval.width at h
  grind [Rat.sub_eq_add_neg]

theorem zetaNatInterval_nested
    (p : Nat) (hp : 2 <= p)
    (n m : Nat) (hnm : n <= m) :
    (zetaNatInterval p n).lo <= (zetaNatInterval p m).lo /\
      (zetaNatInterval p m).lo <= (zetaNatInterval p m).hi /\
      (zetaNatInterval p m).hi <= (zetaNatInterval p n).hi := by
  constructor
  · exact zetaNatPartial_le_of_le p hnm
  · constructor
    · exact zetaNatInterval_ordered p m
    · by_cases hn0 : n = 0
      · by_cases hm0 : m = 0
        · simp [hn0, hm0, zetaNatInterval, zetaNatUpper, zetaNatTailBound]
        · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          change zetaNatUpper p m <= zetaNatUpper p n
          calc
            zetaNatUpper p m <= zetaNatUpper p 1 :=
              zetaNatUpper_le_of_le p hp (by omega : 0 < (1 : Nat)) hmpos
            _ = zetaNatUpper p n := by
              rw [hn0]
              unfold zetaNatUpper zetaNatTailBound zetaNatPartial zetaNatTerm
              simp
              change (0 : Rat) + 1 / (1 : Rat) ^ p + 1 / 1 = 0 + 2
              have hpow : (1 : Rat) ^ p = 1 := by
                clear hp
                induction p with
                | zero => simp
                | succ p ih =>
                    rw [Rat.pow_succ, ih]
                    decide +kernel
              rw [hpow]
              decide +kernel
      · exact zetaNatUpper_le_of_le p hp (Nat.pos_of_ne_zero hn0) hnm

theorem zetaNatWidthsShrinkToZero (p : Nat) :
    RealCompute.WidthsShrinkToZero (zetaNatInterval p) := by
  intro eps
  let N : Nat := eps.val.den + 1
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  exact ⟨N, by
    intro n hn
    rw [zetaNatInterval_width]
    unfold zetaNatTailBound
    rw [if_neg (Nat.ne_of_gt (Nat.lt_of_lt_of_le hNpos hn))]
    have hsmallN : 1 / (N : Rat) <= eps.val := by
      dsimp [N]
      exact FTC.one_div_den_succ_le_of_pos eps.property
    exact Rat.le_trans
      (one_div_nat_le_one_div_nat_of_le (a := N) (b := n) hNpos hn)
      hsmallN⟩

theorem zetaNatInterval_width_le_one_div (p n : Nat) (hn : 0 < n) :
    (zetaNatInterval p n).width <= 1 / (n : Rat) := by
  rw [zetaNatInterval_width]
  unfold zetaNatTailBound
  simp [Nat.ne_of_gt hn]

theorem zetaNatInterval_width_le_of_denominator_budget
    (p : Nat) {n : Nat} {eps : Rat}
    (heps : 0 < eps) (hbudget : eps.den + 1 <= n) :
    (zetaNatInterval p n).width <= eps := by
  have hbase : 0 < eps.den + 1 := Nat.succ_pos eps.den
  have hn : 0 < n := Nat.lt_of_lt_of_le hbase hbudget
  calc
    (zetaNatInterval p n).width <= 1 / (n : Rat) :=
      zetaNatInterval_width_le_one_div p n hn
    _ <= 1 / (((eps.den + 1 : Nat) : Rat)) :=
      one_div_nat_le_one_div_nat_of_le hbase hbudget
    _ <= eps := FTC.one_div_den_succ_le_of_pos heps

theorem zetaNatInterval_reaches_of_positive_tolerance
    (p : Nat) (eps : QPos) :
    ∃ n : Nat, (zetaNatInterval p n).width <= eps.val := by
  refine ⟨eps.val.den + 1, ?_⟩
  exact zetaNatInterval_width_le_of_denominator_budget
    p eps.property (Nat.le_refl (eps.val.den + 1))

theorem zetaNatInterval_later_contained_in_target_of_budget
    (p : Nat) (hp : 2 <= p) (target : QInterval)
    {n m : Nat} {eps : Rat}
    (heps : 0 < eps) (hbudget : eps.den + 1 <= n) (hnm : n <= m)
    (htarget : target.ContainsInterval (zetaNatInterval p n)) :
    target.ContainsInterval (zetaNatInterval p m) /\
      (zetaNatInterval p m).width <= eps := by
  have htarget_stage := zetaNatInterval_nested p hp n m hnm
  have hmBudget : eps.den + 1 <= m := Nat.le_trans hbudget hnm
  constructor
  · unfold QInterval.ContainsInterval at htarget ⊢
    constructor
    · exact Rat.le_trans htarget.1 htarget_stage.1
    · exact Rat.le_trans htarget_stage.2.2 htarget.2
  · exact zetaNatInterval_width_le_of_denominator_budget p heps hmBudget

theorem zetaNatPartial_later_in_target_of_budget
    (p : Nat) (hp : 2 <= p) (target : QInterval)
    {n m : Nat} {eps : Rat}
    (heps : 0 < eps) (hbudget : eps.den + 1 <= n) (hnm : n <= m)
    (htarget : target.ContainsInterval (zetaNatInterval p n)) :
    target.lo <= zetaNatPartial p m /\
      zetaNatPartial p m <= target.hi /\
      (zetaNatInterval p m).width <= eps := by
  have htarget_stage := zetaNatInterval_nested p hp n m hnm
  have hmBudget : eps.den + 1 <= m := Nat.le_trans hbudget hnm
  have hwidth := zetaNatInterval_width_le_of_denominator_budget p heps hmBudget
  have hordered := zetaNatInterval_ordered p m
  have hpartial_hi : zetaNatPartial p m <= (zetaNatInterval p m).hi := by
    change (zetaNatInterval p m).lo <= (zetaNatInterval p m).hi
    exact hordered
  constructor
  · exact Rat.le_trans htarget.1 htarget_stage.1
  · constructor
    · exact Rat.le_trans hpartial_hi
        (Rat.le_trans htarget_stage.2.2 htarget.2)
    · exact hwidth

theorem zetaNatRaw_validCompute (p : Nat) (hp : 2 <= p) :
    RealCompute.ValidCompute (zetaNatInterval p) := by
  constructor
  · exact zetaNatInterval_width_nonneg p
  · constructor
    · exact zetaNatInterval_nested p hp
    · exact zetaNatWidthsShrinkToZero p

def zetaNatRaw (p : Nat) : RealCompute where
  compute := zetaNatInterval p
  rate := .power
    1 1 1 (by omega)
    (by
      intro n hn
      rw [zetaNatInterval_width]
      unfold zetaNatTailBound
      rw [if_neg (by omega : n ≠ 0)]
      rw [Rat.pow_one]
      exact Rat.le_refl)

def zetaNat (p : Nat) (hp : 2 <= p) : RealCompute.Certified :=
  RealCompute.Certified.ofRaw (zetaNatRaw p) (zetaNatRaw_validCompute p hp)


/-- Constructive data for a Dirichlet character: a conductor and a computable
complex-valued function on natural numbers.

The character laws are kept as predicates below, so we can first build and
compute with explicit characters, then prove the laws as needed. -/
structure DirichletCharacter where
  conductor : Nat
  value : Nat -> QComplex

namespace DirichletCharacter

def IsPeriodic (chi : DirichletCharacter) : Prop :=
  forall n : Nat, chi.value (n + chi.conductor) = chi.value n

def VanishesOffUnits (chi : DirichletCharacter) : Prop :=
  forall n : Nat, Nat.gcd n chi.conductor ≠ 1 -> chi.value n = QComplex.zero

def IsMultiplicative (chi : DirichletCharacter) : Prop :=
  forall m n : Nat, chi.value (m * n) = QComplex.mul (chi.value m) (chi.value n)

def IsGenuine (chi : DirichletCharacter) : Prop :=
  chi.IsPeriodic /\ chi.VanishesOffUnits /\ chi.IsMultiplicative

end DirichletCharacter

/-- One term `chi(k) / k^s`, with the conventional indexing `k >= 1`. -/
def dirichletLTerm (chi : DirichletCharacter) (s k : Nat) : QComplex :=
  QComplex.scaleRat (1 / ((k : Rat) ^ s)) (chi.value k)

/-- The finite partial sum `sum_{k=1}^n chi(k) / k^s`. -/
def dirichletLPartial (chi : DirichletCharacter) (s n : Nat) : QComplex :=
  (List.range n).foldl
    (fun acc k => QComplex.add acc (dirichletLTerm chi s (k + 1)))
    QComplex.zero

def chi4Value (n : Nat) : QComplex :=
  QComplex.ofRat
    (if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1)

/-- The primitive character of conductor 4. -/
def chi4 : DirichletCharacter where
  conductor := 4
  value := chi4Value

/-- The real-valued function behind `chi4`, useful for the alternating
one-dimensional computation. -/
def characterModFour (n : Nat) : Rat :=
  (chi4.value n).re

/-- Finite odd-denominator partial sums for `L(1, chi)`, for real-valued
characters. -/
def dirichletLOddPartialAtOne (chi : Nat -> Rat) (n : Nat) : Rat :=
  (List.range n).foldl
    (fun acc k => acc + chi (2 * k + 1) / ((2 * k + 1 : Nat) : Rat)) 0

def dirichletLChi4OddPartialAtOne (n : Nat) : Rat :=
  dirichletLOddPartialAtOne characterModFour n

/-- The Dirichlet L-value `L(1, chi4)` as a raw real. -/
def dirichletLChi4AtOne : RealCompute where
  compute := fun n =>
    let state : Prod Rat Rat := (List.range n).foldl
      (fun state (i : Nat) =>
        let term1 : Rat := 1 / (4 * i + 3)
        let term2 : Rat := 1 / (4 * i + 5)
        let lo := state.1 - term1
        let hi := lo + term2
        (hi, lo))
      (1, 0)
    { lo := state.2, hi := state.1 }

/-- Conventional alias: the Dirichlet beta function is `L(s, chi4)`. -/
def dirichletBetaAtOne : RealCompute :=
  dirichletLChi4AtOne

end DirichletSeries

end ComputableAnalysis


