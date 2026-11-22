-- Prove2me | Definitions.Def_MegiddoLP_CoefficientScan
-- name    : MegiddoLP_CoefficientScan
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T21:11:14.450806+00:00
-- url     : https://prove2.me/theorems/1012c232-3f3c-4fbd-bce0-db7648d7d832
-- title:
--   A real-RAM scan for linear program coefficient bounds
-- statement:
--   A single pass over the coefficient matrix computes a positive lower bound on nonzero coefficient magnitudes. Its reciprocal bounds all magnitudes from above.
-- source:
--   Nimrod Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, JACM 31(1), 1984, §3.2, p. 119, implementation for the change of coordinates. https://theory.stanford.edu/~megiddo/pdf/lplin.pdf

import Definitions.Def_MegiddoLP_MachineDSL
import Definitions.Def_SmaleNinth_BSSMachine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace MegiddoLP.FixedDim

open Matrix SmaleNinth MachineDSL

/-! A real-RAM scan for the bounds used in the Vandermonde change of coordinates.
For each nonzero coefficient `a` it multiplies an accumulator by
`a² / (1 + a²)²`. This factor is positive and at most each of
`1`, `|a|`, and `1 / |a|`. Exact real arithmetic keeps the product positive. -/

private noncomputable def coefficientFactor (a : ℝ) : ℝ :=
  if a = 0 then 1 else a ^ 2 / (1 + a ^ 2) ^ 2

private theorem coefficientFactor_spec (a : ℝ) :
    0 < coefficientFactor a ∧ coefficientFactor a ≤ 1 ∧
      (a ≠ 0 → coefficientFactor a ≤ |a|) ∧ |a| * coefficientFactor a ≤ 1 := by
  by_cases ha : a = 0
  · simp [coefficientFactor, ha]
  have h := abs_nonneg a
  have hs : |a| ^ 2 = a ^ 2 := sq_abs a
  have hpos : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have hbase : 0 < 1 + a ^ 2 := by positivity
  have habs : |a| ≤ 1 + a ^ 2 := by nlinarith [sq_nonneg (|a| - 1)]
  simp only [coefficientFactor, if_neg ha]
  refine ⟨div_pos hpos (sq_pos_of_pos hbase), ?_, fun _ => ?_, ?_⟩
  · apply (div_le_iff₀ (sq_pos_of_pos hbase)).2
    nlinarith [sq_nonneg (a ^ 2)]
  · apply (div_le_iff₀ (sq_pos_of_pos hbase)).2
    rw [← hs] at habs ⊢
    calc
      |a| ^ 2 ≤ |a| * (1 + |a| ^ 2) := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_left habs h
      _ ≤ |a| * (1 + |a| ^ 2) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ h
        nlinarith [sq_nonneg (|a| ^ 2)]
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hbase)).2
    calc
      |a| * a ^ 2 ≤ (1 + a ^ 2) * a ^ 2 := mul_le_mul_of_nonneg_right habs hpos.le
      _ ≤ 1 * (1 + a ^ 2) ^ 2 := by
        rw [one_mul, pow_two (1 + a ^ 2)]
        exact mul_le_mul_of_nonneg_left (by linarith) hbase.le

private def multiplyFactor : Stmt :=
  .seq (.prim (.add 5 4 1)) <|
    .seq (.prim (.mul 5 5 5)) <|
    .seq (.prim (.div 4 4 5)) (.prim (.mul 2 2 4))

private def coeffBody : Stmt :=
  .seq (.prim (.load 3 0)) <|
    .seq (.prim (.mul 4 3 3)) <|
    .seq (.ifLeZero 4 .skip multiplyFactor) <|
    .seq (.prim (.pinc 0)) (.prim (.sub 0 0 1))

private theorem coeffBody_runs (s : MState) (hone : s.regs 1 = 1) :
    ∃ t, Runs coeffBody s t 10 ∧
      t.mem = s.mem ∧ t.ptrs 0 = s.ptrs 0 + 1 ∧
      t.regs 0 = s.regs 0 - 1 ∧ t.regs 1 = 1 ∧
      t.regs 2 = s.regs 2 * coefficientFactor (s.mem (s.ptrs 0)) := by
  let a := s.mem (s.ptrs 0)
  let u := (Prim.mul 4 3 3).step ((Prim.load 3 0).step s)
  have hsq : u.regs 4 = a ^ 2 := by simp [u, a, Prim.step, pow_two]
  suffices ∃ v, Runs (.ifLeZero 4 .skip multiplyFactor) u v 6 ∧
      v.mem = s.mem ∧ v.ptrs = s.ptrs ∧ v.regs 0 = s.regs 0 ∧ v.regs 1 = 1 ∧
      v.regs 2 = s.regs 2 * coefficientFactor a by
    obtain ⟨v, hrun, hm, hp, hzero, h1, h2⟩ := this
    have hinc := (Runs.prim (.pinc 0) v).seq (Runs.prim (.sub 0 0 1) _)
    refine ⟨_, (Runs.prim (.load 3 0) s).seq
      ((Runs.prim (.mul 4 3 3) _).seq (hrun.seq hinc)), ?_⟩
    simp [Prim.step, hm, hp, hzero, h1, h2, a]
  by_cases ha : a = 0
  · refine ⟨u, (Runs.ifLeZero_true (e := multiplyFactor)
      (by simp [hsq, ha]) (Runs.skip u)).mono (by decide), ?_⟩
    simp [u, Prim.step, hone, coefficientFactor, ha]
  · have hpos : ¬ u.regs 4 ≤ 0 := by rw [hsq]; exact not_le.mpr (sq_pos_of_ne_zero ha)
    have hrun : Runs multiplyFactor u _ 4 :=
      (Runs.prim (.add 5 4 1) u).seq ((Runs.prim (.mul 5 5 5) _).seq
        ((Runs.prim (.div 4 4 5) _).seq (Runs.prim (.mul 2 2 4) _)))
    refine ⟨_, Runs.ifLeZero_false (t := .skip) hpos hrun, ?_⟩
    simp [u, a, Prim.step, hone, coefficientFactor, ha, pow_two, add_comm]

/-- The scan works on any contiguous coefficient block, in linear RAM time.
Register 0 holds the number of cells, register 1 holds one, and the accumulator
in register 2 starts in `(0, 1]`. Pointer 0 holds the start address. -/
theorem coefficient_scan_runs (n : ℕ) (s : MState)
    (hcount : s.regs 0 = (n : ℝ)) (hone : s.regs 1 = 1)
    (hacc : 0 < s.regs 2) (hacc₁ : s.regs 2 ≤ 1) :
    ∃ t, Runs (.whilePos 0 coeffBody) s t (12 * n + 1) ∧
      t.mem = s.mem ∧ 0 < t.regs 2 ∧ t.regs 2 ≤ s.regs 2 ∧
      ∀ j : ℕ, j < n → let a := s.mem (s.ptrs 0 + j)
        (a ≠ 0 → t.regs 2 ≤ |a|) ∧ |a| * t.regs 2 ≤ 1 := by
  induction n generalizing s with
  | zero => exact ⟨s, Runs.whilePos_exit (by simp [hcount]), rfl, hacc, le_rfl, by simp⟩
  | succ n ih =>
    obtain ⟨u, hbody, hmem, hptr, hzero, h1, h2⟩ := coeffBody_runs s hone
    obtain ⟨hfactor, hfactor₁, hlower, hupper⟩ := coefficientFactor_spec (s.mem (s.ptrs 0))
    have hu : u.regs 0 = (n : ℝ) := by simp [hzero, hcount]
    have hu₂ : 0 < u.regs 2 := by rw [h2]; exact mul_pos hacc hfactor
    have hu_le : u.regs 2 ≤ s.regs 2 := by
      rw [h2]
      exact mul_le_of_le_one_right hacc.le hfactor₁
    have hu_factor : u.regs 2 ≤ coefficientFactor (s.mem (s.ptrs 0)) := by
      rw [h2]
      exact mul_le_of_le_one_left hfactor.le hacc₁
    obtain ⟨t, hrest, hm, ht, htu, hbounds⟩ := ih u hu h1 hu₂ (hu_le.trans hacc₁)
    have hpos : 0 < s.regs 0 := by rw [hcount]; positivity
    refine ⟨t, (Runs.whilePos_step hpos hbody hrest).mono (by omega),
      hm.trans hmem, ht, htu.trans hu_le, ?_⟩
    intro j hj
    cases j with
    | zero =>
      simp only [Nat.cast_zero, add_zero]
      exact ⟨fun hn => htu.trans (hu_factor.trans (hlower hn)),
        (mul_le_mul_of_nonneg_left (htu.trans hu_factor) (abs_nonneg _)).trans hupper⟩
    | succ j =>
      simpa [hmem, hptr, Nat.cast_succ, add_assoc, add_comm 1 (j : ℤ)] using hbounds j (by omega)

/-- Read the row count, set the accumulator to one, and start at the
first coefficient of the standard LP encoding. -/
private def coeffInit (d : ℕ) : Stmt :=
  .seq (.prim (.load 0 0)) <|
    .seq (.prim (.const 1 1)) <|
    .seq (.prim (.const 2 1)) <|
    .seq (.prim (.const 3 (d : ℝ))) <|
    .seq (.prim (.mul 0 0 3)) (.prim (.pset 0 2))

/-- Compute positive lower and upper magnitude bounds for the input matrix.
The result is `lo = regs 2` and `hi = 1 / lo`. The input stays available. -/
noncomputable def scanCoefficients (d : ℕ) : Stmt :=
  .seq (coeffInit d) (.whilePos 0 coeffBody)

theorem scanCoefficients_runs {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) :
    ∃ t, Runs (scanCoefficients d) ⟨fun _ => 0, fun _ => 0, encodeLP A b⟩ t
        ((12 * d + 7) * (n + 1)) ∧
      t.mem = encodeLP A b ∧ 0 < t.regs 2 ∧ t.regs 2 ≤ 1 ∧
      ∀ i j, (A i j ≠ 0 → t.regs 2 ≤ |A i j|) ∧ |A i j| ≤ 1 / t.regs 2 := by
  let x := encodeLP A b
  let s₀ : MState := ⟨fun _ => 0, fun _ => 0, x⟩
  let s := (Prim.pset 0 2).step ((Prim.mul 0 0 3).step ((Prim.const 3 (d : ℝ)).step
    ((Prim.const 2 1).step ((Prim.const 1 1).step ((Prim.load 0 0).step s₀)))))
  have hinit : Runs (coeffInit d) s₀ s 6 :=
    (Runs.prim (.load 0 0) _).seq ((Runs.prim (.const 1 1) _).seq
      ((Runs.prim (.const 2 1) _).seq ((Runs.prim (.const 3 (d : ℝ)) _).seq
        ((Runs.prim (.mul 0 0 3) _).seq (Runs.prim (.pset 0 2) _)))))
  obtain ⟨t, hrun, hmem, hpos, hle, hb⟩ := coefficient_scan_runs (n * d) s
    (by simp [s, s₀, Prim.step, x, encodeLP]) (by simp [s, Prim.step])
    (by simp [s, Prim.step]) (by simp [s, Prim.step])
  have htime : 6 + (12 * (n * d) + 1) ≤ (12 * d + 7) * (n + 1) := by
    have h : 0 ≤ 12 * d + 7 * n := Nat.zero_le _
    nlinarith
  refine ⟨t, (hinit.seq hrun).mono htime, hmem, hpos, by simpa [s, Prim.step] using hle, ?_⟩
  intro i j
  have hidx : i.val * d + j.val < n * d := by
    calc
      i.val * d + j.val < i.val * d + d := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ n * d := Nat.mul_le_mul_right _ i.isLt
  have hread : x (2 + ((i.val * d + j.val : ℕ) : ℤ)) = A i j := by
    have hd : 0 < d := j.pos
    have hj := j.isLt
    unfold x encodeLP
    rw [if_neg (by omega), if_neg (by omega), if_pos (by exact_mod_cast
      (show 2 ≤ 2 + (i.val * d + j.val) ∧
        2 + (i.val * d + j.val) < 2 + n * d by omega))]
    have he : (2 + ((i.val * d + j.val : ℕ) : ℤ) - 2).toNat = i.val * d + j.val := by omega
    rw [he]
    unfold matrixEntryRM
    rw [dif_pos ⟨hidx, hd⟩]
    congr 1
    · apply Fin.ext
      change (i.val * d + j.val) / d = i.val
      rw [Nat.mul_comm i.val, Nat.mul_add_div hd, Nat.div_eq_of_lt hj, Nat.add_zero]
    · apply Fin.ext
      change (i.val * d + j.val) % d = j.val
      rw [Nat.mul_comm i.val, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  have h := hb (i.val * d + j.val) hidx
  simp only [s, s₀, Prim.step, Function.update_self] at h
  rw [hread] at h
  exact ⟨h.1, (le_div_iff₀ hpos).2 h.2⟩

end MegiddoLP.FixedDim


