-- Prove2me | Definitions.Def_MegiddoLP_ZeroVariable
-- name    : MegiddoLP_ZeroVariable
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T21:10:57.213222+00:00
-- url     : https://prove2.me/theorems/5d78f275-2ce7-4fc7-86a3-905740decf49
-- title:
--   A real-RAM feasibility decider for zero-dimensional linear programming
-- statement:
--   In zero dimensions, feasibility is equivalent to every right-hand side being nonpositive. A real pointer machine scans the standard input and decides in at most eight times the number of rows plus eight steps.
-- source:
--   Nimrod Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, JACM 31(1), 1984, §5, p. 126, zero-dimensional base case. https://theory.stanford.edu/~megiddo/pdf/lplin.pdf

import Definitions.Def_MegiddoLP_MachineDSL
import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace MegiddoLP.FixedDim

open Matrix LinearOptimization SmaleNinth MachineDSL

/-- The exact real-RAM feasibility specification at a fixed dimension. -/
def HasLinearFeasibilityProgram (d : ℕ) : Prop :=
  ∃ (R : RAMProgram) (C : ℕ),
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ),
      ∃ result : Bool,
        RAMDecidesInTime R (encodeLP A b) (C * (n + 1)) result ∧
        (result = true ↔ (polyhedron A b).Nonempty)

private def scanBody : Stmt :=
  .seq (.prim (.load 2 0)) <|
    .seq (.ifLeZero 2 .skip (.prim (.const 3 1))) <|
    .seq (.prim (.pinc 0)) (.prim (.sub 0 0 1))

private theorem scanBody_runs (s : MState) :
    ∃ t, Runs scanBody s t 6 ∧
      t.mem = s.mem ∧ t.ptrs 0 = s.ptrs 0 + 1 ∧
      t.regs 0 = s.regs 0 - s.regs 1 ∧ t.regs 1 = s.regs 1 ∧
      (t.regs 3 ≤ 0 ↔ s.regs 3 ≤ 0 ∧ s.mem (s.ptrs 0) ≤ 0) := by
  let u := (Prim.load 2 0).step s
  have hload : Runs (.prim (.load 2 0)) s u 1 := Runs.prim _ _
  suffices ∃ v, Runs (.ifLeZero 2 .skip (.prim (.const 3 1))) u v 3 ∧
      v.mem = s.mem ∧ v.ptrs = s.ptrs ∧ v.regs 0 = s.regs 0 ∧ v.regs 1 = s.regs 1 ∧
      (v.regs 3 ≤ 0 ↔ s.regs 3 ≤ 0 ∧ s.mem (s.ptrs 0) ≤ 0) by
    obtain ⟨v, hcmp, hmem, hptr, hzero, hone, hflag⟩ := this
    refine ⟨_, hload.seq (hcmp.seq ((Runs.prim (.pinc 0) v).seq
      (Runs.prim (.sub 0 0 1) _))), ?_⟩
    simp [Prim.step, hmem, hptr, hzero, hone, hflag]
  by_cases h : s.mem (s.ptrs 0) ≤ 0
  · refine ⟨u, (Runs.ifLeZero_true (e := .prim (.const 3 1))
      (s₁ := u) (by simpa [u, Prim.step] using h) (Runs.skip u)).mono (by decide), ?_⟩
    simp [u, Prim.step, h]
  · refine ⟨(Prim.const 3 1).step u,
      Runs.ifLeZero_false (t := .skip) (by simpa [u, Prim.step] using h)
        (Runs.prim (.const 3 1) u), ?_⟩
    simp [u, Prim.step, h]

private theorem scanLoop_runs (n : ℕ) (s : MState)
    (hcount : s.regs 0 = (n : ℝ)) (hone : s.regs 1 = 1) :
    ∃ t, Runs (.whilePos 0 scanBody) s t (8 * n + 1) ∧
      (t.regs 3 ≤ 0 ↔ s.regs 3 ≤ 0 ∧ ∀ j : ℕ, j < n → s.mem (s.ptrs 0 + j) ≤ 0) := by
  induction n generalizing s with
  | zero =>
    refine ⟨s, Runs.whilePos_exit (by simp [hcount]), ?_⟩
    simp
  | succ n ih =>
    obtain ⟨u, hbody, hmem, hptr, hzero, hone', hflag⟩ := scanBody_runs s
    have hu : u.regs 0 = (n : ℝ) := by rw [hzero, hcount, hone]; push_cast; ring
    obtain ⟨t, hrest, ht⟩ := ih u hu (hone'.trans hone)
    have hpos : 0 < s.regs 0 := by rw [hcount]; positivity
    refine ⟨t, (Runs.whilePos_step hpos hbody hrest).mono (by omega), ?_⟩
    rw [ht, hflag, hmem, hptr, and_assoc]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨hfirst, htail⟩ j hj
      cases j with
      | zero => simpa using hfirst
      | succ j =>
        simpa [Nat.cast_succ, add_assoc, add_comm 1 (j : ℤ)] using htail j (by omega)
    · intro hall
      refine ⟨by simpa using hall 0 (by omega), fun j hj => ?_⟩
      simpa [Nat.cast_succ, add_assoc, add_comm 1 (j : ℤ)] using hall (j + 1) (by omega)

private def scanInit : Stmt :=
  .seq (.prim (.load 0 0)) (.seq (.prim (.const 1 1)) (.prim (.pset 0 2)))

private theorem scanInit_runs (x : ℤ → ℝ) :
    ∃ s, Runs scanInit ⟨fun _ => 0, fun _ => 0, x⟩ s 3 ∧
      s.regs 0 = x 0 ∧ s.regs 1 = 1 ∧ s.regs 3 = 0 ∧ s.ptrs 0 = 2 ∧ s.mem = x := by
  refine ⟨_, (Runs.prim (.load 0 0) _).seq ((Runs.prim (.const 1 1) _).seq
    (Runs.prim (.pset 0 2) _)), ?_⟩
  simp [Prim.step]

private theorem encodeLP_zeroDim_rhs {n : ℕ} (A : Matrix (Fin n) (Fin 0) ℝ)
    (b : Fin n → ℝ) (j : Fin n) : encodeLP A b (2 + (j.val : ℤ)) = b j := by
  unfold encodeLP
  simp only [Nat.cast_zero, mul_zero, add_zero]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_pos (by omega)]
  congr 1
  apply Fin.ext
  change (2 + (j.val : ℤ) - 2).toNat = j.val
  omega

/-- Zero-dimensional LP is a scan of the right-hand sides. -/
theorem lp_feasibility_linear_time_zero : HasLinearFeasibilityProgram 0 := by
  refine ⟨buildDecider (.seq scanInit (.whilePos 0 scanBody)) 3, 8, fun n A b => ?_⟩
  let x := encodeLP A b
  obtain ⟨s, hinit, h0, h1, h3, hptr, hmem⟩ := scanInit_runs x
  have hcount : s.regs 0 = (n : ℝ) := by simp [h0, x, encodeLP]
  obtain ⟨t, hloop, ht⟩ := scanLoop_runs n s hcount h1
  refine ⟨decide (t.regs 3 ≤ 0), ?_, ?_⟩
  · obtain ⟨k, hk, hr⟩ := buildDecider_decides (rAns := 3) (hinit.seq hloop)
    exact ⟨k, hk.trans (by omega), hr⟩
  · simp only [decide_eq_true_eq, ht, h3, le_refl, true_and, hptr, hmem]
    have hread : (∀ j : ℕ, j < n → x (2 + j) ≤ 0) ↔ ∀ j : Fin n, b j ≤ 0 := by
      constructor
      · intro h j
        simpa only [x, encodeLP_zeroDim_rhs A b j] using h j.val j.isLt
      · intro h j hj
        simpa only [x, encodeLP_zeroDim_rhs A b ⟨j, hj⟩] using h ⟨j, hj⟩
    rw [hread]
    have hmul (y : Fin 0 → ℝ) (i : Fin n) : (A *ᵥ y) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, Finset.sum_of_isEmpty]
    constructor
    · intro hall
      refine ⟨0, fun i => ?_⟩
      rw [hmul]
      exact hall i
    · rintro ⟨y, hy⟩ i
      simpa only [hmul y i] using hy i

end MegiddoLP.FixedDim


