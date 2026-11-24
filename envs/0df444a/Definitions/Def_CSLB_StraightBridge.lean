-- Prove2me | Definitions.Def_CSLB_StraightBridge
-- name    : CSLB_StraightBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:58:37.863893+00:00
-- url     : https://prove2.me/theorems/d26b0e5d-a7cb-4ec6-be5a-0819a68f0592
-- title:
--   Coded sorting bridge: StraightBridge
-- statement:
--   # Straight-line two-buffer programs on the external-memory machine
--
--   A list of `TwoWordBlockLift` commands (two block buffers `left`, `right`; reads and writes of
--   whole blocks; free computation on the buffers) is run by the machine of
--   `Def_CodedSorting_Machine`: memory words `[0, B)` hold `left`, words `[B, 2B)` hold `right`,
--   and command number `t` is executed at step `t`. Every read or write of the list is one block
--   transfer of the machine, and the machine halts after the last command.
--
--   Part of the bridge from the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 to the platform model `CodedSorting_Machine` of the external-memory machine, used to prove Theorem 3.1.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, Theorem 3.1 (p.4) and Appendix D (p.39)

import Definitions.Def_CodedSorting_Machine
import Definitions.Def_CSL_Sorting_SmallMemory_SmallSort

/-! # Straight-line two-buffer programs on the external-memory machine

A list of `TwoWordBlockLift` commands (two block buffers `left`, `right`; reads and writes of
whole blocks; free computation on the buffers) is run by the machine of
`Def_CodedSorting_Machine`: memory words `[0, B)` hold `left`, words `[B, 2B)` hold `right`,
and command number `t` is executed at step `t`. Every read or write of the list is one block
transfer of the machine, and the machine halts after the last command. -/

set_option autoImplicit false

namespace CSLB.StraightBridge
open CodedSorting CSL

variable {M B w : ℕ}

def leftOf (hBM : 2 * B ≤ M) (m : Mem M w) : Fin B → Word w := fun i => m ⟨i.val, by omega⟩
def rightOf (hBM : 2 * B ≤ M) (m : Mem M w) : Fin B → Word w :=
  fun i => m ⟨B + i.val, by omega⟩

def setLR (hBM : 2 * B ≤ M) (m : Mem M w) (l r : Fin B → Word w) : Mem M w := fun i =>
  if h : i.val < B then l ⟨i.val, h⟩
  else if h2 : i.val < 2 * B then r ⟨i.val - B, by omega⟩ else m i

/-- The block view of the word disk. -/
def blocks (B : ℕ) (D : Disk w) : ℕ → Fin B → Word w := fun a i => D (a * B + i.val)

def offL (hBM : 2 * B ≤ M) : Fin (M - B + 1) := ⟨0, by omega⟩
def offR (hBM : 2 * B ≤ M) : Fin (M - B + 1) := ⟨B, by omega⟩

def cmdStep (hBM : 2 * B ≤ M) (cmd : TwoWordBlockLift.Command B (Word w)) (m : Mem M w) :
    Mem M w × IOAct M B :=
  match cmd with
  | .readLeft a => (m, .read a (offL hBM))
  | .readRight f => (m, .read (f (leftOf hBM m, rightOf hBM m)) (offR hBM))
  | .writeLeft a => (m, .write (offL hBM) a)
  | .writeRight f => (m, .write (offR hBM) (f (leftOf hBM m, rightOf hBM m)))
  | .cpu f => (setLR hBM m (f (leftOf hBM m, rightOf hBM m)).1 (f (leftOf hBM m, rightOf hBM m)).2,
      .none)

/-- The machine program executing `code`, one command per step. -/
def program (hBM : 2 * B ≤ M) (code : List (TwoWordBlockLift.Command B (Word w))) :
    Program M B w where
  step t m := if h : t < code.length then cmdStep hBM code[t] m else (m, .halt)

/-- The two-buffer state seen in a machine configuration. -/
def view (hBM : 2 * B ≤ M) (c : Config M w) : TwoWordBlockLift.State B (Word w) :=
  ⟨leftOf hBM c.mem, rightOf hBM c.mem, blocks B c.disk⟩

theorem blocks_ext {D E : Disk w} (h : ∀ a (i : Fin B), D (a * B + i.val) = E (a * B + i.val)) :
    blocks B D = blocks B E := by
  funext a i; exact h a i

theorem view_eq {s t : TwoWordBlockLift.State B (Word w)} (h1 : s.left = t.left)
    (h2 : s.right = t.right) (h3 : s.disk = t.disk) : s = t := by
  cases s; cases t; simp_all

theorem leftOf_setLR (hBM : 2 * B ≤ M) (m : Mem M w) (l r : Fin B → Word w) :
    leftOf hBM (setLR hBM m l r) = l := by
  funext i; simp [leftOf, setLR, i.isLt]

theorem rightOf_setLR (hBM : 2 * B ≤ M) (m : Mem M w) (l r : Fin B → Word w) :
    rightOf hBM (setLR hBM m l r) = r := by
  funext i
  simp only [rightOf, setLR]
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 1; apply Fin.ext; simp

/-- Reading block `a` at offset `0`. -/
theorem read_left (hBM : 2 * B ≤ M) (m : Mem M w) (D : Disk w) (a : ℕ) :
    leftOf hBM (fun i : Fin M => if (offL hBM : ℕ) ≤ i ∧ (i : ℕ) < (offL hBM : ℕ) + B then
      D (a * B + (i - (offL hBM : ℕ))) else m i) = blocks B D a ∧
    rightOf hBM (fun i : Fin M => if (offL hBM : ℕ) ≤ i ∧ (i : ℕ) < (offL hBM : ℕ) + B then
      D (a * B + (i - (offL hBM : ℕ))) else m i) = rightOf hBM m := by
  constructor
  · funext i; simp [leftOf, offL, blocks, i.isLt]
  · funext i; simp [rightOf, offL]

theorem read_right (hBM : 2 * B ≤ M) (m : Mem M w) (D : Disk w) (a : ℕ) :
    leftOf hBM (fun i : Fin M => if (offR hBM : ℕ) ≤ i ∧ (i : ℕ) < (offR hBM : ℕ) + B then
      D (a * B + (i - (offR hBM : ℕ))) else m i) = leftOf hBM m ∧
    rightOf hBM (fun i : Fin M => if (offR hBM : ℕ) ≤ i ∧ (i : ℕ) < (offR hBM : ℕ) + B then
      D (a * B + (i - (offR hBM : ℕ))) else m i) = blocks B D a := by
  constructor
  · funext i; simp [leftOf, offR, i.isLt]
  · funext i; simp [rightOf, offR, blocks, i.isLt]

theorem write_blocks (hB : 0 < B) (hBM : 2 * B ≤ M) (m : Mem M w) (D : Disk w) (a : ℕ)
    (off : Fin (M - B + 1)) (hoff : (off : ℕ) + B ≤ M) :
    blocks B (fun d => if a * B ≤ d ∧ d < a * B + B then
        (if h : (off : ℕ) + (d - a * B) < M then m ⟨off + (d - a * B), h⟩ else 0) else D d) =
      Function.update (blocks B D) a (fun i : Fin B => m ⟨off + i.val, by omega⟩) := by
  funext b i
  simp only [blocks]
  by_cases hb : b = a
  · subst hb
    rw [Function.update_self, if_pos ⟨by omega, by have := i.isLt; omega⟩,
      dif_pos (by have := i.isLt; omega)]
    congr 2; omega
  · rw [Function.update_of_ne hb, if_neg]
    · rfl
    rintro ⟨h1, h2⟩
    have hi := i.isLt
    rcases Nat.lt_or_gt_of_ne hb with hlt | hgt
    · have : (b + 1) * B ≤ a * B := Nat.mul_le_mul_right B hlt
      rw [Nat.add_mul, one_mul] at this; omega
    · have : (a + 1) * B ≤ b * B := Nat.mul_le_mul_right B hgt
      rw [Nat.add_mul, one_mul] at this
      have : b * B ≤ b * B + i.val := Nat.le_add_right _ _
      omega


theorem offL_val (hBM : 2 * B ≤ M) : ((offL hBM : Fin (M - B + 1)) : ℕ) = 0 := rfl
theorem offR_val (hBM : 2 * B ≤ M) : ((offR hBM : Fin (M - B + 1)) : ℕ) = B := rfl

/-- One machine step executes command `t` of the list. -/
theorem sim_step (hB : 0 < B) (hBM : 2 * B ≤ M) (code : List (TwoWordBlockLift.Command B (Word w)))
    (L : ℕ) (hL : TwoWordBlockFootprint.BoundedCode L code)
    (c : Config M w) (t : ℕ) (ht : t < code.length) (hct : c.t = t) (hh : c.halted = false) :
    (Config.step (program hBM code) c).t = t + 1 ∧
    (Config.step (program hBM code) c).halted = false ∧
    view hBM (Config.step (program hBM code) c) = TwoWordBlockLift.step code[t] (view hBM c) ∧
    (Config.step (program hBM code) c).ios = c.ios + TwoWordBlockLift.cost code[t] ∧
    (Config.step (program hBM code) c).maxEnd ≤ max c.maxEnd (L * B) := by
  have hb : TwoWordBlockFootprint.BoundedCommand L code[t] := hL _ (List.getElem_mem ht)
  have hps : (program hBM code).step t c.mem = cmdStep hBM code[t] c.mem := by
    simp only [program, dif_pos ht]
  generalize code[t] = cmd at hb hps ⊢
  have hblk : ∀ a, a < L → a * B + B ≤ L * B := by
    intro a ha
    have := Nat.mul_le_mul_right B (show a + 1 ≤ L by omega)
    rw [Nat.add_mul, one_mul] at this; exact this
  cases cmd with
  | readLeft a =>
    simp only [cmdStep] at hps
    simp only [Config.step, hh, Bool.false_eq_true, if_false, hps, hct]
    refine ⟨(by first | trivial | rfl | simp [TwoWordBlockLift.cost]), (by first | trivial | rfl | simp [TwoWordBlockLift.cost]), ?_, (by first | trivial | rfl | simp [TwoWordBlockLift.cost]), ?_⟩
    · obtain ⟨h1, h2⟩ := read_left hBM c.mem c.disk a
      exact view_eq h1 h2 rfl
    · simp only [TwoWordBlockFootprint.BoundedCommand] at hb
      exact max_le_max le_rfl (hblk a hb)
  | readRight f =>
    simp only [cmdStep] at hps
    simp only [Config.step, hh, Bool.false_eq_true, if_false, hps, hct]
    refine ⟨(by first | trivial | rfl | simp [TwoWordBlockLift.cost]), (by first | trivial | rfl | simp [TwoWordBlockLift.cost]), ?_, (by first | trivial | rfl | simp [TwoWordBlockLift.cost]), ?_⟩
    · obtain ⟨h1, h2⟩ := read_right hBM c.mem c.disk (f (leftOf hBM c.mem, rightOf hBM c.mem))
      exact view_eq h1 h2 rfl
    · simp only [TwoWordBlockFootprint.BoundedCommand] at hb
      exact max_le_max le_rfl (hblk _ (hb _))
  | writeLeft a =>
    simp only [cmdStep] at hps
    simp only [Config.step, hh, Bool.false_eq_true, if_false, hps, hct]
    refine ⟨(by first | trivial | rfl | simp [TwoWordBlockLift.cost]), (by first | trivial | rfl | simp [TwoWordBlockLift.cost]), ?_, (by first | trivial | rfl | simp [TwoWordBlockLift.cost]), ?_⟩
    · refine view_eq rfl rfl ?_
      simp only [view, TwoWordBlockLift.step]
      rw [write_blocks hB hBM c.mem c.disk a (offL hBM) (by rw [offL_val]; omega)]
      congr 1
      funext i
      simp [leftOf, offL]
    · simp only [TwoWordBlockFootprint.BoundedCommand] at hb
      exact max_le_max le_rfl (hblk a hb)
  | writeRight f =>
    simp only [cmdStep] at hps
    simp only [Config.step, hh, Bool.false_eq_true, if_false, hps, hct]
    refine ⟨(by first | trivial | rfl | simp [TwoWordBlockLift.cost]), (by first | trivial | rfl | simp [TwoWordBlockLift.cost]), ?_, (by first | trivial | rfl | simp [TwoWordBlockLift.cost]), ?_⟩
    · refine view_eq rfl rfl ?_
      simp only [view, TwoWordBlockLift.step]
      rw [write_blocks hB hBM c.mem c.disk _ (offR hBM) (by rw [offR_val]; omega)]
      rfl
    · simp only [TwoWordBlockFootprint.BoundedCommand] at hb
      exact max_le_max le_rfl (hblk _ (hb _))
  | cpu f =>
    simp only [cmdStep] at hps
    simp only [Config.step, hh, Bool.false_eq_true, if_false, hps, hct]
    refine ⟨(by first | trivial | rfl | simp [TwoWordBlockLift.cost]), (by first | trivial | rfl | simp [TwoWordBlockLift.cost]), ?_, (by first | trivial | rfl | simp [TwoWordBlockLift.cost]), le_max_left _ _⟩
    exact view_eq (leftOf_setLR hBM _ _ _) (rightOf_setLR hBM _ _ _) rfl

/-- Running the whole list. -/
theorem sim_run (hB : 0 < B) (hBM : 2 * B ≤ M) (code : List (TwoWordBlockLift.Command B (Word w)))
    (L : ℕ) (hL : TwoWordBlockFootprint.BoundedCode L code) (c : Config M w)
    (h0 : c.t = 0) (hh : c.halted = false) (n : ℕ) (hn : n ≤ code.length) :
    (run (program hBM code) n c).t = n ∧ (run (program hBM code) n c).halted = false ∧
    view hBM (run (program hBM code) n c) = TwoWordBlockLift.execute (code.take n) (view hBM c) ∧
    (run (program hBM code) n c).ios = c.ios + TwoWordBlockLift.transfers (code.take n) ∧
    (run (program hBM code) n c).maxEnd ≤ max c.maxEnd (L * B) := by
  induction n with
  | zero => exact ⟨h0, hh, rfl, by simp [TwoWordBlockLift.transfers, run], le_max_left _ _⟩
  | succ n ih =>
    obtain ⟨ht, hhn, hv, hio, hme⟩ := ih (by omega)
    have hrun : run (program hBM code) (n + 1) c =
        Config.step (program hBM code) (run (program hBM code) n c) := by
      simp only [run, Function.iterate_succ_apply']
    rw [hrun]
    obtain ⟨t1, h1, v1, io1, me1⟩ := sim_step hB hBM code L hL _ n (by omega) ht hhn
    have htake : code.take (n + 1) = code.take n ++ [code[n]] :=
      List.take_succ_eq_append_getElem (by omega)
    refine ⟨t1, h1, ?_, ?_, ?_⟩
    · rw [v1, hv, htake, TwoWordBlockFormat.execute_append]; rfl
    · rw [io1, hio, htake, TwoWordBlockFormat.transfers_append]
      simp [TwoWordBlockLift.transfers]; omega
    · exact me1.trans (max_le hme (le_max_right _ _))

/-- The machine halts one step after the last command. -/
theorem sim_halt (hBM : 2 * B ≤ M) (code : List (TwoWordBlockLift.Command B (Word w)))
    (c : Config M w) (ht : c.t = code.length) (hh : c.halted = false) :
    (Config.step (program hBM code) c).halted = true ∧
    (Config.step (program hBM code) c).disk = c.disk ∧
    (Config.step (program hBM code) c).ios = c.ios ∧
    (Config.step (program hBM code) c).maxEnd = c.maxEnd := by
  have hps : (program hBM code).step c.t c.mem = (c.mem, .halt) := by
    simp only [program, ht, lt_irrefl, dif_neg, not_false_eq_true]
  simp only [Config.step, hh, Bool.false_eq_true, if_false, hps]
  exact ⟨by first | trivial | rfl, by first | trivial | rfl, by first | trivial | rfl,
    by first | trivial | rfl⟩

end CSLB.StraightBridge


