-- Prove2me | Definitions.Def_CSL_Sorting_SmallMemory_Uniform_Loop
-- name    : CSL_Sorting_SmallMemory_Uniform_Loop
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:22:08.829184+00:00
-- url     : https://prove2.me/theorems/a4b0934a-65a5-464f-8614-5cf9f084b8e1
-- title:
--   Coded sorting library: Sorting / SmallMemory / Uniform / Loop
-- statement:
--   Module `CodedSorting.Sorting.SmallMemory.Uniform.Loop` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # A uniform read-PC / execute-table / repeat program
--
--   The program below contains one fixed table body and one loop.  It is not
--   unrolled using a public time bound.  Each iteration first performs a real
--   disk read of the virtual PC into the left word and tests that resident value.
--   The loop exits only when the fetched PC equals the fixed halt tag.
--
--   `Executes` is the terminating program semantics and has no fuel argument.
--   `run` is its bounded evaluator; fuel is only a proof bound.  The last halt
--   test costs one additional I/O.  Physical finite program control has the
--   same convention as in TwoWordPhysicalAddresses; all data-dependent values
--   remain in the two words or on disk.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.SmallMemory.Uniform.Loop

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_SmallMemory_PhysicalAddresses

/-!
# A uniform read-PC / execute-table / repeat program

The program below contains one fixed table body and one loop.  It is not
unrolled using a public time bound.  Each iteration first performs a real
disk read of the virtual PC into the left word and tests that resident value.
The loop exits only when the fetched PC equals the fixed halt tag.

`Executes` is the terminating program semantics and has no fuel argument.
`run` is its bounded evaluator; fuel is only a proof bound.  The last halt
test costs one additional I/O.  Physical finite program control has the
same convention as in TwoWordPhysicalAddresses; all data-dependent values
remain in the two words or on disk.
-/

set_option autoImplicit false
namespace CSL.TwoWordUniformLoop
open TwoWordSpill
namespace Physical
open TwoWordPhysicalAddresses

variable {W : Type*} [DecidableEq W]

structure Program (W : Type*) where
  pcAddress : ℕ
  halt : W
  body : List (Command W)

def check (p : Program W) (s : State W) : State W := step (.readLeft p.pcAddress) s
def next (p : Program W) (s : State W) : State W := execute p.body (check p s)
theorem next_def (p : Program W) (s : State W) :
    execute p.body (check p s) = next p s := rfl

def continues (p : Program W) (s : State W) : Prop := (check p s).left ≠ p.halt

/-- The fixed source code is a while-loop. Its mathematical terminating
semantics does not contain an execution horizon or a runtime fuel register. -/
inductive Executes (p : Program W) : State W → State W → ℕ → Prop where
  | stop (s : State W) (h : (check p s).left = p.halt) : Executes p s (check p s) 1
  | more (s t : State W) (cost : ℕ) (h : continues p s)
      (rest : Executes p (next p s) t cost) :
      Executes p s t (1 + transfers p.body + cost)

def run (p : Program W) : ℕ → State W → Option (State W × ℕ)
  | 0, _ => none
  | fuel+1, s =>
      let fetched := check p s
      if fetched.left = p.halt then some (fetched, 1)
      else (run p fuel (execute p.body fetched)).map
        (fun rest => (rest.1, 1 + transfers p.body + rest.2))

theorem run_sound (p : Program W) (fuel : ℕ) (s t : State W) (cost : ℕ)
    (h : run p fuel s = some (t, cost)) : Executes p s t cost := by
  induction fuel generalizing s t cost with
  | zero => simp [run] at h
  | succ fuel ih =>
      by_cases hc : (check p s).left = p.halt
      · simp [run, hc] at h
        rcases h with ⟨rfl, rfl⟩
        exact .stop s hc
      · cases he : run p fuel (next p s) with
        | none => simp [run, hc, next_def, he] at h
        | some rest =>
            rcases rest with ⟨mid, count⟩
            simp [run, hc, next_def, he] at h
            rcases h with ⟨rfl, rfl⟩
            exact .more s mid count hc (ih _ _ _ he)

/-- A successful evaluation is stable when additional proof fuel is given. -/
theorem run_mono (p : Program W) (fuel extra : ℕ) (s t : State W) (cost : ℕ)
    (h : run p fuel s = some (t, cost)) :
    run p (fuel + extra) s = some (t, cost) := by
  induction fuel generalizing s t cost with
  | zero => simp [run] at h
  | succ fuel ih =>
      by_cases hc : (check p s).left = p.halt
      · simpa [run, hc, Nat.succ_add] using h
      · cases he : run p fuel (next p s) with
        | none => simp [run, hc, next_def, he] at h
        | some rest =>
            rcases rest with ⟨mid, count⟩
            have hre := ih _ _ _ he
            simp [run, hc, next_def, he] at h
            rcases h with ⟨rfl, rfl⟩
            simp [run, hc, next_def, Nat.succ_add, hre]

theorem executes_complete (p : Program W) (s t : State W) (cost : ℕ)
    (h : Executes p s t cost) : ∃ fuel, run p fuel s = some (t, cost) := by
  induction h with
  | stop s hs => exact ⟨1, by simp [run, hs]⟩
  | more s t count hs rest ih =>
      obtain ⟨fuel, hf⟩ := ih
      have hh : (check p s).left ≠ p.halt := hs
      exact ⟨fuel+1, by simp [run, next_def, hh, hf]⟩

/-- Termination certifies the value fetched from the actual external PC
cell, rather than exhaustion of the bounded evaluator's proof fuel. -/
theorem executes_halt_pc (p : Program W) (s t : State W) (cost : ℕ)
    (h : Executes p s t cost) : t.disk p.pcAddress = p.halt := by
  induction h with
  | stop s hs => exact hs
  | more s t count hs rest ih => exact ih

end Physical

variable {R Region W : Type*} [DecidableEq R] [DecidableEq Region] [DecidableEq W]

def sourceRun (table : TwoWordIndirect.Table R Region W) (halt : W) :
    ℕ → TwoWordIndirect.Logical R Region W →
      Option (TwoWordIndirect.Logical R Region W × ℕ)
  | 0, _ => none
  | fuel+1, v =>
      if v.pc = halt then some (v, 0)
      else (sourceRun table halt fuel (TwoWordIndirect.logicalStep table v)).map
        (fun rest => (rest.1, rest.2+1))

/-- Exactly n nonhalt virtual steps, followed by a genuine halt PC. -/
def HaltsAfter (table : TwoWordIndirect.Table R Region W) (halt : W) :
    ℕ → TwoWordIndirect.Logical R Region W → TwoWordIndirect.Logical R Region W → Prop
  | 0, initial, final => initial.pc = halt ∧ final = initial
  | n+1, initial, final => initial.pc ≠ halt ∧
      HaltsAfter table halt n (TwoWordIndirect.logicalStep table initial) final

theorem sourceRun_of_halts (table : TwoWordIndirect.Table R Region W) (halt : W)
    (n : ℕ) (initial final : TwoWordIndirect.Logical R Region W)
    (h : HaltsAfter table halt n initial final) :
    sourceRun table halt (n+1) initial = some (final, n) := by
  induction n generalizing initial with
  | zero => obtain ⟨hh, rfl⟩ := h; simp [sourceRun, hh]
  | succ n ih =>
      obtain ⟨hh, hn⟩ := h
      rw [sourceRun, if_neg hh, ih _ hn]
      rfl

open TwoWordPhysicalAddresses

def program (r regions w : ℕ)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Fin (2^w)))
    (halt : Fin (2^w)) : Physical.Program (Fin (2^w)) :=
  ⟨addressNumber r regions w .pc, halt,
    (TwoWordSpill.Command.writeLeft Address.snapshot :: TwoWordIndirect.tableCode 0 table).map
      (compile (addressNumber r regions w))⟩

@[simp] theorem program_halt (r regions w : ℕ)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Fin (2^w)))
    (halt : Fin (2^w)) : (program r regions w table halt).halt = halt := rfl

def view (r regions w : ℕ) (s : TwoWordPhysicalAddresses.State (Fin (2^w))) :
    TwoWordIndirect.Logical (Fin r) (Fin regions) (Fin (2^w)) :=
  observe (pullback (addressNumber r regions w) s)

theorem check_pc (r regions w : ℕ)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Fin (2^w)))
    (halt : Fin (2^w)) (s : TwoWordPhysicalAddresses.State (Fin (2^w))) :
    (Physical.check (program r regions w table halt) s).left = (view r regions w s).pc := rfl

theorem check_view (r regions w : ℕ)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Fin (2^w)))
    (halt : Fin (2^w)) (s : TwoWordPhysicalAddresses.State (Fin (2^w))) :
    view r regions w (Physical.check (program r regions w table halt) s) =
      view r regions w s := rfl

theorem body_cost (r regions w : ℕ)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Fin (2^w)))
    (halt : Fin (2^w)) :
    transfers (program r regions w table halt).body = 1 + TwoWordIndirect.tableCost table := by
  rw [program, transfers_compile]
  simp only [TwoWordSpill.transfers, TwoWordSpill.cost, TwoWordIndirect.tableCode_cost]

theorem next_view (r regions w : ℕ)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Fin (2^w)))
    (halt : Fin (2^w)) (s : TwoWordPhysicalAddresses.State (Fin (2^w))) :
    view r regions w (Physical.next (program r regions w table halt) s) =
      TwoWordIndirect.logicalStep table (view r regions w s) := by
  have h := TwoWordIndirect.cycleCode_correct (0 : Fin (2^w)) table
    (pullback (addressNumber r regions w) s)
  unfold view Physical.next Physical.check program
  rw [execute_pullback _ (addressNumber_injective r regions w)]
  change observe (TwoWordSpill.execute
      (.writeLeft .snapshot :: TwoWordIndirect.tableCode 0 table)
      (TwoWordSpill.step (.readLeft .pc) (pullback (addressNumber r regions w) s))) = _
  exact h

theorem run_refinement (r regions w : ℕ)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Fin (2^w)))
    (halt : Fin (2^w)) (fuel : ℕ)
    (s : TwoWordPhysicalAddresses.State (Fin (2^w)))
    (final : TwoWordIndirect.Logical (Fin r) (Fin regions) (Fin (2^w))) (steps : ℕ)
    (h : sourceRun table halt fuel (view r regions w s) = some (final, steps)) :
    ∃ t, Physical.run (program r regions w table halt) fuel s =
      some (t, steps * (2 + TwoWordIndirect.tableCost table) + 1) ∧
      view r regions w t = final := by
  induction fuel generalizing s final steps with
  | zero => simp [sourceRun] at h
  | succ fuel ih =>
      by_cases hc : (view r regions w s).pc = halt
      · simp [sourceRun, hc] at h
        rcases h with ⟨rfl, rfl⟩
        refine ⟨Physical.check (program r regions w table halt) s, ?_, check_view _ _ _ _ _ _⟩
        simp [Physical.run, check_pc, hc]
      · cases he : sourceRun table halt fuel
            (TwoWordIndirect.logicalStep table (view r regions w s)) with
        | none => simp [sourceRun, hc, he] at h
        | some rest =>
            rcases rest with ⟨mid, count⟩
            simp [sourceRun, hc, he] at h
            rcases h with ⟨rfl, rfl⟩
            have hn : sourceRun table halt fuel
                (view r regions w (Physical.next (program r regions w table halt) s)) =
                  some (mid, count) := by rw [next_view]; exact he
            obtain ⟨t, ht, hv⟩ := ih _ _ _ hn
            refine ⟨t, ?_, hv⟩
            simp only [Physical.run, check_pc, program_halt, hc, ↓reduceIte, Physical.next_def, ht,
              Option.map_some]
            rw [body_cost, Nat.add_mul, Nat.one_mul]
            try dsimp only [Option.map]
            congr 2
            omega

/-- One fixed looping program terminates whenever the source virtual
program reaches its halt tag. The final halt detection is an actual read
and is charged as the trailing +1. This statement has no physical fuel. -/
theorem terminates_of_source (r regions w : ℕ)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Fin (2^w)))
    (halt : Fin (2^w)) (steps : ℕ)
    (s : TwoWordPhysicalAddresses.State (Fin (2^w)))
    (final : TwoWordIndirect.Logical (Fin r) (Fin regions) (Fin (2^w)))
    (h : HaltsAfter table halt steps (view r regions w s) final) :
    ∃ t, Physical.Executes (program r regions w table halt) s t
      (steps * (2 + TwoWordIndirect.tableCost table) + 1) ∧
      view r regions w t = final := by
  obtain ⟨t, ht, hv⟩ := run_refinement r regions w table halt (steps+1) s final steps
    (sourceRun_of_halts table halt steps _ _ h)
  exact ⟨t, Physical.run_sound _ _ _ _ _ ht, hv⟩

/-- The uniform program is chosen before every input and before the number
of executed virtual steps. Only its immutable table and halt tag are fixed. -/
theorem one_program_all_terminating_inputs (r regions w : ℕ)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Fin (2^w)))
    (halt : Fin (2^w)) :
    ∃ p : Physical.Program (Fin (2^w)),
      ∀ (s : TwoWordPhysicalAddresses.State (Fin (2^w)))
        (final : TwoWordIndirect.Logical (Fin r) (Fin regions) (Fin (2^w))) (steps : ℕ),
      HaltsAfter table halt steps (view r regions w s) final →
      ∃ t, Physical.Executes p s t (steps * (2 + TwoWordIndirect.tableCost table) + 1) ∧
        view r regions w t = final ∧
        steps * (2 + TwoWordIndirect.tableCost table) + 1 ≤
          steps * (2 + 10 * table.length) + 1 := by
  refine ⟨program r regions w table halt, ?_⟩
  intro s final steps hh
  obtain ⟨t, ht, hv⟩ := terminates_of_source r regions w table halt steps s final hh
  refine ⟨t, ht, hv, ?_⟩
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left steps (Nat.add_le_add_left (TwoWordIndirect.tableCost_le table) 2)) 1

end CSL.TwoWordUniformLoop


