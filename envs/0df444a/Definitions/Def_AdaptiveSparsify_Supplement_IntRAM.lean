-- Prove2me | Definitions.Def_AdaptiveSparsify_Supplement_IntRAM
-- name    : AdaptiveSparsify_Supplement_IntRAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:52:17.571418+00:00
-- url     : https://prove2.me/theorems/cbcc756f-ba7c-4661-a417-51f45e033dc6
-- title:
--   The deterministic one-pass integer RAM of Theorem 4
-- statement:
--   The machine of Theorem 4: a deterministic random access machine over the integers.
--
--   Registers $r_0,r_1,\dots$ and memory cells (indexed by $\mathbb Z$) hold integers. A program is a finite list of instructions:
--
--   1. load an integer literal; $+$, $-$, $\times$; floor division (a division by $0$ faults);
--   2. indirect load and store;
--   3. compare and jump: if $r_a\le r_b$ go to instruction $\ell$;
--   4. `next`: read the next integer of the input stream into a register (the cursor advances; past the end it reads $0$);
--   5. `out`: append a register to the output stream;
--   6. `halt`.
--
--   Every executed instruction costs one unit of work. The input is accessible only through `next`, so the program reads each input integer at most once, in order: this is the **one pass** of Theorem 4. The program may store what it reads.
--
--   The machine itself does not limit integer sizes. The unit-cost convention of p.55 ("arithmetic and comparisons on $O(B\log n)$-bit integers have unit cost") is imposed in Theorem 4, which bounds every integer held in a register or memory cell at every step.
--
--   **Formalization Note** An invalid program counter is stuck and charged; halted and faulted states stutter at no cost.
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), §8.1, p.55 (arithmetic model and one pass); Algorithm 3, p.60

import Mathlib

namespace AdaptiveSparsify

/-!
# The deterministic one-pass integer RAM of Theorem 4

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…),
§8.1, p.55: "we use the standard arithmetic-RAM convention that arithmetic and comparisons on
`O(B log n)`-bit integers have unit cost", and Theorem 4's "in one pass over the input".

**Formalization Note.**
* Registers `r[0], r[1], …` and memory cells (indexed by `ℤ`) hold integers. Instructions: load a
  literal; `+ − ×`; floor division (`Int.fdiv`; a division by `0` faults); indirect load and store;
  compare-and-jump `if r[a] ≤ r[b] then goto l`; `next` (read the next input integer); `out` (append a
  register to the output); `halt`. Every executed instruction costs one unit of `work`. An invalid
  program counter is stuck and charged; halted and faulted states stutter at no cost.
* One pass: the input is a list of integers that the program can read only through `next`, which
  returns the integer under the cursor and advances it (`0` past the end). So every input integer is
  read at most once, in order. The program may store what it reads.
* The machine itself puts no bound on integer sizes; the unit-cost convention is enforced by the
  theorem that uses it, which bounds every integer held in a register or memory cell at every step.
-/

namespace Supplement

/-- An instruction of the integer RAM. -/
inductive IntInstr where
  | const (dst : ℕ) (value : ℤ)
  | add (dst a b : ℕ)
  | sub (dst a b : ℕ)
  | mul (dst a b : ℕ)
  | div (dst a b : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  | jumpLE (a b target : ℕ)
  | next (dst : ℕ)
  | out (src : ℕ)
  | halt

/-- A program of the integer RAM: one finite instruction list. -/
abbrev IntProgram := List IntInstr

/-- A state of the integer RAM. -/
structure IntState where
  pc : ℕ
  regs : ℕ → ℤ
  mem : ℤ → ℤ
  cursor : ℕ
  output : List ℤ
  halted : Bool
  faulted : Bool
  work : ℕ

/-- The initial state: everything `0`, empty output, cursor at the first input integer. -/
def intInit : IntState := ⟨0, fun _ => 0, fun _ => 0, 0, [], false, false, 0⟩

/-- One step of `P` on the input stream `input`. -/
def intStep (P : IntProgram) (input : List ℤ) (s : IntState) : IntState :=
  if s.halted || s.faulted then s else
    let t := { s with work := s.work + 1, pc := s.pc + 1 }
    match P[s.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.const d v) => { t with regs := Function.update s.regs d v }
    | some (.add d a b) => { t with regs := Function.update s.regs d (s.regs a + s.regs b) }
    | some (.sub d a b) => { t with regs := Function.update s.regs d (s.regs a - s.regs b) }
    | some (.mul d a b) => { t with regs := Function.update s.regs d (s.regs a * s.regs b) }
    | some (.div d a b) =>
        if s.regs b = 0 then { t with faulted := true }
        else { t with regs := Function.update s.regs d (Int.fdiv (s.regs a) (s.regs b)) }
    | some (.load d a) => { t with regs := Function.update s.regs d (s.mem (s.regs a)) }
    | some (.store a b) => { t with mem := Function.update s.mem (s.regs a) (s.regs b) }
    | some (.jumpLE a b l) => if s.regs a ≤ s.regs b then { t with pc := l } else t
    | some (.next d) =>
        { t with regs := Function.update s.regs d (input.getD s.cursor 0), cursor := s.cursor + 1 }
    | some (.out a) => { t with output := s.output ++ [s.regs a] }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` on `input`. -/
def intRun (P : IntProgram) (input : List ℤ) (t : ℕ) : IntState :=
  (intStep P input)^[t] intInit

/-- Every integer held in a register or memory cell of `s` has absolute value below `R`. -/
def IntState.HeldBelow (s : IntState) (R : ℝ) : Prop :=
  (∀ r, ((|s.regs r| : ℤ) : ℝ) < R) ∧ ∀ a, ((|s.mem a| : ℤ) : ℝ) < R

end Supplement

end AdaptiveSparsify


