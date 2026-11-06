-- Prove2me | Definitions.Def_FixedMachinePrec_RAM
-- name    : FixedMachinePrec_RAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:09.408984+00:00
-- url     : https://prove2.me/theorems/75dd7b9f-8f8d-425f-aa2d-2f127445aa50
-- title:
--   The unit-cost word RAM with input and output tapes
-- statement:
--   A **RAM program** is a finite list of instructions acting on memory cells $[i]$, $i\in\mathbb Z$, holding $W$-bit words:
--
--   1. $[i]:=1$; $[i]:=[j]+[k]$; $[i]:=[j]-[k]$; $[i]:=[j]\cdot[k]$ (modulo $2^W$);
--   2. indirect access $[i]:=[[j]]$ and $[[i]]:=[j]$;
--   3. a jump to position $l$ if $[i]<0$ (signed reading);
--   4. $\mathrm{read}\ i$: $[i]:=$ the next input bit ($0$ or $1$), or $2$ once the input is exhausted;
--   5. $\mathrm{out}\ i$: append the bit $[[i]\ne0]$ to the output tape;
--   6. accept and reject (halt).
--
--   The program starts at position $0$ on all-zero memory with the input word on its input tape; every executed instruction, including the halting one, costs one **elementary operation**. The program *outputs* $w$ within $t$ operations if it halts within $t$ steps with exactly $w$ on its output tape.
--
--   This is the RAM of Section 6: indexed access, assignment, arithmetic and comparison of counters cost one operation, and no operation acts on a whole $N$-bit set.
--
--   **Formalization Note** The instruction set is that of the published `TrulySubcubicAPSP.Instr`, with a sequential input tape and an output tape added; the input is not preloaded into memory, so inputs longer than the address space (a long deadline) can be read.
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), §6, p.20 (RAM model); Theorem 1.1, p.1

import Mathlib

namespace FixedMachinePrec

/-- **Instructions of the unit-cost word RAM** (Jansen, *Precedence Constraint Scheduling on a
Fixed Number of Machines*, manuscript, sha256 08cdf3e1…, §6, p.20: "Access to an indexed array
entry, an assignment, and arithmetic or comparison of indices and counters cost one operation.
… No operation treats an entire N-bit set as one word").

`i j k` name memory cells, `[i]` is the word in cell `i`, `l` is a program position. The
instructions are those of the published `TrulySubcubicAPSP.Instr` (constant 1, addition,
subtraction, multiplication, indirect load and store, a sign test, accept, reject), plus a
sequential input tape (`read i`: `[i] :=` the next input bit as `0`/`1`, or `2` once the input is
exhausted) and an output tape (`out i`: append the bit `[i] ≠ 0`).

**Formalization Note** The input is read bit by bit from a tape instead of being preloaded into
addressed cells, so an input longer than the address space (e.g. a long deadline) can still be
read; the output is a list of bits. -/
inductive RAMInstr where
  | one (i : Int)
  | add (i j k : Int)
  | sub (i j k : Int)
  | mul (i j k : Int)
  | load (i j : Int)
  | store (i j : Int)
  | bltz (i : Int) (l : Nat)
  | read (i : Int)
  | out (i : Int)
  | accept
  | reject

/-- **The run of a RAM program.** `ramExec P t pc mem inp outp` runs `P` from position `pc` on
memory `mem` (`W`-bit words), remaining input `inp` and output so far `outp`; it returns the
verdict and the output tape if `P` halts within `t` steps (the halting step counted, every
executed instruction costing one step), and `none` otherwise. Past its end the program rejects.
Addresses are read as signed integers; `bltz` jumps on a negative word. -/
def ramExec {W : Nat} (P : List RAMInstr) :
    (t pc : Nat) → (mem : Int → BitVec W) → (inp outp : List Bool) → Option (Bool × List Bool)
  | 0, _, _, _, _ => none
  | t + 1, pc, mem, inp, outp =>
    let wr (i : Int) (v : BitVec W) :=
      ramExec P t (pc + 1) (fun x => if x = i then v else mem x) inp outp
    match P.getD pc .reject with
    | .one i => wr i 1
    | .add i j k => wr i (mem j + mem k)
    | .sub i j k => wr i (mem j - mem k)
    | .mul i j k => wr i (mem j * mem k)
    | .load i j => wr i (mem (mem j).toInt)
    | .store i j => wr (mem i).toInt (mem j)
    | .bltz i l => ramExec P t (if (mem i).toInt < 0 then l else pc + 1) mem inp outp
    | .read i =>
      match inp with
      | [] => ramExec P t (pc + 1) (fun x => if x = i then 2 else mem x) [] outp
      | b :: rest =>
        ramExec P t (pc + 1) (fun x => if x = i then (if b then 1 else 0) else mem x) rest outp
    | .out i => ramExec P t (pc + 1) mem inp (outp ++ [decide (mem i ≠ 0)])
    | .accept => some (true, outp)
    | .reject => some (false, outp)

/-- `RAMOutputs W P input output t`: the program `P`, run with word size `W` from position `0` on
all-zero memory with `input` on its input tape, halts within `t` elementary operations with
exactly `output` on its output tape. -/
def RAMOutputs (W : Nat) (P : List RAMInstr) (input output : List Bool) (t : Nat) : Prop :=
  ∃ v : Bool, ramExec (W := W) P t 0 (fun _ => 0) input [] = some (v, output)

end FixedMachinePrec


