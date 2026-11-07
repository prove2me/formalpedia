-- Prove2me | Definitions.Def_RandOrderSort_ImplementsFast
-- name    : RandOrderSort_ImplementsFast
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:04:02.05453+00:00
-- url     : https://prove2.me/theorems/9c0c75bf-e7fe-4c52-969c-6dc531374d58
-- title:
--   The online comparison word-RAM and clause (d) of Theorem 1.1
-- statement:
--   The paper counts "exact comparisons between real values and word operations on counters with $O(\log n)$ bits", and "a word may also store a cell index or a key pointer" (pp.4, 18). This module makes that cost model a machine.
--
--   A machine with word size $W$ has memory $\mathbb N\to\{0,1\}^W$, a program counter, modular arithmetic, bit operations, indirect load and store, and branches; every executed instruction is one step. The real keys are reachable through one instruction only:
--
--   1. `cmp i j k` sets $[i]:=1$ if the arrivals $[j],[k]$ have both arrived and the key of $[j]$ is below the key of $[k]$, and $[i]:=0$ otherwise;
--   2. `place i` irrevocably writes the current arrival to output cell $[i]$ and advances the current arrival, and sets a fault flag if that cell is taken or out of range.
--
--   Initially all memory is zero except that cell $0$ holds $n$. `ImplementsFast A` says: there are one program $P$ and constants $c,C$ such that for every $n\ge 2$ and every execution $(x,\pi,\sigma)$, the run of $P$ with $W=c(\lfloor\log_2 n\rfloor+1)$ halts without fault within $Cn(\lfloor\log_2 n\rfloor+1)$ steps, having made exactly the $n$ placements of $A$ in order, and having written at most $Cn$ distinct memory cells.
--
--   This is what "$O(n\log n)$ comparisons and word operations and $O(n)$ auxiliary words" means in Theorem 1.1 and Proposition 3.3.
--
--   **Formalization Note** The machine follows the conventions of `DynSetCover.DRAM` (platform 4bc97633), whose closed instruction set reads natural-number words and so cannot be reused here. The output array is not part of the memory, as on p.4: "the restriction to $n$ cells concerns the output array". The priorities $\sigma$ are given, as on p.18: the bound "excludes generating the random tie priorities".
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), §1.1, p.4; §3.5, p.18

import Mathlib
import Definitions.Def_RandOrderSort_OnlineCmpAlg

namespace RandOrderSort

/-! # The online comparison word-RAM (cost model of §1.1, p.4, and §3.5, p.18)

Kang, Fan, arXiv:2610.15438 (version of 2026-11-01), p.4: "We count exact comparisons between
real values and word operations on counters with O(log n) bits. Auxiliary memory is allowed; the
restriction to n cells concerns the output array." §3.5, p.18: "We count key comparisons and
unit-cost operations on O(log n)-bit integers. A word may also store a cell index or a key
pointer. The bound excludes generating the random tie priorities and representing arbitrary real
inputs; it includes comparisons of the resulting strict keys and all allocation data structures."

**Formalization Note.** The machine is patterned after `DynSetCover.DRAM` (platform 4bc97633):
memory `ℕ → BitVec W`, a program counter, the arithmetic, bit, indirect-access and branch
instructions with modular arithmetic (`udiv x 0 = 0`, `umod x 0 = x`), one step per executed
instruction, and the set `written` of every memory cell ever written. Its `read`/`write` are
replaced by the two online instructions:
* `cmp i j k`: `[i] := 1` if arrivals `[j]` and `[k]` have both arrived (index at most the current
  arrival `cur`, the number of placements so far) and `key [j] < key [k]`; otherwise `[i] := 0`.
  The real keys are reachable only through this instruction, and nothing is learnt from a query
  about an arrival that has not arrived yet.
* `place i`: if `[i] < n`, `cur < n` and output cell `[i]` is still empty, the current arrival is
  written irrevocably into output cell `[i]` and `cur` advances; otherwise the machine sets a
  `fault` flag and halts.
The output array is not part of the memory (it is not counted as auxiliary words). Initially all
memory is zero except cell `0`, which holds `n`. A run halts at `halt`, when the program counter
leaves the program, or on a fault. -/

/-- The instruction set. `[i]` denotes memory cell `i`. -/
inductive Instr where
  /-- `[i] := 1` -/
  | one (i : ℕ)
  /-- `[i] := [j] + [k]` -/
  | add (i j k : ℕ)
  /-- `[i] := [j] - [k]` -/
  | sub (i j k : ℕ)
  /-- `[i] := [j] * [k]` -/
  | mul (i j k : ℕ)
  /-- `[i] := [j] / [k]` (unsigned) -/
  | udiv (i j k : ℕ)
  /-- `[i] := [j] mod [k]` (unsigned) -/
  | umod (i j k : ℕ)
  /-- bitwise and -/
  | band (i j k : ℕ)
  /-- bitwise or -/
  | bor (i j k : ℕ)
  /-- bitwise xor -/
  | bxor (i j k : ℕ)
  /-- `[i] := [j] <<< [k]` -/
  | shl (i j k : ℕ)
  /-- `[i] := [j] >>> [k]` (logical) -/
  | shr (i j k : ℕ)
  /-- `[i] := [[j]]` -/
  | load (i j : ℕ)
  /-- `[[i]] := [j]` -/
  | store (i j : ℕ)
  /-- jump to `l` if `[i] < 0` as a signed word -/
  | bltz (i l : ℕ)
  /-- jump to `l` -/
  | jmp (l : ℕ)
  /-- `[i] := 1[arrivals [j], [k] have arrived and key [j] < key [k]]` -/
  | cmp (i j k : ℕ)
  /-- place the current arrival into output cell `[i]` -/
  | place (i : ℕ)
  | halt
  deriving DecidableEq

/-- A program is a finite list of instructions; execution starts at index `0`. -/
abbrev Program := List Instr

/-- A configuration with word size `W`. `placed` lists the output cells of the placements made so
far, in order (so `placed.length` is the index of the current arrival), `written` is the set of
memory cells written so far, and `fault` records an illegal `place`. -/
structure Config (W : ℕ) where
  pc : ℕ
  mem : ℕ → BitVec W
  placed : List ℕ
  written : Finset ℕ
  fault : Bool

namespace Config

variable {W : ℕ}

/-- Write `v` into cell `a` and advance the program counter. -/
def assign (c : Config W) (a : ℕ) (v : BitVec W) : Config W :=
  { c with pc := c.pc + 1, mem := Function.update c.mem a v, written := insert a c.written }

end Config

/-- One step of the machine with `n` arrivals whose strict key order is `lt` (on arrival indices).
A halted or faulted configuration is left unchanged. -/
def step {W : ℕ} (P : Program) (n : ℕ) (lt : ℕ → ℕ → Bool) (c : Config W) : Config W :=
  if c.fault then c else
  match P[c.pc]? with
  | none => c
  | some Instr.halt => c
  | some (Instr.one i) => c.assign i 1
  | some (Instr.add i j k) => c.assign i (c.mem j + c.mem k)
  | some (Instr.sub i j k) => c.assign i (c.mem j - c.mem k)
  | some (Instr.mul i j k) => c.assign i (c.mem j * c.mem k)
  | some (Instr.udiv i j k) => c.assign i (BitVec.udiv (c.mem j) (c.mem k))
  | some (Instr.umod i j k) => c.assign i (BitVec.umod (c.mem j) (c.mem k))
  | some (Instr.band i j k) => c.assign i (c.mem j &&& c.mem k)
  | some (Instr.bor i j k) => c.assign i (c.mem j ||| c.mem k)
  | some (Instr.bxor i j k) => c.assign i (c.mem j ^^^ c.mem k)
  | some (Instr.shl i j k) => c.assign i (c.mem j <<< (c.mem k).toNat)
  | some (Instr.shr i j k) => c.assign i (c.mem j >>> (c.mem k).toNat)
  | some (Instr.load i j) => c.assign i (c.mem (c.mem j).toNat)
  | some (Instr.store i j) => c.assign (c.mem i).toNat (c.mem j)
  | some (Instr.bltz i l) =>
      if (c.mem i).msb then { c with pc := l } else { c with pc := c.pc + 1 }
  | some (Instr.jmp l) => { c with pc := l }
  | some (Instr.cmp i j k) =>
      c.assign i (if (c.mem j).toNat ≤ c.placed.length ∧ (c.mem k).toNat ≤ c.placed.length ∧
                      lt (c.mem j).toNat (c.mem k).toNat = true then 1 else 0)
  | some (Instr.place i) =>
      if (c.mem i).toNat < n ∧ c.placed.length < n ∧ (c.mem i).toNat ∉ c.placed then
        { c with pc := c.pc + 1, placed := c.placed ++ [(c.mem i).toNat] }
      else { c with fault := true }

/-- The initial configuration for `n` arrivals: program counter `0`, memory zero except
`[0] = n`, nothing placed or written. -/
def initConfig (W n : ℕ) : Config W :=
  ⟨0, fun a => if a = 0 then BitVec.ofNat W n else 0, [], ∅, false⟩

/-- The configuration after `s` steps of program `P` on `n` arrivals with key order `lt`. -/
def conf (W : ℕ) (P : Program) (n : ℕ) (lt : ℕ → ℕ → Bool) (s : ℕ) : Config W :=
  (step (W := W) P n lt)^[s] (initConfig W n)

/-- A configuration is halted when the program counter points at `halt` or outside the program. -/
def Halted {W : ℕ} (P : Program) (c : Config W) : Prop :=
  P[c.pc]? = none ∨ P[c.pc]? = some Instr.halt

/-- **Clause (d) of Theorem 1.1** ("After generating the priorities, it requires O(n log n)
comparisons and word operations and O(n) auxiliary words", p.4): one program `P` and constants
`c, C` such that for every `n ≥ 2` and every execution `(x, π, σ)`, the run of `P` with word size
`W = c·(⌊log₂ n⌋ + 1)` halts without fault within `C·n·(⌊log₂ n⌋ + 1)` steps, having made exactly
the `n` placements of `A` in order (the `t`-th into cell `cellOf A x π σ t`), and having written at
most `C·n` memory cells. -/
def ImplementsFast (A : OnlineCmpAlg) : Prop :=
  ∃ (P : Program) (c C : ℕ), ∀ n, 2 ≤ n → ∀ (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)),
    Halted P (conf (c * (Nat.log 2 n + 1)) P n (ltOf x π σ) (C * n * (Nat.log 2 n + 1))) ∧
    (conf (c * (Nat.log 2 n + 1)) P n (ltOf x π σ) (C * n * (Nat.log 2 n + 1))).fault = false ∧
    (conf (c * (Nat.log 2 n + 1)) P n (ltOf x π σ) (C * n * (Nat.log 2 n + 1))).placed =
      List.ofFn (fun t : Fin n => cellOf A x π σ t) ∧
    (conf (c * (Nat.log 2 n + 1)) P n (ltOf x π σ) (C * n * (Nat.log 2 n + 1))).written.card ≤
      C * n

end RandOrderSort


