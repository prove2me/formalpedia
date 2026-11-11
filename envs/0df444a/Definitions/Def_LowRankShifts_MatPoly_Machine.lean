-- Prove2me | Definitions.Def_LowRankShifts_MatPoly_Machine
-- name    : LowRankShifts_MatPoly_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:56:34.456199+00:00
-- url     : https://prove2.me/theorems/513321e9-caf5-4d5d-b05f-90fc5f2562b4
-- title:
--   A randomized field-operation machine with a vector oracle, an index memory, operation and query counters
-- statement:
--   The paper counts the running time of its algorithms in field operations and names no machine; this item fixes one.
--
--   1. A **program** is a finite list of instructions over a field $F$; literals are elements of $F$ and no instruction carries a function. The machine has field registers, integer index registers, a field memory indexed by $\mathbb Z$ and an index memory indexed by $\mathbb Z$.
--   2. **Field instructions**: load a literal, $+$, $-$, $\times$, inverse (with $0^{-1}=0$), sample, read or write the field-memory cell addressed by an index register, jump if two field registers are equal.
--   3. **Index instructions**: set to $0$, copy, increment, decrement, $+$, $-$, jump on $\le$, unconditional jump, read or write the index-memory cell addressed by an index register. There is **no multiplication of indices and no conversion between field values and indices**.
--   4. The **query instruction** `query s t` reads the $a$ field cells starting at the address in register $s$ as a vector $v\in F^a$, draws an answer $w\in F^b$ from the oracle's law $O(v)$ with fresh randomness, and writes it into the $b$ cells starting at the address in register $t$. An oracle is a map $O:F^a\to\mathrm{PMF}(F^b)$, so it is memoryless: each query is an independent draw.
--   5. `halt` stops with the failure symbol $\bot$ (for a decision problem: NO); `haltOut a` stops and designates the output starting at the address in register $a$ (for a decision problem: YES). An $n\times m$ matrix output is read row-major (entry $(i,j)$ at base $+\,mi+j$); a vector output of length $m$ from the $m$ cells after the base.
--
--   Every executed instruction except a query adds one to the counter $\mathsf{ops}$; a query adds one to $\mathsf{queries}$. A halted configuration stutters at no cost; an invalid program counter is stuck and charged one operation per step. `sample` draws from a sampling law given to the run (the statements use the uniform law on a finite field). A run is a probability mass function on configurations. Since a running configuration gains exactly one unit of $\mathsf{ops}+\mathsf{queries}$ per step, "every run halts with at most $T$ operations and $Q$ queries" is checked on the law after $\lfloor T\rfloor+\lfloor Q\rfloor+1$ steps (`RunsWithin`), and output probabilities are read off the same law (`finalLaw`, `probOut`).
--
--   An input is laid out by `initConfig`: field blocks consecutively from field address $0$, the start address of each block in the index memory followed by integer data, and a list of integers in the index registers; everything else is $0$.
--
--   **Formalization Note.** The instruction set and cost discipline follow the published `ZamirInversion581_Mult_Machine`, which is not reused because its oracle answers matrix inversions. Without index multiplication and without field-to-index conversion a program cannot pack a matrix into one integer, so nothing is computed for free.
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), p. 8 (PDF 11), §2 (running time in field operations); pp. 13–19 (PDF 16–22), oracle algorithms of Lemma 2.11, Corollary 2.12, Theorems 3.4, 3.5

import Mathlib

set_option autoImplicit false

namespace LowRankShifts.MatPoly

/-!
# A randomized field-operation machine with a vector oracle

Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, *Worst-Case to Average-Case Reductions
for Linear Algebra: Optimal, Simple, and General*, STOC 2027 submission, p. 8: "we [...] state the
running time of our algorithms in terms of numbers of arithmetic operations in the underlying
fields". The paper names no machine; this file fixes one. Its instruction set and cost discipline
follow the published `ZamirInversion581_Mult_Machine`, with two changes: the oracle is a vector
oracle `(Fin a → F) → PMF (Fin b → F)` with dimensions fixed by the statement at hand, and there is
an index memory, so that a polynomial's words can be part of an input.

* A program is a finite list of instructions over a field `F`. Literals are elements of `F`. No
  instruction carries a Lean function.
* Field registers `reg : ℕ → F`, index registers `ireg : ℕ → ℤ`, field memory `mem : ℤ → F`,
  index memory `imem : ℤ → ℤ`.
* Field instructions: literal, `+`, `−`, `×`, inverse (`0⁻¹ = 0`), sample, indirect load/store of
  the field memory at an index register, jump on equality of two field registers.
* Index instructions: set to `0`, copy, increment, decrement, `+`, `−`, jump on `≤`, unconditional
  jump, indirect load/store of the index memory at an index register. There is no index
  multiplication and no conversion between field values and index values.
* `query s t` reads the `a` field cells from address `ireg s`, draws an answer `w : Fin b → F` from
  the oracle with fresh randomness, and writes it into the `b` cells from address `ireg t`.
* `halt` stops with the failure symbol `⊥` (for a decision problem: NO); `haltOut a` stops and
  designates the output starting at address `ireg a` (for a decision problem: YES).
* Costs: every executed instruction except `query` adds `1` to `ops`; a `query` adds `1` to
  `queries` and nothing to `ops`. A halted configuration stutters at no cost. An invalid program
  counter is stuck and charged `1` op per step.
* `sample` draws from the sampling law `samp : PMF F` given to the run; on a finite field the
  statements use the uniform law. A run is a probability mass function on configurations.
-/

/-- The instructions of the machine (see the module note for their semantics). -/
inductive Instr (F : Type*) where
  | const (d : ℕ) (c : F)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | mul (d a b : ℕ)
  | inv (d a : ℕ)
  | sample (d : ℕ)
  | load (d i : ℕ)
  | store (i a : ℕ)
  | jeq (a b L : ℕ)
  | iset0 (d : ℕ)
  | icopy (d a : ℕ)
  | iinc (d : ℕ)
  | idec (d : ℕ)
  | iadd (d a b : ℕ)
  | isub (d a b : ℕ)
  | ijle (a b L : ℕ)
  | jmp (L : ℕ)
  | iload (d i : ℕ)
  | istore (i a : ℕ)
  | query (s t : ℕ)
  | halt
  | haltOut (a : ℕ)

/-- A program: a finite list of instructions. -/
abbrev Program (F : Type*) := List (Instr F)

/-- A program that uses neither `sample` nor `query`: its run is deterministic. -/
def Instr.IsDeterministic {F : Type*} : Instr F → Prop
  | .sample _ => False
  | .query _ _ => False
  | _ => True

/-- Every instruction of the program is deterministic (no `sample`, no `query`). -/
def Program.IsDeterministic {F : Type*} (P : Program F) : Prop :=
  ∀ ins ∈ P, Instr.IsDeterministic ins

/-- A (possibly randomized, memoryless) vector oracle: every query `v` is answered by a fresh
draw from the law `O v`. -/
abbrev VecOracle (F : Type*) (a b : ℕ) := (Fin a → F) → PMF (Fin b → F)

/-- Whether a run is still going, or has halted; `halted true base` designates the output starting
at address `base` (YES), `halted false _` is `⊥` (NO). -/
inductive Status where
  | running
  | halted (accept : Bool) (base : ℤ)

/-- A machine configuration. -/
structure Config (F : Type*) where
  pc : ℕ
  reg : ℕ → F
  ireg : ℕ → ℤ
  mem : ℤ → F
  imem : ℤ → ℤ
  ops : ℕ
  queries : ℕ
  status : Status

/-- Write the vector `w` into the cells `base, …, base + b − 1`; all other cells are unchanged. -/
def writeVec {F : Type*} {b : ℕ} (mem : ℤ → F) (base : ℤ) (w : Fin b → F) : ℤ → F :=
  fun x => if h : 0 ≤ x - base ∧ x - base < b then w ⟨(x - base).toNat, by omega⟩ else mem x

/-- The vector of the `a` cells `base, …, base + a − 1`. -/
def readVec {F : Type*} (a : ℕ) (mem : ℤ → F) (base : ℤ) : Fin a → F :=
  fun k => mem (base + (k : ℤ))

/-- The `n × m` matrix stored row-major from address `base`: entry `(i, j)` at `base + m·i + j`. -/
def readMat {F : Type*} (n m : ℕ) (mem : ℤ → F) (base : ℤ) : Matrix (Fin n) (Fin m) F :=
  fun i j => mem (base + (m : ℤ) * (i : ℤ) + (j : ℤ))

/-- Advance the program counter and charge one operation. -/
def Config.tick {F : Type*} (σ : Config F) : Config F :=
  { σ with pc := σ.pc + 1, ops := σ.ops + 1 }

/-- Charge one operation and jump to `L`. -/
def Config.jumpTo {F : Type*} (σ : Config F) (L : ℕ) : Config F :=
  { σ with pc := L, ops := σ.ops + 1 }

variable {F : Type*} [Field F] [DecidableEq F] {a b : ℕ}

/-- One execution step of instruction `ins` from a running configuration, with sampling law
`samp` and oracle `O`. -/
noncomputable def exec (samp : PMF F) (O : VecOracle F a b) (ins : Instr F) (σ : Config F) :
    PMF (Config F) :=
  match ins with
  | .const d c => PMF.pure { σ.tick with reg := Function.update σ.reg d c }
  | .add d x y => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.reg x + σ.reg y) }
  | .sub d x y => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.reg x - σ.reg y) }
  | .mul d x y => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.reg x * σ.reg y) }
  | .inv d x => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.reg x)⁻¹ }
  | .sample d => samp.map fun c => { σ.tick with reg := Function.update σ.reg d c }
  | .load d i => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.mem (σ.ireg i)) }
  | .store i x => PMF.pure { σ.tick with mem := Function.update σ.mem (σ.ireg i) (σ.reg x) }
  | .jeq x y L => PMF.pure (if σ.reg x = σ.reg y then σ.jumpTo L else σ.tick)
  | .iset0 d => PMF.pure { σ.tick with ireg := Function.update σ.ireg d 0 }
  | .icopy d x => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg x) }
  | .iinc d => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg d + 1) }
  | .idec d => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg d - 1) }
  | .iadd d x y => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg x + σ.ireg y) }
  | .isub d x y => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg x - σ.ireg y) }
  | .ijle x y L => PMF.pure (if σ.ireg x ≤ σ.ireg y then σ.jumpTo L else σ.tick)
  | .jmp L => PMF.pure (σ.jumpTo L)
  | .iload d i => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.imem (σ.ireg i)) }
  | .istore i x => PMF.pure { σ.tick with imem := Function.update σ.imem (σ.ireg i) (σ.ireg x) }
  | .query s t =>
      (O (readVec a σ.mem (σ.ireg s))).map fun w =>
        { σ with
          pc := σ.pc + 1
          queries := σ.queries + 1
          mem := writeVec σ.mem (σ.ireg t) w }
  | .halt => PMF.pure { σ with ops := σ.ops + 1, status := .halted false 0 }
  | .haltOut x => PMF.pure { σ with ops := σ.ops + 1, status := .halted true (σ.ireg x) }

/-- One step of program `P`: a halted configuration stutters at no cost; an invalid program counter
is stuck and charged one operation; otherwise the instruction at `pc` is executed. -/
noncomputable def step (samp : PMF F) (O : VecOracle F a b) (P : Program F) (σ : Config F) :
    PMF (Config F) :=
  match σ.status with
  | .halted _ _ => PMF.pure σ
  | .running =>
      match P[σ.pc]? with
      | none => PMF.pure { σ with ops := σ.ops + 1 }
      | some ins => exec samp O ins σ

/-- The distribution of the configuration after `N` steps from `σ`. -/
noncomputable def run (samp : PMF F) (O : VecOracle F a b) (P : Program F) :
    ℕ → Config F → PMF (Config F)
  | 0, σ => PMF.pure σ
  | N + 1, σ => (run samp O P N σ).bind (step samp O P)

/-- The step budget for the bounds `T` (operations) and `Q` (queries). A running configuration
gains exactly one unit of `ops + queries` per step, so a run of `⌊T⌋₊ + ⌊Q⌋₊ + 1` steps that is
still running has exceeded one of the two bounds. -/
noncomputable def stepBudget (T Q : ℝ) : ℕ := ⌊T⌋₊ + ⌊Q⌋₊ + 1

/-- The law of the configuration after the step budget for `T` and `Q`. -/
noncomputable def finalLaw (samp : PMF F) (O : VecOracle F a b) (P : Program F) (σ₀ : Config F)
    (T Q : ℝ) : PMF (Config F) :=
  run samp O P (stepBudget T Q) σ₀

/-- Every run from `σ₀` halts after at most `T` operations and at most `Q` oracle queries: every
configuration in the support after the step budget has halted, with `ops ≤ T` and
`queries ≤ Q`. -/
def RunsWithin (samp : PMF F) (O : VecOracle F a b) (P : Program F) (σ₀ : Config F)
    (T Q : ℝ) : Prop :=
  ∀ σ ∈ (finalLaw samp O P σ₀ T Q).support,
    σ.status ≠ .running ∧ (σ.ops : ℝ) ≤ T ∧ (σ.queries : ℝ) ≤ Q

/-- The `n × m` matrix output of a configuration: `some` of the matrix stored row-major at the
designated address if it halted with `haltOut`, `none` (`⊥`) otherwise. -/
def outMat (n m : ℕ) (σ : Config F) : Option (Matrix (Fin n) (Fin m) F) :=
  match σ.status with
  | .halted true base => some (readMat n m σ.mem base)
  | _ => none

/-- The length-`m` vector output of a configuration: `some` of the `m` cells from the designated
address if it halted with `haltOut`, `none` (`⊥`) otherwise. -/
def outVec (m : ℕ) (σ : Config F) : Option (Fin m → F) :=
  match σ.status with
  | .halted true base => some (readVec m σ.mem base)
  | _ => none

/-- The verdict of a configuration: `some true` (YES) after `haltOut`, `some false` (NO) after
`halt`, `none` while running. -/
def verdict (σ : Config F) : Option Bool :=
  match σ.status with
  | .halted acc _ => some acc
  | .running => none

/-- The probability that the configuration law `μ` gives the output `x` under the decoding
`out`. -/
noncomputable def probOut {β : Type*} (μ : PMF (Config F)) (out : Config F → β) (x : β) : ℝ :=
  ((μ.map out) x).toReal

/-- The integer list `l` laid out from address `0`; every other cell holds `0`. -/
def listMem {α : Type*} [Zero α] (l : List α) : ℤ → α :=
  fun x => if 0 ≤ x then l.getD x.toNat 0 else 0

/-- The start addresses of consecutive blocks with the given lengths, laid out from address `0`. -/
def blockStarts (lens : List ℕ) : List ℤ :=
  ((lens.scanl (fun acc len => acc + len) (0 : ℕ)).take lens.length).map fun x => (x : ℤ)

/-- The initial configuration of an input: the field blocks `blocks` are laid out consecutively
from field address `0`; the index memory holds, from address `0`, the start address of every
field block (one cell per block, in order) followed by the list `idata`; the index registers hold
the list `args` in order and `0` after it; every other cell, every field register and every
counter is `0`; the program counter is `0`. -/
def initConfig (args : List ℤ) (blocks : List (List F)) (idata : List ℤ) : Config F where
  pc := 0
  reg := fun _ => 0
  ireg := fun r => args.getD r 0
  mem := listMem blocks.flatten
  imem := listMem (blockStarts (blocks.map List.length) ++ idata)
  ops := 0
  queries := 0
  status := .running

/-- An `n × m` matrix as the list of its entries in row-major order. -/
def matList {n m : ℕ} (A : Matrix (Fin n) (Fin m) F) : List F :=
  (List.finRange n).flatMap fun i => (List.finRange m).map fun j => A i j

end LowRankShifts.MatPoly


