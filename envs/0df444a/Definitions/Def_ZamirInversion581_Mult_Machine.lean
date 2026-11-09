-- Prove2me | Definitions.Def_ZamirInversion581_Mult_Machine
-- name    : ZamirInversion581_Mult_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:33.476878+00:00
-- url     : https://prove2.me/theorems/dadb70d6-8b7f-4feb-b572-191d05543fcc
-- title:
--   A randomized field-operation machine with an inversion oracle in every dimension
-- statement:
--   The paper counts field operations but names no machine. This item fixes one, so that "any matrices can be multiplied in time ..." has content.
--
--   1. A **program** is a finite list of instructions over a finite field $F$. Literals are elements of $F$, and no instruction contains a Lean function. The machine has field registers, integer index registers and a field memory indexed by $\mathbb Z$.
--   2. The **field instructions** are: load a literal, $+$, $-$, $\times$, inverse (with $0^{-1}=0$), draw a uniform element of $F$, read or write the memory cell addressed by an index register, and jump if two field registers are equal.
--   3. The **index instructions** are: set to $0$, copy, increment, decrement, $+$, $-$, jump on $\le$, and an unconditional jump. There is no multiplication of indices and no conversion between field values and indices.
--   4. The **query instruction** reads a dimension $m$ from an index register (a negative value reads as $0$) and two base addresses, reads the $m\times m$ matrix stored row by row at the first, draws an answer from $I_m$ with fresh randomness, and writes it row by row at the second.
--   5. A program halts with the failure symbol $\bot$ or with an $n\times n$ matrix read from memory, where $n$ is the output dimension of the statement at hand.
--
--   Every executed instruction costs one unit of the counter $\mathsf{ops}$, except a query in dimension $m$, which adds one to the count $\mathsf{calls}(m)$. A halted configuration stutters at no cost, and an invalid program counter is stuck and charged one unit per step. A run is a probability mass function on configurations. The **total time** of a configuration under $T:\mathbb N\to\mathbb R_{\ge0}$ is computed from its counters:
--
--   $$
--   \mathsf{ops}+\sum_m\mathsf{calls}(m)\,T(m).
--   $$
--
--   On a multiplication input, $B$ occupies addresses $ni+j$, $C$ occupies addresses $n^2+ni+j$, the index registers hold a given list of naturals, and everything else is $0$. On an inversion input the matrix $X$ occupies addresses $ni+j$.
--
--   Nothing is computed for free: no instruction multiplies or inverts a matrix, and the oracle is reached only through the query instruction, at a charge depending on its actual dimension.
--
--   **Formalization Note** The instruction set and cost discipline follow the published `LinSysAmp_Machine`, which is not reused because its oracle has a single dimension and answers linear systems. Since one program is fixed before $n$, the uniformity of the reduction is part of what the statements assert.
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.11, "The running times count field operations"; p.2 Theorem 1.1; p.6 "uniform in the field size q"; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Inverter

set_option autoImplicit false

namespace ZamirInversion581.Mult

/-!
# A randomized field-operation machine with an inversion oracle in every dimension

Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256
175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.2, Theorem 1.1;
p.6 "All estimates in this section are uniform in the field size q"; p.11 "The running times count
field operations".

**Formalization Note.** The paper names no machine; this file fixes one. Its instruction set and
cost discipline follow the published `LinSysAmp_Machine`, which is not reused because its oracle has
one dimension and answers linear systems.

* A program is a finite list of instructions over a finite field `F`. Literals are elements of `F`.
  No instruction carries a Lean function.
* Field registers `reg : ℕ → F`, index registers `ireg : ℕ → ℤ`, field memory `mem : ℤ → F`.
* Field instructions: literal, `+`, `−`, `×`, inverse (`0⁻¹ = 0`), uniform sample, indirect
  load/store at an index register, jump on equality of two field registers.
* Index instructions: set to `0`, copy, increment, decrement, `+`, `−`, jump on `≤`, unconditional
  jump. There is no index multiplication and no cast between field and index values.
* `query r a c` reads the dimension `m` from index register `r` (a negative value reads as `0`), reads
  the `m × m` matrix stored row-major at address `ireg a`, samples an answer from `I m` with fresh
  randomness and writes it row-major at address `ireg c`.
* `halt` outputs `⊥` (`none`); `haltOut a` outputs the `n × n` matrix stored row-major at address
  `ireg a`, where `n` is the output dimension of the statement at hand.
* Costs: every executed instruction except `query` adds `1` to `ops`; a `query` in dimension `m` adds
  `1` to `calls m`. A halted configuration stutters at no cost. An invalid program counter is stuck
  and charged `1` op per step.
* Executions are probability mass functions: `sample` binds the uniform distribution on `F`, `query`
  binds the oracle.
* The total time under `T : ℕ → ℝ≥0` is `ops + Σ_m calls(m) · T(m)`, computed from the counters.
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
  | query (r a c : ℕ)
  | halt
  | haltOut (a : ℕ)

/-- A program: a finite list of instructions. -/
abbrev Program (F : Type*) := List (Instr F)

/-- Whether a run is still going, or has halted with an output (`none` is `⊥`). -/
inductive Status (n : ℕ) (F : Type*) where
  | running
  | done (out : Option (Matrix (Fin n) (Fin n) F))

/-- A machine configuration; `calls m` counts the oracle calls in dimension `m`. -/
structure Config (n : ℕ) (F : Type*) where
  pc : ℕ
  reg : ℕ → F
  ireg : ℕ → ℤ
  mem : ℤ → F
  ops : ℕ
  calls : ℕ →₀ ℕ
  status : Status n F

/-- The `m × m` matrix stored row-major from address `base`. -/
def readMat {F : Type*} (m : ℕ) (mem : ℤ → F) (base : ℤ) : Matrix (Fin m) (Fin m) F :=
  fun i j => mem (base + (m : ℤ) * (i : ℤ) + (j : ℤ))

/-- Write an `m × m` matrix row-major from address `base`; all other cells are unchanged. -/
def writeMat {F : Type*} (m : ℕ) (mem : ℤ → F) (base : ℤ) (M : Matrix (Fin m) (Fin m) F) : ℤ → F :=
  fun x =>
    match ((List.finRange m).flatMap fun i => (List.finRange m).map fun j => (i, j)).find?
        (fun p : Fin m × Fin m => decide (base + (m : ℤ) * (p.1 : ℤ) + (p.2 : ℤ) = x)) with
    | some p => M p.1 p.2
    | none => mem x

/-- Advance the program counter and charge one operation. -/
def Config.tick {n : ℕ} {F : Type*} (σ : Config n F) : Config n F :=
  { σ with pc := σ.pc + 1, ops := σ.ops + 1 }

/-- Charge one operation and jump to `L`. -/
def Config.jumpTo {n : ℕ} {F : Type*} (σ : Config n F) (L : ℕ) : Config n F :=
  { σ with pc := L, ops := σ.ops + 1 }

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- One execution step of instruction `ins` from a running configuration. -/
noncomputable def exec (n : ℕ) (I : InversionOracle F) (ins : Instr F) (σ : Config n F) :
    PMF (Config n F) :=
  match ins with
  | .const d c => PMF.pure { σ.tick with reg := Function.update σ.reg d c }
  | .add d a b => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.reg a + σ.reg b) }
  | .sub d a b => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.reg a - σ.reg b) }
  | .mul d a b => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.reg a * σ.reg b) }
  | .inv d a => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.reg a)⁻¹ }
  | .sample d => (PMF.uniformOfFintype F).map fun c =>
      { σ.tick with reg := Function.update σ.reg d c }
  | .load d i => PMF.pure { σ.tick with reg := Function.update σ.reg d (σ.mem (σ.ireg i)) }
  | .store i a => PMF.pure { σ.tick with mem := Function.update σ.mem (σ.ireg i) (σ.reg a) }
  | .jeq a b L => PMF.pure (if σ.reg a = σ.reg b then σ.jumpTo L else σ.tick)
  | .iset0 d => PMF.pure { σ.tick with ireg := Function.update σ.ireg d 0 }
  | .icopy d a => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg a) }
  | .iinc d => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg d + 1) }
  | .idec d => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg d - 1) }
  | .iadd d a b => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg a + σ.ireg b) }
  | .isub d a b => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg a - σ.ireg b) }
  | .ijle a b L => PMF.pure (if σ.ireg a ≤ σ.ireg b then σ.jumpTo L else σ.tick)
  | .jmp L => PMF.pure (σ.jumpTo L)
  | .query r a c =>
      let m := (σ.ireg r).toNat
      (I m (readMat m σ.mem (σ.ireg a))).map fun W =>
        { σ with
          pc := σ.pc + 1
          calls := σ.calls + Finsupp.single m 1
          mem := writeMat m σ.mem (σ.ireg c) W }
  | .halt => PMF.pure { σ with ops := σ.ops + 1, status := .done none }
  | .haltOut a =>
      PMF.pure { σ with ops := σ.ops + 1, status := .done (some (readMat n σ.mem (σ.ireg a))) }

/-- One step of program `P`: a halted configuration stutters at no cost; an invalid program counter
is stuck and charged one operation; otherwise the instruction at `pc` is executed. -/
noncomputable def step (n : ℕ) (I : InversionOracle F) (P : Program F) (σ : Config n F) :
    PMF (Config n F) :=
  match σ.status with
  | .done _ => PMF.pure σ
  | .running =>
      match P[σ.pc]? with
      | none => PMF.pure { σ with ops := σ.ops + 1 }
      | some ins => exec n I ins σ

/-- The distribution of the configuration after `N` steps from `σ`. -/
noncomputable def run (n : ℕ) (I : InversionOracle F) (P : Program F) :
    ℕ → Config n F → PMF (Config n F)
  | 0, σ => PMF.pure σ
  | N + 1, σ => (run n I P N σ).bind (step n I P)

/-- The initial configuration: the index registers hold the list `args` in order and `0` after it;
the memory is `mem`; all field registers and all counters are `0`; the program counter is `0`. -/
def initConfig {F : Type*} [Zero F] (n : ℕ) (args : List ℕ) (mem : ℤ → F) : Config n F where
  pc := 0
  reg := fun _ => 0
  ireg := fun r => ((args.getD r 0 : ℕ) : ℤ)
  mem := mem
  ops := 0
  calls := 0
  status := .running

/-- The multiplication input: `B` stored row-major from address `0`, `C` from address `n²`, all other
cells `0`; the index registers hold `args`. -/
def multInput {F : Type*} [Zero F] (n : ℕ) (args : List ℕ) (B C : Matrix (Fin n) (Fin n) F) :
    Config n F :=
  initConfig n args (writeMat n (writeMat n (fun _ => 0) ((n : ℤ) * (n : ℤ)) C) 0 B)

/-- The inversion input: `X` stored row-major from address `0`, all other cells `0`; the index
registers hold `args`. -/
def invInput {F : Type*} [Zero F] (n : ℕ) (args : List ℕ) (X : Matrix (Fin n) (Fin n) F) :
    Config n F :=
  initConfig n args (writeMat n (fun _ => 0) 0 X)

/-- The total time `ops + Σ_m calls(m) · T(m)` of a configuration under the charge `T`. -/
noncomputable def totalTime {n : ℕ} {F : Type*} (T : ℕ → NNReal) (σ : Config n F) : ℝ :=
  (σ.ops : ℝ) + σ.calls.sum fun m c => (c : ℝ) * (T m : ℝ)

/-- Every configuration in the support after `N` steps from `σ₀` has halted and has total time at
most `B`. -/
def AllRunsHaltWithin (n : ℕ) (I : InversionOracle F) (P : Program F) (σ₀ : Config n F) (N : ℕ)
    (T : ℕ → NNReal) (B : ℝ) : Prop :=
  ∀ σ ∈ (run n I P N σ₀).support, σ.status ≠ .running ∧ totalTime T σ ≤ B

/-- The probability that the run of `N` steps from `σ₀` has halted with output exactly `x`. -/
noncomputable def outputProb (n : ℕ) (I : InversionOracle F) (P : Program F) (σ₀ : Config n F)
    (N : ℕ) (x : Matrix (Fin n) (Fin n) F) : ℝ :=
  ((run n I P N σ₀).map Config.status (.done (some x))).toReal

end ZamirInversion581.Mult


