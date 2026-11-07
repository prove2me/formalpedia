-- Prove2me | Definitions.Def_LinSysAmp_Machine
-- name    : LinSysAmp_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:57:11.085526+00:00
-- url     : https://prove2.me/theorems/443a0283-94a0-44c1-af4e-5caaa1a9d855
-- title:
--   A randomized field-operation machine with a linear-system oracle
-- statement:
--   The computational model of the paper counts **field operations**: an algorithm can add, multiply, invert and compare elements of a finite field $F$, sample a uniform field element, and read or write a field element, each in one step. This item makes that model precise as a small random-access machine.
--
--   1. A **program** is a finite list of instructions. It works on field registers, integer index registers and a field memory indexed by $\mathbb Z$.
--   2. The **field instructions** are: load a literal from $F$, $+$, $-$, $\times$, inverse (with $0^{-1}=0$), draw a uniform element of $F$, read or write the memory cell addressed by an index register, and jump if two field registers are equal.
--   3. The **index instructions** are: set to $0$, copy, increment, decrement, $+$, $-$, jump on $\le$, and an unconditional jump. There is no multiplication of indices and no conversion between field values and indices.
--   4. The **oracle instruction** reads an $n\times n$ matrix stored row by row and a vector of length $n$ from memory, draws an answer from the oracle's distribution on $F^n$ with fresh randomness, and writes it to memory.
--   5. A program halts either with the failure symbol $\bot$ or with a vector read from memory.
--
--   Every executed instruction costs one unit of the counter $\mathsf{ops}$, except an oracle call, which costs one unit of the separate counter $\mathsf{calls}$. On input $(n,k,t,M,y)$ the index registers $0,1,2$ hold $n,k,t$, the matrix $M$ occupies addresses $n i+j$ and the vector $y$ occupies addresses $n^2+i$, and everything else is $0$. A run is a probability mass function on configurations, and $\mathsf{HaltsWithin}$ says that every configuration in the support after $N$ steps has halted within given budgets of calls and operations.
--
--   This model is what gives the phrase "there is an algorithm running in time ..." in the main theorem its content: nothing is computed for free, and the oracle is reached only through the oracle instruction.
--
--   **Formalization Note** The paper lists the operations but does not fix a machine. The instruction set above is a reading of its §3.1. Index instructions are charged as well, which only makes the operation count more demanding. An oracle is any map from a matrix and a right-hand side to a probability mass function on $F^n$.
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), §3.1 "Model of computation", p.13 (PDF p.15)

import Mathlib

set_option autoImplicit false

namespace LinSysAmp

/-!
# A randomized field-operation machine with a linear-system oracle

G. Couteau, N. Melissaris, T. Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and
Fine-Grained Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…), §3.1 "Model of
computation", p.13 (PDF p.15): "We measure running time in field operations. An algorithm can add,
multiply, invert and compare field elements, sample a uniform field element, and read or write a field
element, each in one step. […] A time-T algorithm halts within T steps on every input. When we use an
algorithm as an oracle, each call uses fresh random coins."

**Formalization Note.** The paper names the operations but not a machine; this file fixes one.

* A program is a finite list of instructions over a finite field `F`. Literals are arbitrary
  elements of `F` (finitely many per program). No instruction carries a Lean function.
* Field registers `reg : ℕ → F`, index registers `ireg : ℕ → ℤ`, field memory `mem : ℤ → F`.
* Field instructions: literal, `+`, `−`, `×`, inverse (`0⁻¹ = 0`, Lean's convention), uniform
  sample, indirect load/store at an index register, jump on equality of two field registers
  ("compare").
* Index instructions: set to `0`, copy, increment, decrement, `+`, `−`, jump on `≤`, and an
  unconditional jump. There is no index multiplication and no cast between field and index values.
* `query a b c` calls the oracle on the `n × n` matrix stored row-major at cells
  `ireg a + n·i + j` and the vector at cells `ireg b + i`, samples the answer from the oracle's
  distribution (fresh randomness at every call), and writes it at cells `ireg c + i`.
* `halt` outputs `⊥` (`none`); `haltOut a` outputs the vector at cells `ireg a + i`.
* Costs: every executed instruction except `query` adds `1` to `ops`; `query` adds `1` to `calls`
  and nothing to `ops`. A program counter outside the program is stuck and charged `1` op per step.
  A halted configuration stutters at no cost. Hence every step of a running configuration adds
  exactly `1` to `ops + calls`.
* Executions are probability mass functions (`PMF`): `sample` binds the uniform distribution on
  `F`, `query` binds the oracle. `run n O P N σ` is the distribution after `N` steps.
* Input layout (`initConfig n k t M y`): index registers `0, 1, 2` hold `n, k, t`, all others `0`;
  `mem (n·i + j) = M i j` and `mem (n² + i) = y i` for `i, j < n`; all other cells, all field
  registers and both counters are `0`; the program counter is `0`.
-/

/-- An oracle for `n × n` linear systems over `F`: a randomized map from a matrix and a right-hand
side to a distribution on candidate solutions. Each call samples afresh.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
abbrev Oracle (n : ℕ) (F : Type*) := Matrix (Fin n) (Fin n) F → (Fin n → F) → PMF (Fin n → F)

/-- The instructions of the machine (see the module note for their semantics).
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
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
  | query (a b c : ℕ)
  | halt
  | haltOut (a : ℕ)

/-- A program: a finite list of instructions.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
abbrev Program (F : Type*) := List (Instr F)

/-- Whether a run is still going, or has halted with an output (`none` is `⊥`).
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
inductive Status (n : ℕ) (F : Type*) where
  | running
  | done (out : Option (Fin n → F))

/-- A machine configuration.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
structure Config (n : ℕ) (F : Type*) where
  pc : ℕ
  reg : ℕ → F
  ireg : ℕ → ℤ
  mem : ℤ → F
  ops : ℕ
  calls : ℕ
  status : Status n F

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The `n × n` matrix stored row-major from address `base`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def readMat (n : ℕ) (mem : ℤ → F) (base : ℤ) : Matrix (Fin n) (Fin n) F :=
  fun i j => mem (base + (n : ℤ) * (i : ℤ) + (j : ℤ))

/-- The length-`n` vector stored from address `base`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def readVec (n : ℕ) (mem : ℤ → F) (base : ℤ) : Fin n → F :=
  fun i => mem (base + (i : ℤ))

/-- Write a length-`n` vector at addresses `base, …, base + n − 1`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def writeVec (n : ℕ) (mem : ℤ → F) (base : ℤ) (w : Fin n → F) : ℤ → F :=
  fun x => match (List.finRange n).find? (fun i : Fin n => decide (base + (i : ℤ) = x)) with
    | some i => w i
    | none => mem x

/-- Write an `n × n` matrix row-major from address `base`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def writeMat (n : ℕ) (mem : ℤ → F) (base : ℤ) (M : Matrix (Fin n) (Fin n) F) : ℤ → F :=
  fun x =>
    match ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)).find?
        (fun p : Fin n × Fin n => decide (base + (n : ℤ) * (p.1 : ℤ) + (p.2 : ℤ) = x)) with
    | some p => M p.1 p.2
    | none => mem x

/-- Advance the program counter and charge one field operation.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def Config.tick {n : ℕ} (σ : Config n F) : Config n F :=
  { σ with pc := σ.pc + 1, ops := σ.ops + 1 }

/-- Charge one field operation and jump to `L`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def Config.jumpTo {n : ℕ} (σ : Config n F) (L : ℕ) : Config n F :=
  { σ with pc := L, ops := σ.ops + 1 }

/-- One execution step of instruction `ins` from a running configuration.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
noncomputable def exec (n : ℕ) (O : Oracle n F) (ins : Instr F) (σ : Config n F) :
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
  | .query a b c =>
      (O (readMat n σ.mem (σ.ireg a)) (readVec n σ.mem (σ.ireg b))).map fun w =>
        { σ with pc := σ.pc + 1, calls := σ.calls + 1, mem := writeVec n σ.mem (σ.ireg c) w }
  | .halt => PMF.pure { σ with ops := σ.ops + 1, status := .done none }
  | .haltOut a =>
      PMF.pure { σ with ops := σ.ops + 1, status := .done (some (readVec n σ.mem (σ.ireg a))) }

/-- One step of program `P`: a halted configuration stutters at no cost; an invalid program counter
is stuck and charged one operation; otherwise the instruction at `pc` is executed.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
noncomputable def step (n : ℕ) (O : Oracle n F) (P : Program F) (σ : Config n F) :
    PMF (Config n F) :=
  match σ.status with
  | .done _ => PMF.pure σ
  | .running =>
      match P[σ.pc]? with
      | none => PMF.pure { σ with ops := σ.ops + 1 }
      | some ins => exec n O ins σ

/-- The distribution of the configuration after `N` steps from `σ`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
noncomputable def run (n : ℕ) (O : Oracle n F) (P : Program F) : ℕ → Config n F → PMF (Config n F)
  | 0, σ => PMF.pure σ
  | N + 1, σ => (run n O P N σ).bind (step n O P)

/-- The input layout: index registers `0, 1, 2` hold `n, k, t`; the matrix `M` is stored row-major
from address `0` and the right-hand side `y` from address `n²`; everything else is `0`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def initConfig (n k t : ℕ) (M : Matrix (Fin n) (Fin n) F) (y : Fin n → F) : Config n F where
  pc := 0
  reg := fun _ => 0
  ireg := fun r => if r = 0 then (n : ℤ) else if r = 1 then (k : ℤ) else if r = 2 then (t : ℤ) else 0
  mem := writeMat n (writeVec n (fun _ => 0) ((n : ℤ) * n) y) 0 M
  ops := 0
  calls := 0
  status := .running

/-- Every run of `N` steps from `σ₀` (every configuration in the support) has halted, made at most
`c` oracle calls and at most `B` field operations.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def HaltsWithin (n : ℕ) (O : Oracle n F) (P : Program F) (σ₀ : Config n F) (N c : ℕ) (B : ℝ) :
    Prop :=
  ∀ σ ∈ (run n O P N σ₀).support, σ.status ≠ .running ∧ σ.calls ≤ c ∧ (σ.ops : ℝ) ≤ B

/-- The probability that the run of `N` steps from `σ₀` has halted with output `some x`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
noncomputable def outputProb (n : ℕ) (O : Oracle n F) (P : Program F) (σ₀ : Config n F) (N : ℕ)
    (x : Fin n → F) : ℝ :=
  ((run n O P N σ₀).map Config.status (.done (some x))).toReal

end LinSysAmp


