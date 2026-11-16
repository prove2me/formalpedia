-- Prove2me | Definitions.Def_LinSysAmp_Supplement_OracleMachine
-- name    : LinSysAmp_Supplement_OracleMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:46:43.579076+00:00
-- url     : https://prove2.me/theorems/2f8d0efa-74ab-41e3-a91f-56bd24b5d12e
-- title:
--   A randomized field-operation machine with a general oracle interface (§3.1)
-- statement:
--   This is the model of computation of §3.1 of the paper, with an oracle interface general enough for every reduction of §§4.2, 5, 6 and 8. Fix a finite field $F$ and a type $H$ of **handles**.
--
--   An **oracle interface** fixes, for every mode $m\in\mathbb N$, an input length $\ell(m)$ and a randomized answer map: on $\ell(m)$ field elements and an optional handle it returns a random list of field elements and an optional handle. Modes let one machine reach several oracles (the preprocessing and query algorithms of a data structure, or key-recovery algorithms of every dimension); handles carry states that the machine stores but cannot inspect. Every call samples afresh.
--
--   A **program** is a finite list of instructions over field registers, integer index registers, a field memory indexed by $\mathbb Z$ and handle registers:
--
--   1. field instructions: literal, $+$, $-$, $\times$, inverse (with $0^{-1}=0$), uniform sample from $F$, indirect load and store, jump on equality;
--   2. index instructions: set to $0$, copy, increment, decrement, $+$, $-$, jump on $\le$, unconditional jump;
--   3. a query instruction, which takes the mode from an index register, reads $\ell(m)$ consecutive memory cells and a handle, writes the answer list into memory and stores the returned handle;
--   4. halting with output $\bot$, with a list of memory cells, or with an integer.
--
--   Every executed instruction other than a query costs one **field operation**; a query costs one **call** (counted in total and per mode). Executions are probability distributions over configurations; the input is placed in memory from address $0$ and the parameters in the index registers. The predicate "halts within $N$ steps with at most $c$ calls and $B$ operations" quantifies over every configuration in the support.
--
--   This machine is the published machine of the mission (same instructions and unit costs) with a general oracle in place of a linear-system solver. It lets the cost statements of the supplement's theorems separate the oracle's own time (charged per call) from the reduction's own work.
--
--   **Formalization Note** A program counter outside the program is stuck and charged one operation per step; a halted configuration stutters at no cost, so every step of a running configuration adds one to calls plus operations, and a run with at most $c$ calls and $B$ operations has halted after $\lceil c\rceil+\lceil B\rceil+1$ steps (`stepBudget`). Matrices are stored row-major.
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), §3.1 "Model of computation", p.13 (PDF p.15)

import Mathlib

set_option autoImplicit false

namespace LinSysAmp.Supplement

/-!
# A randomized field-operation machine with a general oracle interface

G. Couteau, N. Melissaris, T. Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and
Fine-Grained Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…), §3.1 "Model of
computation", p.13 (PDF p.15): "We measure running time in field operations. An algorithm can add,
multiply, invert and compare field elements, sample a uniform field element, and read or write a field
element, each in one step. […] A time-T algorithm halts within T steps on every input. When we use an
algorithm as an oracle, each call uses fresh random coins."

**Formalization Note.** This is the machine of the published `LinSysAmp.Machine` (same field and
index instructions, same unit costs, same stuck and halting conventions), plus an order comparison
of field elements (below), with three further changes needed
by the reductions of §§4.2, 5, 6 and 8, whose oracles are not linear-system solvers.

* *Oracle interface.* An `Iface F H` fixes, for every **mode** `m : ℕ`, how many field cells a
  call reads (`inLen m`) and a randomized answer `call m x h` returning a list of field elements
  and an optional **handle** of the opaque type `H`. The mode lets one machine reach several
  oracles: the preprocessing and query algorithms of an OMv data structure (handles carry the
  data structure's state, which the machine cannot inspect), or the key-recovery algorithms `P_c`
  of every dimension `c`. Each call samples afresh from the oracle's distribution.
* *Query instruction.* `query m a h d h'` takes the mode from index register `m`
  (`Int.toNat`), reads `inLen` cells from address `ireg a`, passes the handle in handle register
  `h`, writes the answer list from address `ireg d`, and stores the returned handle in handle
  register `h'`. It adds `1` to the total call counter `calls` and to the per-mode counter
  `callsAt mode`, and nothing to `ops`.
* *Outputs.* `halt` outputs `⊥` (`none`); `haltOut a l` outputs the list of the `ireg l` cells
  (`Int.toNat`) from address `ireg a`; `haltInt r` outputs the integer in index register `r`.
* *Input layout* (`initConfig par input`): index register `i` holds `par[i]` (else `0`), memory
  cell `i ≥ 0` holds `input[i]` (else `0`), negative cells, field registers, handle registers and
  all counters are `0`/`none`, the program counter is `0`.
* *Order comparison.* §3.1 lets an algorithm "compare field elements", and the proofs of
  Lemma 6.2 and Lemma 6.4 sort field values "for any fixed total order on F_q" in
  `O(t log t)` operations. Besides the equality jump `jeq`, the machine therefore has `jle a b L`,
  which jumps to `L` when `reg a ≤ reg b` in the fixed total order `fieldLE` on `F` (the order
  transported from `Fin (card F)` by `Fintype.equivFin F`); it costs `1` like every comparison.
* Every executed instruction other than `query` costs `1` in `ops`; a program counter outside
  the program is stuck and costs `1` per step; a halted configuration stutters at no cost.
  Executions are probability mass functions; `run I P N σ` is the distribution after `N` steps.
-/

/-- An oracle interface over the field `F` with handle type `H`: in mode `m` a call reads
`inLen m` field cells and an optional handle, and returns a random list of field cells and an
optional handle. Each call samples afresh.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
structure Iface (F : Type*) (H : Type*) where
  inLen : ℕ → ℕ
  call : ℕ → List F → Option H → PMF (List F × Option H)

/-- The instructions of the machine (see the module note).
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
inductive OInstr (F : Type*) where
  | const (d : ℕ) (c : F)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | mul (d a b : ℕ)
  | inv (d a : ℕ)
  | sample (d : ℕ)
  | load (d i : ℕ)
  | store (i a : ℕ)
  | jeq (a b L : ℕ)
  | jle (a b L : ℕ)
  | iset0 (d : ℕ)
  | icopy (d a : ℕ)
  | iinc (d : ℕ)
  | idec (d : ℕ)
  | iadd (d a b : ℕ)
  | isub (d a b : ℕ)
  | ijle (a b L : ℕ)
  | jmp (L : ℕ)
  | query (m a h d h' : ℕ)
  | halt
  | haltOut (a l : ℕ)
  | haltInt (r : ℕ)

/-- A program: a finite list of instructions.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
abbrev OProgram (F : Type*) := List (OInstr F)

/-- An output: a list of field elements, or an integer.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
inductive Out (F : Type*) where
  | vec (l : List F)
  | int (z : ℤ)

/-- Whether a run is still going, or has halted with an output (`none` is `⊥`).
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
inductive OStatus (F : Type*) where
  | running
  | done (out : Option (Out F))

/-- A machine configuration.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
structure OConfig (F : Type*) (H : Type*) where
  pc : ℕ
  reg : ℕ → F
  ireg : ℕ → ℤ
  mem : ℤ → F
  hreg : ℕ → Option H
  ops : ℕ
  calls : ℕ
  callsAt : ℕ → ℕ
  status : OStatus F

variable {F H : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The fixed total order on the field used by the comparison instruction `jle`: `a ≤ b` iff the
index of `a` is at most the index of `b` under the fixed enumeration `Fintype.equivFin F`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15); proofs of Lemma 6.2,
p.37 (PDF p.39), and Lemma 6.4, p.39 (PDF p.41): "for any fixed total order on F_q".) -/
noncomputable def fieldLE (a b : F) : Prop :=
  ((Fintype.equivFin F a : ℕ) ≤ (Fintype.equivFin F b : ℕ))

/-- The list of the `len` cells from address `base`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def readList (mem : ℤ → F) (base : ℤ) (len : ℕ) : List F :=
  (List.range len).map fun i => mem (base + (i : ℤ))

/-- Write the list `l` at addresses `base, …, base + l.length − 1`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def writeList (mem : ℤ → F) (base : ℤ) (l : List F) : ℤ → F :=
  fun x => if base ≤ x ∧ x < base + (l.length : ℤ) then l.getD (x - base).toNat 0 else mem x

/-- Advance the program counter and charge one field operation.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def OConfig.tick (σ : OConfig F H) : OConfig F H :=
  { σ with pc := σ.pc + 1, ops := σ.ops + 1 }

/-- Charge one field operation and jump to `L`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def OConfig.jumpTo (σ : OConfig F H) (L : ℕ) : OConfig F H :=
  { σ with pc := L, ops := σ.ops + 1 }

/-- One execution step of instruction `ins` from a running configuration.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
noncomputable def oexec (I : Iface F H) (ins : OInstr F) (σ : OConfig F H) : PMF (OConfig F H) :=
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
  | .jle a b L =>
      PMF.pure (if (Fintype.equivFin F (σ.reg a) : ℕ) ≤ (Fintype.equivFin F (σ.reg b) : ℕ)
        then σ.jumpTo L else σ.tick)
  | .iset0 d => PMF.pure { σ.tick with ireg := Function.update σ.ireg d 0 }
  | .icopy d a => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg a) }
  | .iinc d => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg d + 1) }
  | .idec d => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg d - 1) }
  | .iadd d a b => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg a + σ.ireg b) }
  | .isub d a b => PMF.pure { σ.tick with ireg := Function.update σ.ireg d (σ.ireg a - σ.ireg b) }
  | .ijle a b L => PMF.pure (if σ.ireg a ≤ σ.ireg b then σ.jumpTo L else σ.tick)
  | .jmp L => PMF.pure (σ.jumpTo L)
  | .query m a h d h' =>
      let mode := (σ.ireg m).toNat
      (I.call mode (readList σ.mem (σ.ireg a) (I.inLen mode)) (σ.hreg h)).map fun r =>
        { σ with
          pc := σ.pc + 1
          calls := σ.calls + 1
          callsAt := Function.update σ.callsAt mode (σ.callsAt mode + 1)
          mem := writeList σ.mem (σ.ireg d) r.1
          hreg := Function.update σ.hreg h' r.2 }
  | .halt => PMF.pure { σ with ops := σ.ops + 1, status := .done none }
  | .haltOut a l =>
      PMF.pure { σ with
        ops := σ.ops + 1
        status := .done (some (.vec (readList σ.mem (σ.ireg a) (σ.ireg l).toNat))) }
  | .haltInt r =>
      PMF.pure { σ with ops := σ.ops + 1, status := .done (some (.int (σ.ireg r))) }

/-- One step of program `P`: a halted configuration stutters at no cost; an invalid program counter
is stuck and charged one operation; otherwise the instruction at `pc` is executed.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
noncomputable def ostep (I : Iface F H) (P : OProgram F) (σ : OConfig F H) : PMF (OConfig F H) :=
  match σ.status with
  | .done _ => PMF.pure σ
  | .running =>
      match P[σ.pc]? with
      | none => PMF.pure { σ with ops := σ.ops + 1 }
      | some ins => oexec I ins σ

/-- The distribution of the configuration after `N` steps from `σ`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
noncomputable def orun (I : Iface F H) (P : OProgram F) : ℕ → OConfig F H → PMF (OConfig F H)
  | 0, σ => PMF.pure σ
  | N + 1, σ => (orun I P N σ).bind (ostep I P)

/-- The input layout: index register `i` holds `par[i]` (else `0`), memory cell `i ≥ 0` holds
`input[i]` (else `0`); everything else is `0` or empty.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def oinit (par : List ℤ) (input : List F) : OConfig F H where
  pc := 0
  reg := fun _ => 0
  ireg := fun r => par.getD r 0
  mem := fun x => if 0 ≤ x then input.getD x.toNat 0 else 0
  hreg := fun _ => none
  ops := 0
  calls := 0
  callsAt := fun _ => 0
  status := .running

/-- Every run of `N` steps from `σ₀` (every configuration in the support) has halted, made at most
`c` oracle calls in total and at most `B` field operations.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def OHaltsWithin (I : Iface F H) (P : OProgram F) (σ₀ : OConfig F H) (N : ℕ) (c : ℝ) (B : ℝ) :
    Prop :=
  ∀ σ ∈ (orun I P N σ₀).support, σ.status ≠ .running ∧ (σ.calls : ℝ) ≤ c ∧ (σ.ops : ℝ) ≤ B

/-- The probability that the run of `N` steps from `σ₀` has halted with output `some o`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
noncomputable def oOutputProb (I : Iface F H) (P : OProgram F) (σ₀ : OConfig F H) (N : ℕ)
    (o : Out F) : ℝ :=
  ((orun I P N σ₀).map OConfig.status (.done (some o))).toReal

/-- The step budget used throughout: a run with at most `c` calls and `B` operations has halted
after `⌈c⌉ + ⌈B⌉ + 1` steps (every running step adds `1` to `ops + calls`).
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
noncomputable def stepBudget (c B : ℝ) : ℕ := ⌈c⌉₊ + ⌈B⌉₊ + 1

/-- Row-major list of the entries of an `n × n` matrix.
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def flatMat {n : ℕ} (A : Matrix (Fin n) (Fin n) F) : List F :=
  (List.finRange n).flatMap fun i => (List.finRange n).map fun j => A i j

/-- The `n × n` matrix stored row-major in a list from offset `off` (missing entries are `0`).
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def unflatMat (n : ℕ) (x : List F) (off : ℕ) : Matrix (Fin n) (Fin n) F :=
  fun i j => x.getD (off + n * i + j) 0

/-- The length-`n` vector stored in a list from offset `off` (missing entries are `0`).
(arXiv:2611.04680, version held, sha256 af7a90ac…, §3.1, p.13 (PDF p.15).) -/
def unflatVec (n : ℕ) (x : List F) (off : ℕ) : Fin n → F :=
  fun i => x.getD (off + i) 0

end LinSysAmp.Supplement


