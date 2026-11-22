-- Prove2me | Definitions.Def_DecrNbhdCover_Supplement_Oracle
-- name    : DecrNbhdCover_Supplement_Oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:29:58.122817+00:00
-- url     : https://prove2.me/theorems/e174798b-31cd-4ed0-915b-085cf01a71b7
-- title:
--   Reductions with black-box access to an algorithm: the oracle word RAM
-- statement:
--   A **reduction** is a program of the word RAM of the mission extended by four instructions, and it runs against an **oracle**, which is a program $A$ of that word RAM.
--
--   1. `spawn` creates a new **instance** of $A$, with its own memory, all zero, and returns its number.
--   2. `send` appends one word to the input of an instance and lets that instance run until it is about to read an input word that it has not been sent, or halts.
--   3. `avail` returns the number of output words of an instance that have not been received yet.
--   4. `recv` returns the next such word.
--
--   The only information that flows from $A$ to the reduction is the sequence of words that the instances write, which is what an online algorithm reports to its user. The reduction is a fixed list of instructions, independent of the code of $A$. An instance never sees a word before it is sent and is never shown an end marker.
--
--   Every executed instruction costs one step, including every instruction executed by an instance, and one more step is charged when control returns from an instance to the reduction. The time of a run is its number of steps, so the time of a reduction includes the time of all its oracle instances. The reduction and all instances have the same word size. Windows, their outputs and their times are defined from the reads of the session input by the reduction itself, as in the published session module.
--
--   This gives a precise meaning to "the algorithm is given black-box access to an $(\alpha,s,T)$-neighborhood-cover algorithm" in Theorems 9.2 and 9.3.
--
--   **Formalization Note** The paper names no machine and does not define black-box access; this is the reading used. An oracle instruction that names an instance that does not exist changes no instance. A reduction is deterministic when it has no `rand` instruction; the instances run on a constant random tape, which a `rand`-free oracle never reads.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), §9, p.67 (PDF 71); Theorems 9.2, 9.3, pp.67–68 (PDF 71–72)

import Mathlib
import Definitions.Def_DecrNbhdCover_Session
import Definitions.Def_DecrNbhdCover_Supplement_FullyDynamic

set_option autoImplicit false

namespace DecrNbhdCover.Supplement

open DynConnWC

/-! # Reductions with black-box access to an algorithm (Theorems 9.2 and 9.3)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), §9, p.67 (PDF 71): "In this section we provide a black-box reduction from
fully dynamic APSP to neighborhood cover in decremental graphs"; Theorem 9.2, p.67: "The algorithm is additionally given black-box
access to an (α, s, T)-neighborhood-cover algorithm."

**Formalization Note.** The paper names no machine and does not define black-box access. A **reduction** is a program `R` of the word RAM
of the mission extended by four instructions, and it runs against an **oracle**: a program `A` of the same word RAM, which `R` never sees.
`spawn` creates a new instance of `A` (its own memory, all zero, nothing read, nothing written) and returns its number; `send` appends one
word to the input of an instance and lets that instance run until it is about to read an input word it has not been sent, or halts;
`avail` returns how many output words of an instance have not been received yet; `recv` returns the next such word. So the only
information that flows from `A` to `R` is the sequence of words the instances write, exactly what an online algorithm reports to its
user, and `R` is fixed independently of the code of `A`. An instance runs online: it never sees a word before it is sent, and it is
never shown an end marker. Every instruction executed costs one step, **including every instruction executed by an instance**, and one
further step is charged when control returns from an instance to `R`; the time of a run is its number of steps, so the time of `R`
includes the time of all its oracle instances. `R` and all instances have the same word size `W`. Instances use the constant tape
`zeroTape` (the oracle is `rand`-free where this is used). Windows, their outputs and their times are defined for the run of `R` on the
session input exactly as in the published session module: window `k` runs from the step at which `R` reads the first word of block `k`
(step `0` for `k = 0`) to the step at which it reads the first word of block `k + 1`. -/

/-- The instructions of a reduction: those of the word RAM, and the four oracle instructions. `[i]` denotes memory cell `i` of the
reduction. -/
inductive OInstr where
  /-- an instruction of the word RAM -/
  | base (i : Instr)
  /-- `[i] :=` the number of a new instance of the oracle -/
  | spawn (i : ℕ)
  /-- append the word `[j]` to the input of instance `[i]`, and let the instance run -/
  | send (i j : ℕ)
  /-- `[i] :=` the number of output words of instance `[j]` not yet received -/
  | avail (i j : ℕ)
  /-- `[i] :=` the next output word of instance `[j]` not yet received (the all-ones word if there is none) -/
  | recv (i j : ℕ)

/-- A reduction is a finite list of instructions; execution starts at index `0`. -/
abbrev OProgram := List OInstr

/-- The word-RAM instruction of a `base` instruction (`halt` for an oracle instruction; used only at `base` instructions). -/
def OInstr.toBase : OInstr → Instr
  | .base i => i
  | _ => Instr.halt

/-- The reduction contains no `rand` instruction: it is deterministic. -/
def ONoRand (R : OProgram) : Prop :=
  ∀ i, OInstr.base (Instr.rand i) ∉ R

/-- An instance of the oracle: its configuration, the words sent to it so far, and the number of its output words already received. -/
structure Inst (W : ℕ) where
  cfg : Config W
  inp : List ℕ
  taken : ℕ

/-- The instance cannot continue: it has halted, or it is about to read an input word that has not been sent. -/
def Inst.waiting {W : ℕ} (A : Program) (x : Inst W) : Bool :=
  match A[x.cfg.pc]? with
  | none => true
  | some Instr.halt => true
  | some (Instr.read _) => decide (x.inp.length ≤ x.cfg.reads)
  | some _ => false

/-- A configuration of a reduction running against an oracle: the configuration of the reduction, the instances created so far, and the
instance that is currently running (`none` when the reduction itself is running). -/
structure OConfig (W : ℕ) where
  main : Config W
  insts : List (Inst W)
  active : Option ℕ

/-- One step of the reduction `R` with oracle `A` on the input words `inp`. While an instance is active, a step executes one instruction
of that instance, or returns control to `R` if the instance cannot continue. Otherwise a step executes one instruction of `R`. An oracle
instruction naming an instance that does not exist has no effect on the instances (`avail` then returns `0` and `recv` the all-ones
word). A halted configuration is left unchanged. -/
def oStep {W : ℕ} (R : OProgram) (A : Program) (inp : List ℕ) (c : OConfig W) : OConfig W :=
  match c.active with
  | some a =>
    match c.insts[a]? with
    | none => { c with active := none }
    | some x =>
      if x.waiting A then { c with active := none }
      else { c with insts := c.insts.set a { x with cfg := step A x.inp (zeroTape W) x.cfg } }
  | none =>
    match R[c.main.pc]? with
    | none => c
    | some (.base _) => { c with main := step (R.map OInstr.toBase) inp (zeroTape W) c.main }
    | some (.spawn i) =>
      { c with main := c.main.assign i (BitVec.ofNat W c.insts.length)
               insts := c.insts ++ [⟨initConfig W, [], 0⟩] }
    | some (.send i j) =>
      match c.insts[(c.main.mem i).toNat]? with
      | none => { c with main := { c.main with pc := c.main.pc + 1 } }
      | some x =>
        { main := { c.main with pc := c.main.pc + 1 }
          insts := c.insts.set (c.main.mem i).toNat { x with inp := x.inp ++ [(c.main.mem j).toNat] }
          active := some (c.main.mem i).toNat }
    | some (.avail i j) =>
      match c.insts[(c.main.mem j).toNat]? with
      | none => { c with main := c.main.assign i 0 }
      | some x => { c with main := c.main.assign i (BitVec.ofNat W (x.cfg.output.length - x.taken)) }
    | some (.recv i j) =>
      match c.insts[(c.main.mem j).toNat]? with
      | none => { c with main := c.main.assign i (BitVec.allOnes W) }
      | some x =>
        match x.cfg.output[x.taken]? with
        | none => { c with main := c.main.assign i (BitVec.allOnes W) }
        | some w =>
          { c with main := c.main.assign i (BitVec.ofNat W w)
                   insts := c.insts.set (c.main.mem j).toNat { x with taken := x.taken + 1 } }

/-- The initial configuration: the reduction at its start, and no instance. -/
def oInit (W : ℕ) : OConfig W := ⟨initConfig W, [], none⟩

/-- The configuration after `t` steps of `R` with oracle `A` on the input words `inp`. -/
def oConf (W : ℕ) (R : OProgram) (A : Program) (inp : List ℕ) (t : ℕ) : OConfig W :=
  (oStep R A inp)^[t] (oInit W)

/-- The `k`-th `read` executed by the reduction itself (counting from `1`) is the instruction executed at step `t`. -/
def OReadsAt (W : ℕ) (R : OProgram) (A : Program) (inp : List ℕ) (k t : ℕ) : Prop :=
  (oConf W R A inp t).active = none ∧
    (∃ i, R[(oConf W R A inp t).main.pc]? = some (.base (Instr.read i))) ∧
    (oConf W R A inp t).main.reads + 1 = k

open Classical in
/-- The step at which the reduction executes its `k`-th `read` (`none` if the run never executes it). -/
noncomputable def oReadStep (W : ℕ) (R : OProgram) (A : Program) (inp : List ℕ) (k : ℕ) : Option ℕ :=
  if h : ∃ t, OReadsAt W R A inp k t then some (Nat.find h) else none

/-- The run executes every read of the session input up to the end marker. -/
def ORunsThrough (W : ℕ) (R : OProgram) (A : Program) (blocks : List (List ℕ)) : Prop :=
  ∀ k ≤ blocks.length, (oReadStep W R A blocks.flatten (startRead blocks k)).isSome

/-- The step at which window `k` starts. -/
noncomputable def oWStart (W : ℕ) (R : OProgram) (A : Program) (blocks : List (List ℕ)) (k : ℕ) : ℕ :=
  if k = 0 then 0 else (oReadStep W R A blocks.flatten (startRead blocks k)).getD 0

/-- The step at which window `k` ends. -/
noncomputable def oWEnd (W : ℕ) (R : OProgram) (A : Program) (blocks : List (List ℕ)) (k : ℕ) : ℕ :=
  (oReadStep W R A blocks.flatten (startRead blocks (k + 1))).getD 0

/-- The number of steps of window `k`, the steps of the oracle instances included. -/
noncomputable def oWTime (W : ℕ) (R : OProgram) (A : Program) (blocks : List (List ℕ)) (k : ℕ) : ℕ :=
  oWEnd W R A blocks k - oWStart W R A blocks k

/-- The words written by the reduction in window `k`. -/
noncomputable def oWOutput (W : ℕ) (R : OProgram) (A : Program) (blocks : List (List ℕ)) (k : ℕ) : List ℕ :=
  (oConf W R A blocks.flatten (oWEnd W R A blocks k)).main.output.drop
    (oConf W R A blocks.flatten (oWStart W R A blocks k)).main.output.length

end DecrNbhdCover.Supplement


