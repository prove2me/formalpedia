-- Prove2me | Definitions.Def_OptAbstention_TLA_Machine
-- name    : OptAbstention_TLA_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:07:07.834072+00:00
-- url     : https://prove2.me/theorems/a30b1502-83ef-496a-bb59-5277da2f94f4
-- title:
--   The randomized sampling real RAM: real-RAM core, uniform tape, labeled-example draws and halting
-- statement:
--   Algorithms are programs of a unit-cost real RAM: the published core (exact $+,-,\times,\div$, comparison jumps, integer pointer registers, indirect real memory), with rational literals only, extended by a pointer-to-real cast, `unif` (the next real of an i.i.d. uniform $[0,1]$ tape, one step), `sample` (writes the $d$ coordinates and the $\pm1$ label of the next labeled example to $d+1$ consecutive cells; cost $d+1$ steps; counts one sample) and `halt`. There is no square root, exponential, logarithm, floor, real-to-integer conversion or linear-programming instruction.
--
--   The random inputs are the example stream, with law $\bar D^{\mathbb N}$, and the tape, with law $\mathrm{Unif}[0,1]^{\mathbb N}$, independent. A program that runs off its end never halts. `HaltsWithin P d ξ ν S T N` says the run from $S$ halts after at most $T$ charged steps and at most $N$ samples; `finalState` is the halted state (or none).
--
--   **Formalization Note.** Running time is the number of charged steps; sample complexity is the number of `sample` instructions executed. Memory layouts of inputs and outputs are fixed in the learner and selector modules.
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 2, Definition 1.1; p. 13, Theorems 6.1, 6.2; pp. 49, 51, Lemmas F.2, F.3 (the paper names no machine)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_OptAbstention_TLA_Sandwiching

/-!
# The randomized sampling real RAM

Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, *Achieving the Optimal Abstention Rate
for Learning with Distribution Shift*, STOC 2027 submission (manuscript sha256 0fb30af1…):
Definition 1.1 (p. 2: the algorithm draws i.i.d. labeled samples and uses its own randomness),
Theorem 6.1 (p. 13: "sample complexity", "runtime"), Theorem 6.2 (p. 13), Lemmas F.2 and F.3
(pp. 49, 51: "randomized algorithm", "runs in time"). The paper names no machine; this file fixes
one.

Encoding.
* The core is the published real RAM `SmaleNinth.RAMInstr` (exact `+ − × ÷`, comparison jumps,
  integer pointer registers, indirect real memory). `Admissible` restricts its real literals to
  rationals and forbids its own `accept`/`reject`.
* Added instructions: `pointerReal` (pointer-to-real cast, one step); `unif` (writes the next real
  of a uniform `[0, 1]` tape, one step); `sample` (writes the `d` coordinates and the `±1` label of
  the next labeled example to the `d + 1` cells starting at the address held in a pointer; cost
  `d + 1`; counts one sample); `halt` (one step). There is no square root, exponential, logarithm,
  floor, real-to-integer conversion or linear-programming instruction.
* Random inputs: the example stream `ξ : ℕ → ℝ^d × Bool` (law `D̄^ℕ`) and the uniform tape
  `ν : ℕ → [0, 1]` (law `Unif[0,1]^ℕ`), independent. The `i`-th `sample` reads `ξ i`, the `i`-th
  `unif` reads `ν i`.
* A program that runs off its end is stuck: every further step is charged and it never halts. A
  halted state is left unchanged, so the final state is the state at any time after halting.
* Inputs and outputs are blocks of memory cells (`blockMem`); the layouts are fixed in the
  learner module.
-/

open MeasureTheory

namespace OptAbstention.TLA

/-- An instruction of the randomized sampling real RAM. -/
inductive Instr where
  /-- An instruction of the published real-RAM core. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `r[dst] := (p[src] : ℝ)`. -/
  | pointerReal (dst src : ℕ)
  /-- `r[dst] :=` the next real of the uniform `[0, 1]` tape. -/
  | unif (dst : ℕ)
  /-- `M[p[addr] + j] :=` coordinate `j` of the next labeled example (`j < d`) and
  `M[p[addr] + d] :=` its label `±1` (cost `d + 1`, one sample). -/
  | sample (addr : ℕ)
  /-- Halt. -/
  | halt

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Rational literals only, and none of the core's own `accept`/`reject`. -/
def Admissible (P : Program) : Prop :=
  ∀ i ∈ P, (∀ dst c, i = .core (.const dst c) → ∃ q : ℚ, c = (q : ℝ)) ∧
    i ≠ .core .accept ∧ i ≠ .core .reject

/-- The program draws no labeled examples. -/
def NoSample (P : Program) : Prop :=
  ∀ i ∈ P, ∀ addr, i ≠ .sample addr

/-- A machine state: the core configuration, the cost counters and the halting flag. -/
structure State where
  /-- Program counter, real registers, pointer registers and memory. -/
  cfg : SmaleNinth.RAMConfig
  /-- Number of labeled examples drawn. -/
  samples : ℕ
  /-- Number of uniform reals drawn. -/
  unifs : ℕ
  /-- Number of time steps. -/
  work : ℕ
  /-- Whether the machine has halted. -/
  halted : Bool

/-- The labeled-example stream. -/
abbrev ExStream (d : ℕ) := ℕ → Pt d × Bool

/-- The uniform tape. -/
abbrev Tape := ℕ → unitInterval

/-- The core instruction at a position (non-core positions are never passed to the core). -/
def Instr.coreOf : Instr → SmaleNinth.RAMInstr
  | .core i => i
  | _ => .accept

/-- Memory with the labeled example `e` written to cells `b, …, b + d` (coordinates, then the
label `±1`). -/
noncomputable def writeExample {d : ℕ} (mem : ℤ → ℝ) (b : ℤ) (e : Pt d × Bool) : ℤ → ℝ :=
  fun j => if h : b ≤ j ∧ j < b + (d : ℤ) then e.1 ⟨(j - b).toNat, by omega⟩
    else if j = b + (d : ℤ) then signOf e.2 else mem j

/-- One step of program `P` in dimension `d` on the example stream `ξ` and the tape `ν`. -/
noncomputable def step (P : Program) (d : ℕ) (ξ : ExStream d) (ν : Tape) (S : State) : State :=
  if S.halted then S else
    let r := S.cfg.regs
    match P[S.cfg.pc]? with
    | none => { S with work := S.work + 1 }
    | some (.core _) =>
        { S with cfg := SmaleNinth.RAMStep (P.map Instr.coreOf) S.cfg, work := S.work + 1 }
    | some (.pointerReal dst src) =>
        { S with cfg := { S.cfg with pc := S.cfg.pc + 1,
                                     regs := Function.update r dst (S.cfg.ptrs src : ℝ) },
                 work := S.work + 1 }
    | some (.unif dst) =>
        { S with cfg := { S.cfg with pc := S.cfg.pc + 1,
                                     regs := Function.update r dst (ν S.unifs : ℝ) },
                 unifs := S.unifs + 1, work := S.work + 1 }
    | some (.sample addr) =>
        { S with cfg := { S.cfg with pc := S.cfg.pc + 1,
                                     mem := writeExample S.cfg.mem (S.cfg.ptrs addr) (ξ S.samples) },
                 samples := S.samples + 1, work := S.work + (d + 1) }
    | some .halt => { S with halted := true, work := S.work + 1 }

/-- The state after `t` iterations. -/
noncomputable def run (P : Program) (d : ℕ) (ξ : ExStream d) (ν : Tape) (S : State) (t : ℕ) :
    State :=
  (step P d ξ ν)^[t] S

/-- `P` started in `S` halts within `T` steps having drawn at most `N` samples. -/
def HaltsWithin (P : Program) (d : ℕ) (ξ : ExStream d) (ν : Tape) (S : State) (T N : ℝ) :
    Prop :=
  ∃ t, (run P d ξ ν S t).halted = true ∧ ((run P d ξ ν S t).work : ℝ) ≤ T ∧
    ((run P d ξ ν S t).samples : ℝ) ≤ N

open Classical in
/-- The final state of `P` started in `S`, or `none` if it never halts. -/
noncomputable def finalState (P : Program) (d : ℕ) (ξ : ExStream d) (ν : Tape) (S : State) :
    Option State :=
  if h : ∃ t, (run P d ξ ν S t).halted = true then some (run P d ξ ν S (Nat.find h)) else none

/-- The start state with pointer registers `ptrs` and memory `mem`; real registers `0`. -/
def initState (ptrs : ℕ → ℤ) (mem : ℤ → ℝ) : State :=
  ⟨⟨0, fun _ => 0, ptrs, mem⟩, 0, 0, 0, false⟩

/-- Memory holding a block of `n` records of width `w` from cell `base` on (record `i`, field `j`
in cell `base + i·w + j`), and `rest` elsewhere. -/
def blockMem (base : ℤ) (w n : ℕ) (cell : Fin n → Fin w → ℝ) (rest : ℤ → ℝ) : ℤ → ℝ :=
  fun j =>
    if base ≤ j then
      if h1 : (j - base).toNat / w < n then
        if h2 : (j - base).toNat % w < w then cell ⟨_, h1⟩ ⟨_, h2⟩ else rest j
      else rest j
    else rest j

/-- The example law `D̄` pushed to `ℝ^d × Bool`. -/
noncomputable def exampleLaw {d : ℕ} {X : Set (Pt d)} (Dbar : Measure (X × Bool)) :
    Measure (Pt d × Bool) :=
  Dbar.map fun p => ((p.1 : Pt d), p.2)

/-- The law of the uniform tape, `Unif[0,1]^ℕ`. -/
noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)

/-- The joint law of the two independent random inputs: `D̄^ℕ ⊗ Unif[0,1]^ℕ`. -/
noncomputable def streamLaw {d : ℕ} {X : Set (Pt d)} (Dbar : Measure (X × Bool))
    [IsProbabilityMeasure Dbar] : Measure (ExStream d × Tape) :=
  haveI : IsProbabilityMeasure (exampleLaw Dbar) :=
    Measure.isProbabilityMeasure_map
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd).aemeasurable
  (Measure.infinitePi fun _ : ℕ => exampleLaw Dbar).prod tapeLaw

/-- The fixed example stream given to programs that draw no samples. -/
def noExamples (d : ℕ) : ExStream d := fun _ => (0, false)

end OptAbstention.TLA


