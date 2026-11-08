-- Prove2me | Definitions.Def_NNPartTree_Machine
-- name    : NNPartTree_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:07:10.886274+00:00
-- url     : https://prove2.me/theorems/0b8a140b-fcb3-478c-b0bf-73cdb6afdf83
-- title:
--   The randomized sampling real RAM with integer memory
-- statement:
--   The model of computation in which "there is an algorithm" is read. The paper names no machine.
--
--   A program is one finite list of instructions, the same for every input. The machine has real registers, integer pointer registers, a random-access real memory and a random-access integer memory, both indexed by $\mathbb Z$. Its instructions are:
--
--   1. exact $+,-,\times,\div$ on reals (with $x/0=0$), rational literals, indirect real load and store through pointers, pointer set, copy, increment and decrement, and the comparison jumps $r_i\le 0$ and $p_q\le p_{q'}$ (the published real-RAM core);
--   2. integer load and store, $p_d:=I[p_a]$ and $I[p_a]:=p_b$;
--   3. a pointer-to-real cast $r_d:=p_q$, and $r_d:=\sqrt{r_a}$;
--   4. a fair coin $r_d\in\{0,1\}$;
--   5. $\mathrm{sample}\ q$, which writes the next unread sample $X_k\in\mathbb R^s$ to the real cells $p_q,\dots,p_q+s-1$;
--   6. halt.
--
--   There is no floor, real-to-integer cast, exponential, logarithm, Gaussian draw, uniform real, or pointer addition or multiplication, and no instruction carries a function. Every executed instruction costs one unit of work except $\mathrm{sample}$, which costs $s$. An invalid program counter is stuck and charged, and after halt the state stutters at no cost.
--
--   Integer memory is what gives constant-time indirect access. Without it a pointer moves by at most one per step, so a query of work $o(nd)$ could neither read most stored points nor write most indices below $n$ into a register, and Theorem 4 would fail for that trivial reason.
--
--   **Formalization Note** The core is the published `SmaleNinth.RAMInstr`. `Admissible` requires rational literals and excludes the core `accept`/`reject`, restricting the existentially chosen program only. `NoSample` also excludes `sample`, and `DetProgram` further excludes `coin`. Coins are read from an infinite tape, one bit per `coin`; samples come from a separate stream, the $k$-th executed `sample` reading entry $k$.
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Theorem 3, p.14 ("receives sample access"), and Theorem 4, p.27 ("There exists a polynomial-time algorithm"); no machine is named

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory

namespace NNPartTree

/-!
# The randomized sampling real RAM with integer memory

S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*,
arXiv:2607.09909 (STOC 2027 submission), held copy of 2026-11-03, sha256 d32992f2…. Theorem 4, p.27,
says "There exists a polynomial-time algorithm … and sample-access to a nearest neighbor pair
distribution", and Theorem 3, p.14, says "receives sample access". No machine is named, so this model
is a reading of those sentences.

**Formalization Note.**
* The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ` (exact `+ − × ÷`,
  literals, indirect load and store through integer pointers, pointer set, copy, increment and
  decrement, the comparison jumps `r ≤ 0` and `p ≤ p'`). The extensions are integer memory, a
  pointer-to-real cast, `√`, a fair coin, `sample` and `halt`.
* Integer memory is what makes indirect access constant-time. Without it a pointer moves by at most
  one per step, so in `t` steps a pointer stays within `t` plus a program constant of `0`. A query of
  work `o(nd)` could then neither read most stored points nor write most answers `k < n` into a pointer
  register, and Theorem 4 would be false on such a machine for a trivial reason: take `d = 1` with `D`
  uniform on self-pairs of `n` points.
* There is no floor, real-to-integer cast, exp, log, Gaussian draw, uniform real, pointer addition or
  pointer multiplication, and no constructor carries a function. Real literals are rational
  (`Admissible`); this restricts the existentially chosen program, never the input.
* `sample q` writes the next unread sample `X_k ∈ ℝˢ` to the real cells `p[q], …, p[q] + s − 1`. It is
  the only access a program has to the unknown distribution, and it costs `s` units of `work`. Every
  other executed instruction costs one unit. An invalid program counter is stuck and charged, so only
  `halt` halts. After `halt` the state stutters at no cost. `samplesUsed` counts executed `sample`s.
* Randomness is a tape of independent fair bits, one bit per executed `coin`, and a separate sample
  stream, the `k`-th executed `sample` reading entry `k`.
-/

/-- The ambient space `ℝᵈ` (Section 3.1, p.10). -/
abbrev Pt (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- An instruction. Register, pointer and label arguments are natural numbers; no constructor
carries a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]` (integer memory).
* `pointerReal d q`: `r[d] := (p[q] : ℝ)`.
* `sqrt d a`: `r[d] := √r[a]` (`Real.sqrt`, so `√x = 0` for `x < 0`).
* `coin d`: `r[d] := 1` if the next tape bit is `true`, else `0`.
* `sample q`: `M[p[q] + i] := X_k i` for `i < s`, where `X_k` is the next unread sample.
* `halt`: stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | sqrt (dst src : ℕ)
  | coin (dst : ℕ)
  | sample (pointer : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every dimension and every input. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core halting instructions `accept`/`reject` do not
occur (the machine stops only through `halt`). -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- An admissible program without `sample`: its data arrive in its input. It may flip coins. -/
def NoSample (P : Program) : Prop :=
  Admissible P ∧ ∀ op ∈ P, ∀ q, op ≠ Instr.sample q

/-- An admissible program with neither `sample` nor `coin`: its run is a function of its input. -/
def DetProgram (P : Program) : Prop :=
  NoSample P ∧ ∀ op ∈ P, ∀ r, op ≠ Instr.coin r

/-- The static core table of `P`: extension instructions are placeholders here and are always
dispatched by `step`. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: the core configuration (program counter, real registers, pointers, real memory),
integer memory, the coin-tape cursor, the number of samples read so far, the halted flag and the work
counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  coinCursor : ℕ
  samplesUsed : ℕ
  halted : Bool
  work : ℕ

/-- Write the sample `x ∈ ℝˢ` to the real cells `base, …, base + s − 1`. -/
noncomputable def writeSample {s : ℕ} (mem : ℤ → ℝ) (base : ℤ) (x : Pt s) : ℤ → ℝ :=
  fun a => if h : base ≤ a ∧ a - base < s then
      x ⟨(a - base).toNat, by omega⟩
    else mem a

/-- One step of program `P` with sample dimension `s`, on coin tape `coins` and sample stream `xs`.
Halted states stutter at no cost; `sample` costs `s`, every other step costs `1`. -/
noncomputable def step (P : Program) (s : ℕ) (coins : ℕ → Bool) (xs : ℕ → Pt s) (st : State) : State :=
  if st.halted then st else
    let t : State := { st with
      work := st.work + 1
      core := { st.core with pc := st.core.pc + 1 } }
    let setReg (d : ℕ) (v : ℝ) : State :=
      { t with core := { t.core with regs := Function.update st.core.regs d v } }
    match P[st.core.pc]? with
    | none => { st with work := st.work + 1 }
    | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) st.core }
    | some (.integerLoad d a) =>
        { t with core := { t.core with
            ptrs := Function.update st.core.ptrs d (st.integerMemory (st.core.ptrs a)) } }
    | some (.integerStore a b) =>
        { t with integerMemory := Function.update st.integerMemory (st.core.ptrs a) (st.core.ptrs b) }
    | some (.pointerReal d q) => setReg d (st.core.ptrs q : ℝ)
    | some (.sqrt d a) => setReg d (Real.sqrt (st.core.regs a))
    | some (.coin d) =>
        { setReg d (if coins st.coinCursor then 1 else 0) with coinCursor := st.coinCursor + 1 }
    | some (.sample q) =>
        { t with
          work := st.work + s
          samplesUsed := st.samplesUsed + 1
          core := { t.core with
            mem := writeSample st.core.mem (st.core.ptrs q) (xs st.samplesUsed) } }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` from `s₀`, on the randomness `ω = (coin tape, sample stream)`. -/
noncomputable def run (P : Program) (s : ℕ) (s₀ : State) (ω : (ℕ → Bool) × (ℕ → Pt s)) (t : ℕ) :
    State :=
  (step P s ω.1 ω.2)^[t] s₀

/-- `st` is the halted state of the run of `P` from `s₀` on `ω`. -/
def IsFinal (P : Program) (s : ℕ) (s₀ : State) (ω : (ℕ → Bool) × (ℕ → Pt s)) (st : State) : Prop :=
  st.halted = true ∧ ∃ t, run P s s₀ ω t = st

/-- The state at the start of a run: program counter, registers, pointers, cursors and work `0`;
integer memory holds the list `ints` from cell `0`, real memory the list `reals` from cell `0`, and
every other cell is `0`. -/
noncomputable def initState (ints : List ℤ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, 0, 0, false, 0⟩

/-- The all-false coin tape, for runs of a program without `coin`. -/
def noCoins : ℕ → Bool := fun _ => false

/-- The empty sample stream of dimension `0`, for runs of a program without `sample`. -/
def noStream : ℕ → Pt 0 := fun _ => 0

/-- The output vector of a halted state: `N` real cells from the address in pointer register `1`. -/
noncomputable def outputVec (N : ℕ) (st : State) : Fin N → ℝ :=
  fun a => st.core.mem (st.core.ptrs 1 + (a : ℕ))

/-- The output matrix of a halted state: `N × N` real cells in row-major order from the address in
pointer register `1`. -/
noncomputable def outputMatrix (N : ℕ) (st : State) : Matrix (Fin N) (Fin N) ℝ :=
  fun a b => st.core.mem (st.core.ptrs 1 + ((a : ℕ) * N + (b : ℕ) : ℕ))

/-- The fair-coin tape: the product of uniform measures on `Bool` over `ℕ`. -/
noncomputable def coinTape : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

instance : IsProbabilityMeasure coinTape := by
  unfold coinTape; infer_instance

end NNPartTree


