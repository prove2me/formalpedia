-- Prove2me | Definitions.Def_FasterSFM_Machine
-- name    : FasterSFM_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:48.888611+00:00
-- url     : https://prove2.me/theorems/05718bd5-3f23-416d-91ac-0a159b6c1f40
-- title:
--   The randomized exact-arithmetic value-oracle RAM and the success event of Theorem 1
-- statement:
--   Theorem 1 speaks about a randomized algorithm in exact real arithmetic that accesses a submodular function $h:2^U\to\mathbb R$, $U=\{0,\dots,n-1\}$, only through a value oracle. This definition makes that model precise.
--
--   A **program** is one finite list of instructions, the same for every $n$. The machine has real registers, integer pointer registers, real and integer random-access memories, bitmaps (subsets of $U$ accessed one bit at a time), a cursor on a tape of fair coins, an output slot and two counters. The instructions are:
--
--   1. the real-RAM core: constants, $+,-,\times,\div$ (with $x/0=0$), indirect load and store, pointer set, copy, increment and decrement, and conditional jumps on $r\le 0$ and on $p\le p'$;
--   2. integer $+,-,\times$ on pointers, integer load and store, and the cast of a pointer to a real;
--   3. $\sqrt{\cdot}$ on a real register (with $\sqrt x=0$ for $x<0$);
--   4. `coin`: load the next fair coin (0 or 1) into a register;
--   5. writing or reading one bit of a bitmap;
--   6. `query`: load $h(X)$ for the set $X$ held in a bitmap;
--   7. `halt`: output the set held in a bitmap.
--
--   A program is **admissible** if all its real literals are rational. The input is $n$, stored in integer memory; $h$ is reachable only through `query` and the coins only through `coin`. Every executed instruction costs one unit of **work**, and each `query` also adds one to the **query** count; after `halt` the machine stops. The coin tape carries the product of fair Bernoulli measures on $\{0,1\}^{\mathbb N}$.
--
--   For a program $P$, constants $C$, $k$ and a tape $\omega$, the **success event** holds when at some step the run has halted with an output $X$ that minimizes $h$, having made at most $Cn^2\log(n+2)$ queries and at most $Cn^3(\log(n+2))^k$ units of work. The total running time of the paper is the query count times $EO$ plus the work.
--
--   **Formalization Note** The scalar core is the published `SmaleNinth.RAMInstr`; the extension design follows the published `LSWNewArcAudit.NewArc` oracle RAM, with a real-valued oracle, $\sqrt{\cdot}$ and a coin tape added. There is no exp, log, floor, real-to-integer cast or set-level instruction.
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, §1, Theorem 1, p.2 ("The algorithm assumes exact real arithmetic"); §2, p.3 (value oracle)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

namespace FasterSFM

/-!
# The randomized exact-arithmetic value-oracle RAM

Ene & Nguyen, *A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization*,
arXiv:2610.25403v1, §1, p.2 ("The algorithm assumes exact real arithmetic"; "randomized algorithm")
and §2, p.3 (the value oracle).

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ`. The extensions
follow the published `LSWNewArcAudit.NewArc` oracle RAM (integer pointer arithmetic, integer memory,
one-bit bitmap access, a value-oracle query that reads a bitmap handle, halting with a set), with
three changes: the oracle is real-valued (`Finset (Fin n) → ℝ`, as on p.3), the machine has a square
root, and it has a fair-coin tape.

**Formalization Note.**
* Ground set `U = Fin n`. The input is `n` alone, in integer memory cell `0`; `h` is reachable only
  through `query`.
* Instructions: the core's `+ − × ÷` (with `x / 0 = 0`), constants, indirect real load/store, pointer
  set/copy/increment/decrement, the two comparisons-and-jumps; integer `+ − ×` on pointers, integer
  load/store, pointer-to-real cast; `sqrt` (`Real.sqrt`, so `√x = 0` for `x < 0`); `coin`; one-bit
  bitmap write/read; `query`; `halt`. There is no exp, log, floor, real-to-integer cast, argmin, sort,
  scan, set copy or clear (readings R4 of the mission).
* Every executed instruction costs one unit of `work`, including `query`, `coin` and `halt`; a query
  also adds one to `queries`. An invalid program counter is stuck and charged. After `halt` the state
  stutters with no further cost (reading R5).
* Randomness is a tape of independent fair coins, one bit per executed `coin` (reading R3).
* Admissible programs use rational literals only and no core `accept`/`reject` (output is by `halt`).
-/

/-- An instruction of the randomized exact-arithmetic value-oracle RAM. Register, pointer and label
arguments are natural numbers; no constructor carries a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd/Sub/Mul d a b`: `p[d] := p[a] ∘ p[b]` on integer pointers.
* `integerLoad d a` / `integerStore a b`: `p[d] := I[p[a]]` / `I[p[a]] := p[b]` (integer memory).
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `sqrt d a`: `r[d] := √(r[a])`.
* `coin d`: `r[d] := 1` if the next tape bit is `true`, else `0`; the tape cursor advances.
* `bitWrite bank elt val`: set bit `p[elt]` of bitmap `p[bank]` to `r[val] ≠ 0`.
* `bitRead d bank elt`: `r[d] := 1` if bit `p[elt]` of bitmap `p[bank]` is set, else `0`.
* `query d bank`: `r[d] := h(bitmap p[bank])`.
* `halt bank`: output the set held in bitmap `p[bank]`. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | pointerMul (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | sqrt (dst src : ℕ)
  | coin (dst : ℕ)
  | bitWrite (bank element value : ℕ)
  | bitRead (dst bank element : ℕ)
  | query (dst bank : ℕ)
  | halt (bank : ℕ)

/-- A program: one finite list of instructions, the same for every input size `n`. -/
abbrev Program := List Instr

/-- Admissibility: every real literal is rational, and the core halting instructions
`accept`/`reject` do not occur (the machine outputs a set through `halt`). This restricts the
existentially chosen program, never the input. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P`: extension instructions are placeholders here and are always
dispatched by `step`. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state for ground set `Fin n`: the core configuration (program counter, real registers,
pointers, real memory), integer memory, bitmaps, the coin-tape cursor, the output, and the two
counters. -/
structure State (n : ℕ) where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  bitmap : ℤ → Finset (Fin n)
  cursor : ℕ
  output : Option (Finset (Fin n))
  queries : ℕ
  work : ℕ

/-- The initial state on input size `n`: program counter `0`, all registers, pointers and real
memory `0`, integer memory holding `n` in cell `0` and `0` elsewhere, all bitmaps empty, cursor at
the first coin, no output, both counters `0`. -/
def init (n : ℕ) : State n :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun i => if i = 0 then (n : ℤ) else 0,
    fun _ => ∅, 0, none, 0, 0⟩

/-- One step of program `P` with value oracle `h` and coin tape `ω`. Halted states stutter at no
cost; every other step costs one unit of work. `h` occurs only in the `query` branch and `ω` only in
the `coin` branch. Bit indices outside `0 ≤ i < n` read `0` and write nothing. -/
noncomputable def step {n : ℕ} (P : Program) (h : Finset (Fin n) → ℝ) (ω : ℕ → Bool)
    (s : State n) : State n := by
  classical
  exact if s.output.isSome then s else
    let t := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) =>
        { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerAdd d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b) } }
    | some (.pointerSub d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b) } }
    | some (.pointerMul d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a * s.core.ptrs b) } }
    | some (.integerLoad d a) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.integerMemory (s.core.ptrs a)) } }
    | some (.integerStore a b) =>
        { t with integerMemory := Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
    | some (.sqrt d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (Real.sqrt (s.core.regs a)) } }
    | some (.coin d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with
            regs := Function.update s.core.regs d (if ω s.cursor then 1 else 0) } }
    | some (.bitWrite b e v) =>
        if hb : 0 ≤ s.core.ptrs e ∧ (s.core.ptrs e).toNat < n then
          let j : Fin n := ⟨(s.core.ptrs e).toNat, hb.2⟩
          let bank := s.core.ptrs b
          let contents := if s.core.regs v = 0 then (s.bitmap bank).erase j
            else insert j (s.bitmap bank)
          { t with bitmap := Function.update s.bitmap bank contents }
        else t
    | some (.bitRead d b e) =>
        let value : ℝ := if hb : 0 ≤ s.core.ptrs e ∧ (s.core.ptrs e).toNat < n then
          if (⟨(s.core.ptrs e).toNat, hb.2⟩ : Fin n) ∈ s.bitmap (s.core.ptrs b) then 1 else 0
          else 0
        { t with core := { t.core with regs := Function.update s.core.regs d value } }
    | some (.query d b) =>
        { t with
          queries := s.queries + 1
          core := { t.core with
            regs := Function.update s.core.regs d (h (s.bitmap (s.core.ptrs b))) } }
    | some (.halt b) => { t with output := some (s.bitmap (s.core.ptrs b)) }

/-- The state after `t` steps of `P` on ground set `Fin n`, oracle `h`, coin tape `ω`. -/
noncomputable def run {n : ℕ} (P : Program) (h : Finset (Fin n) → ℝ) (ω : ℕ → Bool) (t : ℕ) :
    State n :=
  (step P h ω)^[t] (init n)

/-- The fair-coin tape: the product of uniform measures on `Bool` over `ℕ`. -/
noncomputable def coinTape : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure)

/-- The success event of Theorem 1 for program `P`, constants `C`, `k` and tape `ω` (reading R6):
some step `t` of the run has executed `halt` with output `X`, `X` minimizes `h`, and the query and
work counters at that step are at most `C n² log(n+2)` and `C n³ (log(n+2))^k`. -/
def Success (P : Program) (n : ℕ) (h : Finset (Fin n) → ℝ) (C : ℝ) (k : ℕ) (ω : ℕ → Bool) :
    Prop :=
  ∃ t : ℕ, ∃ X : Finset (Fin n), (run P h ω t).output = some X ∧
    (∀ Y : Finset (Fin n), h X ≤ h Y) ∧
    ((run P h ω t).queries : ℝ) ≤ C * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 2) ∧
    ((run P h ω t).work : ℝ) ≤ C * (n : ℝ) ^ 3 * (Real.log ((n : ℝ) + 2)) ^ k

end FasterSFM


