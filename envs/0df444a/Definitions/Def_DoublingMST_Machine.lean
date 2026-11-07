-- Prove2me | Definitions.Def_DoublingMST_Machine
-- name    : DoublingMST_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:24:19.815445+00:00
-- url     : https://prove2.me/theorems/a657b191-72e2-40a6-ada2-1ff7036d7956
-- title:
--   Real RAM with a unit-cost exact-distance oracle (Definition 2.1): instructions, states, runs, input and output layout
-- statement:
--   The machine of **Definition 2.1**. A program is a fixed finite list of instructions, the same for every input. A state consists of real registers $r[i]$, integer (pointer) registers $p[i]$, a real memory $\mathbb Z\to\mathbb R$ and an integer memory $I:\mathbb Z\to\mathbb Z$, both addressed through integer registers, a program counter, and a step counter.
--
--   The instructions are:
--
--   1. the published real-RAM core: real constants (any real number), $+,-,\times,/$ on real registers, real load and store through a pointer, setting, copying, incrementing, decrementing and comparing pointers, and the branches "if $r[i]\le 0$" and "if $p[q]\le p[q']$";
--   2. $p[d]:=p[a]\pm p[b]$, integer load $p[d]:=I[p[a]]$ and store $I[p[a]]:=p[b]$;
--   3. the cast $r[d]:=p[a]$ of an integer to a real;
--   4. the oracle call $r[d]:=d(x,y)$, where $x,y$ are the points whose labels are $p[a],p[b]$;
--   5. `halt`.
--
--   There is no floor, no real-to-integer conversion, no square root, logarithm or exponential, and no random coin. Every executed instruction costs one step.
--
--   The input of $n$ points with labels $\iota(0),\dots,\iota(n-1)$ and accuracy $\epsilon$ is placed as $p[0]=n$, $I[i]=\iota(i)$ for $0\le i<n$, $r[0]=\epsilon$, everything else $0$. At `halt`, the output is the list of $n-1$ pairs $(I[-2i-1],I[-2i-2])$, $0\le i<n-1$. A program **halts within $T$ steps with output `out`** if, for some $k\le T$, it has executed `halt` after exactly $k$ steps and the output cells hold `out`.
--
--   This file fixes the computational model in which the running time of Theorem 1.1 and Lemma 4.3 is measured.
--
--   **Formalization Note** Integer registers support constants, copy, $+$, $-$, increment, decrement, comparison and indirect load/store over unbounded integers, and nothing more: this reading of "ordinary RAM operations, including indirect addressing" makes the machine weaker and an existence claim stronger. Division by zero returns $0$. An oracle call on an integer that is not a label leaves the run stuck forever, as do the core's `accept`/`reject` and an invalid program counter.
--
--   Two further input layouts are used only by Lemmas 4.3 and 3.3 (running time): one also holds the diameter in real register $1$ (footnote 8, p.51), one starts from a net hierarchy in integer memory.
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Definition 2.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
open scoped Classical

namespace DoublingMST

/-!
# The real RAM with a unit-cost exact-distance oracle (Definition 2.1)

Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Definition 2.1, p.11 (PDF p.13).

The core is the published `SmaleNinth.RAMInstr` (real registers, real memory `ℤ → ℝ` addressed
through integer pointer registers, arithmetic `+ − × /`, real constants, pointer set, copy,
increment, decrement, the branches `r ≤ 0` and `p ≤ p'`). The extension follows the shape of the
published `SubsetConvFPRAS.Machine`.

**Formalization Note.**
* Instructions: the core ones; pointer `+` and `−`; integer memory `ℤ → ℤ` with load and store
  through pointers; the cast of a pointer to a real ("Integer values may also be used as exact
  real arithmetic operands"); the distance oracle `dist`; `halt`.
* Integer registers are the core's pointer registers. They support constants, copy, `+`, `−`,
  increment, decrement, comparison and indirect load/store, over unbounded `ℤ`. This is a reading
  of "ordinary RAM operations, including indirect addressing": there is no integer `×`, `÷`,
  `mod`, shift or bit operation, and no word-size bound. Fewer operations make a weaker machine,
  so an existence statement over these programs is the stronger one.
* Not in the language: floor, any real-to-integer conversion, square root, log, exp, coins (the
  claims are deterministic). Real values reach control flow only through the core branch `r ≤ 0`;
  a three-way comparison of two reals takes a subtraction and at most two branches.
* Real constants are arbitrary reals, as the page allows ("a fixed finite collection of real
  constants"); division by zero gives `0` (Lean's `x / 0 = 0`), which a branch on `0` simulates.
* The oracle: `dist dst a b` sets `r[dst] := d(x, y)` where `ι x = p[a]` and `ι y = p[b]`. If
  `p[a]` or `p[b]` is not a label, the run is stuck: it never halts and produces no output.
* Cost: every executed instruction costs one step, including jumps, oracle calls and `halt`.
  The core's `accept`/`reject` and an invalid program counter never halt (the core leaves the
  configuration unchanged at `accept`/`reject`; an invalid counter sets the stuck flag). After
  `halt` the state stutters.
* Input layout (`init`): pointer register `0` holds `n`; integer memory cells `0, …, n − 1` hold the
  labels `ι 0, …, ι (n − 1)`; real register `0` holds `ϵ`; every other register and cell is `0`.
* Output layout (`outputPairs`): at `halt`, the `i`-th pair (`i < n − 1`) is
  `(I[−2i−1], I[−2i−2])` of integer memory.
* Two further input layouts, used only by Lemmas 4.3 and 3.3 (running time):
  `initKnownDiam` also holds the diameter in real register `1` (p.51, footnote 8: "We assume the
  diameter is known in advance for ease of presentation"); `initHierarchy` starts from an integer
  memory holding a net hierarchy (Lemma 3.3's input). The goal theorem uses `init`.
-/

/-- An instruction. Register and pointer arguments are natural numbers.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]`.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]`.
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `dist d a b`: `r[d] := d(ι⁻¹ p[a], ι⁻¹ p[b])` (one oracle call).
* `halt`: stop; the output is read from integer memory. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | dist (dst a b : ℕ)
  | halt

/-- A program: one finite list of instructions, fixed before the input. -/
abbrev Program := List Instr

/-- The static core table of `P`: extension instructions are placeholders, always dispatched by
`step`. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: the core configuration, integer memory, the halted and stuck flags, and the
number of executed instructions. -/
structure State where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  halted : Bool
  stuck : Bool
  work : ℕ

/-- One step of `P` on the `n` labels `ι` with distance oracle `d`. -/
noncomputable def step {n : ℕ} (P : Program) (ι : Fin n → ℤ) (d : Fin n → Fin n → ℝ)
    (s : State) : State :=
  if s.halted || s.stuck then s else
    let t := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1, stuck := true }
    | some (.core _) =>
        { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerAdd dst a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs dst (s.core.ptrs a + s.core.ptrs b) } }
    | some (.pointerSub dst a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs dst (s.core.ptrs a - s.core.ptrs b) } }
    | some (.integerLoad dst a) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs dst (s.integerMemory (s.core.ptrs a)) } }
    | some (.integerStore a b) =>
        { t with integerMemory :=
            Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal dst a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs dst (s.core.ptrs a : ℝ) } }
    | some (.dist dst a b) =>
        if h : (∃ x, ι x = s.core.ptrs a) ∧ (∃ y, ι y = s.core.ptrs b) then
          { t with core := { t.core with
              regs := Function.update s.core.regs dst (d h.1.choose h.2.choose) } }
        else { s with work := s.work + 1, stuck := true }
    | some .halt => { t with halted := true }

/-- The state after `k` steps from `s₀`. -/
noncomputable def run {n : ℕ} (P : Program) (ι : Fin n → ℤ) (d : Fin n → Fin n → ℝ)
    (s₀ : State) (k : ℕ) : State :=
  (step P ι d)^[k] s₀

/-- The initial state on labels `ι` and accuracy `ϵ`: `p[0] = n`, `I[i] = ι i` for `0 ≤ i < n`,
`r[0] = ϵ`, program counter `0`, everything else `0`. -/
noncomputable def init {n : ℕ} (ι : Fin n → ℤ) (ϵ : ℝ) : State where
  core := ⟨0, Function.update (fun _ => 0) 0 ϵ, Function.update (fun _ => 0) 0 (n : ℤ),
    fun _ => 0⟩
  integerMemory := fun i => if h : 0 ≤ i ∧ i.toNat < n then ι ⟨i.toNat, h.2⟩ else 0
  halted := false
  stuck := false
  work := 0

/-- The output list of `n − 1` label pairs: the `i`-th pair is `(I[−2i−1], I[−2i−2])`. -/
def outputPairs (n : ℕ) (s : State) : List (ℤ × ℤ) :=
  List.ofFn fun i : Fin (n - 1) =>
    (s.integerMemory (-2 * (i : ℤ) - 1), s.integerMemory (-2 * (i : ℤ) - 2))

/-- `P`, started on labels `ι` (with oracle `d`) and accuracy `ϵ`, halts within `T` steps with
output `out`: some `k ≤ T` has the run halted after exactly `k` executed steps and the output
cells holding `out`. -/
def HaltsWithin {n : ℕ} (P : Program) (ι : Fin n → ℤ) (d : Fin n → Fin n → ℝ) (ϵ T : ℝ)
    (out : List (ℤ × ℤ)) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ T ∧ (run P ι d (init ι ϵ) k).halted = true ∧
    outputPairs n (run P ι d (init ι ϵ) k) = out

/-- The initial state of Lemma 4.3: as `init`, and real register `1` holds the diameter `Δ`
(p.51, footnote 8: "We assume the diameter is known in advance for ease of presentation"). -/
noncomputable def initKnownDiam {n : ℕ} (ι : Fin n → ℤ) (ϵ Δ : ℝ) : State :=
  { init ι ϵ with
    core := { (init ι ϵ).core with regs := Function.update (init ι ϵ).core.regs 1 Δ } }

/-- `HaltsWithin`, started from `initKnownDiam`. -/
def HaltsWithinKnownDiam {n : ℕ} (P : Program) (ι : Fin n → ℤ) (d : Fin n → Fin n → ℝ) (ϵ Δ T : ℝ)
    (out : List (ℤ × ℤ)) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ T ∧ (run P ι d (initKnownDiam ι ϵ Δ) k).halted = true ∧
    outputPairs n (run P ι d (initKnownDiam ι ϵ Δ) k) = out

/-- The initial state of Lemma 3.3's algorithm: `p[0] = n`, `p[1] = a₀` (the address of the root
record), `r[0] = t`, integer memory `mem` (see `EncodesHierarchy`), everything else `0`. -/
noncomputable def initHierarchy (n : ℕ) (t : ℝ) (a₀ : ℤ) (mem : ℤ → ℤ) : State where
  core := ⟨0, Function.update (fun _ => 0) 0 t,
    Function.update (Function.update (fun _ => 0) 0 (n : ℤ)) 1 a₀, fun _ => 0⟩
  integerMemory := mem
  halted := false
  stuck := false
  work := 0

end DoublingMST


