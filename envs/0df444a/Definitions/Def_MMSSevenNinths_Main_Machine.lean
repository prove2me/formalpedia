-- Prove2me | Definitions.Def_MMSSevenNinths_Main_Machine
-- name    : MMSSevenNinths_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:48:04.339316+00:00
-- url     : https://prove2.me/theorems/425ec430-2671-40c1-8740-3192e99a93f5
-- title:
--   LP-free exact register programs: runs, layouts, call entries and encoding lengths
-- statement:
--   The computation model for §8: the published exact-arithmetic register machine `DynStochMatching.Reward` (natural registers for addresses and counters; real registers with unit-cost $+,-,\times,\div$, $\le$-branches, loads and stores), restricted to **LP-free** programs (`LPFree`: no `lp` instruction), so its linear-programming oracle never acts.
--
--   * `advance` executes one instruction; a state at `halt` or outside the program stays fixed. `stateAt O code s₀ t` is the state after $t$ steps, `Halted` says the current instruction is `halt`, and `HaltsWithin code s₀ budget out` says that, for every oracle, the run reaches `halt` within `budget` executed instructions and the halting state satisfies `out`.
--   * `visitTimes O code s₀ p T` lists the times $t<T$ at which the run is at instruction $p$ and not halted (used for the entry instruction of the Algorithm 1 subroutine).
--   * Input layout: natural registers $0,1$ hold $n,m$; real register $i\cdot m+g$ holds $v_i(e_{g+1})$ (`instanceReals`, row-major; `ratEntries` is the same list for a rational matrix). Output layouts: `OwnerOutput` (real register $g$ holds the integer owner of good $g$) and `MatrixOutput` (real register $i\cdot m+r$ holds a matrix entry).
--   * `ratSize q` is the bit length of $|\mathrm{num}(q)|$ plus that of $\mathrm{den}(q)$; `inputLength` adds list lengths and the bit lengths of all entries. `RegistersWithin s B` says every real register holds a rational of size at most $B$ and every natural register has at most $B$ bits; `SizesWithin code s₀ budget B` says this holds at every step $t\le$ `budget`.
--
--   `CallOutput s base V α` specifies an actual Algorithm 1 return in real registers: success, failed-agent flags, partial-allocation incidence flags, and the update values for failed agents. The main theorem requires this return between each entry and the next entry (or final halt). Allocation owner arrays use real registers because only real memory has indirect loads and stores in the reused machine. Integer owners are represented exactly.
-- source:
--   Huang and Zhou (2026), A Strongly Polynomial-Time 7/9-Approximation Algorithm for Maximin Share Allocations, held STOC 2027 submission, SHA-256 428b298d196be354cea02bcd3b7278ffac7f04104c4bc290b02b6385aa0e405b, §8 and proof of Theorem 8.1, printed pp. 24–26 (PDF 27–29)

import Mathlib
import Definitions.Def_DynStochMatching_Reward_RealMachine
import Definitions.Def_MMSSevenNinths_Main_Algorithm1

open scoped Classical

namespace MMSSevenNinths.Main

open DynStochMatching.Reward

/-! Computation model for §8 of Huang and Zhou (2026) (printed pp. 24–26, PDF 27–29): the
published exact register machine `DynStochMatching.Reward` (real registers with unit-cost
`+ − × ÷` and `≤` comparisons, natural registers for addresses), restricted to programs with
no `lp` instruction, so its LP oracle never acts. A step is one executed instruction. -/

/-- A program is LP-free: it contains no `lp` instruction. -/
def LPFree (code : List Instruction) : Prop :=
  ∀ ins ∈ code, ∀ a b c d e f : ℕ, ins ≠ Instruction.lp a b c d e f

/-- One step of execution; a state at a `halt` instruction or outside the program is frozen. -/
noncomputable def advance (O : LinearOracle) (code : List Instruction) (s : MachineState) :
    MachineState :=
  match code[s.pc]? with
  | none => s
  | some Instruction.halt => s
  | some ins => machineStep O ins s

/-- The state after `t` steps. -/
noncomputable def stateAt (O : LinearOracle) (code : List Instruction) (s₀ : MachineState)
    (t : ℕ) : MachineState :=
  (advance O code)^[t] s₀

/-- The state is at a `halt` instruction. -/
def Halted (code : List Instruction) (s : MachineState) : Prop :=
  code[s.pc]? = some Instruction.halt

/-- The run from `s₀` reaches `halt` within `budget` steps, and the halting state satisfies
`out` (for every oracle; LP-free programs never consult it). -/
def HaltsWithin (code : List Instruction) (s₀ : MachineState) (budget : ℕ)
    (out : MachineState → Prop) : Prop :=
  ∀ O : LinearOracle, ∃ t ≤ budget, Halted code (stateAt O code s₀ t) ∧ out (stateAt O code s₀ t)

/-- The times `t < T` at which the (not yet halted) run is at instruction `p`. Used with `p`
the entry instruction of the Algorithm 1 subroutine: these are the call entries. -/
noncomputable def visitTimes (O : LinearOracle) (code : List Instruction) (s₀ : MachineState)
    (p T : ℕ) : List ℕ :=
  (List.range T).filter
    (fun t => decide ((stateAt O code s₀ t).pc = p ∧ ¬ Halted code (stateAt O code s₀ t)))

/-- Input layout of an instance: natural registers `0, 1` hold `n, m`; real register
`i * m + g` holds `v_i(e_{g+1})` (row-major singleton values). -/
noncomputable def instanceReals {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) : List ℝ :=
  (List.finRange n).flatMap (fun i => (List.finRange m).map (fun g => V i {g}))

/-- Row-major list of a rational singleton-value matrix. -/
def ratEntries {n m : ℕ} (Q : Fin n → Fin m → ℚ) : List ℚ :=
  (List.finRange n).flatMap (fun i => (List.finRange m).map (fun g => Q i g))

/-- Output layout of an allocation: real register `g` holds the integer owner of good `g`.
The published machine has indirect real loads/stores, but no indirect natural loads/stores. -/
def OwnerOutput {n m : ℕ} (s : MachineState) (σ : Fin m → Fin n) : Prop :=
  ∀ g : Fin m, s.reals g.val = ((σ g).val : ℝ)

/-- Return layout of an instrumented Algorithm 1 call in real registers beginning at `base`:
its success flag, `n` failed-agent flags, `n*m` bundle-incidence flags, and `n` slots for
failed agents' update values. These are computed outputs, not supplied witnesses. Recording
this layout costs O(n*m+n) operations and does not require retaining the full test log. -/
noncomputable def CallOutput {n m : ℕ} (s : MachineState) (base : ℕ)
    (V : Fin n → Finset (Fin m) → ℝ) (α : Fin n → ℝ) : Prop :=
  let result := alg1Det V α
  s.reals base = (if result.success then 1 else 0) ∧
  (∀ i : Fin n, s.reals (base + 1 + i.val) =
    (if i ∈ result.failed then 1 else 0)) ∧
  (∀ (i : Fin n) (g : Fin m), s.reals (base + 1 + n + i.val * m + g.val) =
    (if g ∈ result.bundles i then 1 else 0)) ∧
  (∀ i ∈ result.failed, s.reals (base + 1 + n + n * m + i.val) = failureBound V α i)

/-- Output layout of a singleton-value matrix: real register `i * m + r` holds `W i r`. -/
def MatrixOutput {n m : ℕ} (s : MachineState) (W : Fin n → Fin m → ℝ) : Prop :=
  ∀ (i : Fin n) (r : Fin m), s.reals (i.val * m + r.val) = W i r

/-- Binary encoding length of a rational number: bits of `|numerator|` plus bits of the
denominator. -/
def ratSize (q : ℚ) : ℕ :=
  q.num.natAbs.size + q.den.size

/-- Total encoding length of an input: list lengths plus bits of every entry. -/
def inputLength (nats : List ℕ) (qs : List ℚ) : ℕ :=
  nats.length + qs.length + (nats.map Nat.size).sum + (qs.map ratSize).sum

/-- Every register of the state holds a value of encoding length at most `B`: each real
register is a rational of size `≤ B`, each natural register has at most `B` bits. -/
def RegistersWithin (s : MachineState) (B : ℕ) : Prop :=
  (∀ k : ℕ, ∃ q : ℚ, s.reals k = (q : ℝ) ∧ ratSize q ≤ B) ∧ ∀ k : ℕ, (s.naturals k).size ≤ B

/-- All states of the first `budget` steps of the run keep every register within size `B`. -/
def SizesWithin (code : List Instruction) (s₀ : MachineState) (budget B : ℕ) : Prop :=
  ∀ O : LinearOracle, ∀ t ≤ budget, RegistersWithin (stateAt O code s₀ t) B

end MMSSevenNinths.Main


