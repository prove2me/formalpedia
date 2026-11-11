-- Prove2me | Definitions.Def_MixedSpinColorCoding_Counting_Machine
-- name    : MixedSpinColorCoding_Counting_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:58.609654+00:00
-- url     : https://prove2.me/theorems/6ea82d3c-1338-4a5a-b7fc-11c5e0a6978a
-- title:
--   Exact-arithmetic machine with unit-cost operations and the input layout
-- statement:
--   The computational model of Theorem 1.2 (footnote 2: arithmetic operations, comparisons and evaluations of elementary functions have unit cost). A program is one finite list of instructions of the published deterministic real pointer machine `SmaleNinth.RAMInstr` (exact $+,-,\times,\div$ on real registers, real literals, indirect load and store through integer pointers, pointer set/copy/increment/decrement, comparison jumps $r\le0$ and $p\le p'$), extended by a pointer-to-real cast, $\sqrt{\cdot}$, $\exp$, $\log$ and `halt`. Every executed instruction costs one step; a halted state stutters. A program is admissible when its real literals are rational and it uses no core accept/reject. There is no floor, no real-to-integer cast, no randomness, and no instruction evaluating a sum, polynomial or partition function.
--
--   The input of a run is pointer $p[0]=n$ and the memory cells $\varepsilon,\delta,\beta$, then $\gamma_2,\dots,\gamma_{p_{\max}}$, then the disorder order by order, each order's ordered tuples lexicographically; all other cells, registers and pointers are $0$. The output is real register $0$.
-- source:
--   Alina Harbuzova, Saba Lepsveridze, Mahbod Majid, Ankur Moitra, STOC 2027 submission #592 (October 2026), Color Coding for the Sherrington–Kirkpatrick Model, Theorem 1.2 and footnote 2, printed p.2 / PDF p.4. PDF SHA-256 5559e422541f71e2e270b74941f426295f0ea249bd88d4ff218bb950ad81646b; citation_basis: published.

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MixedSpinColorCoding_Counting_Model

open scoped BigOperators

/-!
# The exact-arithmetic model of Theorem 1.2 and the input layout

Source: STOC 2027 submission #592, Theorem 1.2 and footnote 2 (PDF p.4): "Arithmetic
operations, comparisons, and evaluations of elementary functions have unit cost."

The machine is the published deterministic real pointer machine `SmaleNinth.RAMInstr`
(exact `+ − × ÷` on real registers, real literals, indirect load/store through integer pointers,
pointer set/copy/increment/decrement, the comparisons `r ≤ 0` and `p ≤ p'`), extended by a
pointer-to-real cast and the elementary functions `√`, `exp`, `log`, and by `halt`.

* Every executed instruction costs `1` (`work`); a halted state stutters at no cost; an invalid
  program counter is stuck (never halted) and charged.
* `Admissible`: real literals are rational and the core `accept`/`reject` do not occur. There is
  no floor or real-to-integer cast, no randomness, and no instruction carrying a function, so
  partition functions, polynomials and sums are computed only by charged scalar steps.
  (`÷`, `√`, `log` are Lean-total: `x/0 = 0`, `√x = 0` for `x < 0`, `log x = log |x|`; each of
  these values is also obtainable in `O(1)` charged steps, so they add no power.)
* Input layout (`initialState`): pointer `p[0] = n`, all other pointers, all registers and the
  program counter `0`. Memory cells `0, 1, 2` hold `ε, δ, β`; then `γ_2, …, γ_pmax`; then the
  disorder, order by order (`p = 2, …, pmax`), each order's ordered tuples in lexicographic
  order (`tuples`). Every other cell is `0`. The output is real register `0`.
-/

namespace MixedSpinColorCoding.Counting

/-- An instruction: a published core instruction or one of the extensions.
* `pointerReal d q`: `r[d] := (p[q] : ℝ)`.
* `sqrt d a`, `exp d a`, `log d a`: `r[d] := √r[a]`, `e^{r[a]}`, `log r[a]`.
* `halt`: stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerReal (dst pointer : ℕ)
  | sqrt (dst src : ℕ)
  | exp (dst src : ℕ)
  | log (dst src : ℕ)
  | halt

/-- A program: one finite instruction list, the same for every input. -/
abbrev Program := List Instr

/-- Rational real literals only, and no core `accept`/`reject`. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ c) => ∃ q : ℚ, c = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The core table of `P`; extension instructions become placeholders, always dispatched by
`step` before the core table is consulted. -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: core configuration, halted flag and work counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  halted : Bool
  work : ℕ

/-- One step of `P`. Halted states stutter at no cost; every other step costs `1`. -/
noncomputable def step (P : Program) (s : State) : State :=
  if s.halted then s else
    let t : State := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    let setReg (d : ℕ) (v : ℝ) : State :=
      { t with core := { t.core with regs := Function.update s.core.regs d v } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerReal d q) => setReg d (s.core.ptrs q : ℝ)
    | some (.sqrt d a) => setReg d (Real.sqrt (s.core.regs a))
    | some (.exp d a) => setReg d (Real.exp (s.core.regs a))
    | some (.log d a) => setReg d (Real.log (s.core.regs a))
    | some .halt => { t with halted := true }

/-- The state after `k` steps. -/
noncomputable def run (P : Program) (s₀ : State) (k : ℕ) : State :=
  (step P)^[k] s₀

/-- All ordered tuples `Fin p → Fin n`, in lexicographic order (first coordinate slowest). -/
def tuples (n : ℕ) : (p : ℕ) → List (Fin p → Fin n)
  | 0 => [Fin.elim0]
  | p + 1 => (List.finRange n).flatMap fun j =>
      (tuples n p).map fun i => (Fin.cons j i : Fin (p + 1) → Fin n)

/-- The disorder entries, order by order, each order's tuples lexicographically. -/
def disorderCells (n pmax : ℕ) (G : Disorder n pmax) : List ℝ :=
  (List.finRange (pmax - 1)).flatMap fun k =>
    (tuples n (k.val + 2)).map fun i => G ⟨k, i⟩

/-- The input cells: `ε, δ, β`, then `γ_2, …, γ_pmax`, then the disorder. -/
def inputCells (n pmax : ℕ) (γ : ℕ → ℝ) (G : Disorder n pmax) (ε δ β : ℝ) : List ℝ :=
  [ε, δ, β] ++ (List.range (pmax - 1)).map (fun k => γ (k + 2)) ++ disorderCells n pmax G

/-- The initial state on input `(n, γ, G, ε, δ, β)`. -/
noncomputable def initialState (n pmax : ℕ) (γ : ℕ → ℝ) (G : Disorder n pmax)
    (ε δ β : ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun q => if q = 0 then (n : ℤ) else 0,
      fun a => if 0 ≤ a then (inputCells n pmax γ G ε δ β).getD a.toNat 0 else 0⟩,
    false, 0⟩

/-- The output of a state: real register `0`. -/
def output (s : State) : ℝ := s.core.regs 0

end MixedSpinColorCoding.Counting


