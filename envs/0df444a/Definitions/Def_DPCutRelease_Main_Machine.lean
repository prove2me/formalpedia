-- Prove2me | Definitions.Def_DPCutRelease_Main_Machine
-- name    : DPCutRelease_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:11:28.064638+00:00
-- url     : https://prove2.me/theorems/2e5f43c7-65e6-4fde-b705-44cc23330554
-- title:
--   The randomized real RAM of §1.1.1 (arithmetic, comparisons, √, log, exp, floor, ceiling, exact N(0,1) and Lap(1) draws, unit cost), input layout and output
-- statement:
--   The model of computation in which Theorem 1's running time is read. §1.1.1: "Running time is measured in the real RAM model, with constant-cost arithmetic, comparisons, square roots, logarithms, exponentials, floor and ceiling, and exact sampling from the standard Gaussian and Laplace distributions; bit complexity is not analyzed."
--
--   A **program** is one finite list of instructions, the same for every input. The machine has real registers $r_0,r_1,\dots$, integer pointer registers $p_0,p_1,\dots$ and a random-access real memory indexed by $\mathbb Z$. Its instructions are:
--   1. the published real-RAM core: exact $+,-,\times,\div$ (with $x/0=0$), rational literals, indirect load and store through pointers, pointer set, copy, increment and decrement, and the comparison jumps $r_i\le0$ and $p_q\le p_{q'}$;
--   2. the cast $r_d:=p_q$;
--   3. $\sqrt{\cdot}$, $\exp$ and $\log$ of a register;
--   4. $p_d:=\lfloor r_a\rfloor$ and $p_d:=\lceil r_a\rceil$;
--   5. `gauss`, which reads the next entry of an i.i.d. $N(0,1)$ stream, and `lap`, which reads the next entry of an independent i.i.d. $\mathrm{Lap}(1)$ stream;
--   6. halt.
--
--   Every executed instruction costs one step; an invalid program counter is stuck forever, and after halt the state stutters. A run **halts within $T$ steps** if it is halted after at most $T$ steps; the bound must hold on every pair of streams. The **tape measure** makes the two streams i.i.d. $N(0,1)$ and i.i.d. $\mathrm{Lap}(1)$, independent of each other.
--
--   **Input and output.** On input $(n,\gamma,\varepsilon,\delta,\beta,w)$: $p_0=n$; memory cells $0,1,2,3$ hold $\gamma,\varepsilon,\delta,\beta$; cell $4+nu+v$ holds $w_{uv}$ for $u<v$; every other cell, register and pointer is $0$. The output $\tilde w_{uv}$ is read from cell $-1-(nu+v)$ at the first halting step.
--
--   **Formalization Note.** The core is the published `SmaleNinth.RAMInstr`; the extension follows the published pattern of `PolySampIso.Instr` (not imported: it has no floor or ceiling and draws $\mathrm{Exp}(1)$ instead of $\mathrm{Lap}(1)$). `Admissible` requires rational literals and excludes the core `accept`/`reject`; it restricts the existentially chosen program only. `Real.sqrt` and `Real.log` give $\sqrt x=0$ for $x<0$, $\log0=0$ and $\log x=\log|x|$. `finalOutput` reads the output at `haltTime`, the first halted step.
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 5, §1.1.1; p. 13, Algorithm 1 input line; p. 33, footnote 2

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_DPCutRelease_Main_EdgeDP

open MeasureTheory ProbabilityTheory

namespace DPCutRelease.Main

/-!
# The randomized real RAM of §1.1.1, input layout and output

Eliáš et al., arXiv:2611.06670v1, p. 5 (§1.1.1): "Running time is measured in the real RAM
model, with constant-cost arithmetic, comparisons, square roots, logarithms, exponentials, floor
and ceiling, and exact sampling from the standard Gaussian and Laplace distributions; bit
complexity is not analyzed."; p. 13 (Algorithm 1's input line); p. 33 footnote 2 ("bound the
running time on every execution").

**Formalization Note.**
* The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ` (exact
  `+ − × ÷` with `x/0 = 0`, literals, indirect real memory `ℤ → ℝ` through integer pointer
  registers, pointer set, copy, increment and decrement, and the comparison jumps `r[i] ≤ 0` and
  `p[q] ≤ p[q']`). It is extended (following the published pattern of `PolySampIso.Instr`, not
  imported) with: the cast `r[d] := p[q]`; `√`, `exp`, `log` of a register (`Real.sqrt`,
  `Real.log`: `√x = 0` for `x < 0`, `log 0 = 0`, `log x = log |x|`); `floor` and `ceil` from a real
  register into a pointer register (`p[d] := ⌊r[a]⌋`, `⌈r[a]⌉`); `gauss`, which reads the next
  entry of an i.i.d. `N(0,1)` stream; `lap`, which reads the next entry of an independent i.i.d.
  `Lap(1)` stream; and `halt`. No instruction carries a function, an oracle, an eigenvalue, an
  inverse or an optimizer.
* `Admissible`: every real literal is rational and the core `accept`/`reject` do not occur, so
  only `halt` halts. This restricts the program only, never the input.
* Cost: every executed instruction is one step; an invalid program counter is stuck (never
  halts); after `halt` the state stutters. The running time of a run is the first step count at
  which it is halted; `HaltsWithin P s₀ T` says that on **every** pair of streams the run is
  halted within `T` steps.
* Randomness: `Streams = (ℕ → ℝ) × (ℕ → ℝ)`; the `j`-th executed `gauss` reads entry `j` of the
  first stream, the `j`-th executed `lap` entry `j` of the second. `tape` makes the first stream
  i.i.d. `N(0,1)` and, independently, the second i.i.d. `Lap(1)` (`PrivLearn.Generic.laplace 1`).
* Input (`inputState n γ ε δ β w`): pointer `p[0] = n`, other pointers and all registers `0`;
  memory cells `0, 1, 2, 3` hold `γ, ε, δ, β`; cell `4 + n·u + v` holds `w_{uv}` for `u < v`
  (0-based vertices); every other cell is `0`.
* Output (`output`): `w̃_{uv}` is read from cell `−1 − (n·u + v)`, `u < v`, of the state at the
  first halting step (`finalOutput`).
-/

/-- An instruction of the machine. -/
inductive Instr where
  /-- A `SmaleNinth` real-RAM instruction. -/
  | core (instruction : SmaleNinth.RAMInstr)
  /-- `r[dst] := (p[pointer] : ℝ)`. -/
  | pointerReal (dst pointer : ℕ)
  /-- `r[dst] := √r[src]`. -/
  | sqrt (dst src : ℕ)
  /-- `r[dst] := exp r[src]`. -/
  | exp (dst src : ℕ)
  /-- `r[dst] := log r[src]`. -/
  | log (dst src : ℕ)
  /-- `p[dst] := ⌊r[src]⌋`. -/
  | floor (dst src : ℕ)
  /-- `p[dst] := ⌈r[src]⌉`. -/
  | ceil (dst src : ℕ)
  /-- `r[dst] :=` the next unread entry of the `N(0,1)` stream. -/
  | gauss (dst : ℕ)
  /-- `r[dst] :=` the next unread entry of the `Lap(1)` stream. -/
  | lap (dst : ℕ)
  /-- Stop. -/
  | halt

/-- A program: one finite list of instructions, the same for every input. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core halting instructions do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P` (extension instructions are placeholders, dispatched by
`step`). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: the core configuration, the two stream cursors and the halted flag. -/
structure State where
  core : SmaleNinth.RAMConfig
  gaussCursor : ℕ
  lapCursor : ℕ
  halted : Bool

/-- The randomness of a run: the `N(0,1)` stream and the `Lap(1)` stream. -/
abbrev Streams := (ℕ → ℝ) × (ℕ → ℝ)

/-- One step of `P` on the streams `ω`. Halted states and invalid program counters stay put. -/
noncomputable def step (P : Program) (ω : Streams) (s : State) : State :=
  if s.halted then s else
    let next : SmaleNinth.RAMConfig := { s.core with pc := s.core.pc + 1 }
    let setReg (d : ℕ) (v : ℝ) : State :=
      { s with core := { next with regs := Function.update s.core.regs d v } }
    let setPtr (d : ℕ) (v : ℤ) : State :=
      { s with core := { next with ptrs := Function.update s.core.ptrs d v } }
    match P[s.core.pc]? with
    | none => s
    | some (.core _) => { s with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerReal d q) => setReg d (s.core.ptrs q : ℝ)
    | some (.sqrt d a) => setReg d (Real.sqrt (s.core.regs a))
    | some (.exp d a) => setReg d (Real.exp (s.core.regs a))
    | some (.log d a) => setReg d (Real.log (s.core.regs a))
    | some (.floor d a) => setPtr d ⌊s.core.regs a⌋
    | some (.ceil d a) => setPtr d ⌈s.core.regs a⌉
    | some (.gauss d) => { setReg d (ω.1 s.gaussCursor) with gaussCursor := s.gaussCursor + 1 }
    | some (.lap d) => { setReg d (ω.2 s.lapCursor) with lapCursor := s.lapCursor + 1 }
    | some .halt => { s with core := next, halted := true }

/-- The state after `t` steps of `P` from `s₀` on the streams `ω`. -/
noncomputable def run (P : Program) (s₀ : State) (ω : Streams) (t : ℕ) : State :=
  (step P ω)^[t] s₀

/-- Every run of `P` from `s₀` (on every pair of streams) is halted within `T` steps. -/
def HaltsWithin (P : Program) (s₀ : State) (T : ℝ) : Prop :=
  ∀ ω : Streams, ∃ t : ℕ, (t : ℝ) ≤ T ∧ (run P s₀ ω t).halted = true

/-- The first step count at which the run is halted (`0` if it never halts). -/
noncomputable def haltTime (P : Program) (s₀ : State) (ω : Streams) : ℕ :=
  sInf {t | (run P s₀ ω t).halted = true}

open Classical in
/-- The input memory: `γ, ε, δ, β` in cells `0, 1, 2, 3`, `w_{uv}` in cell `4 + n·u + v`
(`u < v`), `0` elsewhere. -/
noncomputable def inputMem (n : ℕ) (γ ε δ β : ℝ) (w : EdgeVec n) : ℤ → ℝ := fun a =>
  if a = 0 then γ else if a = 1 then ε else if a = 2 then δ else if a = 3 then β else
    if h : ∃ e : Pair n, a = 4 + (n : ℤ) * (e.1.1 : ℤ) + (e.1.2 : ℤ) then w h.choose else 0

/-- The initial state on input `(n, γ, ε, δ, β, w)`: program counter, registers and cursors `0`,
not halted, pointer `p[0] = n`, other pointers `0`, memory `inputMem n γ ε δ β w`. -/
noncomputable def inputState (n : ℕ) (γ ε δ β : ℝ) (w : EdgeVec n) : State :=
  ⟨⟨0, fun _ => 0, fun q => if q = 0 then (n : ℤ) else 0, inputMem n γ ε δ β w⟩, 0, 0, false⟩

/-- The released weight vector of a state: `w̃_{uv} = M[−1 − (n·u + v)]`. -/
def output (n : ℕ) (s : State) : EdgeVec n :=
  fun e => s.core.mem (-1 - ((n : ℤ) * (e.1.1 : ℤ) + (e.1.2 : ℤ)))

/-- The output of the run on the streams `ω`, read at the first halting step. -/
noncomputable def finalOutput (n : ℕ) (P : Program) (s₀ : State) (ω : Streams) : EdgeVec n :=
  output n (run P s₀ ω (haltTime P s₀ ω))

/-- The tape measure: i.i.d. `N(0,1)` entries in the first stream and, independently, i.i.d.
`Lap(1)` entries in the second. -/
noncomputable def tape : Measure Streams :=
  (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
    (Measure.infinitePi fun _ : ℕ => PrivLearn.Generic.laplace 1)

end DPCutRelease.Main


