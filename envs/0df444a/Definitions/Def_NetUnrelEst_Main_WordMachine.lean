-- Prove2me | Definitions.Def_NetUnrelEst_Main_WordMachine
-- name    : NetUnrelEst_Main_WordMachine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:14:06.4902+00:00
-- url     : https://prove2.me/theorems/a3166be1-416e-4e21-b7c3-b67b3401f0c6
-- title:
--   The randomized real RAM with capped word instructions, its runs, and the graph input layout
-- statement:
--   The paper counts time on a randomized RAM without naming one. The machine is the published randomized real RAM `NetUnrelDesign_Main_Machine` without oracle: exact real arithmetic $+,-,\times,\div$ and comparisons, indirect real memory, integer pointer registers with $+,-$, an integer memory, a pointer-to-real cast, $\exp$, $\log$, $\sqrt{\cdot}$, a uniform $[0,1]$ draw from the tape, and halt. It has no floor, no real-to-integer conversion, and no instruction acting on a whole graph.
--
--   **Word instructions.** With word size $W$, the extension adds instructions $p[d]:=p[a]\ \mathrm{op}\ p[b]$ on pointer registers, with $\mathrm{op}$ one of $\times$, floor division, mod (by a nonzero word), bitwise and, or, xor, and left and right shift. Each costs one step and is defined only when both operands and the result lie in $[0,2^W)$; otherwise the machine is stuck there, is charged one step per step, and never halts.
--
--   **Runs.** Work counts executed instructions. The total work of a run is $\infty$ when the run does not halt, and the expected work is its lintegral under the uniform tape law. The failure probability for a property is the measure of the runs that do not halt in a state with that property. The output $\hat u$ is real output cell $0$ of the halted state, and $0$ on a non-halting run. A second program can be run after a first one from its halted state with a fresh part of the tape (`resume`).
--
--   **Input layout.** The integer cells hold $n$, $m$, $W$ and then the two endpoint labels ($0$-based) of each edge $0,\dots,m-1$. The real cells hold the reals of the input, for example $\varepsilon,\delta,p_1,\dots,p_m$.
--
--   **Formalization Note.** The base machine's pointer $\pm$ is unbounded, as published; only the new word instructions are capped. `WAdmissible` is the base `Admissible` (rational literals, no core accept/reject) applied to the base instructions.
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 3, §1.1; p. 42, Corollary G.5; p. 43, App. G.3.2

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Machine

open scoped BigOperators ENNReal Classical

noncomputable section

namespace NetUnrelEst.Main

open NetUnrelDesign.Main

/-!
# The randomized real RAM with capped word instructions, and the graph input layout

Mu-Xia Sun, *Near-Linear Estimation of Network Unreliability* (STOC 2027 submission),
doi:10.5281/zenodo.23913531, §1.1 (p. 3), App. G.3.2 (p. 43: machine words, bitwise operations),
Corollary G.5 (p. 42: word-RAM range counting). The paper names no machine; this is the reading.

* The base is the published `NetUnrelDesign.Main` machine used with its no-oracle interface: the
  `SmaleNinth` real-RAM core (exact `+ − × ÷` on reals, comparisons, indirect real memory, integer
  pointer registers), pointer `+`/`−`, an integer memory, a pointer-to-real cast, `exp`, `log`,
  `sqrt`, a uniform `[0,1]` draw from the tape, and `halt`; no floor, no real-to-integer conversion,
  no instruction acting on a whole graph.
* Word instructions act on pointer registers: `p[d] := p[a] op p[b]` with `op` one of `×`, floor
  division, `mod` (by a nonzero word), bitwise `and`, `or`, `xor`, left and right shift. Each costs
  one step and is defined only when both operands and the result lie in `[0, 2^W)` for the word
  size `W`; otherwise the machine is stuck at that instruction, charged one step per step, so the
  run never halts and its work is `∞`.
* `wrun`, `wTotalWork`, `wExpectedWork` (a lintegral over the law `jointLaw` of the uniform tape),
  `wHalts`, `wFailureProb` (the measure of the runs that do not halt in a good state) and
  `wOnEveryHalt` mirror the base machine. `wOutput` is the real output cell `0` of the halted state,
  and `0` on a non-halting run. `resume s` restarts a halted state at instruction `0` with its
  memory, tape cursor and a zero work counter (a second program run after the first).
* Input layout of a graph: integer cells `n, m, W` followed by the `2m` endpoint labels
  (`0`-based) of edges `0, …, m−1`; real cells hold the reals of the input.
-/

/-- The word operations. -/
inductive WordOp where
  | mul | div | mod | band | bor | bxor | shl | shr

/-- The value of a word operation on natural numbers (`none` for a division by zero). -/
def WordOp.eval : WordOp → ℕ → ℕ → Option ℕ
  | .mul, a, b => some (a * b)
  | .div, a, b => if b = 0 then none else some (a / b)
  | .mod, a, b => if b = 0 then none else some (a % b)
  | .band, a, b => some (a &&& b)
  | .bor, a, b => some (a ||| b)
  | .bxor, a, b => some (a ^^^ b)
  | .shl, a, b => some (a <<< b)
  | .shr, a, b => some (a >>> b)

/-- The result of a word operation on pointer values `x, y` with word size `W`, defined only when
`x, y` and the result lie in `[0, 2^W)`. -/
def wordResult (W : ℕ) (op : WordOp) (x y : ℤ) : Option ℤ :=
  if 0 ≤ x ∧ x < 2 ^ W ∧ 0 ≤ y ∧ y < 2 ^ W then
    match op.eval x.toNat y.toNat with
    | some r => if r < 2 ^ W then some (r : ℤ) else none
    | none => none
  else none

/-- An instruction: a base-machine instruction or a word instruction `p[d] := p[a] op p[b]`. -/
inductive WInstr where
  | base (i : Instr)
  | word (op : WordOp) (dst a b : ℕ)

/-- A program of the extended machine. -/
abbrev WProgram := List WInstr

/-- The base table of a program (word instructions are placeholders, dispatched by `wstep`). -/
def baseProgram (P : WProgram) : Program :=
  P.map fun i => match i with
    | .base b => b
    | .word _ _ _ _ => .halt

/-- Every real literal is rational and the core accept/reject instructions do not occur. -/
def WAdmissible (P : WProgram) : Prop := Admissible (baseProgram P)

/-- One step with word size `W`, machine tape `ω` and (unused) oracle tapes `ω'`. -/
def wstep (W : ℕ) (P : WProgram) (ω : ℕ → ℝ) (ω' : ℕ → ℕ → ℝ) (s : State noOracle) :
    State noOracle :=
  if s.halted then s else
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.base _) => step (baseProgram P) noOracleFn ω ω' s
    | some (.word op d a b) =>
        match wordResult W op (s.core.ptrs a) (s.core.ptrs b) with
        | some r => { s with
            work := s.work + 1
            core := { s.core with pc := s.core.pc + 1,
                                  ptrs := Function.update s.core.ptrs d r } }
        | none => { s with work := s.work + 1 }

/-- The state after `t` steps. -/
def wrun (W : ℕ) (P : WProgram) (s₀ : State noOracle) (ω : (ℕ → ℝ) × (ℕ → ℕ → ℝ)) (t : ℕ) :
    State noOracle :=
  (wstep W P ω.1 ω.2)^[t] s₀

/-- Total work (`∞` on a non-halting run). -/
def wTotalWork (W : ℕ) (P : WProgram) (s₀ : State noOracle) (ω : (ℕ → ℝ) × (ℕ → ℕ → ℝ)) :
    ℝ≥0∞ :=
  ⨆ t, ((wrun W P s₀ ω t).work : ℝ≥0∞)

/-- Expected total work under the uniform tape. -/
def wExpectedWork (W : ℕ) (P : WProgram) (s₀ : State noOracle) : ℝ≥0∞ :=
  ∫⁻ ω, wTotalWork W P s₀ ω ∂jointLaw

/-- The run halts. -/
def wHalts (W : ℕ) (P : WProgram) (s₀ : State noOracle) (ω : (ℕ → ℝ) × (ℕ → ℕ → ℝ)) : Prop :=
  ∃ t, (wrun W P s₀ ω t).halted = true

/-- The run halts in a state satisfying `good`. -/
def wHaltsWith (W : ℕ) (P : WProgram) (s₀ : State noOracle) (good : State noOracle → Prop)
    (ω : (ℕ → ℝ) × (ℕ → ℕ → ℝ)) : Prop :=
  ∃ t, (wrun W P s₀ ω t).halted = true ∧ good (wrun W P s₀ ω t)

/-- Every halted state reached on every tape satisfies `good`. -/
def wOnEveryHalt (W : ℕ) (P : WProgram) (s₀ : State noOracle) (good : State noOracle → Prop) :
    Prop :=
  ∀ ω t, (wrun W P s₀ ω t).halted = true → good (wrun W P s₀ ω t)

/-- The probability that the run does not halt in a good state. -/
def wFailureProb (W : ℕ) (P : WProgram) (s₀ : State noOracle) (good : State noOracle → Prop) :
    ℝ≥0∞ :=
  jointLaw {ω | ¬ wHaltsWith W P s₀ good ω}

/-- The halted state (the start state on a non-halting run). -/
def wFinalState (W : ℕ) (P : WProgram) (s₀ : State noOracle) (ω : (ℕ → ℝ) × (ℕ → ℕ → ℝ)) :
    State noOracle :=
  if h : ∃ t, (wrun W P s₀ ω t).halted = true then
    wrun W P s₀ ω (Classical.choose h) else s₀

/-- The real output cell `0` of the halted state; `0` on a non-halting run. -/
def wOutput (W : ℕ) (P : WProgram) (s₀ : State noOracle) (ω : (ℕ → ℝ) × (ℕ → ℕ → ℝ)) : ℝ :=
  if wHalts W P s₀ ω then outReal (wFinalState W P s₀ ω) 0 else 0

/-- Restart a halted state at instruction `0`, keeping memory and tape cursor, with zero work. -/
def resume (s : State noOracle) : State noOracle :=
  { s with halted := false, work := 0, core := { s.core with pc := 0 } }

/-- Integer input cells of a graph: `n, m, W`, then the endpoints of edges `0, …, m−1`. -/
def graphInts {n m : ℕ} (W : ℕ) (ends : Ends n m) : List ℤ :=
  [(n : ℤ), (m : ℤ), (W : ℤ)] ++
    (List.ofFn fun e : Fin m => [((ends e).1 : ℤ), ((ends e).2 : ℤ)]).flatten

end NetUnrelEst.Main


