-- Prove2me | Definitions.Def_BayesOptStop_Scheme_Machine
-- name    : BayesOptStop_Scheme_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:17:57.474767+00:00
-- url     : https://prove2.me/theorems/c8169e86-4f66-450e-a716-8689131bb405
-- title:
--   The cost model: a unit-cost randomized real RAM with online observation and information oracles
-- statement:
--   Programs are finite lists of instructions over the published core `SmaleNinth.RAMInstr` (exact $+,-,\times,\div$, comparisons, indirect real memory, pointer arithmetic by $\pm1$), extended — following the pattern of the published `PureDPQR_Machine` — with integer pointer addition/subtraction, integer memory, a pointer-to-real cast, $\exp$, $\log$, and `unif` (the next cell of a tape of independent Uniform$(0,1)$ values), plus:
--   * `observe`: reveals the canonical index (least $q$ with the same value) of the next observation — the only access to the path; `accept`: selects the latest observation and halts; `halt`: stops with reward $0$;
--   * `probQ`, `valueQ`: the oracles of p. 8, returning $\Pr[X_{t+1}=v_q\mid h_t]$ and $\mathbb E[\max_{t'}X_{t'}\mid h_t]$ for a history stored in integer memory. An oracle is **admissible** if it answers correctly at every history of positive probability; elsewhere it is arbitrary.
--
--   A program is admissible if its real literals are rational and it avoids the core's accept/reject; oracle-free programs (IID, NON-IID) read $\pi$ and the PMF table from input memory. No floor, no real-to-integer cast, no instruction carries a function. Every executed instruction, oracle calls included, costs one step. Input layouts: CORREL (K, m, n; ε, v), NON-IID and IID (K, m, n; ε, v, π, PMF table), Algorithm 3 calls (K, m, n, j, path; α₀, η, κ, v) and Lemma 4 calls (K, m, n, j, t, history; α₀, ε, δ, v); estimates are output in real cell $-1$. The expected reward is over world, path and tape.
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, §2.1, pp. 8–9 (cost and information access model); App. A.2, p. 35

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_BayesOptStop_Scheme_Model

open scoped BigOperators
open MeasureTheory

namespace BayesOptStop.Scheme

/-!
# The cost model: a unit-cost randomized real RAM with online access and information oracles

Source: AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), held STOC 2027 submission,
SHA-256 fecfa05a…c4241, §2.1 p. 8: "We measure running time by the number of arithmetic
operations and calls to the information oracles defined below, counting each as one unit of
time", and the information access model (pp. 8–9; App. A.2, p. 35).

The paper names no machine. This one follows the published pattern `PureDPQR.Machine` on the
published core `SmaleNinth.RAMInstr` (exact `+ − × ÷`, real literals, indirect real memory,
pointer set/copy/increment/decrement, comparison jumps), extended with:
* integer pointer addition/subtraction, an integer memory, a pointer-to-real cast;
* `exp` and `log` (unit cost; `log` is `Real.log`, so `log 0 = 0`; division by `0` is `0`);
* `unif`: the next cell of a tape of independent Uniform(0,1) values;
* `observe`: writes into a pointer register the index of the next observation, and is the only
  access to the realized path. It reveals the **canonical index** of the value `X_t` (the least
  `q` with `v_q = X_t`), i.e. exactly the observed value; after the `n`-th observation it writes
  `-1`;
* `accept`: selects the most recently observed `X_t` and halts (with no observation yet it
  halts with reward `0`); `halt` stops without selecting (reward `0`);
* `probQ`, `valueQ`: the probability and value oracles of p. 8, the only access to `π` and the
  `D^(h)` in the CORREL model. The history is the list of integers in integer memory cells
  `p[b], p[b]+1, …, p[b]+p[len]-1`. `probQ` answers `Pr[X_{t+1} = v_q | h_t]`, `valueQ`
  answers `E[max_{t'} X_{t'} | h_t]` (`Oracle.Admissible`); at a history of probability `0`,
  or one that is not a list of value indices, the answers are arbitrary.

There is no floor, no real-to-integer cast and no pointer multiplication, and no constructor
carries a function. `Admissible` requires rational literals and forbids the core's
`accept`/`reject`; `OracleFree` forbids the oracle instructions (IID and NON-IID models, where
`π` and the PMF table are in input memory instead). Every executed instruction, oracle calls
included, costs one unit; an invalid program counter is stuck and charged, so only `accept`
and `halt` halt. After halting the state stutters at no cost.
-/

/-- An instruction of the machine. -/
inductive Instr where
  /-- A `SmaleNinth` real-RAM instruction. -/
  | core (instruction : SmaleNinth.RAMInstr)
  /-- `p[dst] := p[a] + p[b]`. -/
  | pointerAdd (dst a b : ℕ)
  /-- `p[dst] := p[a] - p[b]`. -/
  | pointerSub (dst a b : ℕ)
  /-- `p[dst] := I[p[address]]` (integer memory). -/
  | integerLoad (dst address : ℕ)
  /-- `I[p[address]] := p[src]`. -/
  | integerStore (address src : ℕ)
  /-- `r[dst] := (p[pointer] : ℝ)`. -/
  | pointerReal (dst pointer : ℕ)
  /-- `r[dst] := exp r[src]`. -/
  | exp (dst src : ℕ)
  /-- `r[dst] := log r[src]`. -/
  | log (dst src : ℕ)
  /-- `r[dst] :=` the next uniform tape value. -/
  | unif (dst : ℕ)
  /-- `p[dst] :=` the canonical index of the next observation (`-1` after the last). -/
  | observe (dst : ℕ)
  /-- Select the most recent observation and halt. -/
  | accept
  /-- `r[dst] := Pr[X_{t+1} = v_{p[q]} | h_t]` for the history stored at `p[base]`, length `p[len]`. -/
  | probQ (dst len base q : ℕ)
  /-- `r[dst] := E[max_{t'} X_{t'} | h_t]` for the history stored at `p[base]`, length `p[len]`. -/
  | valueQ (dst len base : ℕ)
  /-- Halt without selecting. -/
  | halt

/-- A program: one finite list of instructions. -/
abbrev Program := List Instr

/-- Every real literal is rational and the core's `accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The program makes no oracle call (IID and NON-IID models). -/
def OracleFree (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .probQ _ _ _ _ | .valueQ _ _ _ => False
    | _ => True

/-- The static core table of `P` (extension instructions are placeholders, never executed by
the core). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- An oracle: answers to probability queries `(history, q)` and value queries `history`. -/
structure Oracle where
  /-- The probability oracle. -/
  prob : List ℤ → ℤ → ℝ
  /-- The value oracle. -/
  value : List ℤ → ℝ

/-- A machine state. `observed` counts the observations revealed so far; `accepted` is the
(0-based) time of the selected observation. -/
structure State where
  /-- Program counter, real registers, pointer registers, real memory. -/
  core : SmaleNinth.RAMConfig
  /-- Integer memory. -/
  integerMemory : ℤ → ℤ
  /-- Tape cursor. -/
  cursor : ℕ
  /-- Number of observations revealed. -/
  observed : ℕ
  /-- The selected time, if any. -/
  accepted : Option ℕ
  /-- Halted flag. -/
  halted : Bool
  /-- Work counter. -/
  work : ℕ

/-- The history stored in integer memory from cell `p[base]`, of length `p[len]`. -/
def readHistory (s : State) (len base : ℕ) : List ℤ :=
  List.ofFn fun i : Fin (s.core.ptrs len).toNat => s.integerMemory (s.core.ptrs base + (i : ℤ))

/-- One step of `P` with observation stream `obs`, oracle `o` and uniform tape `ω`. -/
noncomputable def step (P : Program) (obs : List ℤ) (o : Oracle) (ω : ℕ → ℝ) (s : State) :
    State :=
  if s.halted then s else
    let t : State := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
    match P[s.core.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) s.core }
    | some (.pointerAdd d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b) } }
    | some (.pointerSub d a b) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b) } }
    | some (.integerLoad d a) =>
        { t with core := { t.core with
            ptrs := Function.update s.core.ptrs d (s.integerMemory (s.core.ptrs a)) } }
    | some (.integerStore a b) =>
        { t with integerMemory :=
            Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b) }
    | some (.pointerReal d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
    | some (.exp d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (Real.exp (s.core.regs a)) } }
    | some (.log d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (Real.log (s.core.regs a)) } }
    | some (.unif d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with regs := Function.update s.core.regs d (ω s.cursor) } }
    | some (.observe d) =>
        { t with
          observed := if s.observed < obs.length then s.observed + 1 else s.observed
          core := { t.core with
            ptrs := Function.update s.core.ptrs d (obs.getD s.observed (-1)) } }
    | some .accept =>
        { t with
          halted := true
          accepted := if s.observed = 0 then none else some (s.observed - 1) }
    | some (.probQ d len base q) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d
              (o.prob (readHistory s len base) (s.core.ptrs q)) } }
    | some (.valueQ d len base) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (o.value (readHistory s len base)) } }
    | some .halt => { t with halted := true }

/-- The state after `k` steps. -/
noncomputable def run (P : Program) (obs : List ℤ) (o : Oracle) (s₀ : State) (ω : ℕ → ℝ)
    (k : ℕ) : State :=
  (step P obs o ω)^[k] s₀

/-- The initial state: all registers, pointers, counters `0`; integer memory holds `ints` from
cell `0`, real memory holds `reals` from cell `0`, all other cells `0`. -/
noncomputable def initState (ints : List ℤ) (reals : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0, 0, 0, none, false, 0⟩

/-- The run halts within `B` steps. -/
def HaltsWithin (P : Program) (obs : List ℤ) (o : Oracle) (s₀ : State) (ω : ℕ → ℝ)
    (B : ℝ) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ B ∧ (run P obs o s₀ ω k).halted = true

open Classical in
/-- The first halted state of the run, if the run halts. -/
noncomputable def finalState (P : Program) (obs : List ℤ) (o : Oracle) (s₀ : State)
    (ω : ℕ → ℝ) : Option State :=
  if h : ∃ k, (run P obs o s₀ ω k).halted = true then some (run P obs o s₀ ω (Nat.find h))
  else none

/-- The real output of a run: real memory cell `-1` at the first halted state, `0` if the run
never halts. -/
noncomputable def output (P : Program) (obs : List ℤ) (o : Oracle) (s₀ : State)
    (ω : ℕ → ℝ) : ℝ :=
  match finalState P obs o s₀ ω with
  | some s => s.core.mem (-1)
  | none => 0

/-- The uniform tape: independent Uniform(0,1) values. -/
noncomputable def uniformTape : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => volume.restrict (Set.Ioo (0 : ℝ) 1)

/-- A tape in the support: every cell in `(0,1)`. -/
def TapeInSupport (ω : ℕ → ℝ) : Prop :=
  ∀ i, ω i ∈ Set.Ioo (0 : ℝ) 1

namespace Instance

variable {K m n : ℕ} (I : Instance K m n)

/-- The canonical index of the value `v_q`: the least index carrying the same value. -/
noncomputable def canonIdx (q : Fin m) : ℤ :=
  (((Finset.univ.filter fun q' => I.v q' = I.v q).min' ⟨q, by simp⟩ : Fin m) : ℕ)

/-- The observation stream of a path: the canonical indices of `X_1, …, X_n`. -/
noncomputable def obsList (ω : Fin n → Fin m) : List ℤ :=
  List.ofFn fun s => I.canonIdx (ω s)

/-- The canonical indices of the history `h_t` of `ω`. -/
noncomputable def histList (t : ℕ) (ω : Fin n → Fin m) : List ℤ :=
  (I.obsList ω).take t

/-- A path is consistent with a history given as a list of value indices. -/
def HistAgree (hs : List (Fin m)) (ω : Fin n → Fin m) : Prop :=
  ∀ s : Fin n, ∀ h : s.val < hs.length, I.v (ω s) = I.v (hs.get ⟨s.val, h⟩)

open Classical in
/-- `Pr[h]` for a history given as a list of value indices. -/
noncomputable def histProb (hs : List (Fin m)) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (I.HistAgree hs), I.prob ω

open Classical in
/-- `E[max_{t'} X_{t'} | h]` for a history `h` (the value oracle's answer). -/
noncomputable def histValue (hs : List (Fin m)) : ℝ :=
  (∑ ω ∈ Finset.univ.filter (I.HistAgree hs), I.prob ω * I.pathMax ω) / I.histProb hs

open Classical in
/-- `Pr[X_{t+1} = v_q | h_t]` for a history `h_t` of length `t < n` (the probability oracle's
answer). -/
noncomputable def histNext (hs : List (Fin m)) (q : Fin m) : ℝ :=
  (∑ ω ∈ Finset.univ.filter (fun ω => I.HistAgree hs ω ∧
      ∃ h : hs.length < n, I.v (ω ⟨hs.length, h⟩) = I.v q), I.prob ω) / I.histProb hs

/-- The oracle answers correctly at every history of positive probability (any list of value
indices of length `≤ n`, canonical or not); elsewhere its answers are arbitrary. -/
def OracleAdmissible (o : Oracle) : Prop :=
  ∀ hs : List (Fin m), hs.length ≤ n → 0 < I.histProb hs →
    o.value (hs.map fun q => ((q : ℕ) : ℤ)) = I.histValue hs ∧
      (hs.length < n → ∀ q : Fin m, o.prob (hs.map fun q => ((q : ℕ) : ℤ)) ((q : ℕ) : ℤ) =
        I.histNext hs q)

/-- The reward of a halted state on the path `ω`: the selected `X_t`, or `0`. -/
noncomputable def acceptedReward (ω : Fin n → Fin m) (s : State) : ℝ :=
  match s.accepted with
  | some k => I.payoff k ω
  | none => 0

/-- The reward of the run of `P` on the path `ω` and tape `u` (`0` if it never halts). -/
noncomputable def runReward (P : Program) (o : Oracle) (s₀ : State) (ω : Fin n → Fin m)
    (u : ℕ → ℝ) : ℝ :=
  match finalState P (I.obsList ω) o s₀ u with
  | some s => I.acceptedReward ω s
  | none => 0

/-- The expected reward `r(A)` of the program: over the world, the path and the tape. -/
noncomputable def programReward (P : Program) (o : Oracle) (s₀ : State) : ℝ :=
  ∑ ω, I.prob ω * ∫ u, I.runReward P o s₀ ω u ∂uniformTape

/-- The CORREL input for accuracy `ε`: integer memory `K, m, n`; real memory `ε, v_0, …, v_{m-1}`.
The prior and the laws are reached only through the oracles. -/
noncomputable def correlInput (ε : ℝ) : State :=
  initState [(K : ℤ), (m : ℤ), (n : ℤ)] (ε :: List.ofFn I.v)

/-- The input of a call `W_j(ω, η, κ)` of the recursive estimator (Algorithm 3, p. 20), CORREL
access: integer memory `K, m, n, j`, then the canonical indices of `ω_1, …, ω_n`; real memory
`α₀, η, κ, v_0, …, v_{m-1}`. The estimate is read from real memory cell `-1` (`output`). -/
noncomputable def inputW (α₀ η κ : ℝ) (j : ℕ) (ω : Fin n → Fin m) : State :=
  initState ([(K : ℤ), (m : ℤ), (n : ℤ), (j : ℤ)] ++ I.obsList ω) ([α₀, η, κ] ++ List.ofFn I.v)

/-- The input of the estimation of `Z^(j)_t(h_t)` (Lemma 4, p. 19), CORREL access: integer memory
`K, m, n, j, t`, then the canonical indices of the history `h_t` of `ω`; real memory
`α₀, ε, δ, v_0, …, v_{m-1}`. The estimate `L^(j)_t(h_t)` is read from real memory cell `-1`. -/
noncomputable def inputZ (α₀ ε δ : ℝ) (j t : ℕ) (ω : Fin n → Fin m) : State :=
  initState ([(K : ℤ), (m : ℤ), (n : ℤ), (j : ℤ), (t : ℤ)] ++ I.histList t ω)
    ([α₀, ε, δ] ++ List.ofFn I.v)

end Instance

/-- The NON-IID input for accuracy `ε`: integer memory `K, m, n`; real memory `ε`, then
`v_0, …, v_{m-1}`, then `π_0, …, π_{K-1}`, then the PMF table row-major in `(h, s, q)`
(`D^(h)_s(v_q)` in cell `1 + m + K + (h·n + s)·m + q`). -/
noncomputable def NonIIDData.input {K m n : ℕ} (D : NonIIDData K m n) (ε : ℝ) : State :=
  initState [(K : ℤ), (m : ℤ), (n : ℤ)]
    (ε :: (List.ofFn D.v ++ List.ofFn D.prior ++
      (List.ofFn fun h => (List.ofFn fun s => List.ofFn fun q => D.pmf h s q).flatten).flatten))

/-- The IID input for accuracy `ε` and horizon `n`: integer memory `K, m, n`; real memory `ε`,
then `v`, then `π`, then the PMF table row-major in `(h, q)` (`D^(h)(v_q)` in cell
`1 + m + K + h·m + q`). -/
noncomputable def IIDData.input {K m : ℕ} (D : IIDData K m) (n : ℕ) (ε : ℝ) : State :=
  initState [(K : ℤ), (m : ℤ), (n : ℤ)]
    (ε :: (List.ofFn D.v ++ List.ofFn D.prior ++
      (List.ofFn fun h => List.ofFn fun q => D.pmf h q).flatten))

/-- The oracle with all answers `0`, passed to oracle-free programs. -/
def Oracle.zero : Oracle := ⟨fun _ _ => 0, fun _ => 0⟩

end BayesOptStop.Scheme


