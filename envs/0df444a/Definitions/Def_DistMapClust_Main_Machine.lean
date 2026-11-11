-- Prove2me | Definitions.Def_DistMapClust_Main_Machine
-- name    : DistMapClust_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:04:15.810411+00:00
-- url     : https://prove2.me/theorems/a896f473-f7c0-42e8-9ce9-f8d0cc8fcd4a
-- title:
--   The randomized oracle real RAM with opaque point registers, unit-cost oracles and a uniform tape
-- statement:
--   The paper states running times in the computational model of the metric representation and lets the Ball Intersection Algorithm be "supplied only as an oracle" (§2.1); it fixes no machine. This definition fixes one. The scalar core is the published real RAM `SmaleNinth.RAMInstr` (exact $+,-,\times,\div$, rational literals, comparison jumps, integer pointer registers, indirect real memory), extended with integer pointer arithmetic, integer memory, a pointer-to-real cast, a draw from an i.i.d. uniform $[0,1]$ tape, and halt. There is deliberately no floor or other real-to-integer conversion: together with unit-cost multiplication and division it would let a program do integer arithmetic on exponentially long numbers and so solve PSPACE-hard problems in polynomially many steps, a far stronger machine than the paper's. Reals reach the integers only through comparison jumps.
--
--   Points of the metric space are opaque values held in point registers and a point memory; the only operations on them are copying and the oracles: $\mathrm{dist}$ writes $\delta(u,v)$ to a real register, and $\mathrm{ballInt}$ calls the Ball Intersection oracle on a request set read from memory, writing the returned center and a success flag. Numerical oracles evaluate the objective $f$ on a matrix, the outer norm $f'$ on a vector, a distance mapping $h_{t,\ell}$, and the function $\lambda$, each on reals read from consecutive memory cells. Every executed instruction, oracle calls included, costs one step:
--   $$\text{steps of a run}=\#\{\text{instructions executed up to and including halt}\}\ (\infty\text{ if it never halts}).$$
--   The law of a run is the product of uniform measures on the tape.
--
--   **Formalization Note.** `Instr`, `Program`, `Admissible` (rational literals, no core `accept`/`reject`), `Oracles α`, `State α`, `step`, `run`, `HaltsWithin`, `finalState`, `initState`, `tapeLaw = Measure.infinitePi (volume on unitInterval)`, `steps`. A program counter outside the program is stuck and charged, so only `halt` halts; a halted state stutters at no cost. No instruction enumerates the facility set or compares points.
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), p. 8 (§1.2), p. 20 (§2.1), pp. 64–65 (§A.1)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

/-!
# The randomized oracle real RAM with opaque point registers

Herold, Spoerhase, Kipouridis, Marx, *A Unified Framework for Parameterized Approximation of
Clustering Objectives via Distance Mappings*, STOC 2027 submission (manuscript sha256 1d00c842…):
§2.1 (p. 20: "If this algorithm is supplied only as an oracle, the bounds below count ordinary
computation and oracle calls separately"), §1.2 (p. 8: the algorithm "accesses only the distances of
the underlying metric"), §A.1 (pp. 64–65: norms and mappings evaluated as subroutines). The paper
fixes no machine; this file fixes one, as a reading.

Encoding.
* The scalar core is the published real RAM `SmaleNinth.RAMInstr` (exact `+ − × ÷` with `x / 0 = 0`,
  literals, indirect real memory, integer pointer registers, comparison jumps). `Admissible`
  restricts real literals to rationals and forbids the core's `accept`/`reject`.
* Added: integer pointer addition and subtraction, integer memory, pointer-to-real cast, `unif`
  (the next real of a uniform `[0, 1]` tape), and `halt`. There is no `floor` or other
  real-to-integer conversion: with unit-cost `×`, `÷` it would give the machine integer division
  of exponentially long numbers, and with it polynomial-time PSPACE (Schönhage 1979), a far
  stronger machine than the paper's. Reals reach the integers only through comparison jumps.
* Points of the metric space are opaque elements of a type `α`, held in point registers and a point
  memory. The only operations on them are copying (`pointLoad`, `pointStore`, `pointCopy`) and the
  oracles: `dist` (`r[dst] := δ(u, v)`), `ballInt` (calls the Ball Intersection oracle on the
  request set read from memory, with error `μ = r[err]`; writes the returned center and a success
  flag `1`/`0`). No instruction enumerates the facility set or compares points.
* Numerical oracles read a list of reals from consecutive memory cells (start and length in pointer
  registers): `evalObj` (the objective `f` on a matrix), `evalNorm` (the outer norm `f'` on a vector),
  `evalMap` (a distance mapping `h_{t,ℓ}`, writing its value to memory), and `lam`
  (`r[dst] := λ(r[src])`). `Oracles α` bundles what an instance supplies.
* Every executed instruction costs one unit of `work`, oracle calls included. An invalid program
  counter is stuck and charged, so only `halt` halts; a halted state stutters at no cost.
-/

open MeasureTheory

namespace DistMapClust.Main

/-- What an instance supplies to the machine. -/
structure Oracles (α : Type) where
  /-- the distance function -/
  dist : α → α → ℝ
  /-- the Ball Intersection oracle: requests, error `μ`, a center or failure -/
  ball : Finset (α × ℝ) → ℝ → Option α
  /-- the objective on a matrix written as a list of reals -/
  obj : List ℝ → ℝ
  /-- the outer norm on a vector written as a list of reals -/
  norm : List ℝ → ℝ
  /-- the distance mapping `(t, ℓ)` applied to a vector written as a list of reals -/
  map : ℕ → ℕ → List ℝ → List ℝ
  /-- the function `λ` -/
  lam : ℝ → ℝ

/-- An instruction. Register, pointer and label arguments are natural numbers; no constructor
carries a function or a point.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd d a b`, `pointerSub d a b`: `p[d] := p[a] ± p[b]`.
* `integerLoad d a`, `integerStore a b`: `p[d] := I[p[a]]`, `I[p[a]] := p[b]` (integer memory).
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `unif d`: `r[d] :=` the next real of the uniform tape.
* `pointLoad d a`, `pointStore a s`, `pointCopy d s`: `q[d] := Q[p[a]]`, `Q[p[a]] := q[s]`,
  `q[d] := q[s]` (point registers `q`, point memory `Q`).
* `dist d u v`: `r[d] := δ(q[u], q[v])`.
* `ballInt d flag base len err`: with `m = p[len]`, the requests are
  `(Q[p[base] + t], M[p[base] + t])` for `t < m`; calls the oracle with error `r[err]`; on success
  `q[d] :=` the center and `r[flag] := 1`, on failure `r[flag] := 0`.
* `evalObj d base len`, `evalNorm d base len`: `r[d] :=` the oracle on `M[p[base] .. p[base] + p[len])`.
* `evalMap t l base len outp`: writes `h_{p[t], p[l]}(M[p[base] .. p[base] + p[len]))` to the cells
  from `p[outp]` on.
* `lam d a`: `r[d] := λ(r[a])`.
* `halt`: stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst src : ℕ)
  | unif (dst : ℕ)
  | pointLoad (dst address : ℕ)
  | pointStore (address src : ℕ)
  | pointCopy (dst src : ℕ)
  | dist (dst u v : ℕ)
  | ballInt (dst flag base len err : ℕ)
  | evalObj (dst base len : ℕ)
  | evalNorm (dst base len : ℕ)
  | evalMap (t l base len outp : ℕ)
  | lam (dst src : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every input. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core's `accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- The static core table of `P` (non-core positions are placeholders, never executed by the core). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state: the core configuration (program counter, real registers, pointers, real
memory), integer memory, point registers, point memory, the tape cursor, the halted flag and the
work counter. -/
structure State (α : Type) where
  core : SmaleNinth.RAMConfig
  intMem : ℤ → ℤ
  pts : ℕ → α
  ptMem : ℤ → α
  cursor : ℕ
  halted : Bool
  work : ℕ

/-- The uniform tape. -/
abbrev Tape := ℕ → unitInterval

/-- The reals in the cells `base, …, base + len − 1`. -/
def readList (mem : ℤ → ℝ) (base : ℤ) (len : ℕ) : List ℝ :=
  List.ofFn fun t : Fin len => mem (base + (t : ℕ))

/-- Memory with the list `l` written to the cells from `base` on. -/
def writeList (mem : ℤ → ℝ) (base : ℤ) (l : List ℝ) : ℤ → ℝ :=
  fun z => if base ≤ z ∧ z < base + l.length then l.getD (z - base).toNat 0 else mem z

open Classical in
/-- The request set `{(Q[base + t], M[base + t]) | t < len}`. -/
noncomputable def readRequests {α : Type} (ptMem : ℤ → α) (mem : ℤ → ℝ) (base : ℤ) (len : ℕ) :
    Finset (α × ℝ) :=
  (List.ofFn fun t : Fin len => (ptMem (base + (t : ℕ)), mem (base + (t : ℕ)))).toFinset

/-- One step of program `P` with oracles `O` on tape `ν`. Halted states stutter at no cost; every
other step costs one unit of work. -/
noncomputable def step {α : Type} (P : Program) (O : Oracles α) (ν : Tape) (s : State α) :
    State α :=
  if s.halted then s else
    let c := s.core
    let t : State α := { s with work := s.work + 1, core := { c with pc := c.pc + 1 } }
    let setR (d : ℕ) (x : ℝ) : State α :=
      { t with core := { t.core with regs := Function.update c.regs d x } }
    let setP (d : ℕ) (z : ℤ) : State α :=
      { t with core := { t.core with ptrs := Function.update c.ptrs d z } }
    match P[c.pc]? with
    | none => { s with work := s.work + 1 }
    | some (.core _) => { t with core := SmaleNinth.RAMStep (coreProgram P) c }
    | some (.pointerAdd d a b) => setP d (c.ptrs a + c.ptrs b)
    | some (.pointerSub d a b) => setP d (c.ptrs a - c.ptrs b)
    | some (.integerLoad d a) => setP d (s.intMem (c.ptrs a))
    | some (.integerStore a b) =>
        { t with intMem := Function.update s.intMem (c.ptrs a) (c.ptrs b) }
    | some (.pointerReal d a) => setR d (c.ptrs a : ℝ)
    | some (.unif d) => { (setR d (ν s.cursor : ℝ)) with cursor := s.cursor + 1 }
    | some (.pointLoad d a) => { t with pts := Function.update s.pts d (s.ptMem (c.ptrs a)) }
    | some (.pointStore a v) => { t with ptMem := Function.update s.ptMem (c.ptrs a) (s.pts v) }
    | some (.pointCopy d v) => { t with pts := Function.update s.pts d (s.pts v) }
    | some (.dist d u v) => setR d (O.dist (s.pts u) (s.pts v))
    | some (.ballInt d flag base len err) =>
        match O.ball (readRequests s.ptMem c.mem (c.ptrs base) (c.ptrs len).toNat) (c.regs err) with
        | some x => { (setR flag 1) with pts := Function.update s.pts d x }
        | none => setR flag 0
    | some (.evalObj d base len) => setR d (O.obj (readList c.mem (c.ptrs base) (c.ptrs len).toNat))
    | some (.evalNorm d base len) =>
        setR d (O.norm (readList c.mem (c.ptrs base) (c.ptrs len).toNat))
    | some (.evalMap tt l base len outp) =>
        let value := O.map (c.ptrs tt).toNat (c.ptrs l).toNat
          (readList c.mem (c.ptrs base) (c.ptrs len).toNat)
        { t with core := { t.core with mem := writeList c.mem (c.ptrs outp) value } }
    | some (.lam d a) => setR d (O.lam (c.regs a))
    | some .halt => { t with halted := true }

/-- The state after `n` steps. -/
noncomputable def run {α : Type} (P : Program) (O : Oracles α) (ν : Tape) (s₀ : State α)
    (n : ℕ) : State α :=
  (step P O ν)^[n] s₀

/-- The run halts having done at most `T` work. -/
def HaltsWithin {α : Type} (P : Program) (O : Oracles α) (ν : Tape) (s₀ : State α) (T : ℝ) :
    Prop :=
  ∃ n, (run P O ν s₀ n).halted = true ∧ ((run P O ν s₀ n).work : ℝ) ≤ T

open Classical in
/-- The halted state of the run, or `none` if it never halts. -/
noncomputable def finalState {α : Type} (P : Program) (O : Oracles α) (ν : Tape) (s₀ : State α) :
    Option (State α) :=
  if h : ∃ n, (run P O ν s₀ n).halted = true then some (run P O ν s₀ (Nat.find h)) else none

/-- The start state: program counter, registers, pointers, cursor and work `0`; integer memory
holds `ints` from cell `0`, real memory `reals` from cell `0`, point memory `points` from cell `0`;
every other integer or real cell is `0`, and every point register and other point cell holds
`dflt`. -/
noncomputable def initState {α : Type} (ints : List ℤ) (reals : List ℝ) (points : List α)
    (dflt : α) : State α :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩,
    fun z => if 0 ≤ z then ints.getD z.toNat 0 else 0,
    fun _ => dflt,
    fun z => if 0 ≤ z then points.getD z.toNat dflt else dflt,
    0, false, 0⟩

/-- The law of the tape: i.i.d. uniform on `[0, 1]`. -/
noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)

/-- The number of steps of a run, `∞` if it never halts. -/
noncomputable def steps {α : Type} (P : Program) (O : Oracles α) (ν : Tape) (s₀ : State α) :
    ENNReal :=
  match finalState P O ν s₀ with
  | some S => (S.work : ENNReal)
  | none => ⊤

end DistMapClust.Main


