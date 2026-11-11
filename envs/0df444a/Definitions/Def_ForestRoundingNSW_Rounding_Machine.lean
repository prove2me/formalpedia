-- Prove2me | Definitions.Def_ForestRoundingNSW_Rounding_Machine
-- name    : ForestRoundingNSW_Rounding_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:50:30.989888+00:00
-- url     : https://prove2.me/theorems/9aad3670-71bd-49dd-bb3d-66bf620fe742
-- title:
--   The randomized real RAM with exact unit-cost oracles for f_i, F_{f_i} and ∂_j F_{f_i}; input layout, output bundles, tape law
-- statement:
--   The algorithms run on a **unit-cost randomized real RAM**: the published real-RAM core (exact $+,-,\times,\div$ on reals, comparisons, real registers, integer pointer registers, indirect real memory), extended with pointer addition and subtraction, the cast of a pointer to a real, an instruction `unif` that reads the next real of an i.i.d. uniform $[0,1]$ tape, three **exact oracle instructions** for the lower functions $g_1,\dots,g_n$, and `halt`:
--
--   * `evalf`: $g_i(T)$ for a $0/1$ block $T$ of length $m$ in memory;
--   * `evalF`: $F_{g_i}(z)$ for a real block $z$ of length $m$;
--   * `evalD`: $\partial_k F_{g_i}(z)$.
--
--   This is the paper's exact-evaluation convention ("we assume exact access to $F$ and $\nabla F$"). Every executed instruction, oracle calls included, costs one step. A program is **admissible** if its real literals are rational and it stops only through `halt`; `NoUnif` marks a deterministic program.
--
--   On input $(n,m,x,G,(E_i))$ the pointer registers hold $p[0]=n$, $p[1]=m$, memory cell $i m+j$ holds $x_{ij}$, cell $nm+j$ the indicator of $j\in G$, and cell $nm+m+im+j$ the indicator of $j\in E_i$. At halt, cell $-1-(im+j)$ holds output entry $(i,j)$: `outBundles` reads it as bundles $S_i=\{j:\text{cell}=1\}$, `outMatrix` as a real matrix. The randomness is the tape $\nu\in[0,1]^{\mathbb N}$ with law `tapeLaw` $=\mathrm{Unif}[0,1]^{\mathbb N}$.
--
--   **Formalization Note.** An oracle call with an agent or coordinate index out of range, or a program counter outside the program, makes the run stuck: it never halts. A run that never halts outputs empty bundles (the zero matrix); every theorem asserts halting on every tape, so this value is never used. There is no floor, real-to-integer conversion, integer multiplication, root, exponential or logarithm instruction.
-- source:
--   Feng, Hu, Li, Zhang, Correlated Forest Rounding for Unweighted Nash Social Welfare, STOC 2027 submission (manuscript sha256 0c7af642…), p. 14, §2.2 (exact-evaluation convention); p. 19, Lemma 3.1; p. 22, Lemma 3.3; p. 24, Proposition 3.4

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_ForestRoundingNSW_Rounding_SetFunctions

/-!
# The randomized real RAM with exact oracles for the lower functions

Feng, Hu, Li, Zhang, *Correlated Forest Rounding for Unweighted Nash Social Welfare*, STOC 2027
submission (manuscript sha256 0c7af642…): §2.2 (p. 14, "we assume exact access to F and ∇F"),
Lemma 3.1 (p. 19: "polynomially many exact derivative evaluations, arithmetic operations, and
comparisons"), Lemma 3.3 (p. 22) and Proposition 3.4 (p. 24: "polynomially many arithmetic
operations and evaluations of the lower functions and their multilinear derivatives"). The paper
names no machine; this file fixes one.

Encoding.
* The core is the published real RAM `SmaleNinth.RAMInstr` (exact `+ − × ÷` on reals with
  `x / 0 = 0`, real literals, the jumps `r ≤ 0` and `p ≤ p'`, integer pointer registers with
  set/copy/increment/decrement, indirect real memory `ℤ → ℝ`). `Admissible` restricts its real
  literals to rationals and forbids its own `accept`/`reject`: a run stops only through `halt`.
* Added instructions: pointer `+` and `−`; the cast of a pointer to a real; `unif`, which writes
  the next real of an i.i.d. uniform `[0, 1]` tape; three exact oracle instructions for the
  lower functions `g_i` (agent `i = p[a]`, `0 ≤ i < n`): `evalf` writes `g_i(T)` for the set
  `T = {j < m : M[p[b] + j] = 1}`, `evalF` writes `F_{g_i}(z)` for `z_j = M[p[b] + j]` (`j < m`),
  `evalD` writes `∂_k F_{g_i}(z)` for `k = p[c]`, `0 ≤ k < m`; and `halt`. An oracle call with an
  agent or coordinate index out of range makes the run stuck. There is no floor, no
  real-to-integer conversion, no integer multiplication, no square root, exponential or logarithm.
* Cost: every executed instruction, oracle calls included, is one step (`work`). A program
  counter outside the program makes the run stuck; a stuck run is charged every further step and
  never halts. After `halt` the state is unchanged.
* Randomness: the tape `ν : ℕ → [0, 1]`; the `k`-th executed `unif` reads `ν k`. The law of the
  tape is `tapeLaw = Unif[0, 1]^ℕ` (`Measure.infinitePi`). The oracles are deterministic.
* Input (`initState n m x G E`): pointer registers `p[0] = n`, `p[1] = m`; real memory cell
  `i·m + j` holds `x_ij` (`i < n`, `j < m`), cell `n·m + j` the indicator of `j ∈ G`, cell
  `n·m + m + i·m + j` the indicator of `j ∈ E_i`; every other cell and register is `0`.
* Output: at halt, real cell `−1 − (i·m + j)` holds entry `(i, j)` of an `n × m` output block.
  `outBundles` reads it as bundles `S_i = {j : cell = 1}`, `outMatrix` as a real matrix; a run
  that never halts outputs empty bundles / the zero matrix.
-/

open MeasureTheory

namespace ForestRoundingNSW.Rounding

/-- An instruction of the randomized oracle real RAM. -/
inductive Instr where
  /-- An instruction of the published real-RAM core. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `p[dst] := p[a] + p[b]`. -/
  | pointerAdd (dst a b : ℕ)
  /-- `p[dst] := p[a] − p[b]`. -/
  | pointerSub (dst a b : ℕ)
  /-- `r[dst] := (p[src] : ℝ)`. -/
  | pointerReal (dst src : ℕ)
  /-- `r[dst] :=` the next real of the uniform `[0, 1]` tape. -/
  | unif (dst : ℕ)
  /-- `r[dst] := g_{p[a]}({j < m : M[p[b] + j] = 1})`. -/
  | evalf (dst a b : ℕ)
  /-- `r[dst] := F_{g_{p[a]}}(z)` with `z_j = M[p[b] + j]`. -/
  | evalF (dst a b : ℕ)
  /-- `r[dst] := ∂_{p[c]} F_{g_{p[a]}}(z)` with `z_j = M[p[b] + j]`. -/
  | evalD (dst a c b : ℕ)
  /-- Halt. -/
  | halt

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Rational literals only, and none of the core's own `accept`/`reject`. -/
def Admissible (P : Program) : Prop :=
  ∀ i ∈ P, (∀ dst c, i = .core (.const dst c) → ∃ q : ℚ, c = (q : ℝ)) ∧
    i ≠ .core .accept ∧ i ≠ .core .reject

/-- The program draws no uniform reals (a deterministic program). -/
def NoUnif (P : Program) : Prop :=
  ∀ i ∈ P, ∀ dst, i ≠ .unif dst

/-- The core instruction at a position (non-core positions are never passed to the core). -/
def Instr.coreOf : Instr → SmaleNinth.RAMInstr
  | .core i => i
  | _ => .accept

/-- A machine state: core configuration, number of uniform reals drawn, number of executed
steps, and the halted and stuck flags. -/
structure State where
  /-- Program counter, real registers, pointer registers and memory. -/
  cfg : SmaleNinth.RAMConfig
  /-- Number of uniform reals drawn. -/
  unifs : ℕ
  /-- Number of executed steps. -/
  work : ℕ
  /-- Whether the machine has halted. -/
  halted : Bool
  /-- Whether the run is stuck (invalid program counter or oracle index). -/
  stuck : Bool

/-- The uniform tape. -/
abbrev Tape := ℕ → unitInterval

/-- The lower functions, one per agent, given to the oracle instructions. -/
abbrev Oracle (n m : ℕ) := Fin n → Finset (Fin m) → ℝ

/-- The real vector `(M[a + j])_{j < m}`. -/
def readVec (mem : ℤ → ℝ) (a : ℤ) (m : ℕ) : Fin m → ℝ :=
  fun j => mem (a + (j : ℤ))

open Classical in
/-- The set `{j < m : M[a + j] = 1}`. -/
noncomputable def readSet (mem : ℤ → ℝ) (a : ℤ) (m : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun j => mem (a + (j : ℤ)) = 1

/-- One step of program `P` with oracle `g` on the tape `ν`. -/
noncomputable def step {n m : ℕ} (P : Program) (g : Oracle n m) (ν : Tape) (S : State) :
    State :=
  if S.halted || S.stuck then S else
    let c := S.cfg
    let next (c' : SmaleNinth.RAMConfig) : State :=
      { S with cfg := { c' with pc := c.pc + 1 }, work := S.work + 1 }
    let stuck : State := { S with stuck := true, work := S.work + 1 }
    match P[c.pc]? with
    | none => stuck
    | some (.core _) =>
        { S with cfg := SmaleNinth.RAMStep (P.map Instr.coreOf) c, work := S.work + 1 }
    | some (.pointerAdd dst a b) =>
        next { c with ptrs := Function.update c.ptrs dst (c.ptrs a + c.ptrs b) }
    | some (.pointerSub dst a b) =>
        next { c with ptrs := Function.update c.ptrs dst (c.ptrs a - c.ptrs b) }
    | some (.pointerReal dst src) =>
        next { c with regs := Function.update c.regs dst (c.ptrs src : ℝ) }
    | some (.unif dst) =>
        { (next { c with regs := Function.update c.regs dst (ν S.unifs : ℝ) }) with
          unifs := S.unifs + 1 }
    | some (.evalf dst a b) =>
        if h : 0 ≤ c.ptrs a ∧ (c.ptrs a).toNat < n then
          next { c with regs := (Function.update c.regs dst
            (g ⟨(c.ptrs a).toNat, h.2⟩ (readSet c.mem (c.ptrs b) m))) }
        else stuck
    | some (.evalF dst a b) =>
        if h : 0 ≤ c.ptrs a ∧ (c.ptrs a).toNat < n then
          next { c with regs := (Function.update c.regs dst
            (NonmonotoneSubmod.Shared.F (g ⟨(c.ptrs a).toNat, h.2⟩) (readVec c.mem (c.ptrs b) m))) }
        else stuck
    | some (.evalD dst a k b) =>
        if h : (0 ≤ c.ptrs a ∧ (c.ptrs a).toNat < n) ∧ (0 ≤ c.ptrs k ∧ (c.ptrs k).toNat < m) then
          next { c with regs := (Function.update c.regs dst
            (partialDeriv (NonmonotoneSubmod.Shared.F (g ⟨(c.ptrs a).toNat, h.1.2⟩))
              ⟨(c.ptrs k).toNat, h.2.2⟩ (readVec c.mem (c.ptrs b) m))) }
        else stuck
    | some .halt => { S with halted := true, work := S.work + 1 }

/-- The state after `t` steps from `S`. -/
noncomputable def run {n m : ℕ} (P : Program) (g : Oracle n m) (ν : Tape) (S : State) (t : ℕ) :
    State :=
  (step P g ν)^[t] S

/-- `P` started in `S` halts after at most `T` executed steps. -/
def HaltsWithin {n m : ℕ} (P : Program) (g : Oracle n m) (ν : Tape) (S : State) (T : ℕ) :
    Prop :=
  ∃ t, (run P g ν S t).halted = true ∧ (run P g ν S t).work ≤ T

open Classical in
/-- The halted state of `P` started in `S`, or `none` if it never halts. -/
noncomputable def finalState {n m : ℕ} (P : Program) (g : Oracle n m) (ν : Tape) (S : State) :
    Option State :=
  if h : ∃ t, (run P g ν S t).halted = true then some (run P g ν S (Nat.find h)) else none

/-- The value at cell `a` of an `r × w` block stored row-major from cell `base` (`none` outside
the block). -/
def blockAt (base : ℤ) (r w : ℕ) (cell : Fin r → Fin w → ℝ) (a : ℤ) : Option ℝ :=
  if base ≤ a then
    if h1 : (a - base).toNat / w < r then
      if h2 : (a - base).toNat % w < w then some (cell ⟨_, h1⟩ ⟨_, h2⟩) else none
    else none
  else none

/-- The indicator `1_{j ∈ T}`. -/
def ind {m : ℕ} (T : Finset (Fin m)) (j : Fin m) : ℝ :=
  if j ∈ T then 1 else 0

/-- The input memory: `x` at cells `i·m + j`, the indicator of `G` at `n·m + j`, the indicators
of the `E_i` at `n·m + m + i·m + j`, and `0` elsewhere. -/
def inputMem (n m : ℕ) (x : Fin n → Fin m → ℝ) (G : Finset (Fin m)) (E : Fin n → Finset (Fin m)) :
    ℤ → ℝ :=
  fun a =>
    ((blockAt 0 n m x a).getD
      ((blockAt ((n * m : ℕ) : ℤ) 1 m (fun _ j => ind G j) a).getD
        ((blockAt ((n * m + m : ℕ) : ℤ) n m (fun i j => ind (E i) j) a).getD 0)))

/-- The initial state on input `(n, m, x, G, E)`: `p[0] = n`, `p[1] = m`, memory `inputMem`,
program counter, registers and counters `0`. -/
def initState (n m : ℕ) (x : Fin n → Fin m → ℝ) (G : Finset (Fin m))
    (E : Fin n → Finset (Fin m)) : State where
  cfg := ⟨0, fun _ => 0, fun k => if k = 0 then (n : ℤ) else if k = 1 then (m : ℤ) else 0,
    inputMem n m x G E⟩
  unifs := 0
  work := 0
  halted := false
  stuck := false

/-- Output cell `(i, j)`: real memory cell `−1 − (i·m + j)`. -/
def outCell {n m : ℕ} (s : State) (i : Fin n) (j : Fin m) : ℝ :=
  s.cfg.mem (-1 - ((i : ℤ) * m + j))

open Classical in
/-- The bundles `S_i = {j : output cell (i, j) = 1}` of the halted run (`∅` if it never
halts). -/
noncomputable def outBundles {n m : ℕ} (P : Program) (g : Oracle n m) (S : State) (ν : Tape) :
    Fin n → Finset (Fin m) :=
  match finalState P g ν S with
  | some s => fun i => Finset.univ.filter fun j => outCell s i j = 1
  | none => fun _ => ∅

/-- The real output matrix of the halted run (`0` if it never halts). -/
noncomputable def outMatrix {n m : ℕ} (P : Program) (g : Oracle n m) (S : State) (ν : Tape) :
    Fin n → Fin m → ℝ :=
  match finalState P g ν S with
  | some s => fun i j => outCell s i j
  | none => fun _ _ => 0

/-- The law of the uniform tape, `Unif[0, 1]^ℕ`. -/
noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)

end ForestRoundingNSW.Rounding


