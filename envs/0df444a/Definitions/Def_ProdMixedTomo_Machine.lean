-- Prove2me | Definitions.Def_ProdMixedTomo_Machine
-- name    : ProdMixedTomo_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:17:31.347628+00:00
-- url     : https://prove2.me/theorems/e4af52d1-bb75-4250-becc-10f2bdeae603
-- title:
--   The randomized measuring real RAM, its run law, input layouts and output decoders
-- statement:
--   The paper's algorithms ("runs in poly$(N)$ time", "using only single-copy, single-qubit measurements") are programs of one machine, fixed here because the paper names none.
--
--   **Instructions.** The published real-RAM core (exact $+,-,\times,\div$ with $x/0=0$, rational literals, indirect real memory through integer pointer registers, pointer set/copy/increment/decrement, comparison jumps), plus pointer addition/subtraction, an integer memory, a pointer-to-real cast, and:
--   1. `coin d`: a fair random bit into a register;
--   2. `measure a`: consumes **one fresh copy** of the unknown $n$-qubit state $\rho$, reads a direction $b_j\in\mathbb R^3$ for each qubit $j$ from memory, measures every qubit $j$ with $\{P(b_j),I-P(b_j)\}$ and writes the outcome bits $s\in\{0,1\}^n$ to memory. The outcome law is the Born law
--   $$
--   \Pr[s]=\operatorname{Re}\operatorname{tr}\Bigl(\rho\cdot\bigotimes_{j} Q_j(s_j)\Bigr),\qquad Q_j(0)=P(b_j),\ Q_j(1)=I-P(b_j);
--   $$
--   distinct calls use independent copies, and the directions may depend on earlier outcomes (adaptivity). This is the only access to $\rho$;
--   3. `halt`.
--
--   A program is a finite list of instructions; it is **admissible** if its literals are rational and it does not use the core's accept/reject, and **classical** if it contains no `measure`. There is no square root, floor, real-to-integer cast, exponential, logarithm or eigensolver. Each executed instruction costs one step; only `halt` halts.
--
--   **Probability.** One step is a probability kernel on machine states (Dirac, a fair coin, or the Born weights); the run law after $t$ steps is its $t$-fold composition. "On every run" means every state reachable along transitions of positive probability.
--
--   **Layouts.** A learner receives $n,N$ in pointer registers and $\epsilon,\delta$ in memory; at halt, memory cells $4j,\dots,4j+3$ hold a direction $b_j$ and a weight $\lambda_j$, decoded as $\hat\pi=\bigotimes_j\bigl((1-\bar\lambda_j)P(b_j)+\bar\lambda_j(I-P(b_j))\bigr)$ with $\bar\lambda_j=\operatorname{clip}(\lambda_j)$, always a product mixed state. A classical program receives $n,N$, two real parameters and the $N$ sample points as $0/1$ reals; its output is the vector in memory cells $0,\dots,n-1$, read as $\mathrm{Bern}(\operatorname{clip}(\cdot))$ when a distribution is required.
--
--   **Formalization Note** The state space carries the discrete σ-algebra and `runLaw` composes the step kernel with `Measure.bind`. Classical programs are run on the trivial $0$-qubit state; they never execute `measure`. Failure probabilities are measures of failure sets.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Corollary 3.3, p.16 (PDF p.18); Theorem 3.1 and Algorithm 1, p.15 (PDF p.17); Theorem 4.5, p.22 (PDF p.24); Theorem 1.8, p.6 (PDF p.8); machine model is a reading of the mission (the paper names none)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_ProdMixedTomo_States
import Definitions.Def_ProdMixedTomo_BinaryProduct

namespace ProdMixedTomo

/-!
# The randomized measuring real RAM, its run law, input layouts and output decoders

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Corollary 3.3, p.16 (PDF p.18):
"There is an algorithm, using only single-copy, single-qubit measurements, which given N ≥ N0
copies of ρ … runs in poly(N) time"; Theorem 3.1, p.15 (PDF p.17); Algorithm 1, p.15; Theorem 4.5,
p.22 (PDF p.24); Theorem 1.8, p.6 (PDF p.8). The paper names no machine model.

**Formalization Note (the machine).** The machine is the published real-RAM core
`SmaleNinth.RAMInstr` (exact `+ − × ÷` with `x/0 = 0`, real literals, indirect real memory
`ℤ → ℝ` through integer pointer registers, pointer set/copy/increment/decrement, comparison jumps),
extended (after the pattern of `LogitRankDistill.Instr`) by
* integer pointer addition/subtraction, an integer memory `ℤ → ℤ`, a pointer-to-real cast;
* `coin d`: `r[d] := 0` or `1`, one fair bit;
* `measure a`: consumes one fresh copy of the unknown `n`-qubit state `ρ`. For `j < n` it reads a
  direction `b_j = (M[p[a]+3j], M[p[a]+3j+1], M[p[a]+3j+2]) ∈ ℝ³`, measures qubit `j` of the copy
  with the projective pair `{P(b_j), I − P(b_j)}` (all qubits of the copy at once, a product
  measurement), and writes the outcome `s_j ∈ {0,1}` (`0` ↔ `P(b_j)`) into `M[p[a] + 3n + j]`.
  The outcome law is the Born law `Pr[s] = Re tr(ρ · ⨂ⱼ Q_j(s_j))`, `Q_j(0) = P(b_j)`,
  `Q_j(1) = I − P(b_j)`; distinct calls use independent copies (`ρ^{⊗N}`), so outcomes are
  independent given the history, and the directions may depend on earlier outcomes (adaptivity).
  This instruction is the only access to `ρ`;
* `halt`.
No instruction carries a state, a function or a real other than a literal; `Admissible` requires
rational literals and forbids the core's `accept`/`reject`. There is no square root, floor,
real-to-integer cast, `exp`/`log`, eigensolver or uniform real draw. Every executed instruction
(including `measure`) costs one step; an invalid program counter is stuck and charged, so only
`halt` halts; a halted state stutters at no cost.

**Formalization Note (probability).** The state space carries the discrete σ-algebra. One step is
a finite probability kernel `stepLaw` (Dirac for deterministic instructions, ½/½ for `coin`,
the Born weights for `measure`); `runLaw` is its `t`-fold composition from an initial state.
`Reach t` is the set of states reachable in `t` steps along transitions of positive weight
("every run"). A *classical* program never contains `measure`; its law does not depend on `ρ`
and is computed with the trivial `0`-qubit state.

**Formalization Note (layouts).** Learner input: pointer registers `p[0] = n`, `p[1] = N`, real
memory `M[0] = ϵ`, `M[1] = δ`, everything else `0`. Learner output (at halt): for `j < n`, the
cells `M[4j], M[4j+1], M[4j+2]` hold a direction `b_j` and `M[4j+3]` a weight `λ_j`, decoded as
`π̂_j = (1 − λ̄_j) P(b_j) + λ̄_j (I − P(b_j))` with `λ̄_j` the clip of `λ_j` to `[0,1]`; the decoded
output is always a product mixed state. Classical input: `p[0] = n`, `p[1] = N`, `M[0] = a`,
`M[1] = b` (two real parameters, e.g. `ϵ` and `δ`), and sample `i < N`, coordinate `j < n` as the
real `0`/`1` in `M[2 + n i + j]`. Classical output: `M[j]`, `j < n`, a vector in `ℝⁿ`; as a
distribution it is decoded to `Bern(clip(M[0..n−1]))`.
-/

open MeasureTheory

/-- An instruction of the randomized measuring real RAM. -/
inductive Instr where
  /-- A `SmaleNinth` real-RAM instruction. -/
  | core (instruction : SmaleNinth.RAMInstr)
  /-- `p[dst] := p[a] + p[b]`. -/
  | pointerAdd (dst a b : ℕ)
  /-- `p[dst] := p[a] − p[b]`. -/
  | pointerSub (dst a b : ℕ)
  /-- `p[dst] := I[p[address]]` (integer memory). -/
  | integerLoad (dst address : ℕ)
  /-- `I[p[address]] := p[src]`. -/
  | integerStore (address src : ℕ)
  /-- `r[dst] := (p[pointer] : ℝ)`. -/
  | pointerReal (dst pointer : ℕ)
  /-- `r[dst] :=` a fair random bit (`0` or `1`). -/
  | coin (dst : ℕ)
  /-- Measure one fresh copy of `ρ`, qubit `j` along the direction in `M[p[a]+3j .. p[a]+3j+2]`;
  outcomes into `M[p[a]+3n+j]`. -/
  | measure (address : ℕ)
  /-- Halt. -/
  | halt

/-- A program: one finite list of instructions. -/
abbrev Program := List Instr

/-- Every real literal is rational and the core's `accept`/`reject` do not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True

/-- A classical program: it contains no `measure` instruction. -/
def IsClassical (P : Program) : Prop := ∀ a : ℕ, Instr.measure a ∉ P

/-- The static core table of `P` (extension instructions are placeholders, never executed by the
core). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun op => match op with
    | .core i => i
    | _ => .const 0 0

/-- A machine state. -/
structure MState where
  /-- Program counter, real registers, pointer registers, real memory. -/
  core : SmaleNinth.RAMConfig
  /-- Integer memory. -/
  intMem : ℤ → ℤ
  /-- Number of copies of `ρ` consumed (`measure` instructions executed). -/
  copies : ℕ
  /-- Halted flag. -/
  halted : Bool
  /-- Number of instructions executed. -/
  work : ℕ

/-- The discrete σ-algebra on machine states. -/
instance : MeasurableSpace MState := ⊤

/-- The state after a non-halting instruction whose effect is the given update (pc advanced,
one step charged). -/
def advance (s : MState) : MState :=
  { s with work := s.work + 1, core := { s.core with pc := s.core.pc + 1 } }

/-- One deterministic step (every instruction except `coin` and `measure`). -/
noncomputable def detStep (P : Program) (s : MState) : MState :=
  let t := advance s
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
          ptrs := Function.update s.core.ptrs d (s.intMem (s.core.ptrs a)) } }
  | some (.integerStore a b) =>
      { t with intMem := Function.update s.intMem (s.core.ptrs a) (s.core.ptrs b) }
  | some (.pointerReal d a) =>
      { t with core := { t.core with
          regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
  | some (.coin _) => t
  | some (.measure _) => t
  | some .halt => { t with halted := true }

/-- The result of `coin d` with outcome bit `c`. -/
def coinResult (s : MState) (d : ℕ) (c : Bool) : MState :=
  let t := advance s
  { t with core := { t.core with
      regs := Function.update s.core.regs d (if c then 1 else 0) } }

/-- The measurement directions `b_j ∈ ℝ³`, `j < n`, read by `measure a`. -/
def directions (n : ℕ) (s : MState) (a : ℕ) : Fin n → Fin 3 → ℝ :=
  fun j k => s.core.mem (s.core.ptrs a + 3 * (j : ℤ) + (k : ℤ))

/-- The one-qubit effect for outcome bit `o` along direction `b`: `P(b)` for `0`, `I − P(b)`
for `1`. -/
noncomputable def effect (b : Fin 3 → ℝ) (o : Bool) : Matrix Bool Bool ℂ :=
  if o then 1 - proj b else proj b

/-- The Born weight `Re tr(ρ · ⨂ⱼ Q_j(o_j))` of the outcome string `o` when every qubit `j` is
measured along `b_j`. -/
noncomputable def bornWeight {n : ℕ} (ρ : QMat n) (b : Fin n → Fin 3 → ℝ) (o : Cube n) : ℝ :=
  (ρ * prodMat (fun j => effect (b j) (o j))).trace.re

/-- The result of `measure a` with outcome string `o`: one copy consumed, `o_j` written as the
real `0`/`1` into `M[p[a] + 3n + j]`. -/
noncomputable def measureResult (n : ℕ) (s : MState) (a : ℕ) (o : Cube n) : MState :=
  let t := advance s
  let base := s.core.ptrs a + 3 * (n : ℤ)
  { t with
    copies := s.copies + 1
    core := { t.core with
      mem := fun z =>
        if h : base ≤ z ∧ z < base + n then
          (if o ⟨(z - base).toNat, by omega⟩ then 1 else 0)
        else s.core.mem z } }

/-- One step of `P` on the unknown `n`-qubit state `ρ`, as a probability kernel. -/
noncomputable def stepLaw {n : ℕ} (P : Program) (ρ : QMat n) (s : MState) : Measure MState :=
  if s.halted then Measure.dirac s else
    match P[s.core.pc]? with
    | some (.coin d) =>
        (1 / 2 : ENNReal) • Measure.dirac (coinResult s d false) +
        (1 / 2 : ENNReal) • Measure.dirac (coinResult s d true)
    | some (.measure a) =>
        ∑ o : Cube n, ENNReal.ofReal (bornWeight ρ (directions n s a) o) •
          Measure.dirac (measureResult n s a o)
    | _ => Measure.dirac (detStep P s)

/-- The law of the state after `t` steps of `P` on `ρ` from `s₀`. -/
noncomputable def runLaw {n : ℕ} (P : Program) (ρ : QMat n) (s₀ : MState) : ℕ → Measure MState
  | 0 => Measure.dirac s₀
  | t + 1 => (runLaw P ρ s₀ t).bind (stepLaw P ρ)

/-- The states reachable in `t` steps along transitions of positive weight. -/
def Reach {n : ℕ} (P : Program) (ρ : QMat n) (s₀ : MState) : ℕ → Set MState
  | 0 => {s₀}
  | t + 1 => {s' | ∃ s ∈ Reach P ρ s₀ t, stepLaw P ρ s {s'} ≠ 0}

/-- The trivial `0`-qubit state, used to run classical programs. -/
def trivialState : QMat 0 := 1

/-- The run law of a (classical) program, which never touches the quantum state. -/
noncomputable def cRunLaw (P : Program) (s₀ : MState) (t : ℕ) : Measure MState :=
  runLaw P trivialState s₀ t

/-- The states a (classical) program reaches in `t` steps. -/
def cReach (P : Program) (s₀ : MState) (t : ℕ) : Set MState :=
  Reach P trivialState s₀ t

/-- The initial state: pointer registers `p[k] = ptrs[k]`, real memory `M[k] = reals[k]` for
`k ≥ 0`, all other cells, registers and counters `0`, not halted. -/
noncomputable def initState (ptrs : List ℤ) (reals : List ℝ) : MState :=
  ⟨⟨0, fun _ => 0, fun k => ptrs.getD k 0,
      fun z => if 0 ≤ z then reals.getD z.toNat 0 else 0⟩, fun _ => 0, 0, false, 0⟩

/-- The learner's input: `p[0] = n`, `p[1] = N`, `M[0] = ϵ`, `M[1] = δ`. -/
noncomputable def learnerInput (n N : ℕ) (ϵ δ : ℝ) : MState :=
  initState [(n : ℤ), (N : ℤ)] [ϵ, δ]

/-- The samples flattened row by row as reals `0`/`1`. -/
noncomputable def flatSamples {n N : ℕ} (S : Fin N → Cube n) : List ℝ :=
  (List.finRange N).flatMap fun i => (List.finRange n).map fun j => if S i j then 1 else 0

/-- A classical program's input: `p[0] = n`, `p[1] = N`, `M[0] = a`, `M[1] = b`, then the
samples, `M[2 + n i + j] = S i j`. -/
noncomputable def classicalInput (n N : ℕ) (a b : ℝ) (S : Fin N → Cube n) : MState :=
  initState [(n : ℤ), (N : ℤ)] ([a, b] ++ flatSamples S)

/-- The learner's output decoded as a product mixed state:
`π̂ = ⨂ⱼ ((1 − λ̄ⱼ) P(bⱼ) + λ̄ⱼ (I − P(bⱼ)))`, `bⱼ = (M[4j], M[4j+1], M[4j+2])`,
`λ̄ⱼ = clip(M[4j+3])`. -/
noncomputable def decodeState (n : ℕ) (s : MState) : QMat n :=
  prodMat fun j =>
    let b : Fin 3 → ℝ := fun k => s.core.mem (4 * (j : ℤ) + (k : ℤ))
    let lam : ℝ := clip01 (s.core.mem (4 * (j : ℤ) + 3))
    ((1 - lam : ℝ) : ℂ) • proj b + ((lam : ℝ) : ℂ) • (1 - proj b)

/-- A classical program's output vector `(M[0], …, M[n−1]) ∈ ℝⁿ`. -/
def outVec (n : ℕ) (s : MState) : Fin n → ℝ := fun j => s.core.mem (j : ℤ)

/-- A classical program's output as a binary product distribution `Bern(clip(outVec))`. -/
noncomputable def outBern (n : ℕ) (s : MState) : Cube n → ℝ :=
  bern fun j => clip01 (outVec n s j)

/-- The probability, over `N` i.i.d. samples from `q` and the program's coins, that the classical
program `P` run for `T` steps on input `(n, N, a, b, samples)` ends in a state satisfying `bad`. -/
noncomputable def sampleFail (P : Program) (n N : ℕ) (a b : ℝ) (q : Cube n → ℝ) (T : ℕ)
    (bad : MState → Prop) : ENNReal :=
  ∑ S : Fin N → Cube n, ENNReal.ofReal (∏ i, q (S i)) *
    cRunLaw P (classicalInput n N a b S) T {s | bad s}

end ProdMixedTomo


