-- Prove2me | Definitions.Def_BlockLewisIPM_Machine
-- name    : BlockLewisIPM_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:48:07.367504+00:00
-- url     : https://prove2.me/theorems/ff6bd8d4-dde7-4ddd-9a00-f51d1187ee8b
-- title:
--   The randomized exact-arithmetic barrier-and-conjugate oracle RAM and the success event of Theorem 54
-- statement:
--   Theorem 54 speaks about an algorithm with constant-time oracle access to the value, gradient and Hessian of each $\phi_i$, and to the value and gradient of its Fenchel conjugate. This definition makes that model precise.
--
--   A **program** is one finite list of instructions, the same for every instance. The machine has real registers, integer pointer registers, real and integer random-access memories, a cursor on a tape of independent $N(0,1)$ reals, and a work counter. The instructions are:
--
--   1. the real-RAM core: constants, $+,-,\times,\div$ (with $x/0=0$), indirect load and store, pointer set, copy, increment and decrement, and conditional jumps;
--   2. integer $+,-,\times$ on pointers, integer load and store, and the cast of a pointer to a real;
--   3. $\sqrt{\cdot}$ (with $\sqrt x=0$ for $x<0$), $\exp$ and $\log$;
--   4. `gauss`: load the next tape real;
--   5. `primalOracle`: for a block $i$ and a point $x_i$ in memory, write $\phi_i(x_i)$, $\nabla\phi_i(x_i)$, $\nabla^2\phi_i(x_i)$ if $x_i\in\operatorname{int}K_i$, at a cost of $(1+n_i)^2$; otherwise the machine faults and stops, with no answer;
--   6. `dualOracle`: for a block $i$ and a point $y$, write $\phi_i^*(y)$ and $\nabla\phi_i^*(y)$, at a cost of $1+n_i$;
--   7. `halt`.
--
--   A program is **admissible** if its real literals are rational. The input is $m,n,d,(n_i)$ in integer memory and $A,b,c,\delta$ in real memory; the barriers are reachable only through the oracles, and $K_i$, $\kappa$ and $z$ are not in memory. All other instructions cost one unit.
--
--   A run **succeeds** if at some step it has halted without fault, its work is at most
--
--   $$C\,n_{\max}^k\,\bigl(nd+d^{5/2}\bigr)\,\bigl(\log(n+d+\kappa+1/\delta+2)\bigr)^k,$$
--
--   and its output $x$ satisfies $x\in K$, $A^\top x=b$ and $c^\top x\le\delta+c^\top y$ for every feasible $y$.
--
--   **Formalization Note** The model is a reading of Theorem 54, which prints none. There is no floor, real-to-integer cast, sort or matrix instruction, and no instruction carries a function. `log` is Mathlib's, so $\log 0=0$ and $\log(-x)=\log x$.
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), Theorem 54, p.49; footnote 1, p.2; Definition 16, p.14; Algorithm 3, p.40

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_BlockLewisIPM_Instance

namespace BlockLewisIPM

/-!
# The randomized exact-arithmetic barrier-and-conjugate oracle RAM

Zhang, Wright, *A Fast Lewis-weight Interior Point Method for Linear Optimization over
Product-Domain* (manuscript, sha256 66072000…), Theorem 54, p.49, footnote 1, p.2 ("constant-time
oracle access to the value, gradient, and Hessian of `ϕ_i`, and to the value and gradient of its
Fenchel conjugate"), Definition 16, p.14 (`e^{λa}`), and Algorithm 3, p.40 (uniform samples).

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ`. Theorem 54 says "in
time" and prints no model, so the model is a reading (R3).

**Formalization Note.**
* Instructions: the core's `+ − × ÷` (with `x / 0 = 0`), constants, indirect real load and store,
  pointer set, copy, increment, decrement, and the two comparisons with jump; integer `+ − ×` on
  pointers, integer load and store, pointer-to-real cast; `sqrt` (`√x = 0` for `x < 0`); `exp`; `log`
  (Mathlib's `Real.log`: `log 0 = 0`, `log (-x) = log x`); `gauss`; `primalOracle`; `dualOracle`;
  `halt`. There is no floor, real-to-integer cast, argmin, sort or matrix instruction. No constructor
  carries a function.
* Every executed instruction costs one unit of `work`. An answered `primalOracle` costs `(1 + n_i)²`,
  which covers the `1 + n_i + n_i²` cells it writes, and an answered `dualOracle` costs `1 + n_i`
  (reading R5). Under `n_i = O(1)` both are the constant time of Theorem 54.
* `primalOracle` reads a block index from a pointer and `n_i` real cells. If the point is in
  `int K_i` it writes `ϕ_i`, then the gradient, then the Hessian in row-major order. On a point outside
  `int K_i`, or an invalid block index, the machine enters an absorbing fault state with no answer, so
  a query leaks no membership information. `dualOracle` writes `ϕ_i*`, then its gradient; `ϕ_i*` is
  finite everywhere as `K_i` is compact, so only an invalid block index faults (reading R5).
* The barrier occurs only in the two oracle branches and the sets `K_i` only in their domain test and
  conjugate. Randomness is a tape of independent `N(0,1)` reals, one per executed `gauss` (reading R4).
* Halted and faulted states stutter at no cost; an invalid program counter is stuck and charged.
* Admissible programs use rational literals only and no core `accept` or `reject`. This restricts
  the existentially chosen program and never an input.
* Memory layout. Integer cells `0, 1, 2` hold `m, n, d`, and cell `3 + i` holds `n_i`. Real cells from
  `0` on hold `A` in row-major order, then `b`, `c`, then the accuracy `δ`. Coordinates of `ℝⁿ` are
  numbered consecutively by `finSigmaFinEquiv` (reading R8). Every other cell is `0`. `K_i`, `ϕ_i`, `κ`
  and `z` are not in memory (reading R9). On `halt` the output `x_j` is read from real cell `-1 - j`.
* The time bound writes `Õ` as `C n_max^k (nd + d^{5/2}) (log(n + d + κ + 1/δ + 2))^k`, with `k` before
  the instance, so `n_max^k` is the "polynomial of block size" of Theorem 54 (reading R1).
-/

open Matrix

/-- An instruction of the machine. Register, pointer and label arguments are natural numbers; no
constructor carries a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd/Sub/Mul d a b`: `p[d] := p[a] ∘ p[b]`.
* `integerLoad d a` / `integerStore a b`: `p[d] := I[p[a]]` / `I[p[a]] := p[b]`.
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `sqrt d a`: `r[d] := √(r[a])`. `exp d a`: `r[d] := e^{r[a]}`. `log d a`: `r[d] := log r[a]`.
* `gauss d`: `r[d] :=` the next tape real; the cursor advances.
* `primalOracle b x o`: query `ϕ_{p[b]}` at the point in cells `M[p[x] + l]`, writing the answer from
  cell `M[p[o]]` on.
* `dualOracle b y o`: query `ϕ*_{p[b]}` at the point in cells `M[p[y] + l]`, writing the answer from
  cell `M[p[o]]` on.
* `halt`: stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerAdd (dst a b : ℕ)
  | pointerSub (dst a b : ℕ)
  | pointerMul (dst a b : ℕ)
  | integerLoad (dst address : ℕ)
  | integerStore (address src : ℕ)
  | pointerReal (dst pointer : ℕ)
  | sqrt (dst src : ℕ)
  | exp (dst src : ℕ)
  | log (dst src : ℕ)
  | gauss (dst : ℕ)
  | primalOracle (blockPtr xBase outBase : ℕ)
  | dualOracle (blockPtr yBase outBase : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every instance. -/
abbrev Program := List Instr

/-- Admissibility: every real literal is rational, and the core halting instructions do not occur
(the machine stops through `halt`). -/
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

/-- A machine state: the core configuration (program counter, real registers, pointers, real
memory), integer memory, the tape cursor, the halted and faulted flags, and the work. -/
structure State where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  cursor : ℕ
  halted : Bool
  faulted : Bool
  work : ℕ

/-- The initial state on the given integer and real memories: program counter `0`, all registers
and pointers `0`, cursor at the first tape real, no flag raised, no work done. -/
def init (ints : ℤ → ℤ) (reals : ℤ → ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, reals⟩, ints, 0, false, false, 0⟩

/-- The cells of a primal answer at a point of a block of dimension `k`, by offset: offset `0` is
the value, offsets `1, …, k` the gradient, offsets `k + 1, …, k + k²` the Hessian in row-major order.
Other offsets are `0` and are never written. -/
noncomputable def primalAnswer {k : ℕ} (φ : Eu k → ℝ) (x : Fin k → ℝ) (o : ℕ) : ℝ :=
  if o = 0 then φ (WithLp.toLp 2 x)
  else if h₁ : o - 1 < k then gradVec φ x ⟨o - 1, h₁⟩
  else if h₂ : o - 1 - k < k * k then
    hessMat φ x
      ⟨(o - 1 - k) / k, Nat.div_lt_of_lt_mul h₂⟩
      ⟨(o - 1 - k) % k, Nat.mod_lt _ (Nat.pos_of_mul_pos_right (by omega : 0 < k * k))⟩
  else 0

/-- The cells of a dual answer at a point of a block of dimension `k`, by offset: offset `0` is the
value of `ϕ*`, offsets `1, …, k` its gradient. Other offsets are `0` and are never written. -/
noncomputable def dualAnswer {k : ℕ} (φstar : Eu k → ℝ) (y : Fin k → ℝ) (o : ℕ) : ℝ :=
  if o = 0 then φstar (WithLp.toLp 2 y)
  else if h₁ : o - 1 < k then gradVec φstar y ⟨o - 1, h₁⟩
  else 0

/-- One step of program `P` on instance `I` and tape `ω`. Halted and faulted states stutter at no
cost. Every other step costs one unit of work, an answered `primalOracle` costs `(1 + n_i)²` and an
answered `dualOracle` costs `1 + n_i`. `I.φ` and `I.K` occur only in the oracle branches and `ω` only
in the `gauss` branch. An invalid program counter is stuck and charged. -/
noncomputable def step {m : ℕ} (P : Program) (I : Instance (Fin m)) (ω : ℕ → ℝ) (s : State) :
    State := by
  classical
  exact if s.halted || s.faulted then s else
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
    | some (.exp d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (Real.exp (s.core.regs a)) } }
    | some (.log d a) =>
        { t with core := { t.core with
            regs := Function.update s.core.regs d (Real.log (s.core.regs a)) } }
    | some (.gauss d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with regs := Function.update s.core.regs d (ω s.cursor) } }
    | some (.primalOracle b x o) =>
        if hb : 0 ≤ s.core.ptrs b ∧ (s.core.ptrs b).toNat < m then
          let i : Fin m := ⟨(s.core.ptrs b).toNat, hb.2⟩
          let k := I.dim i
          let pt : Fin k → ℝ := fun l => s.core.mem (s.core.ptrs x + (l : ℕ))
          if WithLp.toLp 2 pt ∈ interior (I.K i) then
            { t with
              work := s.work + (1 + k) ^ 2
              core := { t.core with
                mem := fun a =>
                  if s.core.ptrs o ≤ a ∧ a < s.core.ptrs o + (1 + k + k * k : ℕ) then
                    primalAnswer (I.φ i) pt (a - s.core.ptrs o).toNat
                  else s.core.mem a } }
          else { t with faulted := true }
        else { t with faulted := true }
    | some (.dualOracle b y o) =>
        if hb : 0 ≤ s.core.ptrs b ∧ (s.core.ptrs b).toNat < m then
          let i : Fin m := ⟨(s.core.ptrs b).toNat, hb.2⟩
          let k := I.dim i
          let pt : Fin k → ℝ := fun l => s.core.mem (s.core.ptrs y + (l : ℕ))
          { t with
            work := s.work + (1 + k)
            core := { t.core with
              mem := fun a =>
                if s.core.ptrs o ≤ a ∧ a < s.core.ptrs o + (1 + k : ℕ) then
                  dualAnswer (conj (I.K i) (I.φ i)) pt (a - s.core.ptrs o).toNat
                else s.core.mem a } }
        else { t with faulted := true }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` from the initial state `s₀`. -/
noncomputable def run {m : ℕ} (P : Program) (I : Instance (Fin m)) (ω : ℕ → ℝ) (s₀ : State)
    (t : ℕ) : State :=
  (step P I ω)^[t] s₀

/-- The Gaussian tape: independent `N(0,1)` reals (reading R4). -/
noncomputable def tape : MeasureTheory.Measure (ℕ → ℝ) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.gaussianReal 0 1)

namespace Instance

variable {m : ℕ} (I : Instance (Fin m))

/-- The consecutive numbering of a flat coordinate: `(i, l)` of §3.1 from `j ∈ Fin n`. -/
def unflat (j : Fin I.n) : BIdx I.dim := finSigmaFinEquiv.symm j

/-- The number in `Fin n` of the coordinate `(i, l)`. -/
def flat (j : BIdx I.dim) : Fin I.n := finSigmaFinEquiv j

/-- The integer input memory. -/
def intMem : ℤ → ℤ := fun a =>
  if a = 0 then m
  else if a = 1 then I.n
  else if a = 2 then I.d
  else if h : 3 ≤ a ∧ (a - 3).toNat < m then I.dim ⟨(a - 3).toNat, h.2⟩
  else 0

/-- The real input memory for accuracy `δ`, by nonnegative offset. -/
noncomputable def realMemAt (δ : ℝ) (o : ℕ) : ℝ :=
  let n := I.n
  let d := I.d
  if h₁ : o < n * d then
    I.A (I.unflat ⟨o / d, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h₁)⟩)
      ⟨o % d, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro h; simp [h] at h₁))⟩
  else if h₂ : o - n * d < d then I.b ⟨o - n * d, h₂⟩
  else if h₃ : o - n * d - d < n then I.c (I.unflat ⟨o - n * d - d, h₃⟩)
  else if o - n * d - d - n = 0 then δ
  else 0

/-- The real input memory for accuracy `δ`. Negative cells are `0`. -/
noncomputable def realMem (δ : ℝ) : ℤ → ℝ := fun a =>
  if 0 ≤ a then I.realMemAt δ a.toNat else 0

/-- The run of `P` on `I` with accuracy `δ` and tape `ω`. -/
noncomputable def runOn (P : Program) (δ : ℝ) (ω : ℕ → ℝ) (t : ℕ) : State :=
  run P I ω (init I.intMem (I.realMem δ)) t

/-- The output read from a state: `x_j` is real cell `-1 - j`. -/
def output (s : State) : I.Vec :=
  fun j => s.core.mem (-1 - (((I.flat j : Fin I.n) : ℕ) : ℤ))

/-- The time bound `C n_max^k (nd + d^{5/2}) (log(n + d + κ + 1/δ + 2))^k` of Theorem 54 (reading
R1). -/
noncomputable def timeBound (κ δ C : ℝ) (k : ℕ) : ℝ :=
  C * (I.nmax : ℝ) ^ k * ((I.n : ℝ) * I.d + (I.d : ℝ) ^ ((5 : ℝ) / 2)) *
    (Real.log ((I.n : ℝ) + I.d + κ + 1 / δ + 2)) ^ k

/-- The success event of Theorem 54 at `(P, I, δ, κ, C, k, ω)`: at some step the run has halted
without fault, within the time bound, and its output is in `K`, satisfies `A⊤x = b` exactly and is
`δ`-optimal against every feasible point (reading R7). -/
def Success (P : Program) (δ κ C : ℝ) (k : ℕ) (ω : ℕ → ℝ) : Prop :=
  ∃ t : ℕ,
    (I.runOn P δ ω t).halted = true ∧
    (I.runOn P δ ω t).faulted = false ∧
    ((I.runOn P δ ω t).work : ℝ) ≤ I.timeBound κ δ C k ∧
    I.Feasible (I.output (I.runOn P δ ω t)) ∧
    ∀ y, I.Feasible y → I.c ⬝ᵥ I.output (I.runOn P δ ω t) ≤ δ + I.c ⬝ᵥ y

end Instance

end BlockLewisIPM


