-- Prove2me | Definitions.Def_AdaptiveSparsify_Machine
-- name    : AdaptiveSparsify_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:41.142215+00:00
-- url     : https://prove2.me/theorems/e5761aad-6402-427f-acde-86b29535c5d9
-- title:
--   The randomized exact-arithmetic barrier-oracle RAM
-- statement:
--   The computational model of Theorem 1 and Theorem 3: a random access machine over the reals, with one finite program for all instances.
--
--   The scalar core is the published pointer machine over $\mathbb R$ (`SmaleNinth.RAMInstr`): real $+,-,\times,\div$ with $x/0=0$, indirect load and store, pointer set, copy, increment and decrement, and comparisons with jumps. It is extended with:
--
--   1. integer arithmetic on pointers, integer memory, and a pointer-to-real cast;
--   2. $\sqrt{\cdot}$ (with $\sqrt x=0$ for $x<0$) and $\exp$;
--   3. a draw of the next real of a tape of independent $N(0,1)$ reals;
--   4. a barrier oracle: from a block index $i$ and $n_i$ real cells holding a point, it writes $\phi_i$, then $\nabla\phi_i$, then $\nabla^2\phi_i$ in row-major order, if the point lies in $\operatorname{int}K_i$; on any other point, or an invalid block index, the machine enters an absorbing fault state and receives no answer;
--   5. `yield`, the exchange with the adversary of Theorem 3, and `halt`.
--
--   Each executed instruction costs one unit of work, an answered oracle call costs $(1+n_i)^2$, and a halted, faulted or yielded state stutters at no cost. There is no logarithm, floor, real-to-integer cast, sort, argmin or matrix instruction. A program is admissible when its real literals are rational and it stops through `halt`.
--
--   This is the access model of §1.3 and §3.1: values, gradients and Hessians of the barrier in constant time per call for $n_i\le C_K$, and the arithmetic of the paper's algorithm, which uses exponentials in Definition 4.3, square roots of Hessians, and Gaussian sketches in Lemma 2.1.
--
--   **Formalization Note** No constructor carries a function, so nothing computes for free between oracle calls. The barrier occurs only in the oracle branch and the sets $K_i$ only in its domain test.
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), §1.3, p.6; §3.1, p.12; Lemma 2.1, p.10; Definition 4.3, p.17

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_AdaptiveSparsify_Linear

namespace AdaptiveSparsify

/-!
# The randomized exact-arithmetic barrier-oracle RAM

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…),
§1.3, p.6 ("access to values, gradients, and Hessians of the barrier functions at any point in
constant time"), and §3.1, p.12 ("each oracle call takes O(1) time"); Lemma 2.1, p.10, for the
Gaussian samples and Definition 4.3, p.17, for the exponentials of the step.

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ`. The design follows
the published `LSWNewArcAudit.NewArc` oracle RAM: a finite instruction list, no instruction carrying
a function, unit charge per executed instruction, stuttering after halt, and an invalid program
counter that is stuck and charged.

**Formalization Note.**
* Instructions: the core's `+ − × ÷` (with `x / 0 = 0`), constants, indirect real load and store,
  pointer set, copy, increment, decrement, and the two comparisons with jump; integer `+ − ×` on
  pointers, integer load and store, pointer-to-real cast; `sqrt` (`√x = 0` for `x < 0`); `exp`
  (reading R3); `gauss` (reading R4); `oracle` (reading R5); `yield` (the exchange of Theorem 3,
  used only by the game in `AdaptiveSparsify.DynamicGame`); `halt`. There is no log, floor,
  real-to-integer cast, argmin, sort, or matrix instruction.
* Every executed instruction costs one unit of `work`. An `oracle` call that answers costs
  `(1 + n_i)²` units, which covers the `1 + n_i + n_i²` cells it writes; under `n_i ≤ C_K` this is
  the constant time of p.12.
* An `oracle` call reads a block index from a pointer register and `n_i` real cells. If the point
  is in `int K_i` it writes the value, then the gradient, then the Hessian in row-major order. On a
  point outside `int K_i`, or an invalid block index, the machine enters an absorbing fault state
  and receives no answer, so a query leaks no membership information (reading R5). The barrier
  occurs only in that branch and the sets `K_i` only in its domain test.
* Randomness is a tape of independent `N(0,1)` reals, one per executed `gauss` (reading R4).
* Admissible programs use rational literals only and no core `accept` or `reject`. This restricts
  the existentially chosen program and never an input.
-/

/-- An instruction of the machine. Register, pointer and label arguments are natural numbers; no
constructor carries a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerAdd/Sub/Mul d a b`: `p[d] := p[a] ∘ p[b]`.
* `integerLoad d a` / `integerStore a b`: `p[d] := I[p[a]]` / `I[p[a]] := p[b]`.
* `pointerReal d a`: `r[d] := (p[a] : ℝ)`.
* `sqrt d a`: `r[d] := √(r[a])`. `exp d a`: `r[d] := e^{r[a]}`.
* `gauss d`: `r[d] :=` the next tape real; the cursor advances.
* `oracle b x o`: query the barrier of block `p[b]` at the point in cells `M[p[x] + l]`, writing the
  answer from cell `M[p[o]]` on.
* `yield`: hand control to the adversary of the dynamic game.
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
  | gauss (dst : ℕ)
  | oracle (blockPtr xBase outBase : ℕ)
  | yield
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

/-- The barrier data reachable through `oracle`: the blocks, the sets and the barrier functions. -/
structure BarrierEnv where
  /-- The block structure. -/
  blocks : Blocks
  /-- The convex sets `K_i`. -/
  K : ∀ i, Set (EuclideanSpace ℝ (Fin (blocks.dim i)))
  /-- The barriers `φ_i`. -/
  φ : ∀ i, EuclideanSpace ℝ (Fin (blocks.dim i)) → ℝ

/-- The environment with no blocks: every `oracle` call faults. -/
def BarrierEnv.empty : BarrierEnv :=
  ⟨⟨0, Fin.elim0⟩, fun i => i.elim0, fun i => i.elim0⟩

/-- A machine state: the core configuration (program counter, real registers, pointers, real
memory), integer memory, the tape cursor, the halted, faulted and yielded flags, and the work. -/
structure State where
  core : SmaleNinth.RAMConfig
  integerMemory : ℤ → ℤ
  cursor : ℕ
  halted : Bool
  faulted : Bool
  yielded : Bool
  work : ℕ

/-- The initial state on the given integer and real memories: program counter `0`, all registers
and pointers `0`, cursor at the first tape real, no flag raised, no work done. -/
def init (ints : ℤ → ℤ) (reals : ℤ → ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun _ => 0, reals⟩, ints, 0, false, false, false, 0⟩

/-- The cells of an oracle answer at a point of a block of dimension `k`, by offset: offset `0` is
the value, offsets `1, …, k` the gradient, offsets `k + 1, …, k + k²` the Hessian in row-major
order. Other offsets are `0` and are never written. -/
noncomputable def oracleAnswer {k : ℕ} (φ : EuclideanSpace ℝ (Fin k) → ℝ) (x : Fin k → ℝ)
    (o : ℕ) : ℝ :=
  if o = 0 then φ (WithLp.toLp 2 x)
  else if h₁ : o - 1 < k then gradVec φ x ⟨o - 1, h₁⟩
  else if h₂ : o - 1 - k < k * k then
    hessMat φ x
      ⟨(o - 1 - k) / k, Nat.div_lt_of_lt_mul h₂⟩
      ⟨(o - 1 - k) % k, Nat.mod_lt _ (Nat.pos_of_mul_pos_right (by omega : 0 < k * k))⟩
  else 0

/-- One step of program `P` with barrier environment `E` and tape `ω`. Halted, faulted and yielded
states stutter at no cost. Every other step costs one unit of work, and an answered `oracle` call
costs `(1 + n_i)²`. `E.φ` and `E.K` occur only in the `oracle` branch and `ω` only in the `gauss`
branch. An invalid program counter is stuck and charged. -/
noncomputable def step (P : Program) (E : BarrierEnv) (ω : ℕ → ℝ) (s : State) : State := by
  classical
  exact if s.halted || s.faulted || s.yielded then s else
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
    | some (.gauss d) =>
        { t with
          cursor := s.cursor + 1
          core := { t.core with regs := Function.update s.core.regs d (ω s.cursor) } }
    | some (.oracle b x o) =>
        if hb : 0 ≤ s.core.ptrs b ∧ (s.core.ptrs b).toNat < E.blocks.m then
          let i : Fin E.blocks.m := ⟨(s.core.ptrs b).toNat, hb.2⟩
          let k := E.blocks.dim i
          let pt : Fin k → ℝ := fun l => s.core.mem (s.core.ptrs x + (l : ℕ))
          if WithLp.toLp 2 pt ∈ interior (E.K i) then
            { t with
              work := s.work + (1 + k) ^ 2
              core := { t.core with
                mem := fun a =>
                  if s.core.ptrs o ≤ a ∧ a < s.core.ptrs o + (1 + k + k * k : ℕ) then
                    oracleAnswer (E.φ i) pt (a - s.core.ptrs o).toNat
                  else s.core.mem a } }
          else { t with faulted := true }
        else { t with faulted := true }
    | some .yield => { t with yielded := true }
    | some .halt => { t with halted := true }

/-- The state after `t` steps of `P` from the initial state `s₀`. -/
noncomputable def run (P : Program) (E : BarrierEnv) (ω : ℕ → ℝ) (s₀ : State) (t : ℕ) : State :=
  (step P E ω)^[t] s₀

/-- The Gaussian tape: independent `N(0,1)` reals. -/
noncomputable def tape : MeasureTheory.Measure (ℕ → ℝ) :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.gaussianReal 0 1)

end AdaptiveSparsify


