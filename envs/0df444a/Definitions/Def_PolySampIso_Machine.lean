-- Prove2me | Definitions.Def_PolySampIso_Machine
-- name    : PolySampIso_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:35.696824+00:00
-- url     : https://prove2.me/theorems/55a6b073-3fce-4e18-9b45-6ce0d2acb1af
-- title:
--   The real RAM with one-dimensional Gaussian and exponential samples
-- statement:
--   The model of computation in which the running times of the paper are read. The paper says only "We work in the real RAM model, where we assume scalar operations can be done in $O(1)$ time" and "We assume sample access to one-dimensional Gaussian and exponential distributions in $O(1)$ time" (§2.1).
--
--   A program is one finite list of instructions, the same for every input. The machine has real registers $r_0,r_1,\dots$, integer pointer registers $p_0,p_1,\dots$ and a random-access real memory indexed by $\mathbb Z$. Its instructions are:
--
--   1. exact $+,-,\times,\div$ on reals (with $x/0=0$), rational literals, indirect load and store through pointers, pointer set, copy, increment and decrement, and the comparison jumps $r_i\le 0$ and $p_q\le p_{q'}$ (the published real-RAM core);
--   2. a pointer-to-real cast $r_d:=p_q$;
--   3. $\sqrt{\cdot}$, $\exp$ and $\log$ of a register;
--   4. $\mathrm{gauss}$, which reads the next entry of an i.i.d. $\mathcal N(0,1)$ stream, and $\mathrm{expo}$, which reads the next entry of an independent i.i.d. $\mathrm{Exp}(1)$ stream;
--   5. halt.
--
--   Every executed instruction costs one unit of work; an invalid program counter is stuck and charged, and after halt the state stutters at no cost. There is no floor, no real-to-integer cast, no coin and no uniform draw (a coin is the sign of a Gaussian draw; $e^{-E}$ with $E\sim\mathrm{Exp}(1)$ is uniform on $(0,1)$).
--
--   The input of a run consists of $m,n$ in pointers $p_0,p_1$, three scalars in cells $0,1,2$, a point $x_0\in\mathbb R^n$ in cells $3,\dots,2+n$, the matrix $A\in\mathbb R^{m\times n}$ row by row, the vector $b\in\mathbb R^m$, and then further scalars; the output is the point $x\in\mathbb R^n$ with $x_j$ in cell $-1-j$.
--
--   **Formalization Note** The core is the published `SmaleNinth.RAMInstr`. `Admissible` requires rational literals and excludes the core `accept`/`reject`; it restricts the existentially chosen program only. `tape` is the product of the two i.i.d. streams; `finalOutput` reads the output at the first halting step.
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), §2.1, pp.7–8 (PDF pp.9–10)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-!
# The real RAM with one-dimensional Gaussian and exponential samples

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), §2.1, pp.7–8 (PDF pp.9–10): "We work in the real
RAM model, where we assume scalar operations can be done in O(1) time" and "We assume sample
access to one-dimensional Gaussian and exponential distributions in O(1) time." No instruction
list is given, so this machine is a reading of those two sentences.

The scalar core is the published `SmaleNinth.RAMInstr` pointer machine over `ℝ` (exact
`+ − × ÷`, literals, indirect load and store through integer pointers, pointer set, copy,
increment and decrement, and the comparison jumps `r ≤ 0` and `p ≤ p'`). The extensions are a
pointer-to-real cast, `√`, `exp`, `log`, a draw of `N(0,1)`, a draw of `Exp(1)` and `halt`.

**Formalization Note.**
* Real literals are rational and the core `accept`/`reject` do not occur (`Admissible`). This
  restricts the existentially chosen program, never the input. No constructor carries a
  function, and there is no floor, real-to-integer cast, coin or uniform-real draw (a fair coin
  is the sign of a Gaussian draw, a uniform draw is `exp(−E)` for `E ∼ Exp(1)`).
* Cost: every executed instruction adds `1` to `work`. An invalid program counter is stuck and
  charged, so only `halt` halts. After `halt` the state stutters at no cost.
* Randomness: two independent streams `ℕ → ℝ`; the `k`-th executed `gauss` reads entry `k` of
  the Gaussian stream, the `k`-th executed `expo` entry `k` of the exponential stream. The tape
  measure makes the entries i.i.d. `N(0,1)` and i.i.d. `Exp(1)`, independent of each other.
* Input layout (`inputState`): pointer `p[0] = m`, `p[1] = n`, other pointers `0`; memory holds
  three scalars in cells `0, 1, 2`, the point `x₀ ∈ ℝⁿ` in cells `3, …, 2 + n`, the matrix
  `A ∈ ℝ^{m×n}` row by row in cells `3 + n + i·n + j`, the vector `b ∈ ℝ^m` in cells
  `3 + n + mn + i`, then a list of further scalars from cell `3 + n + mn + m` on; every other
  cell is `0`. Output (`output`): the point `x ∈ ℝⁿ` with `x_j = M[−1 − j]`.
-/

/-- An instruction. Register, pointer and label arguments are natural numbers; no constructor
carries a function.
* `core i`: a `SmaleNinth` real-RAM instruction.
* `pointerReal d q`: `r[d] := (p[q] : ℝ)`.
* `sqrt d a`, `exp d a`, `log d a`: `r[d] := √r[a]`, `e^{r[a]}`, `log r[a]` (`Real.sqrt`,
  `Real.log`, so `√x = 0` for `x < 0` and `log x = log |x|`, `log 0 = 0`).
* `gauss d`: `r[d] :=` the next unread entry of the `N(0,1)` stream.
* `expo d`: `r[d] :=` the next unread entry of the `Exp(1)` stream.
* `halt`: stop. -/
inductive Instr where
  | core (instruction : SmaleNinth.RAMInstr)
  | pointerReal (dst pointer : ℕ)
  | sqrt (dst src : ℕ)
  | exp (dst src : ℕ)
  | log (dst src : ℕ)
  | gauss (dst : ℕ)
  | expo (dst : ℕ)
  | halt

/-- A program: one finite list of instructions, the same for every input. -/
abbrev Program := List Instr

/-- Every real literal is rational, and the core halting instructions `accept`/`reject` do not
occur (the machine stops only through `halt`). -/
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

/-- A machine state: the core configuration (program counter, real registers, pointers,
memory), the two stream cursors, the halted flag and the work counter. -/
structure State where
  core : SmaleNinth.RAMConfig
  gaussCursor : ℕ
  expoCursor : ℕ
  halted : Bool
  work : ℕ

/-- The randomness of a run: the `N(0,1)` stream and the `Exp(1)` stream. -/
abbrev Streams := (ℕ → ℝ) × (ℕ → ℝ)

/-- One step of program `P` on the streams `ω`. Halted states stutter at no cost; every other
step costs `1`. -/
noncomputable def step (P : Program) (ω : Streams) (s : State) : State :=
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
    | some (.gauss d) =>
        { setReg d (ω.1 s.gaussCursor) with gaussCursor := s.gaussCursor + 1 }
    | some (.expo d) =>
        { setReg d (ω.2 s.expoCursor) with expoCursor := s.expoCursor + 1 }
    | some .halt => { t with halted := true }

/-- The state after `k` steps of `P` from `s₀` on the streams `ω`. -/
noncomputable def run (P : Program) (s₀ : State) (ω : Streams) (k : ℕ) : State :=
  (step P ω)^[k] s₀

/-- The input memory: scalars `head` in cells `0, 1, 2`, then `x₀`, `A` (row major), `b`, then
the scalars `tail`; every other cell is `0`. -/
noncomputable def inputMem {m n : ℕ} (head : Fin 3 → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (tail : List ℝ) : ℤ → ℝ := fun a =>
  if h : 0 ≤ a ∧ a < 3 then head ⟨a.toNat, by omega⟩
  else if h : 3 ≤ a ∧ a < 3 + n then x₀ ⟨(a - 3).toNat, by omega⟩
  else if h : 3 + n ≤ a ∧ a < 3 + n + m * n then
    A ⟨((a - 3 - n).toNat) / n, by
        have hn : 0 < n := by
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0; omega
          · exact h0
        rw [Nat.div_lt_iff_lt_mul hn]; omega⟩
      ⟨((a - 3 - n).toNat) % n, Nat.mod_lt _ (by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0; omega
        · exact h0)⟩
  else if h : 3 + n + m * n ≤ a ∧ a < 3 + n + m * n + m then
    b ⟨(a - 3 - n - m * n).toNat, by omega⟩
  else if 3 + n + m * n + m ≤ a then tail.getD (a - 3 - n - m * n - m).toNat 0
  else 0

/-- The initial state of a run on the input `inputMem head x₀ A b tail`: program counter,
registers, cursors and work `0`, not halted; pointer `p[0] = m`, `p[1] = n`, others `0`. -/
noncomputable def inputState {m n : ℕ} (head : Fin 3 → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (tail : List ℝ) : State :=
  ⟨⟨0, fun _ => 0, fun q => if q = 0 then (m : ℤ) else if q = 1 then (n : ℤ) else 0,
      inputMem head x₀ A b tail⟩, 0, 0, false, 0⟩

/-- The output of a state: the point of `ℝⁿ` with coordinates `x_j = M[−1 − j]`. -/
noncomputable def output (n : ℕ) (s : State) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j => s.core.mem (-1 - (j : ℤ))

/-- The first step count at which the run is halted (`0` if it never halts). -/
noncomputable def haltTime (P : Program) (s₀ : State) (ω : Streams) : ℕ :=
  sInf {k | (run P s₀ ω k).halted = true}

/-- The output of the run on the streams `ω`, read at the halting time. Halted states stutter,
so every later state has the same output. -/
noncomputable def finalOutput (n : ℕ) (P : Program) (s₀ : State) (ω : Streams) :
    EuclideanSpace ℝ (Fin n) :=
  output n (run P s₀ ω (haltTime P s₀ ω))

/-- The tape measure: i.i.d. `N(0,1)` entries in the first stream and, independently, i.i.d.
`Exp(1)` entries in the second. -/
noncomputable def tape : Measure Streams :=
  haveI := isProbabilityMeasure_expMeasure (one_pos (α := ℝ))
  (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
    (Measure.infinitePi fun _ : ℕ => expMeasure 1)

end PolySampIso


