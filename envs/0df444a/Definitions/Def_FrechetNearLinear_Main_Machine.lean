-- Prove2me | Definitions.Def_FrechetNearLinear_Main_Machine
-- name    : FrechetNearLinear_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:35:52.722884+00:00
-- url     : https://prove2.me/theorems/62f10dd3-a66a-4978-b4db-ff149fb6e246
-- title:
--   The cost model: a deterministic unit-cost real RAM with square root and integer indexing; input and output layouts
-- statement:
--   The paper names no machine model. The algorithms of the mission are programs of a deterministic unit-cost **real RAM**: the published `SmaleNinth.RAMInstr` core (exact $+,-,\times,\div$ with $x/0=0$, real literals, indirect real memory $M:\mathbb Z\to\mathbb R$ addressed by integer pointer registers, pointer set/copy/increment/decrement, jumps on $r\le 0$ and $p\le p'$, `accept`, `reject`) plus three instructions:
--   - `sqrt`: $r[\mathit{dst}]:=\sqrt{r[\mathit{src}]}$ (`Real.sqrt`, $0$ on negative arguments);
--   - `idx`: $p[q]:=r[\mathit{src}]$ when $r[\mathit{src}]$ is an integer; on a non-integer the machine is stuck forever;
--   - `ofPtr`: $r[\mathit{dst}]:=p[q]$.
--
--   A program is **admissible** when every real literal is rational. There is no floor of a non-integer, no exponential or logarithm, no randomness and no oracle; every executed instruction costs one step. A configuration is halted when its program counter points at `accept` or `reject`.
--
--   **Inputs.** `initCfg ps xs` has program counter $0$, all real registers $0$, pointer registers $p[k]=ps_k$ and memory $M[k]=xs_k$ for $0\le k<|xs|$, and $0$ everywhere else. The input of the Fréchet problem (`curveInput P Q`) is $p[0]=n$, $p[1]=m$, $M[i d+j]=(p_i)_j$ for $i<n$ and $M[nd+id+j]=(q_i)_j$ for $i<m$, $j<d$.
--
--   **Outputs.** `ComputesWithin A s T D`: started in $s$, $A$ reaches `accept` within $T$ steps and then $M[-1]=D$. `ComputesPointWithin`: output point $(M[-1],M[-2])$. `ComputesListWithin`: output list $w$ with $M[-1]=|w|$ and $w_k=(M[-2-2k],M[-3-2k])$. `ComputesValueListWithin`: value $M[-1]$, and a list with $M[-2]=|w|$, $w_k=(M[-3-2k],M[-4-2k])$. `flatPts w` lists the coordinates $x_0,y_0,x_1,y_1,\dots$.
--
--   **Formalization Note** The core alone cannot add two pointers or store a pointer in memory, so arrays and pointer-based structures could not be addressed in $O(1)$; `idx` and `ofPtr` provide integer indexing with a real-valued integer. Rational literals keep a constant from encoding information. The pattern follows the published `TruncLowDeg_Recovery_Machine` (sqrt, rational literals) and `OptRobustCD_Machine` (exact-integer indexing), without importing them.
-- source:
--   Huang, Wang, Zhang, Constant Approximation of Fréchet Distance in Near-Linear Time, STOC 2027 submission (manuscript sha256 08be7e65…dd2d), p. 2, Theorem 1.1; p. 3 (near-linear time); p. 33, §7.1 (last paragraph)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_FrechetNearLinear_Main_Frechet

/-!
# The cost model: a deterministic unit-cost real RAM with square root and integer indexing

Huang, Wang, Zhang, *Constant Approximation of Fréchet Distance in Near-Linear Time*, STOC 2027
submission (manuscript sha256 08be7e65…dd2d), p. 2 Theorem 1.1 ("computes in `O(n^{1+ε})`
time"), p. 3 ("near-linear refers to this `O(n^{1+ε})` guarantee"). The paper names no machine;
this is the reading of the mission.

* The instruction set is the published core `SmaleNinth.RAMInstr` (exact `+ − × ÷` with
  `x / 0 = 0`, real literals, indirect real memory `ℤ → ℝ` addressed by integer pointer
  registers, pointer set/copy/increment/decrement, jumps on `r ≤ 0` and `p ≤ p'`,
  `accept`/`reject`) plus three instructions:
  `sqrt` (`r[dst] := √r[src]`, `Real.sqrt`, so negative arguments give `0`),
  `idx` (`p[q] := r[src]` when `r[src]` is an integer; on a non-integer the machine is stuck
  forever and never halts), and `ofPtr` (`r[dst] := p[q]`).
* `Admissible` restricts real literals to rationals, so no constant can encode information.
* There is no floor of a non-integer, no exp/log, no randomness and no oracle. Every executed
  instruction costs one step. The machine is deterministic.
* A configuration is halted when its program counter points at `accept` or `reject`; the step
  leaves it unchanged from then on. A program counter outside the program is stuck.
* Inputs are given by `initCfg ps xs`: pointer registers `p[k] = ps[k]`, memory cells
  `M[k] = xs[k]` for `k < |xs|`, every other cell, register and pointer `0`.
* Outputs: a real value in `M[-1]`; a point `(M[-1], M[-2])`; a list of `K` points as
  `M[-1] = K`, `(M[-2-2k], M[-3-2k])` for `k < K`; a value with a list of points as
  `M[-1]` (value), `M[-2] = K`, `(M[-3-2k], M[-4-2k])`.
-/

namespace FrechetNearLinear.Main

/-- An instruction: a `SmaleNinth` core instruction, square root, or integer indexing. -/
inductive Instr where
  /-- A core real-RAM instruction. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `r[dst] := √r[src]`. -/
  | sqrt (dst src : ℕ)
  /-- `p[q] := r[src]` if `r[src]` is an integer; stuck otherwise. -/
  | idx (q src : ℕ)
  /-- `r[dst] := p[q]`. -/
  | ofPtr (dst q : ℕ)

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Every real literal of the program is rational. -/
def Admissible (A : Program) : Prop :=
  ∀ dst : ℕ, ∀ c : ℝ, Instr.core (.const dst c) ∈ A → ∃ x : ℚ, c = (x : ℝ)

/-- The core instruction at a position holding a core instruction (`accept` as a placeholder
for the extensions, which `step` never hands to the core). -/
def Instr.coreOf : Instr → SmaleNinth.RAMInstr
  | .core i => i
  | _ => .accept

/-- One step of program `A`. -/
noncomputable def step (A : Program) (s : SmaleNinth.RAMConfig) : SmaleNinth.RAMConfig :=
  match A[s.pc]? with
  | some (.sqrt dst src) =>
      ⟨s.pc + 1, Function.update s.regs dst (Real.sqrt (s.regs src)), s.ptrs, s.mem⟩
  | some (.idx q src) =>
      if ((⌊s.regs src⌋ : ℤ) : ℝ) = s.regs src then
        ⟨s.pc + 1, s.regs, Function.update s.ptrs q ⌊s.regs src⌋, s.mem⟩
      else s
  | some (.ofPtr dst q) =>
      ⟨s.pc + 1, Function.update s.regs dst ((s.ptrs q : ℤ) : ℝ), s.ptrs, s.mem⟩
  | _ => SmaleNinth.RAMStep (A.map Instr.coreOf) s

/-- The configuration after `t` steps. -/
noncomputable def run (A : Program) (s : SmaleNinth.RAMConfig) (t : ℕ) : SmaleNinth.RAMConfig :=
  (step A)^[t] s

/-- `s` is halted in the accepting state. -/
def Accepted (A : Program) (s : SmaleNinth.RAMConfig) : Prop :=
  A[s.pc]? = some (.core .accept)

/-- The initial configuration: program counter `0`, all real registers `0`, pointer registers
`p[k] = ps[k]` (`0` beyond), memory `M[k] = xs[k]` for `0 ≤ k < |xs|` (`0` elsewhere). -/
noncomputable def initCfg (ps : List ℤ) (xs : List ℝ) : SmaleNinth.RAMConfig where
  pc := 0
  regs := fun _ => 0
  ptrs := fun q => ps.getD q 0
  mem := fun a => if 0 ≤ a then xs.getD a.toNat 0 else 0

/-- `A` started in `s` reaches `accept` within `T` steps. -/
def AcceptsWithin (A : Program) (s : SmaleNinth.RAMConfig) (T : ℝ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ Accepted A (run A s t)

/-- `A` started in `s` reaches `accept` within `T` steps with output value `D = M[-1]`. -/
def ComputesWithin (A : Program) (s : SmaleNinth.RAMConfig) (T : ℝ) (D : ℝ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ Accepted A (run A s t) ∧ (run A s t).mem (-1) = D

/-- `A` reaches `accept` within `T` steps with output point `z = (M[-1], M[-2])`. -/
def ComputesPointWithin (A : Program) (s : SmaleNinth.RAMConfig) (T : ℝ) (z : ℝ × ℝ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ Accepted A (run A s t) ∧
    (run A s t).mem (-1) = z.1 ∧ (run A s t).mem (-2) = z.2

/-- `A` reaches `accept` within `T` steps with output list `w`: `M[-1] = |w|` and
`w[k] = (M[-2-2k], M[-3-2k])`. -/
def ComputesListWithin (A : Program) (s : SmaleNinth.RAMConfig) (T : ℝ)
    (w : List (ℝ × ℝ)) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ Accepted A (run A s t) ∧
    (run A s t).mem (-1) = (w.length : ℝ) ∧
    ∀ k : ℕ, ∀ h : k < w.length,
      (run A s t).mem (-2 - 2 * (k : ℤ)) = w[k].1 ∧ (run A s t).mem (-3 - 2 * (k : ℤ)) = w[k].2

/-- `A` reaches `accept` within `T` steps with output value `U = M[-1]` and output list `w`:
`M[-2] = |w|` and `w[k] = (M[-3-2k], M[-4-2k])`. -/
def ComputesValueListWithin (A : Program) (s : SmaleNinth.RAMConfig) (T : ℝ) (U : ℝ)
    (w : List (ℝ × ℝ)) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ T ∧ Accepted A (run A s t) ∧ (run A s t).mem (-1) = U ∧
    (run A s t).mem (-2) = (w.length : ℝ) ∧
    ∀ k : ℕ, ∀ h : k < w.length,
      (run A s t).mem (-3 - 2 * (k : ℤ)) = w[k].1 ∧ (run A s t).mem (-4 - 2 * (k : ℤ)) = w[k].2

/-- The coordinates of a vertex sequence, vertex by vertex: `(p₀)₀, …, (p₀)_{d-1}, (p₁)₀, …`. -/
noncomputable def coords {d n : ℕ} (P : Fin n → E d) : List ℝ :=
  (List.ofFn P).flatMap fun p => List.ofFn fun j : Fin d => p j

/-- The input of the Fréchet problem: `p[0] = n`, `p[1] = m`, `M[i·d + j] = (pᵢ)ⱼ` for `i < n`,
`M[n·d + i·d + j] = (qᵢ)ⱼ` for `i < m`, `j < d`; all else `0`. -/
noncomputable def curveInput {d n m : ℕ} (P : Fin n → E d) (Q : Fin m → E d) :
    SmaleNinth.RAMConfig :=
  initCfg [(n : ℤ), (m : ℤ)] (coords P ++ coords Q)

/-- The coordinates of a list of points of the plane: `x₀, y₀, x₁, y₁, …`. -/
def flatPts (w : List (ℝ × ℝ)) : List ℝ := w.flatMap fun z => [z.1, z.2]

end FrechetNearLinear.Main


