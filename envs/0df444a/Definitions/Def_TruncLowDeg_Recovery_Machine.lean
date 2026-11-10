-- Prove2me | Definitions.Def_TruncLowDeg_Recovery_Machine
-- name    : TruncLowDeg_Recovery_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:24:28.353275+00:00
-- url     : https://prove2.me/theorems/2d2a698e-0680-4a98-859e-eedda7fb544b
-- title:
--   The cost model: a deterministic unit-cost real RAM with square root, its input and output layout
-- statement:
--   The paper states running times without naming a machine. The mission's reading is a **deterministic unit-cost real RAM**: the published core `SmaleNinth.RAMInstr` (exact $+,-,\times,\div$ with $x/0=0$, real literals, indirect real memory addressed by integer pointer registers, pointer set/copy/increment/decrement, jumps on $r\le0$ and $p\le p'$, `accept`, `reject`) together with one instruction $r[\mathrm{dst}]:=\sqrt{r[\mathrm{src}]}$. A program is a finite list of instructions; it is **admissible** when every real literal is rational, so no constant can encode information. There is no floor, exponential, logarithm, eigenvalue, SVD or matrix-square-root instruction, no randomness and no oracle. Every executed instruction costs one step.
--
--   A configuration is **halted** when its program counter points at `accept` or `reject`; from then on it does not change. A program counter outside the program is stuck forever and never halts. `reject` means Fail and `accept` means a pair is returned.
--
--   **Input layout.** On input $(d,k,n,\alpha_0,\varepsilon,\delta,X_1,\dots,X_n)$: pointer registers $p[0]=d$, $p[1]=k$, $p[2]=n$; real memory $M[0]=\alpha_0$, $M[1]=\varepsilon$, $M[2]=\delta$ and $M[3+i\,d+j]=(X_i)_j$ for $0\le i<n$, $0\le j<d$; everything else is $0$.
--
--   **Output layout.** On `accept`, $(\hat\mu_0)_j=M[-1-j]$ and $(\hat\Sigma_0)_{ij}=M[-1-d-(i\,d+j)]$.
--
--   **Formalization Note.** `run P s t` is the configuration after $t$ steps, `Halted P s` the halting predicate, `initConfig` the input layout and `output P d s` the decoded output (`none` unless the program counter is at `accept`). The square root is `Real.sqrt`, which is $0$ on negative numbers.
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 25, Theorem 6.1; pp. 33–35, Lemma 6.8 (machine reading)

import Definitions.Def_TruncLowDeg_Recovery_Basic
import Definitions.Def_SmaleNinth_RealRAM

namespace TruncLowDeg.Recovery

/-!
# The cost model: a deterministic unit-cost real RAM with square root

Vári-Kakas, Wiedmer, *A General Approach to Polynomial-Time Truncated Learning via Low-Degree
Moments*, STOC 2027 submission (manuscript sha256 613f0e39…), p. 25 Theorem 6.1 ("runs in
`n d^{O(k)}` time") and pp. 33–35 Lemma 6.8 (runtime analysis). The paper names no machine; this
is the reading of the mission.

* The instruction set is the published core `SmaleNinth.RAMInstr` (exact `+ − × ÷` with
  `x / 0 = 0`, real literals, indirect real memory addressed by integer pointer registers,
  pointer set/copy/increment/decrement, comparison jumps on `r ≤ 0` and `p ≤ p'`,
  `accept`/`reject`) plus one instruction `sqrt` (`r[dst] := √r[src]`, `Real.sqrt`, so the
  square root of a negative number is `0`).
* `Admissible` restricts real literals to rationals, so no constant can encode information.
* There is no floor, no exp/log, no eigenvalue, SVD or matrix-square-root instruction, no
  randomness and no oracle. Every executed instruction costs one step.
* A configuration is halted when its program counter points at `accept` or `reject`; the core
  step leaves it unchanged from then on. A program counter outside the program is stuck and
  never halts. `reject` means `Fail`; `accept` means a pair is returned.
* **Input layout.** Pointer registers `p[0] = d`, `p[1] = k`, `p[2] = n`; real memory
  `M[0] = α₀`, `M[1] = ε`, `M[2] = δ`, and `M[3 + i·d + j] = (X_i)_j` for `i < n`, `j < d`
  (samples row by row, `0`-based); every other cell, register and pointer is `0`.
* **Output layout.** On `accept`: `µ̂₀_j = M[−1 − j]` and `(Σ̂₀)_{ij} = M[−1 − d − (i·d + j)]`.
-/

/-- An instruction: a `SmaleNinth` real-RAM instruction, or `r[dst] := √r[src]`. -/
inductive Instr where
  /-- A core real-RAM instruction. -/
  | core (i : SmaleNinth.RAMInstr)
  /-- `r[dst] := √r[src]`. -/
  | sqrt (dst src : ℕ)

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- Every real literal of the program is rational. -/
def Admissible (P : Program) : Prop :=
  ∀ dst : ℕ, ∀ c : ℝ, Instr.core (.const dst c) ∈ P → ∃ q : ℚ, c = (q : ℝ)

/-- The core table of `P` (a `sqrt` slot becomes a placeholder never executed by the core). -/
def coreProgram (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun i => match i with
    | .core c => c
    | .sqrt _ _ => .const 0 0

/-- One step. -/
noncomputable def step (P : Program) (s : SmaleNinth.RAMConfig) : SmaleNinth.RAMConfig :=
  match P[s.pc]? with
  | some (.sqrt dst src) =>
      ⟨s.pc + 1, Function.update s.regs dst (Real.sqrt (s.regs src)), s.ptrs, s.mem⟩
  | _ => SmaleNinth.RAMStep (coreProgram P) s

/-- The configuration after `t` steps. -/
noncomputable def run (P : Program) (s : SmaleNinth.RAMConfig) (t : ℕ) : SmaleNinth.RAMConfig :=
  (step P)^[t] s

/-- `s` is halted (its program counter points at `accept` or `reject`). -/
def Halted (P : Program) (s : SmaleNinth.RAMConfig) : Prop :=
  P[s.pc]? = some (.core .accept) ∨ P[s.pc]? = some (.core .reject)

/-- The initial configuration on input `(d, k, n, α₀, ε, δ, X₁, …, X_n)`. -/
noncomputable def initConfig (d k n : ℕ) (α₀ ε δ : ℝ) (X : Fin n → Vec d) :
    SmaleNinth.RAMConfig where
  pc := 0
  regs := fun _ => 0
  ptrs := fun q => if q = 0 then (d : ℤ) else if q = 1 then (k : ℤ) else if q = 2 then (n : ℤ)
    else 0
  mem := fun a =>
    if a = 0 then α₀ else if a = 1 then ε else if a = 2 then δ
    else if h : 3 ≤ a ∧ a < 3 + (n : ℤ) * d then
      X ⟨(a - 3).toNat / d, by
          have hd : 0 < d := by
            rcases Nat.eq_zero_or_pos d with h0 | h0
            · subst h0; simp at h; omega
            · exact h0
          have : (a - 3).toNat < n * d := by omega
          exact (Nat.div_lt_iff_lt_mul hd).2 this⟩
        ⟨(a - 3).toNat % d, by
          have hd : 0 < d := by
            rcases Nat.eq_zero_or_pos d with h0 | h0
            · subst h0; simp at h; omega
            · exact h0
          exact Nat.mod_lt _ hd⟩
    else 0

open Classical in
/-- The output read from a halted configuration: `none` (`Fail`) on `reject`, otherwise the pair
`(µ̂₀, Σ̂₀)` from the output block. -/
noncomputable def output (P : Program) (d : ℕ) (s : SmaleNinth.RAMConfig) :
    Option (Vec d × Mat d) :=
  if P[s.pc]? = some (.core .accept) then
    some (WithLp.toLp 2 (fun j => s.mem (-1 - (j : ℤ))),
      Matrix.of fun i j => s.mem (-1 - (d : ℤ) - ((i : ℤ) * d + j)))
  else none

end TruncLowDeg.Recovery


