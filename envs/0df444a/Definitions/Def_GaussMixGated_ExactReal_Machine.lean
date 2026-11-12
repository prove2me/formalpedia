-- Prove2me | Definitions.Def_GaussMixGated_ExactReal_Machine
-- name    : GaussMixGated_ExactReal_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:24:19.092452+00:00
-- url     : https://prove2.me/theorems/ba3d5e6f-d5ca-4cd6-9188-cbf32ee84c3f
-- title:
--   The exact-real machine: instructions, runs, work, admissibility, trainer and sampler
-- statement:
--   This definition fixes the computational model of Theorem 1.1. A **program** is a finite list of instructions acting on real registers $r[0],r[1],\dots$, integer pointer registers $p[0],p[1],\dots$ and a real memory $M:\mathbb Z\to\mathbb R$. The instructions are those of the published real pointer machine (real $+,-,\times,\div$ with $x/0=0$, rational or real constants, indirect load and store $M[p[q]]$, pointer set/copy/increment/decrement, the tests $r[i]\le 0$ and $p[q]\le p[q']$ with jumps, and `accept`), together with
--
--   1. $r[\mathrm{dst}]:=\sqrt{r[i]}$, $\exp r[i]$, $\log r[i]$;
--   2. $r[\mathrm{dst}]:=$ the next entry of an ideal standard Gaussian tape;
--   3. a call to an **oracle channel** $j$: it reads a query block of $M$ starting at $p[q]$, writes the channel's answer into the same block, and advances the channel's call counter.
--
--   Every executed instruction costs one unit of **work**; an oracle call costs one unit plus the channel's charge plus one unit per real written. A configuration at `accept` is **halted** and stays fixed. A completed run costs its accumulated nonterminal work plus one unit for `accept`; repeated observation of a halted state adds no charge. A program **halts within $N$** if this total is at most $N$. A program is **admissible** when every real literal is rational and `reject` does not occur.
--
--   For Theorem 1.1 the **trainer** starts with $d,k,\varepsilon,\delta$ in cells $0$–$3$ and $d,k$ in pointer registers $0,1$, and has one channel returning the next sample $x_t\in\mathbb R^d$ of its sample tape. At its halt the pointer register $0$ holds a length $\ell$ and the **description** is $M[0],\dots,M[\ell-1]$. The **sampler** starts with the description in cells $0,\dots,\ell-1$, has no oracle, and its output is $(M[0],\dots,M[d-1])$ at its halt; $\hat P$ is the law of this output when the Gaussian tape is i.i.d. $N(0,1)$.
--
--   This is the model paragraph of the paper: unit-cost exact real arithmetic, comparisons, square roots, exponentials and logarithms, and ideal Gaussian draws. No floor, real-to-pointer cast or bit operation is provided.
--
--   **Formalization Note** Lean's total functions give $\log x=\log|x|$, $\log 0=0$ and $\sqrt x=0$ for $x<0$; a program can test signs before using them. Rational literals prevent non-computable advice in constants.
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 3 (printed p. 1), model paragraph after Theorem 1.1; §2.3, PDF p. 8

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM

open MeasureTheory ProbabilityTheory

noncomputable section

namespace GaussMixGated.ExactReal

/-!
# The exact-real machine (Zheng–Xie–He, STOC 2027 #36, model paragraph, PDF p. 3)

The published real pointer machine `SmaleNinth.RAMInstr` (real `+ − × ÷` with `x / 0 = 0`,
constants, indirect load/store through integer pointers, pointer set/copy/increment/decrement,
comparisons `r ≤ 0` and `p ≤ p'` with jumps, `accept`) is extended by the operations the paper
adds: square roots, exponentials and logarithms, a draw of an ideal standard Gaussian, and calls
to oracle channels. Every executed instruction costs one unit of work; an oracle call costs one
unit plus the channel's own charge plus one unit per real coordinate written. No floor, no
real-to-pointer cast, no bit operation and no pointer multiplication is available.
-/

/-- An instruction: a core real-RAM instruction, `r[dst] := √r[i]`, `r[dst] := exp r[i]`,
`r[dst] := log r[i]`, `r[dst] :=` the next standard Gaussian of the Gaussian tape, or a call to
oracle channel `j` whose query and answer block starts at memory address `p[q]`. -/
inductive Instr : Type
  | core (i : SmaleNinth.RAMInstr)
  | sqrt (dst i : ℕ)
  | exp (dst i : ℕ)
  | log (dst i : ℕ)
  | gauss (dst : ℕ)
  | oracle (j q : ℕ)

/-- A program: a finite list of instructions, executed from position `0`. -/
abbrev Program := List Instr

/-- An oracle channel: the call reads `inDim` real cells as its query, writes `outDim` real
cells as its answer, and is charged `cost` extra units. `answer t x` is the answer of the
`t`-th call (counting from `0`) to this channel at query `x`. -/
structure Channel where
  inDim : ℕ
  outDim : ℕ
  cost : ℕ
  answer : ℕ → (ℕ → ℝ) → (ℕ → ℝ)

/-- The channel that is used for every index beyond the list of channels: it reads and writes
nothing and answers `0`. -/
def Channel.silent : Channel := ⟨0, 0, 0, fun _ _ _ => 0⟩

/-- The environment of a run: the Gaussian tape and the list of oracle channels. -/
structure Env where
  gtape : ℕ → ℝ
  chans : List Channel

/-- Channel `j` of the environment. -/
def Env.chan (e : Env) (j : ℕ) : Channel := e.chans.getD j Channel.silent

/-- A configuration: program counter, real registers, integer pointer registers, memory, the
number of Gaussian draws used, the number of calls made to each channel, and the work spent. -/
structure State where
  pc : ℕ
  regs : ℕ → ℝ
  ptrs : ℕ → ℤ
  mem : ℤ → ℝ
  gused : ℕ
  calls : ℕ → ℕ
  work : ℕ

/-- The published one-step semantics of the core instruction `c`, executed at position `s.pc`
(jump targets are absolute positions). -/
def coreStep (c : SmaleNinth.RAMInstr) (s : State) : SmaleNinth.RAMConfig :=
  SmaleNinth.RAMStep (List.replicate s.pc SmaleNinth.RAMInstr.reject ++ [c])
    ⟨s.pc, s.regs, s.ptrs, s.mem⟩

/-- Write the answer block `ans 0, …, ans (len − 1)` into memory cells `base, …, base + len − 1`. -/
def writeBlock (mem : ℤ → ℝ) (base : ℤ) (len : ℕ) (ans : ℕ → ℝ) : ℤ → ℝ :=
  fun z => if base ≤ z ∧ z < base + len then ans (z - base).toNat else mem z

/-- One step of program `P` in environment `e`. A configuration at `accept`, at `reject`, or with
a program counter outside the program is left unchanged (no work is charged). -/
def step (P : Program) (e : Env) (s : State) : State :=
  match P[s.pc]? with
  | none => s
  | some (.core c) =>
      match c with
      | .accept => s
      | .reject => s
      | c =>
          let t := coreStep c s
          { s with pc := t.pc, regs := t.regs, ptrs := t.ptrs, mem := t.mem, work := s.work + 1 }
  | some (.sqrt dst i) =>
      { s with pc := s.pc + 1, regs := Function.update s.regs dst (Real.sqrt (s.regs i)),
               work := s.work + 1 }
  | some (.exp dst i) =>
      { s with pc := s.pc + 1, regs := Function.update s.regs dst (Real.exp (s.regs i)),
               work := s.work + 1 }
  | some (.log dst i) =>
      { s with pc := s.pc + 1, regs := Function.update s.regs dst (Real.log (s.regs i)),
               work := s.work + 1 }
  | some (.gauss dst) =>
      { s with pc := s.pc + 1, regs := Function.update s.regs dst (e.gtape s.gused),
               gused := s.gused + 1, work := s.work + 1 }
  | some (.oracle j q) =>
      let ch := e.chan j
      let base := s.ptrs q
      let query : ℕ → ℝ := fun i => if i < ch.inDim then s.mem (base + i) else 0
      let ans := ch.answer (s.calls j) query
      { s with pc := s.pc + 1, mem := writeBlock s.mem base ch.outDim ans,
               calls := Function.update s.calls j (s.calls j + 1),
               work := s.work + 1 + ch.cost + ch.outDim }

/-- The configuration after `t` steps. -/
def run (P : Program) (e : Env) (s₀ : State) (t : ℕ) : State := (step P e)^[t] s₀

/-- The configuration is halted: its instruction is `accept`. -/
def Halted (P : Program) (s : State) : Prop := P[s.pc]? = some (.core .accept)

/-- Work of a completed run: the accumulated nonterminal work plus one execution of `accept`.
The halting configuration remains fixed under `step`, so repeated observation never charges
the terminal instruction again. -/
def haltingWork (s : State) : ℕ := s.work + 1

/-- `P` halts from `s₀` in environment `e` having spent at most `N` units of work, including
one unit for its terminal `accept`. -/
def HaltsWithin (P : Program) (e : Env) (s₀ : State) (N : ℝ) : Prop :=
  ∃ t, Halted P (run P e s₀ t) ∧ (haltingWork (run P e s₀ t) : ℝ) ≤ N

/-- The halting configuration (the first halted one); `s₀` if the run never halts. -/
def final (P : Program) (e : Env) (s₀ : State) : State :=
  open Classical in
  if h : ∃ t, Halted P (run P e s₀ t) then run P e s₀ (Nat.find h) else s₀

/-- **Admissible programs**: every real literal is rational and `reject` does not occur. -/
def Admissible (P : Program) : Prop :=
  ∀ ins ∈ P, (∀ (dst : ℕ) (c : ℝ), ins = .core (.const dst c) → ∃ r : ℚ, c = r) ∧
    ins ≠ .core .reject

/-- The program makes no oracle call. -/
def OracleFree (P : Program) : Prop := ∀ ins ∈ P, ∀ j q, ins ≠ .oracle j q

/-- The program draws no Gaussian. -/
def GaussFree (P : Program) : Prop := ∀ ins ∈ P, ∀ dst, ins ≠ .gauss dst

/-- Memory holding the list `xs` in cells `0, 1, …` and `0` elsewhere. -/
def listMem (xs : List ℝ) : ℤ → ℝ := fun z => if 0 ≤ z then xs.getD z.toNat 0 else 0

/-- Pointer registers holding the list `ps` in registers `0, 1, …` and `0` elsewhere. -/
def listPtrs (ps : List ℤ) : ℕ → ℤ := fun i => ps.getD i 0

/-- The initial configuration with memory `m` and pointer registers `p`; all real registers,
counters and the program counter are `0`. -/
def initState (m : ℤ → ℝ) (p : ℕ → ℤ) : State := ⟨0, fun _ => 0, p, m, 0, fun _ => 0, 0⟩

/-- Memory `m` with the vector `x ∈ ℝ^d` additionally written in cells `−1, −2, …, −d`
(`x_i` in cell `−1 − i`). -/
def withPoint {d : ℕ} (m : ℤ → ℝ) (x : Fin d → ℝ) : ℤ → ℝ :=
  fun z => if h : z < 0 ∧ (-1 - z).toNat < d then x ⟨(-1 - z).toNat, h.2⟩ else m z

/-- A vector of `ℝ^d` as a sequence of reals (zero beyond `d`). -/
def toSeq {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℕ → ℝ :=
  fun i => if h : i < d then x ⟨i, h⟩ else 0

/-- The vector of `ℝ^d` formed by the first `d` terms of a sequence. -/
def ofSeq (d : ℕ) (f : ℕ → ℝ) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => f i)

/-- The length `ℓ` of the output description: pointer register `0` at the halt. -/
def descLen (s : State) : ℕ := (s.ptrs 0).toNat

/-- The output description: the memory cells `0, …, ℓ − 1` at the halt. -/
def desc (s : State) : List ℝ := (List.range (descLen s)).map (fun i => s.mem i)

/-- The channel answering the `t`-th call with the vector `xs t` (no query is read). -/
def obsChannel {d : ℕ} (xs : ℕ → EuclideanSpace ℝ (Fin d)) (cost : ℕ := 0) : Channel :=
  ⟨0, d, cost, fun t _ => toSeq (xs t)⟩

/-- The i.i.d. tape of a law: `Measure.infinitePi` of copies of `μ`. -/
def iidTape {α : Type*} [MeasurableSpace α] (μ : Measure α) : Measure (ℕ → α) :=
  Measure.infinitePi (fun _ : ℕ => μ)

/-- The tape of independent ideal standard Gaussians. -/
def gaussTape : Measure (ℕ → ℝ) := iidTape (gaussianReal 0 1)

/-! ## Trainer and sampler (Theorem 1.1) -/

/-- The trainer's initial configuration: cells `0–3` hold `d, k, ε, δ`; pointer registers `0, 1`
hold `d, k`. -/
def trainerStart (d k : ℕ) (ε δ : ℝ) : State :=
  initState (listMem [(d : ℝ), (k : ℝ), ε, δ]) (listPtrs [(d : ℤ), (k : ℤ)])

/-- The trainer's environment: the Gaussian tape `g` and one channel, channel `0`, returning
the next sample `xs t` of the sample tape (one call = one sample, `d` coordinates). -/
def trainerEnv {d : ℕ} (xs : ℕ → EuclideanSpace ℝ (Fin d)) (g : ℕ → ℝ) : Env :=
  ⟨g, [obsChannel xs]⟩

/-- The trainer's halting configuration on sample tape `xs` and Gaussian tape `g`. -/
def trainerFinal (T : Program) (d k : ℕ) (ε δ : ℝ) (xs : ℕ → EuclideanSpace ℝ (Fin d))
    (g : ℕ → ℝ) : State :=
  final T (trainerEnv xs g) (trainerStart d k ε δ)

/-- The sampler's initial configuration: the description in cells `0, …, ℓ − 1`, everything
else `0`. -/
def samplerStart (D : List ℝ) : State := initState (listMem D) (fun _ => 0)

/-- The sampler's environment: the Gaussian tape `g` and no oracle channel. -/
def samplerEnv (g : ℕ → ℝ) : Env := ⟨g, []⟩

/-- The output point of the sampler `S` on description `D` and Gaussian tape `g`: the memory
cells `0, …, d − 1` at the halt. -/
def samplerOut (d : ℕ) (S : Program) (D : List ℝ) (g : ℕ → ℝ) : EuclideanSpace ℝ (Fin d) :=
  ofSeq d (fun i => (final S (samplerEnv g) (samplerStart D)).mem i)

/-- The law `P̂` of a single output of the sampler `S` run on description `D`. -/
def samplerLaw (d : ℕ) (S : Program) (D : List ℝ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  gaussTape.map (samplerOut d S D)

end GaussMixGated.ExactReal


