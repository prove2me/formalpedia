-- Prove2me | Definitions.Def_ThinShellSampling_Prog
-- name    : ThinShellSampling_Prog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:30.663616+00:00
-- url     : https://prove2.me/theorems/9d0d9687-6ebd-471e-b7e0-ef7a824faa27
-- title:
--   Randomized evaluation-oracle programs, their runs, output law and query count
-- statement:
--   An **oracle program** on $\mathbb R^n$ is a finite-branching tree built from three instructions:
--
--   1. return a value;
--   2. **query** a point $x$: receive $V(x)\in\mathbb R\cup\{\infty\}$ and continue (cost $1$);
--   3. **sample** a fresh uniform real $u\in[0,1]$ and continue (cost $0$).
--
--   A program is run against an oracle $V$ on a random stream $\omega=(\omega_0,\omega_1,\dots)$ of i.i.d. uniform reals. The run **halts** if it finishes after finitely many steps; its **output** and **query count** (the number of query instructions executed) are then defined. The **output law** is the law of the output, and the **expected number of queries** is $\mathbb E_\omega[\#\text{queries}]\in[0,\infty]$.
--
--   This is the model of zeroth-order sampling with an evaluation oracle in which the paper counts queries ("query complexity").
--
--   **Formalization Note** The program does not take $V$ as an argument: $V$ enters only through the run, so a program learns $V$ only from answers to its queries. Arithmetic is free. A non-halting run has output a default value and query count $\infty$. The output law is a push-forward of the stream law; a non-measurable output map would give the zero measure, whose Rényi divergence to any law is $\infty$.
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), §1, p.1 (PDF p.3); Theorem 1.7, p.5 (PDF p.7); §2.2.1, p.17 (PDF p.19)

import Mathlib

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory
open scoped ENNReal

/-- **Randomized evaluation-oracle programs** on `ℝⁿ` returning a value of type `α`.

Kook, Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity*, STOC 2027 submission
(manuscript sha256 25a041a9…), §1, p.1 (PDF p.3): "the query complexity of sampling … using an
evaluation oracle"; Theorem 1.7, p.5 (PDF p.7): "Given access to an evaluation oracle for `V`".

* `pure a` returns `a`;
* `query x k` asks the oracle for `V(x) ∈ ℝ ∪ {∞}` and continues with `k (V x)` (cost `1`);
* `sample k` draws a fresh `Uniform[0, 1]` real `u` and continues with `k u` (cost `0`).

**Formalization Note.** Query complexity charges only oracle calls; arithmetic in continuations is
free. A program is a tree that does **not** mention `V`: the potential enters only through `run`, so
a program learns `V` only from answers to its queries. -/
inductive Prog (n : ℕ) (α : Type) : Type where
  | pure : α → Prog n α
  | query : EuclideanSpace ℝ (Fin n) → (WithTop ℝ → Prog n α) → Prog n α
  | sample : (ℝ → Prog n α) → Prog n α

/-- Sequential composition of programs (monadic bind). -/
def Prog.bind {n : ℕ} {α β : Type} : Prog n α → (α → Prog n β) → Prog n β
  | .pure a, f => f a
  | .query x k, f => .query x (fun v => (k v).bind f)
  | .sample k, f => .sample (fun u => (k u).bind f)

/-- **Run with fuel.** `runF V f p ω` runs `p` against the oracle `V` on the random stream
`ω : ℕ → [0, 1]` (the `i`-th `sample` reads `ω i`), allowing at most `f` steps. It returns
`some (a, c)` with the result `a` and the number `c` of oracle queries made, or `none` if the fuel
runs out. -/
def runF {n : ℕ} {α : Type} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) :
    ℕ → Prog n α → (ℕ → unitInterval) → Option (α × ℕ)
  | 0, _, _ => none
  | _ + 1, .pure a, _ => some (a, 0)
  | f + 1, .query x k, ω => (runF V f (k (V x)) ω).map (fun r => (r.1, r.2 + 1))
  | f + 1, .sample k, ω => runF V f (k (ω 0 : ℝ)) (fun i => ω (i + 1))

/-- The run of `p` against `V` on the stream `ω` **halts** (finishes with some finite fuel). -/
def Halts {n : ℕ} {α : Type} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (p : Prog n α)
    (ω : ℕ → unitInterval) : Prop :=
  ∃ f, (runF V f p ω).isSome

/-- The **result** (value and query count) of a halting run, computed with the least sufficient
fuel; `none` if the run does not halt. -/
noncomputable def result {n : ℕ} {α : Type} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
    (p : Prog n α) (ω : ℕ → unitInterval) : Option (α × ℕ) := by
  classical
  exact if h : Halts V p ω then runF V (Nat.find h) p ω else none

/-- The **output** of the run, with the default value `d` for a non-halting run. -/
noncomputable def output {n : ℕ} {α : Type} (d : α) (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
    (p : Prog n α) (ω : ℕ → unitInterval) : α :=
  ((result V p ω).map Prod.fst).getD d

/-- The **number of oracle queries** of the run, `⊤` for a non-halting run. -/
noncomputable def queryCount {n : ℕ} {α : Type} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
    (p : Prog n α) (ω : ℕ → unitInterval) : ℕ∞ :=
  match result V p ω with
  | some r => (r.2 : ℕ∞)
  | none => ⊤

/-- **The law of the random stream**: i.i.d. `Uniform[0, 1]` coordinates (the infinite product of
Lebesgue measure on `[0, 1]`). -/
noncomputable def streamMeasure : Measure (ℕ → unitInterval) :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

/-- **The output law** of a program returning points of `ℝⁿ`: the push-forward of the stream law
under the output map (default `0` for a non-halting run).

**Formalization Note.** `Measure.map` of a map that is not a.e.-measurable is the zero measure, whose
Rényi divergence to any probability measure is `∞` (`renyi`); the goal also asserts a.e.-measurability
explicitly. -/
noncomputable def lawOf {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
    (p : Prog n (EuclideanSpace ℝ (Fin n))) : Measure (EuclideanSpace ℝ (Fin n)) :=
  streamMeasure.map (output 0 V p)

/-- **Expected number of oracle queries** `E[#queries] ∈ [0, ∞]` of a program run against `V`. -/
noncomputable def expQueries {n : ℕ} {α : Type} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
    (p : Prog n α) : ℝ≥0∞ :=
  ∫⁻ ω, (queryCount V p ω : ℝ≥0∞) ∂streamMeasure

end ThinShellSampling


