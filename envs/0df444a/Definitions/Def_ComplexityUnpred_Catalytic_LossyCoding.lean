-- Prove2me | Definitions.Def_ComplexityUnpred_Catalytic_LossyCoding
-- name    : ComplexityUnpred_Catalytic_LossyCoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:03:30.719197+00:00
-- url     : https://prove2.me/theorems/22ff4cf1-8bd1-4e0b-921a-372e1465cbf8
-- title:
--   LossyCoding, D^ext, NonSol, in-place machines and the graph G(C, D, M) (Definitions 4.9, 4.11, 4.13, 4.14)
-- statement:
--   Let $n\ge1$. A **LossyCoding instance** is a pair $C:\{0,1\}^n\to\{0,1\}^{n-1}$, $D:\{0,1\}^{n-1}\to\{0,1\}^n$; $x\in\{0,1\}^n$ is a **solution** if $D(C(x))\neq x$. The **extension** $D^{\mathrm{ext}}:\{0,1\}^n\to\{0,1\}^n$ is $D^{\mathrm{ext}}(x)=D(x_{<n})$, and $\mathrm{NonSol}(C,D)=\{x\in\{0,1\}^n: D(C(x))=x\}$.
--
--   An **in-place machine** with read-write input $y\in\{0,1\}^n$ and $\ell$-bit states is described by its configurations $(y,\sigma)$, $\sigma\in\{0,1\}^\ell$ (the state: everything but the input tape, i.e. control state, head positions and work tape): a one-step map $M(y,\sigma)$, the start state $\sigma_{\mathrm{start}}$, the halting states, and the input-head position $\text{input-head}(\sigma)\in[n]$, such that a step changes the input tape at most at $\text{input-head}(\sigma)$. $M^{(t)}$ is $t$ steps, $\mathrm{time}(M(y))$ the number of steps from $(y,\sigma_{\mathrm{start}})$ before a halting state is reached, and $M$ **computes $D^{\mathrm{ext}}$** if on every $y\in\{0,1\}^n$ it halts with $D^{\mathrm{ext}}(y)$ on the input tape.
--
--   The graph **$G(C,D,M)$** is the hypercube digraph of dimension $n$ with $(\ell+1)$-bit labels whose edges are, for $x\in\mathrm{NonSol}(C,D)$, $b\in\{0,1\}$ and $0\le t<\mathrm{time}(M(C(x)\circ b))$, the copies
--   $$e_{x,b,t}=\big(M^{(t)}(C(x)\circ b,\sigma_{\mathrm{start}})_1,\ M^{(t+1)}(C(x)\circ b,\sigma_{\mathrm{start}})_1\big),\qquad \mathrm{lab}(e_{x,b,t})=M^{(t)}(C(x)\circ b,\sigma_{\mathrm{start}})_2\circ b,$$
--   with $\mathrm{ind}(l)=\text{input-head}(l_{\le\ell})$: the computation paths of $M$ on the inputs $C(x)\circ b$, projected to the input tape.
--
--   **Formalization Note** `InPlaceMachine n ℓ` is the configuration interface of p. 34 (state $\sigma$ coded in exactly $\ell$ bits, step, start, halting test, input head, locality of a step). Every in-place Turing machine, with any fixed read-only advice whose head position is part of $\sigma$, and an injective $\ell$-bit code of its states, is one; $\ell$-bit codes that are not states still get some input-head value. `time` is `sInf` of the halting times (it is $0$ if $M$ never halts, a case excluded wherever it is used by `ComputesDext`). Indices are 0-based; $C(x)\circ b$ is `snocBit`, $\sigma\circ b$ is `snocLabel`, $l_{\le\ell}$ is `initLabel`.
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, pp. 33–36, Definitions 4.9, 4.11, 4.13, 4.14 and the notation of p. 34

import Mathlib
import Definitions.Def_ComplexityUnpred_Catalytic_WeakExcess

namespace ComplexityUnpred.Catalytic

open Classical

/-! Agarwala, Dorfman, *The Complexity of Unpredictability*, arXiv:2611.05956v1, §4.2:
Definition 4.9 (LossyCoding), 4.11 (`Dext`), 4.13 (`NonSol`), pp. 33–34; the configuration
notation of p. 34; Definition 4.14 (the graph `G(C, D, M)`), pp. 35–36.

**In-place machines.** "For an in-place Turing machine `M`, we denote the configuration of `M` by
a tuple `(y, σ)`, where `y` is the string on the read-write input tape, and `σ` is all remaining
information about the configuration of `M` … We refer to the second element … as the state of
`M` … the length of `σ` … We will refer to this as the state size of `M`. … `M(y, σ)` … `M^{(t)}(y, σ)`
… `input-head(σ)` … `σ_start` … `time(M(y))`" (p. 34). An `InPlaceMachine n ℓ` is exactly this
interface for read-write inputs of length `n` and states coded in `ℓ` bits: a deterministic
one-step map on configurations `(y, σ)`, the start state, the halting states, the input-head
position read off a state, and the locality of a Turing-machine step (a step changes the input
tape only under the input head). Every in-place Turing machine (with any fixed read-only advice,
its head position kept in `σ`) whose states are coded injectively in `ℓ` bits is one; codes of
`ℓ` bits that are not states are given some value of `input-head`, as any total code must. -/

/-- The abstract in-place machine on read-write inputs `y ∈ {0,1}ⁿ` with `ℓ`-bit states. -/
structure InPlaceMachine (n ℓ : ℕ) where
  /-- One step: `M(y, σ)`. -/
  step : (Fin n → Bool) × (Fin ℓ → Bool) → (Fin n → Bool) × (Fin ℓ → Bool)
  /-- `σ_start`. -/
  start : Fin ℓ → Bool
  /-- The halting states. -/
  halted : (Fin ℓ → Bool) → Bool
  /-- `input-head(σ)`, 0-based. -/
  inputHead : (Fin ℓ → Bool) → Fin n
  /-- A step changes the read-write input tape at most under the input head. -/
  step_local : ∀ (y : Fin n → Bool) (σ : Fin ℓ → Bool) (i : Fin n),
    (step (y, σ)).1 i ≠ y i → i = inputHead σ

namespace InPlaceMachine

variable {n ℓ : ℕ}

/-- `M^{(t)}(y, σ)`: the configuration after `t` steps. -/
def run (M : InPlaceMachine n ℓ) (t : ℕ) (c : (Fin n → Bool) × (Fin ℓ → Bool)) :
    (Fin n → Bool) × (Fin ℓ → Bool) :=
  M.step^[t] c

/-- `time(M(y))`: the number of steps before `M`, started on `(y, σ_start)`, reaches a halting
state. (`sInf ∅ = 0` if it never halts; every statement using `time` assumes that `M` halts on
the relevant inputs.) -/
noncomputable def time (M : InPlaceMachine n ℓ) (y : Fin n → Bool) : ℕ :=
  sInf {t | M.halted (M.run t (y, M.start)).2 = true}

end InPlaceMachine

/-- `x_{<n}`: the first `n − 1` bits of `x ∈ {0,1}ⁿ`. -/
def prefixBits {n : ℕ} (x : Fin n → Bool) : Fin (n - 1) → Bool :=
  fun i => x ⟨i.val, by have h1 := i.isLt; omega⟩

/-- `s ∘ b`: the bit `b` appended to `s ∈ {0,1}^{n−1}`, a string in `{0,1}ⁿ` (for `n ≥ 1`). -/
def snocBit {n : ℕ} (s : Fin (n - 1) → Bool) (b : Bool) : Fin n → Bool :=
  fun i => if h : i.val < n - 1 then s ⟨i.val, h⟩ else b

/-- `σ ∘ b ∈ {0,1}^{ℓ+1}` for `σ ∈ {0,1}^ℓ`. -/
def snocLabel {ℓ : ℕ} (σ : Fin ℓ → Bool) (b : Bool) : Fin (ℓ + 1) → Bool :=
  fun i => if h : i.val < ℓ then σ ⟨i.val, h⟩ else b

/-- `l_{≤ℓ}`: the first `ℓ` bits of `l ∈ {0,1}^{ℓ+1}`. -/
def initLabel {ℓ : ℕ} (l : Fin (ℓ + 1) → Bool) : Fin ℓ → Bool :=
  fun i => l i.castSucc

/-- **Definition 4.9** (p. 33): `x ∈ {0,1}ⁿ` is a solution to LossyCoding on `(C, D)`, where
`C : {0,1}ⁿ → {0,1}^{n−1}` and `D : {0,1}^{n−1} → {0,1}ⁿ`, if `D(C(x)) ≠ x`. -/
def IsLossySolution {n : ℕ} (C : (Fin n → Bool) → Fin (n - 1) → Bool)
    (D : (Fin (n - 1) → Bool) → Fin n → Bool) (x : Fin n → Bool) : Prop :=
  D (C x) ≠ x

/-- **Definition 4.11** (p. 34): `D^ext(x) := D(x_{<n})` for `x ∈ {0,1}ⁿ`. -/
def Dext {n : ℕ} (D : (Fin (n - 1) → Bool) → Fin n → Bool) (x : Fin n → Bool) : Fin n → Bool :=
  D (prefixBits x)

/-- **Definition 4.13** (p. 34): `NonSol(C, D) := {x ∈ {0,1}ⁿ | D(C(x)) = x}`. -/
noncomputable def NonSol {n : ℕ} (C : (Fin n → Bool) → Fin (n - 1) → Bool)
    (D : (Fin (n - 1) → Bool) → Fin n → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => D (C x) = x)

/-- `M` computes `D^ext` (Definition 2.13 for the in-place machine): on every input
`y ∈ {0,1}ⁿ`, started in `σ_start`, `M` halts, and when it halts the input tape holds
`D^ext(y)`. -/
def InPlaceMachine.ComputesDext {n ℓ : ℕ} (M : InPlaceMachine n ℓ)
    (D : (Fin (n - 1) → Bool) → Fin n → Bool) : Prop :=
  ∀ y : Fin n → Bool, (∃ t, M.halted (M.run t (y, M.start)).2 = true) ∧
    (M.run (M.time y) (y, M.start)).1 = Dext D y

/-- **Definition 4.14** (pp. 35–36): the graph `G(C, D, M) = (V, E, lab, ind)` with
`V = {0,1}ⁿ`, `ℓ + 1`-bit labels, and the multiset of edges
`e_{x,b,t} := (M^{(t)}(C(x)∘b, σ_start)₁, M^{(t+1)}(C(x)∘b, σ_start)₁)` for `x ∈ NonSol(C, D)`,
`b ∈ {0,1}`, `0 ≤ t < time(M(C(x)∘b))` (copies retained), labelled
`lab(e_{x,b,t}) := M^{(t)}(C(x)∘b, σ_start)₂ ∘ b`; and `ind(l) := input-head(l_{≤ℓ})`. -/
noncomputable def lossyGraph {n ℓ : ℕ} (C : (Fin n → Bool) → Fin (n - 1) → Bool)
    (D : (Fin (n - 1) → Bool) → Fin n → Bool) (M : InPlaceMachine n ℓ) :
    HypercubeDigraph n (ℓ + 1) where
  E := (NonSol C D).val.bind fun x =>
    (Finset.univ : Finset Bool).val.bind fun b =>
      (Multiset.range (M.time (snocBit (C x) b))).map fun t =>
        ((M.run t (snocBit (C x) b, M.start)).1,
         (M.run (t + 1) (snocBit (C x) b, M.start)).1,
         snocLabel (M.run t (snocBit (C x) b, M.start)).2 b)
  ind := fun l => M.inputHead (initLabel l)

end ComplexityUnpred.Catalytic


