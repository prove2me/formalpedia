-- Prove2me | Definitions.Def_LimitsLifting_Approximation_Supplement_SliceBarrier
-- name    : LimitsLifting_Approximation_Supplement_SliceBarrier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:33:53.532229+00:00
-- url     : https://prove2.me/theorems/16fa109e-49a9-424c-bac8-33a2db5d41a0
-- title:
--   §5 — error sets, Razborov's distances $\rho(f,\mathcal M)$ and $\rho(f,\mathcal M,x)$, slices, essential inputs, threshold-circuit sizes and $\Gamma$
-- statement:
--   This definition file sets up the objects of §5 of the paper on top of the published approximation models.
--
--   Fix $n$ and a domain $Z_n\subseteq\{0,1\}^n$. A **legitimate model** $\mathcal M$ over $Z_n$ of circuits over $\{\vee_2,\wedge_2\}$ (Definition 5.1) is a set $\mathcal M$ of Boolean functions on $Z_n$ that contains the constants $0,1$ and every input $x_i$, together with commutative operations $\bar\wedge,\bar\vee:\mathcal M\times\mathcal M\to\mathcal M$ (the published `ApproxModel`). Identifying a function with its set of ones, the **error sets** (Definition 5.3) of a gate $\circ\in\{\vee,\wedge\}$ at $g,h\in\mathcal M$ are
--
--   $$\delta_\circ(g,h)=\big(g\mathbin{\bar\circ}h\setminus g\circ h\big)\cup\big(g\circ h\setminus g\mathbin{\bar\circ}h\big),$$
--
--   the points where the approximate gate differs from the exact one, and $\Delta$ is the family of all of them.
--
--   1. **Distance** (Definition 5.4): $\rho(f,\mathcal M)$ is the least $t$ such that for some $g\in\mathcal M$ the set $f\oplus g$ is covered by $t$ members of $\Delta$, and $\rho(f,\mathcal M)=\infty$ if there is no such $t$.
--   2. **Probabilistic distance** (printed p. 27): for a random input $x$ on $Z_n$, let $d=\max_{\delta\in\Delta}\mathbb P[x\in\delta]$; then $\rho(f,\mathcal M,x)=\min_{g\in\mathcal M}\mathbb P[f(x)\neq g(x)]/d$ if $d\neq0$, and $\rho(f,\mathcal M,x)=0$ otherwise.
--   3. **Slices**: $f$ is an $\ell$-slice if $f(x)=1$ for every $x\in Z_n$ with more than $\ell$ ones and $f(x)=0$ for every $x\in Z_n$ with fewer than $\ell$ ones.
--   4. **Essential inputs**: writing $\hat f:\{0,1\}^n\to\{0,1,\star\}$ for $f$ extended by $\star$ off $Z_n$, input $i$ is essential if switching $x_i$ changes $\hat f$ at some point; $n_0$ is the number of essential inputs.
--   5. **Threshold sizes**: $T^k_\ell$ is one iff at least $\ell$ of its $k$ inputs are one, and $X_i$ denotes the inputs other than $x_i$. $\tilde t_{\ell,k}$ is the least number of gates of a monotone $k$-input $k$-output circuit computing $(T^{k-1}_\ell(X_1),\dots,T^{k-1}_\ell(X_k))$, with gates shared by several outputs counted once; $t_{\ell,k}$ is the least size of a monotone circuit computing $T^k_\ell$.
--   6. **The factor** $\Gamma=12\big(3(n_0+1)+\tilde t_{\ell,n_0}+t_{\ell,n_0}+t_{\ell+1,n_0}+2\big)$.
--
--   These are the quantities in which the approximation barrier for slices (Theorem 5.6) and its key lemma (Lemma 5.7) are stated.
--
--   **Formalization Note** Inputs are indexed by `Fin n`, a partial function is a function on the subtype $Z_n$, and laws of random variables are probability mass functions (`PMF`). $\rho(f,\mathcal M)$ takes values in `ℕ∞` (infimum of the empty set is $\infty$); $\rho(f,\mathcal M,x)$ is computed in `ℝ≥0∞` with the paper's convention at $d=0$; maxima and minima are over finite nonempty families, so they are attained. Circuit sizes count binary $\wedge/\vee$ gates (constants and inputs are free) and use the published straight-line `Circuit` format; a minimum-size circuit always exists, so the natural-number infima are genuine minima. Out-of-range thresholds ($\ell\ge k$) and $k=0$ are covered by the same definitions (constant outputs, size $0$).
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), §5.1–5.2: Definitions 5.1–5.4 printed pp. 25–26 (PDF pp. 26–27); probabilistic distance, ℓ-slices, T^n_ℓ, T̃^n_ℓ, t̃_{ℓ,n}, Th^n_ℓ, t_{ℓ,n} printed p. 27 (PDF p. 28); essential inputs and Γ printed p. 28 (PDF p. 29); partial-map convention §2.1 printed p. 9 (PDF p. 10).

import Mathlib
import Definitions.Def_LimitsLifting_Approximation_ApproxModel

noncomputable section

namespace LimitsLifting.Approximation.Supplement

open Classical
open scoped ENNReal
open LimitsLifting.Approximation

/-! # Error sets, Razborov's distances, slices, essential inputs and threshold-circuit sizes

Carenini, Cavalar, Grosser, Pich, *Limits of Lifting*, STOC 2027 submission #309, §5
(printed pp. 25–28, PDF pp. 26–29): Definitions 5.1–5.4, the probabilistic distance
`ρ(f, M, x)` (printed p. 27), `ℓ`-slices, the threshold functions `T^n_ℓ`, the shared
threshold network `T̃^n_ℓ` of size `t̃_{ℓ,n}`, the circuits `Th^n_ℓ` of size `t_{ℓ,n}`
(printed p. 27), the essential inputs `n₀` (printed p. 28) and the factor `Γ` (printed p. 28).

A legitimate model over `Z ⊆ {0,1}ⁿ` of circuits over `{∨₂, ∧₂}` (Definition 5.1) is the published
`ApproxModel Z`: a set `M` of functions `Z → Bool` containing `0, 1` and every `xᵢ`, with
commutative operations `∧̄, ∨̄` that map `M × M` into `M`. Inputs are indexed by `Fin n`. -/

variable {n : ℕ}

/-- The Hamming weight (number of ones) of a point of `{0,1}ⁿ`. -/
def weight (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

/-- `f ∈ F(Z)` is an `ℓ`-slice: `f(x) = 1` for every `x ∈ Z` with more than `ℓ` ones, and
`f(x) = 0` for every `x ∈ Z` with fewer than `ℓ` ones (values at weight `ℓ` are arbitrary). -/
def IsSlice {Z : Set (Fin n → Bool)} (ℓ : ℕ) (f : Z → Bool) : Prop :=
  ∀ z : Z, (ℓ < weight z.1 → f z = true) ∧ (weight z.1 < ℓ → f z = false)

/-- The partial map `f̂ : {0,1}ⁿ → {0,1,⋆}` of a partial function `f` with domain `Z`
(§2.1): `f̂(x) = f(x)` on `Z` and `⋆` (`none`) off `Z`. -/
def partialMap {Z : Set (Fin n → Bool)} (f : Z → Bool) (x : Fin n → Bool) : Option Bool :=
  if h : x ∈ Z then some (f ⟨x, h⟩) else none

/-- Input `i` is essential for `f`: switching the value of `xᵢ` changes the output `f̂` (an
element of `{0,1,⋆}`) on some assignment of the remaining inputs. -/
def IsEssential {Z : Set (Fin n → Bool)} (f : Z → Bool) (i : Fin n) : Prop :=
  ∃ x : Fin n → Bool, partialMap f x ≠ partialMap f (Function.update x i (!x i))

/-- `n₀`: the number of essential inputs of `f`. -/
def essentialCount {Z : Set (Fin n → Bool)} (f : Z → Bool) : ℕ :=
  (Finset.univ.filter (fun i => IsEssential f i)).card

/-- The error set `δ_∧(g, h) = δ⁺_∧(g, h) ∪ δ⁻_∧(g, h)`: the points where the approximate
conjunction `g ∧̄ h` differs from the exact conjunction `g ∧ h`. -/
def andErr {Z : Set (Fin n → Bool)} (A : ApproxModel Z) (g h : Z → Bool) : Set Z :=
  {z | A.andOp g h z ≠ (g z && h z)}

/-- The error set `δ_∨(g, h) = δ⁺_∨(g, h) ∪ δ⁻_∨(g, h)`. -/
def orErr {Z : Set (Fin n → Bool)} (A : ApproxModel Z) (g h : Z → Bool) : Set Z :=
  {z | A.orOp g h z ≠ (g z || h z)}

/-- The family `Δ` of error sets of the model (Definition 5.3): all `δ_∘(g, h)` with
`g, h ∈ M` and `∘ ∈ {∨₂, ∧₂}`. -/
def errorSets {Z : Set (Fin n → Bool)} (A : ApproxModel Z) : Set (Set Z) :=
  {E | ∃ g ∈ A.M, ∃ h ∈ A.M, E = andErr A g h ∨ E = orErr A g h}

/-- Razborov's distance `ρ(f, M)` (Definition 5.4): the least number `t` of error sets of the
model whose union covers `f ⊕ g` for some `g ∈ M`; `∞` (`⊤`) if there is no such `t`. -/
def distGen {Z : Set (Fin n → Bool)} (A : ApproxModel Z) (f : Z → Bool) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ g ∈ A.M, ∃ T : Finset (Set Z), (↑T : Set (Set Z)) ⊆ errorSets A ∧
    (T.card : ℕ∞) = t ∧ ∀ z : Z, f z ≠ g z → ∃ E ∈ T, z ∈ E}

/-- The probabilistic distance `ρ(f, M, x)` for a random input `x` with law `ν` on `Z`
(printed p. 27): with `d = max_{δ ∈ Δ} P[x ∈ δ]`, it is `min_{g ∈ M} P[f(x) ≠ g(x)] / d` if
`d ≠ 0`, and `0` if `d = 0`. -/
def distProb {Z : Set (Fin n → Bool)} (A : ApproxModel Z) (f : Z → Bool) (ν : PMF Z) : ℝ≥0∞ :=
  let d : ℝ≥0∞ := ⨆ E ∈ errorSets A, ν.toOuterMeasure E
  if d = 0 then 0 else (⨅ g ∈ A.M, ν.toOuterMeasure {z | f z ≠ g z}) / d

/-- A multi-output circuit with `k` outputs over the gate format of `Circuit`: a straight-line
program of binary `∧`/`∨` gates (shared by all outputs) and one output operand per output. -/
structure MultiCircuit (ι : Type) (k : ℕ) where
  gates : List (Bool × Operand ι × Operand ι)
  outputs : Fin k → Operand ι

/-- The single-output circuit of the `j`-th output (same gate list). -/
def MultiCircuit.toCircuit {ι : Type} {k : ℕ} (C : MultiCircuit ι k) (j : Fin k) : Circuit ι :=
  ⟨C.gates, C.outputs j⟩

/-- Every gate refers only to earlier gates, and every output to an existing gate. -/
def MultiCircuit.WellFormed {ι : Type} {k : ℕ} (C : MultiCircuit ι k) : Prop :=
  (∀ m (hm : m < C.gates.length),
      (C.gates[m]).2.1.RefsBelow m ∧ (C.gates[m]).2.2.RefsBelow m) ∧
    ∀ j, (C.outputs j).RefsBelow C.gates.length

/-- No negative literal occurs in the gates or the outputs. -/
def MultiCircuit.IsMonotone {ι : Type} {k : ℕ} (C : MultiCircuit ι k) : Prop :=
  (∀ g ∈ C.gates, (∀ i, g.2.1 ≠ .lit i false) ∧ (∀ i, g.2.2 ≠ .lit i false)) ∧
    ∀ j i, C.outputs j ≠ .lit i false

/-- The size of a multi-output circuit: its number of distinct `∧`/`∨` gates (each shared gate is
counted once). -/
def MultiCircuit.size {ι : Type} {k : ℕ} (C : MultiCircuit ι k) : ℕ := C.gates.length

/-- `T^{k-1}_ℓ(Xᵢ)`: whether at least `ℓ` of the inputs other than `xᵢ` are one. -/
def thresholdOthers (ℓ : ℕ) {k : ℕ} (i : Fin k) (x : Fin k → Bool) : Bool :=
  decide (ℓ ≤ (Finset.univ.filter (fun j => j ≠ i ∧ x j = true)).card)

/-- `t̃_{ℓ,k}`: the least size of a well-formed monotone `k`-input `k`-output circuit `T̃^k_ℓ`
computing `(T^{k-1}_ℓ(X₁), …, T^{k-1}_ℓ(X_k))` on all of `{0,1}^k`, gates shared between the
outputs counted once. (Such a circuit always exists, so the infimum is attained.) -/
def sharedThresholdSize (ℓ k : ℕ) : ℕ :=
  sInf {s : ℕ | ∃ C : MultiCircuit (Fin k) k, C.WellFormed ∧ C.IsMonotone ∧
    (∀ (j : Fin k) (x : Fin k → Bool), (C.toCircuit j).eval x = thresholdOthers ℓ j x) ∧
    C.size = s}

/-- `t_{ℓ,k}`: the least size of a well-formed monotone circuit `Th^k_ℓ` computing the threshold
function `T^k_ℓ` (one iff at least `ℓ` ones) on all of `{0,1}^k`. -/
def thresholdSize (ℓ k : ℕ) : ℕ :=
  monotoneSize (fun x : (Set.univ : Set (Fin k → Bool)) => decide (ℓ ≤ weight x.1))

/-- The factor `Γ = 12(3(n₀ + 1) + t̃_{ℓ,n₀} + t_{ℓ,n₀} + t_{ℓ+1,n₀} + 2)` (printed p. 28). -/
def Gamma (ℓ n₀ : ℕ) : ℕ :=
  12 * (3 * (n₀ + 1) + sharedThresholdSize ℓ n₀ + thresholdSize ℓ n₀ + thresholdSize (ℓ + 1) n₀ + 2)

end LimitsLifting.Approximation.Supplement

end


