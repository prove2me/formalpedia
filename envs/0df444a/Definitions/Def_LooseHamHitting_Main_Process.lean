-- Prove2me | Definitions.Def_LooseHamHitting_Main_Process
-- name    : LooseHamHitting_Main_Process
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:17:51.965674+00:00
-- url     : https://prove2.me/theorems/6c3be0fe-9e46-4d59-a66a-aa9393da5d21
-- title:
--   The random 3-uniform hypergraph process as a uniform ordering of the triples; τ₁, τ_LHC; the exposure (B, T, ℓ) at τ₁; Ω(V, m, ℓ)
-- statement:
--   The **random 3-uniform hypergraph process** on $[n]$ (p. 1) starts from $H_0=\emptyset$ and, for $0\le t<\binom n3$, adds to $H_t$ a triple chosen uniformly from $\binom{[n]}3\setminus H_t$. Equivalently, take a uniformly random ordering $\sigma$ of all $N=\binom n3$ triples and let $H_t$ be the set of the first $t$ of them; probabilities are counting probabilities over the $N!$ orderings. The **hitting times** are
--   $$\tau_1=\min\{t:\delta_1(H_t)\ge1\},\qquad \tau_{LHC}=\min\{t: H_t\text{ contains a loose Hamilton cycle}\},$$
--   each undefined ($\top$) if no such $t$ exists; the event $\tau_{LHC}=\tau_1$ requires both to be defined and equal.
--
--   **Exposure at $\tau_1$** (pp. 14–15): $d_0=\lfloor0.01\log n\rfloor$, $B=\{v:d_{H_{\tau_1}}(v)\le d_0\}$, $T=\{e\in H_{\tau_1}:e\cap B\ne\emptyset\}$, and for an exposed edge set $T$, $\ell_w=\max\{0,d_0+1-d_T(w)\}$. For a finite vertex set $V$,
--   $$\Omega(V,m,\ell)=\Big\{F\subseteq\binom V3:\ |F|=m,\ d_F(v)\ge\ell_v\ \forall v\in V\Big\}.$$
--
--   **Formalization Note.** An ordering is an equivalence `Fin N ≃ {e : Finset (Fin n) // e.card = 3}` with `N` the number of triples ($=\binom n3$); `H_t` is the image of the positions `< t`. $\tau_1,\tau_{LHC}$ take values in `WithTop ℕ`. `hitGraph σ` is $H_{\tau_1}$ (for $n\le2$, where $\tau_1$ is undefined, it is $H_0$; this case plays no role).
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 1 (process, hitting times); pp. 14–15 (exposure); p. 13 (Definition 4.1)

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph

set_option autoImplicit false

/-!
# The random 3-uniform hypergraph process, `τ₁`, `τ_LHC` and the exposure at `τ₁`

León, Liu, arXiv:2610.29894v1, p. 1 (process, hitting times), pp. 14–15 (exposure).

Encoding of the process: a uniformly random ordering `σ` of all `N = \binom{n}{3}` triples of
`[n] = Fin n`; `H_t` is the set of the first `t` triples. This has the law of the process
(`H_0 = ∅`, each step adds a uniformly chosen missing triple), and `H_t` has exactly `t` edges
for `t ≤ N`. Probabilities are counting probabilities over the finite set of orderings.
-/

namespace LooseHamHitting.Main

noncomputable section

open Classical

/-- The triples of `[n]`. -/
abbrev Trip (n : ℕ) : Type := {e : Finset (Fin n) // e.card = 3}

/-- `N = \binom{n}{3}`, the number of triples (as a cardinality). -/
abbrev numTriples (n : ℕ) : ℕ := Fintype.card (Trip n)

/-- An ordering of all triples of `[n]`: position `i` holds the `i`-th triple. -/
abbrev Ordering (n : ℕ) : Type := Fin (numTriples n) ≃ Trip n

/-- `H_t`: the 3-graph formed by the first `t` triples of the ordering. -/
def prefixGraph {n : ℕ} (σ : Ordering n) (t : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ.filter (fun i : Fin (numTriples n) => i.val < t)).image (fun i => (σ i).val)

/-- Probability of an event under the uniform law on orderings. -/
def probOrd (n : ℕ) (E : Ordering n → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / (Fintype.card (Ordering n) : ℝ)

/-- Conditional probability `P[E | X]` under the uniform law on orderings. -/
def condProbOrd (n : ℕ) (E X : Ordering n → Prop) : ℝ :=
  ((Finset.univ.filter (fun σ => E σ ∧ X σ)).card : ℝ) / ((Finset.univ.filter X).card : ℝ)

/-- `τ₁ := min{t : δ₁(H_t) ≥ 1}`, `⊤` if no such `t`. -/
def tau1 {n : ℕ} (σ : Ordering n) : WithTop ℕ :=
  if h : ∃ t, 1 ≤ minDegree Finset.univ (prefixGraph σ t) then ((Nat.find h : ℕ) : WithTop ℕ)
  else ⊤

/-- `τ_LHC := min{t : H_t contains a loose Hamilton cycle}`, `⊤` (undefined) if none. -/
def tauLHC {n : ℕ} (σ : Ordering n) : WithTop ℕ :=
  if h : ∃ t, ContainsLooseHamCycle Finset.univ (prefixGraph σ t) then
    ((Nat.find h : ℕ) : WithTop ℕ)
  else ⊤

/-- The event `τ_LHC = τ₁` (both defined and equal). -/
def HittingTimesEqual {n : ℕ} (σ : Ordering n) : Prop :=
  ∃ t : ℕ, tau1 σ = (t : WithTop ℕ) ∧ tauLHC σ = (t : WithTop ℕ)

/-- `τ₁` as a natural number (`0` in the degenerate case `τ₁ = ⊤`, which happens only for
`n ≤ 2`). -/
def tau1Nat {n : ℕ} (σ : Ordering n) : ℕ :=
  if h : ∃ t, 1 ≤ minDegree Finset.univ (prefixGraph σ t) then Nat.find h else 0

/-- `H_{τ₁}`. -/
def hitGraph {n : ℕ} (σ : Ordering n) : Finset (Finset (Fin n)) :=
  prefixGraph σ (tau1Nat σ)

/-- `d₀ := ⌊0.01 log n⌋`. -/
def d0 (n : ℕ) : ℕ := ⌊(0.01 : ℝ) * Real.log n⌋₊

/-- `B := {v : d_{H_{τ₁}}(v) ≤ d₀}`. -/
def lowSet {n : ℕ} (σ : Ordering n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => degree (hitGraph σ) v ≤ d0 n)

/-- `T := {e ∈ H_{τ₁} : e ∩ B ≠ ∅}`. -/
def exposedEdges {n : ℕ} (σ : Ordering n) : Finset (Finset (Fin n)) :=
  (hitGraph σ).filter (fun e => ¬ Disjoint e (lowSet σ))

/-- `ℓ_w := max{0, d₀ + 1 − d_T(w)}` for the exposed edge set `T`. -/
def residualBound (n : ℕ) (T : Finset (Finset (Fin n))) (w : Fin n) : ℕ :=
  (d0 n + 1) - degree T w

/-- The set `Ω(V, m, ℓ)` of 3-graphs on `V` with `m` edges and `d_F(v) ≥ ℓ_v` for every `v ∈ V`
(Definition 4.1, on a general finite vertex set). -/
def OmegaV {α : Type*} (V : Finset α) (m : ℕ) (ℓ : α → ℕ) : Finset (Finset (Finset α)) :=
  ((V.powersetCard 3).powersetCard m).filter (fun F => ∀ v ∈ V, ℓ v ≤ degree F v)

end

end LooseHamHitting.Main


