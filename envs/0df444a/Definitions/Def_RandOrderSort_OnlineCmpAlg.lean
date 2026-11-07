-- Prove2me | Definitions.Def_RandOrderSort_OnlineCmpAlg
-- name    : RandOrderSort_OnlineCmpAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:03:10.833106+00:00
-- url     : https://prove2.me/theorems/446f7ff9-9fc1-4174-bf35-7a37e6546131
-- title:
--   The random order online sorting model: stream, keys, comparison-only algorithms, cost, OPT and $\rho$
-- statement:
--   A fixed multiset $X=\{x_1,\dots,x_n\}$ of $n$ reals, with indices distinguishing equal occurrences, arrives in the order of a uniform permutation $\pi$. Each arrival is placed at once and irrevocably into one of exactly $n$ cells. Ties are broken by an independent uniform permutation $\sigma$: the arrival at time $t$ carries the lexicographic key $(x_{\pi(t)},\sigma(t))$, and the output stores only its original value.
--
--   This module defines:
--
--   1. the strict key order on arrivals (`keyLt`, `ltOf`) and the comparison table of the arrivals $0,\dots,t$ (`cmpTable`);
--   2. **a deterministic online algorithm using only comparisons** (`OnlineCmpAlg`): a rule that receives $n$, the time $t$ and the table of strict key comparisons among the arrivals $0,\dots,t$, and returns the cell of arrival $t$;
--   3. the cell of an arrival (`cellOf`) and **legality** (`Legal`): on every execution the $n$ arrivals go to $n$ distinct cells among $0,\dots,n-1$;
--   4. the completed array $A$ (`outVal`), and display (1),
--   $$\mathrm{cost}(A)=\sum_{i=1}^{n-1}|A[i+1]-A[i]|,\qquad \mathrm{OPT}(X)=\max X-\min X,\qquad \rho(A)=\begin{cases}\mathrm{cost}(A)/\mathrm{OPT}(X),&\mathrm{OPT}(X)>0,\\ 1,&\mathrm{OPT}(X)=0;\end{cases}$$
--   5. the uniform probability and expectation on a finite type (`uniformProb`, `uniformExp`);
--   6. the crossing counts $C(q)$ (`valueCrossings`) and $C_a$ (`rankCrossings`), and the ratio and rank crossings of an arbitrary placement (`placeRatio`, `placeCa`, `ordVal`).
--
--   All later statements of the mission are written in these terms.
--
--   **Formalization Note** The multiset is `x : Fin n → ℝ`, the paper's own indexing of occurrences. Arrivals and cells are 0-based, so the paper's $A[i]$ is cell $i-1$. A rule sees no value, no equality of values and no future arrival; it needs no internal state, because its earlier decisions are recomputable from the earlier sub-tables. The uniform law on `Perm (Fin n) × Perm (Fin n)` makes $\pi$ and $\sigma$ independent.
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), §1.1, pp.3–4, display (1); §4, p.19 (C(q)); §4.6, p.37 (C_a)

import Mathlib

namespace RandOrderSort

/-! # Random order online sorting: the model (1) and comparison-only online algorithms

M. Kang, C. Fan, *Optimal High Probability Bounds for Random Order Online Sorting*,
arXiv:2610.15438 (version of 2026-11-01), §1.1, pp.3–4, display (1).

A fixed multiset `X = {x_1, …, x_n}` of `n` reals (indices distinguishing equal occurrences)
arrives in the order of a uniform permutation `π`; each arrival is placed at once and for ever into
one of exactly `n` cells. Ties are broken by an independent uniform priority permutation `σ`: the
arrival at time `t` carries the lexicographic key `(x_{π(t)}, σ(t))`.

**Formalization Note.**
* The multiset is `x : Fin n → ℝ` (the paper's own indexing of occurrences). Arrival times and
  cells are 0-based: arrival `t : Fin n` has value `x (π t)` and key `(x (π t), σ t)`; the paper's
  cell `A[i]`, `1 ≤ i ≤ n`, is cell `i − 1`.
* An online algorithm "using only comparisons" is a placement rule `place n t tbl` that receives
  `n`, the time `t` and the table `tbl a b` of the strict key comparisons `key a < key b` among
  the arrivals `0, …, t`, and returns the cell of arrival `t`. It sees no value, no equality of
  values and no future arrival. A rule needs no internal state, since its earlier decisions are
  recomputable from the earlier sub-tables.
* `ρ` is `cost/OPT` when `OPT > 0` and `1` when `OPT = 0`, exactly as (1); `log` is `Real.log`.
* `P_{π,σ}` is the uniform probability on `Perm (Fin n) × Perm (Fin n)`, so `π` and `σ` are
  independent.
-/

/-- The strict lexicographic key order on arrivals: arrival `s` precedes arrival `t` when
`(x (π s), σ s) < (x (π t), σ t)` lexicographically (§1.1, p.3). -/
def keyLt {n : ℕ} (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)) (s t : Fin n) : Prop :=
  x (π s) < x (π t) ∨ (x (π s) = x (π t) ∧ σ s < σ t)

/-- The key order as a Boolean relation on arrival indices in `ℕ`; indices `≥ n` compare false. -/
noncomputable def ltOf {n : ℕ} (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)) (a b : ℕ) : Bool :=
  by classical exact
    if h : a < n ∧ b < n then decide (keyLt x π σ ⟨a, h.1⟩ ⟨b, h.2⟩) else false

/-- The comparison table available at time `t`: the strict key comparisons among arrivals
`0, …, t`. -/
noncomputable def cmpTable {n : ℕ} (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)) (t : ℕ) :
    Fin (t + 1) → Fin (t + 1) → Bool :=
  fun a b => ltOf x π σ a.1 b.1

/-- **A deterministic online algorithm using only comparisons** (Theorem 1.1, p.4): `place n t tbl` is the output cell of arrival `t`, computed from `n`, `t` and the
strict key comparisons `tbl` among the arrivals `0, …, t`. -/
structure OnlineCmpAlg where
  place : (n t : ℕ) → (Fin (t + 1) → Fin (t + 1) → Bool) → ℕ

/-- The cell into which `A` places arrival `t` on the stream `x ∘ π` with priorities `σ`. -/
noncomputable def cellOf (A : OnlineCmpAlg) {n : ℕ} (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n))
    (t : Fin n) : ℕ :=
  A.place n t.1 (cmpTable x π σ t.1)

/-- **Legality** at size `n`: on every execution (every `x`, `π`, `σ`) the `n` arrivals go into
`n` distinct cells among the `n` cells `0, …, n − 1`, i.e. the placement is a bijection onto the
array. -/
def Legal (A : OnlineCmpAlg) (n : ℕ) : Prop :=
  ∀ (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)),
    Function.Injective (cellOf A x π σ) ∧ ∀ t, cellOf A x π σ t < n

/-- The arrival stored in cell `c`, if any. -/
noncomputable def occupant (A : OnlineCmpAlg) {n : ℕ} (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n))
    (c : ℕ) : Option (Fin n) :=
  by classical exact if h : ∃ t, cellOf A x π σ t = c then some (Classical.choose h) else none

/-- The completed array `A[c]`: the original value of the arrival stored in cell `c`
(`0` for a cell left empty, which a legal run never does). -/
noncomputable def outVal (A : OnlineCmpAlg) {n : ℕ} (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n))
    (c : ℕ) : ℝ :=
  match occupant A x π σ c with
  | some t => x (π t)
  | none => 0

/-- `cost(A) = ∑_{i=1}^{n−1} |A[i+1] − A[i]|` (display (1)), in 0-based cells. -/
noncomputable def cost (A : OnlineCmpAlg) {n : ℕ} (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i ∈ Finset.range (n - 1), |outVal A x π σ (i + 1) - outVal A x π σ i|

/-- `OPT(X) = max X − min X` (display (1)). -/
noncomputable def OPT {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (⨆ i, x i) - (⨅ i, x i)

/-- The realized competitive ratio `ρ(A)` of (1): `cost/OPT` if `OPT > 0`, and `1` if `OPT = 0`. -/
noncomputable def ratio (A : OnlineCmpAlg) {n : ℕ} (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)) : ℝ :=
  if 0 < OPT x then cost A x π σ / OPT x else 1

/-- The uniform probability of an event on a finite type. -/
noncomputable def uniformProb {α : Type*} [Fintype α] (E : α → Prop) : ℝ :=
  by classical exact ((Finset.univ.filter E).card : ℝ) / (Fintype.card α : ℝ)

/-- The uniform expectation of a real function on a finite type. -/
noncomputable def uniformExp {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / (Fintype.card α : ℝ)

/-- The number of adjacent output pairs (cells `i, i+1`, `i < n − 1`) whose occupants lie on
opposite sides of a cut, the cut being given by the predicate `up` ("above the cut") on arrivals.
An empty cell counts as below the cut. -/
noncomputable def crossings (A : OnlineCmpAlg) {n : ℕ} (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n))
    (up : Fin n → Prop) : ℕ :=
  by classical exact
    ((Finset.range (n - 1)).filter (fun i =>
      (∃ t, occupant A x π σ i = some t ∧ up t) ≠
        (∃ t, occupant A x π σ (i + 1) = some t ∧ up t))).card

/-- `C(q)` (§4, p.19): the number of adjacent output pairs on opposite sides of the numerical
threshold `q`, the side of an entry being `1[x > q]` (`β_q`, p.20). -/
noncomputable def valueCrossings (A : OnlineCmpAlg) {n : ℕ} (x : Fin n → ℝ)
    (π σ : Equiv.Perm (Fin n)) (q : ℝ) : ℕ :=
  crossings A x π σ (fun t => q < x (π t))

/-- The 1-based rank of arrival `t` in the strict key order. -/
noncomputable def keyRank {n : ℕ} (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)) (t : Fin n) : ℕ :=
  by classical exact (Finset.univ.filter (fun s => keyLt x π σ s t)).card + 1

/-- `C_a` (§4.6, p.37): the number of adjacent output pairs with one rank at most `a` and the other
greater than `a` (ranks 1-based in the strict key order). -/
noncomputable def rankCrossings (A : OnlineCmpAlg) {n : ℕ} (x : Fin n → ℝ)
    (π σ : Equiv.Perm (Fin n)) (a : ℕ) : ℕ :=
  crossings A x π σ (fun t => a < keyRank x π σ t)

/-- The value of a vector at an index in `ℕ` (`0` outside `0, …, n − 1`). -/
def vecVal {n : ℕ} (x : Fin n → ℝ) (a : ℕ) : ℝ := if h : a < n then x ⟨a, h⟩ else 0

/-- For a placement `e` (cell `c ↦` item `e c`) of items with values `v`, the value in cell `c`. -/
def placeVal {n : ℕ} (v : Fin n → ℝ) (e : Equiv.Perm (Fin n)) (c : ℕ) : ℝ :=
  if h : c < n then v (e ⟨c, h⟩) else 0

/-- The ratio (1) of an arbitrary placement `e` of the items with values `v`. -/
noncomputable def placeRatio {n : ℕ} (v : Fin n → ℝ) (e : Equiv.Perm (Fin n)) : ℝ :=
  if 0 < OPT v then
    (∑ i ∈ Finset.range (n - 1), |placeVal v e (i + 1) - placeVal v e i|) / OPT v
  else 1

/-- `C_a` of an arbitrary placement `e`, the items having 0-based ranks `r` in the strict key
order: adjacent cells with one rank at most `a` and the other greater than `a` (1-based ranks;
a 0-based rank `r i < a` is a 1-based rank `≤ a`). -/
def placeCa {n : ℕ} (r : Fin n ≃ Fin n) (e : Equiv.Perm (Fin n)) (a : ℕ) : ℕ :=
  ((Finset.range (n - 1)).filter (fun i =>
    if h : i + 1 < n then
      decide ((r (e ⟨i, by omega⟩)).1 < a) ≠ decide ((r (e ⟨i + 1, h⟩)).1 < a)
    else false)).card

/-- The `(a+1)`-th smallest value `x_{(a+1)}` (0-based `a`) when the item of 0-based rank `a` is
`r.symm a`. -/
def ordVal {n : ℕ} (v : Fin n → ℝ) (r : Fin n ≃ Fin n) (a : ℕ) : ℝ :=
  if h : a < n then v (r.symm ⟨a, h⟩) else 0

end RandOrderSort


