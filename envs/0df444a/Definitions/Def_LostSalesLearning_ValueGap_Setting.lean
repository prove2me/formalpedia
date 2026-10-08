-- Prove2me | Definitions.Def_LostSalesLearning_ValueGap_Setting
-- name    : LostSalesLearning_ValueGap_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:55:27.768374+00:00
-- url     : https://prove2.me/theorems/1636ad0c-3c36-483b-b935-8e4a62fcb46d
-- title:
--   Definitions 2.1, 2.4, B.1, pp. 7–8, 19 — the base-stock MRP M(x, s): S^x, transition (6), pseudo-cost (7), value V^x_T, total sales and on-hand, the order ⪰
-- statement:
--   This file sets up the Markov reward process $\mathcal M(x,\mathbf s_1)$ of Agrawal and Jia: a periodic-review, single-product inventory system with lost sales, a deterministic lead time $L\ge 0$, and a base-stock policy with level $x$.
--
--   **States.** A state is a vector $\mathbf s=(s(0),s(1),\dots,s(L))\in\mathbb R^{L+1}$. Its entry $s(0)$ is the on-hand inventory after the current period's arrival, and $s(1),\dots,s(L)$ are the outstanding orders, $s(L)$ the most recent. The set
--   $$\mathcal S^x=\Big\{\mathbf s\in\mathbb R^{L+1} : s(i)\ge 0 \text{ for all } i,\ \sum_{i=0}^{L}s(i)=x\Big\}$$
--   is the set of states of a base-stock policy with level $x$.
--
--   **Transition (6).** In each period a demand $d_t\ge 0$ is drawn and the sales are $y_t=\min\{s_t(0),d_t\}$. The next state is
--   $$\mathbf s_{t+1}=\big(s_t(0)-y_t+s_t(1),\ s_t(2),\ \dots,\ s_t(L),\ y_t\big)$$
--   when $L\ge 1$: the oldest outstanding order arrives, and the base-stock policy orders exactly the units just sold. When $L=0$ the state $(s(0))$ is unchanged, because the replacement order arrives at once. On a demand path $d=(d_1,d_2,\dots)$ this determines the trajectory $\mathbf s_1=\mathbf s,\mathbf s_2,\dots$, the on-hand inventory $I_t=s_t(0)$ and the sales $y_t=\min\{I_t,d_t\}$.
--
--   **Costs.** With a holding cost $h$ and a lost-sales penalty $p$ per unit, the pseudo-cost (7) of period $t$ is
--   $$C^x_t=h\,(s_t(0)-y_t)-p\,y_t .$$
--   The total on-hand inventory and the total sales over $T$ periods are
--   $$m^x_T(\mathbf s)=\sum_{t=1}^{T}I_t,\qquad n^x_T(\mathbf s)=\sum_{t=1}^{T}y_t,$$
--   both computed along a given demand path.
--
--   **Value (Definition 2.4).** When the demands are independent and identically distributed with law $F$ on $[0,\infty)$, the value of horizon $T$ from the start state $\mathbf s$ is
--   $$V^x_T(\mathbf s)=\mathbb E\Big[\sum_{t=1}^{T}C^x_t\ \Big|\ \mathbf s_1=\mathbf s\Big].$$
--
--   **The order ⪰ (Definition B.1).** For states $\mathbf s,\mathbf s'$, write $\mathbf s'\succeq\mathbf s$ if $\mathbf s'=\mathbf s+\delta$ with $\delta_0+\dots+\delta_L=0$ and there is some $0\le k\le L-1$ such that $\delta_i\ge 0$ for $i\le k$ and $\delta_i\le 0$ for $i>k$: the inventory of $\mathbf s'$ is shifted toward the near end of the pipeline. Finally, $\hat{\mathbf s}=(x,0,\dots,0)$ is the state with all inventory on hand.
--
--   The first strict crossing times of the two on-hand inventories define the alternating times $(\sigma_i,\tau_{i+1})$ of Definition B.4, when those crossings exist. These objects are the language of Lemma 2.5 and of the comparison lemmas of Appendix B.
--
--   **Formalization Note** States are functions `Fin (L + 1) → ℝ`, demands a path `ℕ → ℝ≥0` and time is 0-based: `traj s d 0` is the paper's $\mathbf s_1$, `traj s d t` is $\mathbf s_{t+1}$, and $\sum_{t=1}^T$ is a sum over `Finset.range T`. The law $F$ is a probability measure on `ℝ≥0` and the demand path has the product law `Measure.infinitePi (fun _ => F)`. Definition 2.4 sums $C^x(\mathbf s_t)=\mathbb E[C^x_t\mid \mathbf s_t]$; the Lean value sums $C^x_t$ directly, which is equal by the tower property and is the form used in the proof of Lemma 2.5 (p. 8). `Dominates s' s` means $\mathbf s'\succeq\mathbf s$, and its split index $k$ ranges over $k+1\le L$. The value is a Bochner integral; its integrand is measurable and, on $\mathcal S^x$, bounded by $T(h+p)x$ in absolute value.
-- source:
--   Agrawal & Jia, Learning in Structured MDPs with Convex Cost Functions, arXiv:1905.04337v1, pp. 3, 7–8 and 19–21, §1.1, Definitions 2.1, 2.4, B.1, B.4, (6), (7); m^x_T, n^x_T and ŝ in the proof of Lemma 2.5, pp. 8–9

import Mathlib

namespace LostSalesLearning.ValueGap

open MeasureTheory
open scoped NNReal

/-- `S^x` (Definition 2.1, p. 7): the `(L + 1)`-dimensional nonnegative vectors whose components
sum to `x`. A state `s = (s(0), s(1), …, s(L))` has `s(0)` the on-hand inventory after the current
period's arrival and `s(1), …, s(L)` the outstanding orders, `s(L)` the most recent. -/
def Sx (L : ℕ) (x : ℝ) : Set (Fin (L + 1) → ℝ) :=
  {s | (∀ i, 0 ≤ s i) ∧ ∑ i, s i = x}

/-- The transition (6) of the MRP `M(x, s₁)` (Definition 2.1, p. 7) under demand `dₜ`:
with sales `y = min (s 0) dₜ`, the next state is `(s(0) − y + s(1), s(2), …, s(L), y)` when
`L ≥ 1`. When `L = 0` the state `(s(0))` is unchanged (the base-stock order arrives at once). -/
noncomputable def step {L : ℕ} (s : Fin (L + 1) → ℝ) (dt : ℝ) : Fin (L + 1) → ℝ :=
  Function.update (Fin.snoc (α := fun _ => ℝ) (Fin.tail s) (min (s 0) dt)) 0
    (s 0 - min (s 0) dt + Fin.snoc (α := fun _ => ℝ) (Fin.tail s) (min (s 0) dt) 0)

/-- The state trajectory driven by the demand path `d`, with 0-based time: `traj s d 0 = s` is the
paper's `s₁`, and `traj s d t` is the paper's `s_{t+1}`. -/
noncomputable def traj {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) : ℕ → Fin (L + 1) → ℝ
  | 0 => s
  | t + 1 => step (traj s d t) (d t)

@[simp] theorem traj_zero {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) : traj s d 0 = s := rfl

@[simp] theorem traj_succ {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t : ℕ) :
    traj s d (t + 1) = step (traj s d t) (d t) := rfl

/-- On-hand inventory `I = s(0)` at (0-based) time `t`. -/
noncomputable def onHand {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t : ℕ) : ℝ :=
  traj s d t 0

/-- Sales `y = min(I, d)` at (0-based) time `t`. -/
noncomputable def sales {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t : ℕ) : ℝ :=
  min (traj s d t 0) (d t)

/-- The pseudo-cost (7), `C^x_t = h (s_t(0) − y_t) − p y_t`, at (0-based) time `t`. -/
noncomputable def pseudoCost {L : ℕ} (h p : ℝ) (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t : ℕ) : ℝ :=
  h * (onHand s d t - sales s d t) - p * sales s d t

/-- Total sales `n^x_T(s) = Σ_{t=1}^T y_t` over the first `T` periods, on the demand path `d`. -/
noncomputable def totalSales {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, sales s d t

/-- Total on-hand inventory `m^x_T(s) = Σ_{t=1}^T I_t` over the first `T` periods, on `d`. -/
noncomputable def totalOnHand {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, onHand s d t

/-- The value `V^x_T(s)` (Definition 2.4, p. 8), in the form `E[Σ_{t=1}^T C^x_t | s₁ = s]` used in
the proof of Lemma 2.5: the expectation of the summed pseudo-costs when the demands are i.i.d.
with law `F`. -/
noncomputable def value {L : ℕ} (h p : ℝ) (F : Measure ℝ≥0) [IsProbabilityMeasure F] (T : ℕ)
    (s : Fin (L + 1) → ℝ) : ℝ :=
  ∫ d, ∑ t ∈ Finset.range T, pseudoCost h p s d t ∂(Measure.infinitePi fun _ : ℕ => F)

/-- The order of Definition B.1 (p. 19): `Dominates s' s` is `s' ⪰ s`, i.e.
`s' = s + δ` with `δ₀ + ⋯ + δ_L = 0` and some `0 ≤ k ≤ L − 1` such that `δᵢ ≥ 0` for `i ≤ k` and
`δᵢ ≤ 0` for `i > k`. -/
def Dominates {L : ℕ} (s' s : Fin (L + 1) → ℝ) : Prop :=
  ∑ i, s' i = ∑ i, s i ∧
    ∃ k : ℕ, k + 1 ≤ L ∧ (∀ i : Fin (L + 1), (i : ℕ) ≤ k → s i ≤ s' i) ∧
      (∀ i : Fin (L + 1), k < (i : ℕ) → s' i ≤ s i)

/-- The first time strictly after `n` at which `P` holds, if there is one. The `Option` value
records that a crossing need not occur (Definition B.4, p. 21). -/
noncomputable def firstAfter (P : ℕ → Prop) (n : ℕ) : Option ℕ :=
  by
    classical
    exact if h : ∃ t : ℕ, n < t ∧ P t then some (Nat.find h) else none

/-- The crossing times of Definition B.4 (p. 21), with the paper's `σ₀ = 1` represented by
Lean time `0`. The pair at index `i` is `(σᵢ, τᵢ₊₁)`. A missing crossing is `none`; this also
covers paths on which the two chains never meet. -/
noncomputable def alternationTimes {L : ℕ} (s s' : Fin (L + 1) → ℝ)
    (d : ℕ → ℝ≥0) : ℕ → Option ℕ × Option ℕ
  | 0 =>
      let σ : Option ℕ := some 0
      (σ, σ.bind (firstAfter (fun t => onHand s' d t < onHand s d t)))
  | i + 1 =>
      let previous := alternationTimes s s' d i
      let σ := previous.2.bind (firstAfter (fun t => onHand s d t < onHand s' d t))
      (σ, σ.bind (firstAfter (fun t => onHand s' d t < onHand s d t)))

/-- The state `ŝ = (x, 0, …, 0)` of p. 9: all inventory on hand, nothing on order. -/
def fullState (L : ℕ) (x : ℝ) : Fin (L + 1) → ℝ :=
  fun i => if (i : ℕ) = 0 then x else 0

end LostSalesLearning.ValueGap


