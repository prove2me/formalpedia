-- Prove2me | Definitions.Def_OncePaid_Sparse_OncePaid
-- name    : OncePaid_Sparse_OncePaid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T13:45:27.620212+00:00
-- url     : https://prove2.me/theorems/328287ae-8d98-4974-9f16-496d78afd810
-- title:
--   Once-paid subsequence instances: purchases, the retained word $w[S]$ and the objective $f_T$ with $\min\emptyset=+\infty$
-- statement:
--   A **source** of length $L$ over an alphabet $\alpha$ and a finite set $X$ of resource labels is a sequence of pairs $(a_1,r_1),\dots,(a_L,r_L)$: position $i$ carries the symbol $a_i\in\alpha$ and the label $r_i\in X$. A **purchase** is a set $S\subseteq X$; buying it activates every position whose label lies in $S$, and $w[S]$ denotes the word of the symbols of the activated positions, in source order. For a target word $T$, the purchase $S$ is **feasible** when $T$ is a (not necessarily contiguous) subsequence of $w[S]$. Given real prices $c\in\mathbb R^X$ (of any sign), the **once-paid objective** (Eq. (1.1)) is
--
--   $$
--   f_T(c)=\min_{S\in F_T}\ \sum_{x\in S}c_x,\qquad F_T=\{S\subseteq X:\ T\text{ is a subsequence of }w[S]\},
--   $$
--
--   with the convention $\min\emptyset=+\infty$. Each label is paid once, however many of its positions are used.
--
--   This is the optimization problem whose min-plus circuit complexity the mission studies; the forced-run sources built from bipartite graphs are instances of it.
--
--   **Formalization Note** The source is a `List (α × X)`, `w[S]` is a filtered list, and feasibility is `List.Sublist`. The value lives in `WithTop ℝ`, where `⊤` is $+\infty$ (the value of an instance with no feasible purchase); `X` is a `Fintype` and the minimum is a `Finset.inf` over all feasible subsets.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 1 (problem statement) and p. 2, §1.1, Eq. (1.1) (PDF pp. 3–4)

import Mathlib

namespace OncePaid.Sparse

/-!
# Once-paid subsequence instances and the objective `f_T`

Chao, Li, Gao, Wang, *Once-Paid Subsequences and the Cost of Min-Plus Approximation*,
STOC 2027 submission (manuscript sha256 9dc21472…), p. 1 (problem), p. 2 §1.1, Eq. (1.1).

* A source of length `L` is a list of pairs `(a_i, r_i)`: position `i` carries the symbol `a_i`
  (in an alphabet `α`) and the resource label `r_i ∈ X`.
* A purchase `S ⊆ X` keeps exactly the positions whose label lies in `S`; `w[S]` is the word of
  their symbols, in source order (`retainedWord`).
* `S` is feasible for the target `T` when `T` is a (not necessarily contiguous) subsequence of
  `w[S]` (`List.Sublist`).
* `f_T(c) = min_{S ∈ F_T} Σ_{x ∈ S} c_x`, with the convention `min ∅ = +∞`. Prices are arbitrary
  reals (signed prices are allowed); the value lives in `WithTop ℝ`, where `⊤ = +∞` is the value
  of an infeasible instance.
-/

/-- The word `w[S]` retained after buying the labels in `S`: the symbols of the positions whose
label belongs to `S`, in source order. -/
noncomputable def retainedWord {α X : Type} (w : List (α × X)) (S : Finset X) : List α := by
  classical
  exact (w.filter (fun p => decide (p.2 ∈ S))).map Prod.fst

/-- The purchase `S` is feasible for the target `T`: `T` is a subsequence of `w[S]`. -/
def IsFeasiblePurchase {α X : Type} (w : List (α × X)) (T : List α) (S : Finset X) : Prop :=
  T.Sublist (retainedWord w S)

/-- The once-paid objective (1.1): `f_T(c) = min { Σ_{x ∈ S} c_x : T is a subsequence of w[S] }`
over all purchases `S ⊆ X`, with `min ∅ = +∞ = ⊤`. -/
noncomputable def onceOpt {α X : Type} [Fintype X] (w : List (α × X)) (T : List α)
    (c : X → ℝ) : WithTop ℝ := by
  classical
  exact ((Finset.univ : Finset (Finset X)).filter (fun S => IsFeasiblePurchase w T S)).inf
    (fun S => ((∑ x ∈ S, c x : ℝ) : WithTop ℝ))

end OncePaid.Sparse


