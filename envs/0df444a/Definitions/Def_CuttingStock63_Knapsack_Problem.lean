-- Prove2me | Definitions.Def_CuttingStock63_Knapsack_Problem
-- name    : CuttingStock63_Knapsack_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:41:47.882651+00:00
-- url     : https://prove2.me/theorems/908ab277-2056-48b9-aa90-82c45e2183f7
-- title:
--   Changes in the Algorithm, p. 865, (1) — the knapsack problem, M_j = max(c_j, M̄_j), prefixes (α)_s, extensions
-- statement:
--   This module fixes the knapsack problem (1) of Gilmore and Gomory and the vector notation of Step (1) of their Knapsack Method.
--
--   There are $m$ demanded lengths $l_1,\dots,l_m$ with linear programming prices $b_1,\dots,b_m$. A **column** for a stock length $L$ is a vector $(\alpha)_m=(a_1,\dots,a_m)$ of nonnegative integers with $\sum_{i=1}^m l_ia_i\le L$. The **knapsack problem** (1) is
--   $$
--   \bar M=\max\Big\{\sum_{i=1}^m b_ia_i \;:\; a_i\in\mathbb Z_{\ge0},\ \sum_{i=1}^m l_ia_i\le L\Big\}.
--   $$
--   For an integer $0\le s\le m$ and a vector $(\alpha)_m$, the module defines:
--
--   1. $\lambda\cdot(\alpha)_s=\sum_{i=1}^{s} l_ia_i$ and $\beta\cdot(\alpha)_s=\sum_{i=1}^{s} b_ia_i$, the length and the price of the first $s$ coefficients (the prefix $(\alpha)_s$); with $s=m$ these are the two sides of (1).
--   2. **Fits**: $(\alpha)_m$ satisfies the constraint of (1), $\lambda\cdot(\alpha)_m\le L$.
--   3. **Extension**: $(\alpha')_m$ is an extension of $(\alpha)_s$ if its first $s$ coefficients are those of $(\alpha)_s$.
--   4. **The value $M$**: a number $v$ is *the maximum of the cost $c$ and of $\bar M$* if $c\le v$, every column for $L$ has price at most $v$, and either $v=c$ or $v$ is the price of some column for $L$. This is the paper's $M_j=\max(c_j,\bar M_j)$ for the stock length $L_j$ with cost $c_j$.
--   5. $b_{s+1}$ and $l_{s+1}$, the price and length of the item after the prefix, with the paper's slack item $a_{m+1}$ ($b_{m+1}=0$, $l_{m+1}=1$) at $s=m$.
--   6. $(\alpha^1)_s$: the vector $(\alpha)_m$ with its $s$-th coefficient replaced by $a_s-1$.
--
--   These are the objects in which every step of the Knapsack Method and every claim of its justification is phrased.
--
--   **Formalization Note** Items are indexed by `Fin m` from 0, so the paper's 1-based level $s$ is a natural number and the prefix $(\alpha)_s$ is the set of coordinates with index `< s`. The value $M$ is a predicate `IsKnapsackMax` rather than a supremum, so that it keeps its meaning when no column fits ($v=c$); a real `sSup` would return 0 there. $a_s-1$ is truncated subtraction in $\mathbb N$, which is applied only where $a_s\neq0$. A `Decidable` instance for `Fits` (classical, on the reals) lets the algorithm module write Step (3) as an `if`.
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), p. 865, (1); pp. 866–867, definition of M_j; p. 867, Knapsack Method, Step (1) and Step (4)

import Mathlib

namespace CuttingStock63.Knapsack

/-! Gilmore & Gomory, *A linear programming approach to the cutting stock problem—Part II*,
Opns. Res. 11 (1963): the knapsack problem (1) of p. 865, its maximum M_j = max(c_j, M̄_j) of
pp. 866–867, and the vector notions of Step (1) of the Knapsack Method, p. 867.

Items are indexed by `Fin m` (0-based). The paper's 1-based level `s` (1 ≤ s ≤ m) is a natural
number; the prefix (α)_s consists of the coordinates `i` with `i.val < s`. The paper's item
a_{s+1} is the item with `val = s` when `s < m`, and the slack item a_{m+1} when `s = m`. -/

/-- λ·(α)_s = Σ_{i=1}^{s} l_i a_i: the length used by the first `s` coefficients of `a`.
With `s = m` this is the left side of the constraint of (1). -/
noncomputable def lam {m : ℕ} (l : Fin m → ℝ) (a : Fin m → ℕ) (s : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < s), l i * (a i : ℝ)

/-- β·(α)_s = Σ_{i=1}^{s} b_i a_i: the price of the first `s` coefficients of `a`.
With `s = m` this is the objective of (1). -/
noncomputable def bet {m : ℕ} (b : Fin m → ℝ) (a : Fin m → ℕ) (s : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < s), b i * (a i : ℝ)

/-- The constraint of (1): Σ_{i=1}^{m} l_i a_i ≤ L. -/
def Fits {m : ℕ} (l : Fin m → ℝ) (L : ℝ) (a : Fin m → ℕ) : Prop :=
  lam l a m ≤ L

noncomputable instance {m : ℕ} (l : Fin m → ℝ) (L : ℝ) (a : Fin m → ℕ) :
    Decidable (Fits l L a) :=
  inferInstanceAs (Decidable (lam l a m ≤ L))

/-- `a'` is an extension of (α)_s: the first `s` coefficients of `a'` are those of `a`. -/
def IsExtension {m : ℕ} (a a' : Fin m → ℕ) (s : ℕ) : Prop :=
  ∀ i : Fin m, i.val < s → a' i = a i

/-- `v` is the maximum of the cost `c` and of the maximum M̄ of the knapsack problem (1) with stock
length `L`: `c ≤ v`, every nonnegative integer vector satisfying the constraint of (1) has
objective at most `v`, and `v` is either `c` or attained by such a vector. Stated without `sSup`,
so it remains meaningful when no vector fits (then `v = c`). -/
def IsKnapsackMax {m : ℕ} (l b : Fin m → ℝ) (L c v : ℝ) : Prop :=
  c ≤ v ∧ (∀ a : Fin m → ℕ, Fits l L a → bet b a m ≤ v) ∧
    (v = c ∨ ∃ a : Fin m → ℕ, Fits l L a ∧ bet b a m = v)

/-- b_{s+1}: the price of the item following the prefix (α)_s; the slack item a_{m+1} has
b_{m+1} = 0. -/
def nextB {m : ℕ} (b : Fin m → ℝ) (s : ℕ) : ℝ :=
  if h : s < m then b ⟨s, h⟩ else 0

/-- l_{s+1}: the length of the item following the prefix (α)_s; the slack item a_{m+1} has
l_{m+1} = 1. -/
def nextL {m : ℕ} (l : Fin m → ℝ) (s : ℕ) : ℝ :=
  if h : s < m then l ⟨s, h⟩ else 1

/-- (α¹)_s of Step (4): `a` with its paper-`s`-th coefficient (0-based index `s − 1`) replaced
by a_s − 1 (truncated subtraction in ℕ; it is applied only where a_s ≠ 0). -/
def decrAt {m : ℕ} (a : Fin m → ℕ) (s : ℕ) : Fin m → ℕ :=
  fun i => if i.val + 1 = s then a i - 1 else a i

end CuttingStock63.Knapsack


