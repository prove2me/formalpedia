-- Prove2me | Definitions.Def_PalmQueueing_Ordering_PartialOrders
-- name    : PalmQueueing_Ordering_PartialOrders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T01:37:42.561547+00:00
-- url     : https://prove2.me/theorems/a95e6eaa-bb46-463b-9eb9-379f6795c5af
-- title:
--   Partial orderings on ℝⁿ: coordinatewise, majorization, Schur-convexity
-- statement:
--   Let $\mathcal{R}$ be a binary relation on a set $S$ which is reflexive and transitive;
--   then $\mathcal{R}$ is a **partial semi-ordering** on $S$, and a **partial ordering** if it is also
--   antisymmetric.
--
--   For $S = \mathbb{R}^n$, the **coordinatewise** partial ordering is
--   $$ x \le y \iff x_1 \le y_1, \dots, x_n \le y_n . \tag{4.1.1} $$
--
--   On $S = \mathbb{R}^n$, the **majorization** partial semi-ordering $\prec$ is defined by
--   $x \prec y$ if
--   $$ \sum_{k=l}^{n} x_{\gamma(k)} \le \sum_{k=l}^{n} y_{\beta(k)}, \quad l = 2,\dots,n ; \qquad
--   \sum_{k=1}^{n} x_{\gamma(k)} = \sum_{k=1}^{n} y_{\beta(k)} , \tag{4.1.2} $$
--   where $\gamma$ and $\beta$ are permutations of $1,\dots,n$ that reorder $x$ and $y$ increasingly.
--   The top-$l$ partial sums of $x$ are dominated by those of $y$ while the totals agree: $y$ is the
--   more spread-out distribution of the same total. "This is almost a partial ordering as $x \prec y$
--   and $y \prec x$ imply that $x = y$ up to a permutation of the coordinates."
--
--   Remark 4.1.1 records that if $x \prec y$ then (4.1.2) holds for **all** permutations $\gamma$,
--   provided $\beta$ reorders $y$.
--
--   A function $f : \mathbb{R}^n \to \mathbb{R}$ is **Schur-convex** when it is monotone for $\prec$.
--   The book's economic reading of majorization: if a fixed amount of money is distributed among $n$
--   individuals, $x \prec y$ says $x$ is the more equal repartition.
--
--   Neither order is in Mathlib: there is no majorization and no Schur-convexity, and
--   `Order/Monotone/*` is about something else.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, §4.1.1, p. 261

import Mathlib

/-!
# Partial orderings on `ℝⁿ`: coordinatewise, majorization, Schur-convexity (§4.1.1, p.261)

The two orders §4.1 compares service disciplines with. Neither is in Mathlib: there is no
majorization order and no Schur-convexity, and `Order/Monotone/*` is about something else.
-/

namespace PalmQueueing.Ordering

open Finset

/-- `(4.1.1)`: the **coordinatewise** partial ordering on `ℝⁿ`, `x ≤ y` iff `x₁ ≤ y₁, …, xₙ ≤ yₙ`.
Mathlib's `Pi.le` is this; named here because §4.1 names it. -/
def CoordLe {n : ℕ} (x y : Fin n → ℝ) : Prop := ∀ i, x i ≤ y i

/-- `γ` **reorders** `x` increasingly: `x_{γ(1)} ≤ x_{γ(2)} ≤ … ≤ x_{γ(n)}` (p.261). -/
def Reorders {n : ℕ} (g : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : Prop :=
  Monotone fun k => x (g k)

/-- `(4.1.2)`: the **majorization** partial semi-ordering `≺` on `ℝⁿ`. `x ≺ y` if

`Σ_{k=l}^{n} x_{γ(k)} ≤ Σ_{k=l}^{n} y_{β(k)}` for `l = 2, …, n`, and
`Σ_{k=1}^{n} x_{γ(k)} = Σ_{k=1}^{n} y_{β(k)}`,

where `γ` and `β` are permutations that reorder `x` and `y` increasingly.

The top-`l` partial sums of `x` are dominated by those of `y` while the totals agree: `y` is the
more spread-out distribution of the same total. "This is almost a partial ordering as `x ≺ y` and
`y ≺ x` imply that `x = y` up to a permutation of the coordinates."

Remark 4.1.1 notes that if `x ≺ y` then (4.1.2) holds for **all** permutations `γ`, provided `β`
reorders `y`; the definition fixes one reordering of each. -/
def Majorized {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∃ g b : Equiv.Perm (Fin n), Reorders g x ∧ Reorders b y ∧
    (∀ l : Fin n, ∑ k ∈ univ.filter (fun k : Fin n => l ≤ k), x (g k)
        ≤ ∑ k ∈ univ.filter (fun k : Fin n => l ≤ k), y (b k)) ∧
    ∑ k, x (g k) = ∑ k, y (b k)

/-- `f : ℝⁿ → ℝ` is **Schur-convex** (§4.1.1): it is monotone for the majorization order,
`x ≺ y ⟹ f(x) ≤ f(y)`. -/
def SchurConvex {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, Majorized x y → f x ≤ f y

/-- `y₋ = (yₙ, …, y₁)`, the reversal used in Lemma 4.1.2 (p.267). -/
def reverseVec {n : ℕ} (y : Fin n → ℝ) : Fin n → ℝ := fun i => y (Fin.rev i)

end PalmQueueing.Ordering


