-- Prove2me | Definitions.Def_IwataFF_SFM_Basic
-- name    : IwataFF_SFM_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:42.831039+00:00
-- url     : https://prove2.me/theorems/8df495f1-87f2-4c46-ad8a-634e780b5275
-- title:
--   Submodularity, base polyhedron $B(f)$, exchange capacity, linear orderings and greedy extreme bases ((1.1), (2.1), (2.3), pp. 2–5)
-- statement:
--   Let $V$ be a finite set of elements of an ambient type $\alpha$ with decidable equality, and let $f$ be a real function on the finite subsets of $\alpha$, read on the subsets of $V$.
--
--   - $f$ is **submodular on $V$** if $f(X) + f(Y) \ge f(X \cup Y) + f(X \cap Y)$ for all $X, Y \subseteq V$.
--   - For $x : \alpha \to \mathbb{R}$ and a finite set $X$, $x(X) = \sum_{v \in X} x(v)$.
--   - The **base polyhedron** is
--   $$B(f) = \{x \in \mathbb{R}^V \mid x(V) = f(V),\ x(X) \le f(X) \text{ for all } X \subseteq V\},$$
--   where a vector of $\mathbb{R}^V$ is a function $\alpha \to \mathbb{R}$ that vanishes outside $V$.
--   - $\chi_u$ is the unit vector of $u$, and the **exchange capacity** is $\mathrm{ec}(x,u,v) = \sup\{t \in \mathbb{R} \mid x + t(\chi_u - \chi_v) \in B(f)\}$ (2.1). For a base $x$ and distinct $u, v \in V$ the supremum is attained, so it is the paper's maximum.
--   - $x^-(v) = \min\{0, x(v)\}$.
--   - A **linear ordering** $L = (v_1, \dots, v_n)$ of $V$ is a list without repetitions whose elements are exactly those of $V$. $L(v_k) = \{v_1, \dots, v_k\}$. The **greedy** vector of $L$ is $y(v_i) = f(L(v_i)) - f(L(v_{i-1}))$ with $L(v_0) = \emptyset$ (2.3), and $0$ off the list.
--   - $u$ **immediately succeeds** $v$ in $L$ if $v$ is in $L$ and the entry after $v$ is $u$. The list obtained by **interchanging** $u$ and $v$ swaps these two values.
--   - $X$ is a **minimizer** of $f$ over $V$ if $X \subseteq V$ and $f(X) \le f(Y)$ for all $Y \subseteq V$.
--
--   **Formalization Note** The ground set is a `Finset` of an ambient type so that §4's algorithm can apply the same objects to a ground set that shrinks and whose elements are contracted blocks. Values of a vector off $V$ are fixed to $0$ in $B(f)$, so $B(f)$ is the paper's subset of $\mathbb{R}^V$. `ec` is defined by (2.1) through `sSup`; Lean's `sSup` returns $0$ on an empty or unbounded set, which never happens for a base.
-- source:
--   Iwata, Fleischer & Fujishige, A Combinatorial, Strongly Polynomial-Time Algorithm for Minimizing Submodular Functions, arXiv:math/0004089v1, pp. 2, 4–5, (1.1), (2.1), (2.3)

import Mathlib

namespace IwataFF.SFM

/-! Iwata, Fleischer & Fujishige, arXiv:math/0004089v1, §1–§2, pp. 2–5.

The ground set is a finite set `V : Finset α` inside an ambient type `α` with decidable
equality (§2, p. 4: "Let V be a finite nonempty set of cardinality |V| = n"); the ambient type
lets the strongly polynomial algorithm of §4 run the same objects on a ground set that shrinks
and whose elements are contracted blocks. A set function is `f : Finset α → ℝ`, read on the
subsets of `V` only. A vector `x ∈ ℝ^V` is `x : α → ℝ`, read on `V`. A linear ordering
`L = (v₁, …, v_n)` of `V` is a duplicate-free list with exactly the elements of `V`. -/

/-- p. 2: `f` is submodular on the subsets of `V`:
`f(X) + f(Y) ≥ f(X ∪ Y) + f(X ∩ Y)` for all `X, Y ⊆ V`. -/
def SubmodularOn {α : Type} [DecidableEq α] (V : Finset α) (f : Finset α → ℝ) : Prop :=
  ∀ X ⊆ V, ∀ Y ⊆ V, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y

/-- p. 2, (1.1): `x(X) = ∑_{v ∈ X} x(v)`. -/
noncomputable def xsum {α : Type} (x : α → ℝ) (X : Finset α) : ℝ :=
  ∑ v ∈ X, x v

/-- (1.1), p. 2: the base polyhedron
`B(f) = {x ∈ ℝ^V | x(V) = f(V), x(X) ≤ f(X) for all X ⊆ V}`.
A vector of `ℝ^V` is encoded as a function `α → ℝ` vanishing outside `V`. -/
def basePoly {α : Type} (V : Finset α) (f : Finset α → ℝ) : Set (α → ℝ) :=
  {x | (∀ a, a ∉ V → x a = 0) ∧ xsum x V = f V ∧ ∀ X ⊆ V, xsum x X ≤ f X}

/-- p. 4: the unit vector `χ_u` (`χ_u(v) = 1` if `v = u`, `0` otherwise). -/
def chi {α : Type} [DecidableEq α] (u : α) : α → ℝ :=
  fun a => if a = u then 1 else 0

/-- (2.1), p. 4: the exchange capacity
`ec(x, u, v) = max{α ∈ ℝ | x + α(χ_u − χ_v) ∈ B(f)}`, as the supremum of that set.
For a base `x ∈ B(f)` and distinct `u, v ∈ V` the set is nonempty (it contains `0`), bounded
above and closed, so the supremum is the paper's maximum. (Lean's `sSup` returns `0` on an
empty or unbounded set; that case never occurs for a base.) -/
noncomputable def ec {α : Type} [DecidableEq α] (V : Finset α) (f : Finset α → ℝ)
    (x : α → ℝ) (u v : α) : ℝ :=
  sSup {t : ℝ | x + t • (chi u - chi v) ∈ basePoly V f}

/-- p. 5: `x⁻(v) = min{0, x(v)}`. -/
noncomputable def xneg {α : Type} (x : α → ℝ) : α → ℝ :=
  fun a => min 0 (x a)

/-- p. 4: `L` is a linear ordering `(v₁, …, v_n)` of `V`: a list without repetitions whose
elements are exactly the elements of `V`. -/
def IsOrdering {α : Type} (V : Finset α) (L : List α) : Prop :=
  L.Nodup ∧ ∀ a, a ∈ L ↔ a ∈ V

/-- p. 4: `L(v_k) = {v₁, …, v_k}`, the elements of `L` up to and including `v_k`. -/
def prefixSet {α : Type} [DecidableEq α] (L : List α) (v : α) : Finset α :=
  (L.take (L.idxOf v + 1)).toFinset

/-- (2.3), p. 4: the greedy algorithm of Edmonds,
`y(v_i) = f(L(v_i)) − f(L(v_{i−1}))` with `L(v₀) = ∅`; the extreme base generated by `L`.
(Vanishes outside the list.) -/
noncomputable def greedy {α : Type} [DecidableEq α] (f : Finset α → ℝ) (L : List α) :
    α → ℝ :=
  fun v => if v ∈ L then f (L.take (L.idxOf v + 1)).toFinset - f (L.take (L.idxOf v)).toFinset
    else 0

/-- p. 4–5: the linear ordering obtained from `L` by interchanging `u` and `v`. -/
def swapAdj {α : Type} [DecidableEq α] (L : List α) (u v : α) : List α :=
  L.map (fun a => if a = u then v else if a = v then u else a)

/-- p. 5: `u` immediately succeeds `v` in `L` (`v` and `u` are consecutive, `v` first). -/
def ImmSucc {α : Type} [DecidableEq α] (L : List α) (u v : α) : Prop :=
  v ∈ L ∧ L[L.idxOf v + 1]? = some u

/-- `X ⊆ V` minimizes `f` over the subsets of `V`. -/
def IsMinimizer {α : Type} (V : Finset α) (f : Finset α → ℝ) (X : Finset α) : Prop :=
  X ⊆ V ∧ ∀ Y ⊆ V, f X ≤ f Y

end IwataFF.SFM


