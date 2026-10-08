-- Prove2me | Definitions.Def_BellmanDP_Fibonacci_SearchModel
-- name    : BellmanDP_Fibonacci_SearchModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T14:27:47.165212+00:00
-- url     : https://prove2.me/theorems/019d5d9b-f9f2-4d47-aea9-87ceef1575ac
-- title:
--   Search procedures, strict unimodality and the lengths $L_n$ searchable with $n$ evaluations
-- statement:
--   This file fixes the model of sequential search behind Bellman's § 22.
--
--   1. **The book's Fibonacci numbers.** $F_0 = F_1 = 1$ and $F_n = F_{n-1} + F_{n-2}$ for $n \ge 2$, so that $(F_n) = 1, 1, 2, 3, 5, 8, \dots$.
--   2. **Search procedures.** A search procedure is a finite decision tree. At an internal node it names a point $x$ at which the unknown function is to be evaluated, and it continues with a subtree chosen according to the observed value $f(x)$; at a leaf it stops and announces an answer. The $k$-th evaluation point may therefore depend on all values observed so far, but on nothing else about $f$: the procedure is deterministic and adaptive, observes exact function values, and its cost on $f$ is the number of evaluations made along the path that $f$ determines.
--   3. **Strict unimodality.** A function $f$ is strictly unimodal on $[0, L]$ with maximum at $m$ if $0 \le m \le L$, $f$ is strictly increasing on $[0, m]$ and strictly decreasing on $[m, L]$. No continuity is assumed, and $m = 0$ or $m = L$ is allowed; $m$ is the unique maximizer of $f$ on $[0, L]$.
--   4. **Locating the maximum.** A procedure announcing an interval $[a, b]$ locates the maximum on $[0, L]$ within length $\delta$ using at most $n$ values if, for every $f$ strictly unimodal on $[0, L]$ with maximum at $m$, it evaluates $f$ at most $n$ times and announces $a \le b$ with $b - a \le \delta$ and $m \in [a, b]$.
--   5. **The searchable lengths.** $\mathcal L_n$ is the set of lengths $L > 0$ for which some procedure locates the maximum on $[0, L]$ within unit length using at most $n$ values. Bellman's quantity (Eq. (22.1)) is
--   $$F_n = \sup \mathcal L_n .$$
--   6. **The discrete version.** A function $f$ on the points $0, 1, \dots, N-1$ is strictly unimodal with maximum at $m$ if $m < N$, $f$ is strictly increasing on $\{0, \dots, m\}$ and strictly decreasing on $\{m, \dots, N-1\}$. $\mathcal K_n$ is the set of $N \ge 1$ for which some procedure (querying points $0, 1, 2, \dots$ and announcing a point) evaluates at most $n$ values and announces exactly $m$, for every such $f$. Bellman's $K_n$ is the largest element of $\mathcal K_n$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Functions are `ℝ → ℝ` (resp. `ℕ → ℝ`); only their values on $[0, L]$ (resp. on $\{0, \dots, N-1\}$) are constrained, so evaluating outside the domain yields no information. The announced interval is not required to lie inside $[0, L]$ or to have length exactly one; intersecting with $[0, L]$ and enlarging it inside $[0, L]$ shows this is equivalent to Bellman's "sub-interval of unit length" whenever $L \ge 1$. In Mathlib's indexing $F_n$ is `Nat.fib (n + 1)`.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, § 22, Eq. (22.1) and Theorem 11 (Eq. (22.2)), p. 34; discrete version before Theorem 12, p. 36

import Mathlib

namespace BellmanDP.Fibonacci

/-- Bellman, *Dynamic Programming*, Ch. I, § 22, Theorem 11, p. 34: the book's Fibonacci
sequence, with `F₀ = F₁ = 1` and `F_n = F_{n−1} + F_{n−2}` for `n ≥ 2`.
(In Mathlib's indexing this is `Nat.fib (n + 1)`.) -/
def bookFib : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => bookFib (n + 1) + bookFib n

/-- A deterministic, adaptive search procedure, as a decision tree. At a `query x next` node the
procedure calculates the value `f x` of the unknown function and continues with the subtree
`next (f x)`; at a `stop b` node it stops and announces `b`. Along any path, the point queried at
each step is determined by the values observed at the earlier steps, and by nothing else about
`f`. `α` is the type of points that may be queried, `β` the type of announcements. -/
inductive SearchTree (α β : Type) : Type where
  | stop : β → SearchTree α β
  | query : α → (ℝ → SearchTree α β) → SearchTree α β

namespace SearchTree

variable {α β : Type}

/-- The announcement of the procedure `T` when run against the function `f`. -/
def result : SearchTree α β → (α → ℝ) → β
  | stop b, _ => b
  | query x next, f => result (next (f x)) f

/-- The number of values of `f` the procedure `T` calculates when run against `f`. -/
def cost : SearchTree α β → (α → ℝ) → ℕ
  | stop _, _ => 0
  | query x next, f => cost (next (f x)) f + 1

end SearchTree

/-- Ch. I, § 22, p. 34: `f` is *strictly unimodal on `[0, L]` with maximum at `m`*: `m ∈ [0, L]`,
`f` is strictly increasing on `[0, m]` and strictly decreasing on `[m, L]`. No continuity is
assumed; the endpoint cases `m = 0` and `m = L` are allowed. `m` is then the unique maximizer of
`f` on `[0, L]` (its single relative maximum). -/
def IsStrictUnimodalOn (f : ℝ → ℝ) (L m : ℝ) : Prop :=
  m ∈ Set.Icc 0 L ∧ StrictMonoOn f (Set.Icc 0 m) ∧ StrictAntiOn f (Set.Icc m L)

/-- The procedure `T` (announcing a closed interval `[a, b]` as the pair `(a, b)`) *always locates
the maximum of a strictly unimodal function on `[0, L]` within length `δ` by calculating at most
`n` values*: for every `f` strictly unimodal on `[0, L]` with maximum at `m`, `T` calculates at
most `n` values of `f`, and the interval `[a, b]` it announces satisfies `a ≤ b`, `b − a ≤ δ` and
`m ∈ [a, b]`. -/
def Locates (T : SearchTree ℝ (ℝ × ℝ)) (L δ : ℝ) (n : ℕ) : Prop :=
  ∀ (f : ℝ → ℝ) (m : ℝ), IsStrictUnimodalOn f L m →
    T.cost f ≤ n ∧
    (T.result f).1 ≤ (T.result f).2 ∧
    (T.result f).2 - (T.result f).1 ≤ δ ∧
    m ∈ Set.Icc (T.result f).1 (T.result f).2

/-- Ch. I, § 22, p. 34: the set of interval lengths `L_n > 0` such that the maximum of every
strictly unimodal function on `[0, L_n]` can always be located on a sub-interval of unit length
by calculating at most `n` values of the function. Bellman's `F_n = Sup L_n` (Eq. (22.1)) is the
least upper bound of this set. -/
def feasibleLengths (n : ℕ) : Set ℝ :=
  {L : ℝ | 0 < L ∧ ∃ T : SearchTree ℝ (ℝ × ℝ), Locates T L 1 n}

/-- Ch. I, § 22, p. 36 (discrete version): `f` is *strictly unimodal on the points
`0, 1, …, N − 1` with maximum at `m`*: `m < N`, `f` is strictly increasing on `{0, …, m}` and
strictly decreasing on `{m, …, N − 1}`. -/
def IsStrictUnimodalOnPoints (f : ℕ → ℝ) (N m : ℕ) : Prop :=
  m < N ∧ StrictMonoOn f (Set.Iic m) ∧ StrictAntiOn f (Set.Ico m N)

/-- Ch. I, § 22, p. 36: the set of numbers `N ≥ 1` of points such that the maximum of every
strictly unimodal function on the points `0, …, N − 1` can always be identified in `n`
computations: some procedure querying points (natural numbers) calculates at most `n` values
and announces exactly the maximizer `m`. Bellman's `K_n` is the greatest element of this set. -/
def identifiableSizes (n : ℕ) : Set ℕ :=
  {N : ℕ | 1 ≤ N ∧ ∃ T : SearchTree ℕ ℕ, ∀ (f : ℕ → ℝ) (m : ℕ),
    IsStrictUnimodalOnPoints f N m → T.cost f ≤ n ∧ T.result f = m}

end BellmanDP.Fibonacci


