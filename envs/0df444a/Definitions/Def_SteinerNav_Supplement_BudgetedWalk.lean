-- Prove2me | Definitions.Def_SteinerNav_Supplement_BudgetedWalk
-- name    : SteinerNav_Supplement_BudgetedWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:12:37.45072+00:00
-- url     : https://prove2.me/theorems/922b6f9b-c9d4-440c-bf8b-8776a4b829df
-- title:
--   Budgeted greedy descent, its candidate sets, scan count and the budget $k=\lceil\log_\alpha(2\Delta\max\{1,(C_\alpha+1)/\zeta\})\rceil$
-- statement:
--   Let $G=(P\cup R,E)$ be a directed graph on input points $P$ and Steiner points $R$ in $\mathbb R^d$, let $q\in\mathbb R^d$ be a query and $\alpha>1$.
--
--   1. $C_\alpha=\dfrac{\alpha+1}{\alpha-1}$.
--   2. For $\Delta\ge1$ and $\zeta>0$ the **search budget** is
--   $$k=\Big\lceil\log_\alpha\Big(2\Delta\max\Big\{1,\frac{C_\alpha+1}{\zeta}\Big\}\Big)\Big\rceil .$$
--   3. A **budgeted walk** with budget $k$ is a sequence $x_0,\dots,x_j$ with $x_0\in P$ and $j\le k$ in which every $x_{i+1}$ is a strict greedy move from $x_i$ toward $q$ (an out-neighbor of $x_i$ closest to $q$, strictly closer than $x_i$), and which stops before the budget ($j<k$) only at a greedy local minimum (no out-neighbor strictly closer to $q$).
--   4. A **candidate set** for such a walk is a finite set of input points that contains every input point among $x_0,\dots,x_j$ and, if the final vertex $x_j$ is a Steiner point, all out-neighbors of $x_j$.
--   5. The **scan count** of the walk is $j+1$ if $j<k$ (the final vertex is scanned to recognize a local minimum) or $x_j\in R$ (it is scanned at the cutoff), and $j$ otherwise: one adjacency-list scan per move plus at most one more.
--
--   These objects state the bounded-search-budget guarantee (Theorem 6) for approximate nearest-neighbor search on Steiner navigable graphs.
--
--   **Formalization Note** The walk is a function $\mathbb N\to\mathbb R^d$ of which only $x_0,\dots,x_j$ matter; ties among closest out-neighbors are unrestricted. A candidate set may contain more input points than the required ones (for example every scanned out-neighbor), which covers every reading of "input points evaluated". The ceiling is the natural-number ceiling, equal to the integer ceiling since the argument of the logarithm is at least $2$ when $\Delta\ge1$.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee62135a42ef49d815773f6af7f50ba344b9460d6007d849529b707b183), §6.3, p.22 (C_α); Theorem 6, p.24 and its proof, pp.24–25 (PDF pp.22, 24–25)

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_GreedyRun

namespace SteinerNav.Supplement

/-- The constant `C_α = (α + 1)/(α − 1)` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §6.3, p.22). -/
noncomputable def approxConst (α : ℝ) : ℝ :=
  (α + 1) / (α - 1)

/-- The search budget `k = ⌈log_α(2Δ max{1, (C_α + 1)/ζ})⌉` of Theorem 6
(Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Theorem 6, p.24).

**Formalization Note** `Δ` is passed as a real number (the aspect ratio of the input points); the
ceiling is `Nat.ceil`, which agrees with the integer ceiling because the argument of the logarithm is
at least `2` whenever `Δ ≥ 1`. -/
noncomputable def searchBudget (α Δ ζ : ℝ) : ℕ :=
  ⌈Real.logb α (2 * Δ * max 1 ((approxConst α + 1) / ζ))⌉₊

/-- A budgeted strict greedy descent toward `q` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Theorem 6, p.24): the
walk `x 0, …, x j` starts at an input point, each `x (i+1)` is a strict greedy move from `x i`, at most
`k` moves are made, and the walk stops before the budget only at a greedy local minimum.

**Formalization Note** The walk is a function `ℕ → Pt d` of which only `x 0, …, x j` matter. Ties are
unrestricted (`GreedyStep` allows every closest out-neighbor). A walk with `j = k` stops at the
cutoff whether or not `x k` is a local minimum. -/
def IsBudgetedWalk {d : ℕ} (E : Finset (Pt d × Pt d)) (P : Finset (Pt d)) (q : Pt d) (k j : ℕ)
    (x : ℕ → Pt d) : Prop :=
  x 0 ∈ P ∧ j ≤ k ∧ (∀ i < j, GreedyStep E q (x i) (x (i + 1))) ∧ (j < k → GreedyLocalMin E q (x j))

/-- `Cand` is a valid candidate set for the budgeted walk `x 0, …, x j`
(Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Theorem 6, p.24): it consists of input points, it contains every
input point visited by the walk, and, if the final vertex `x j` is a Steiner point, it contains all
out-neighbors of `x j`.

**Formalization Note** "The input points evaluated" is not pinned down further on the page; these
are the candidates the procedure must evaluate, and every larger set of input points (for example,
all scanned out-neighbors) is allowed. -/
def IsCandidateSet {d : ℕ} (E : Finset (Pt d × Pt d)) (P R : Finset (Pt d)) (j : ℕ) (x : ℕ → Pt d)
    (Cand : Finset (Pt d)) : Prop :=
  Cand ⊆ P ∧ (∀ i ≤ j, x i ∈ P → x i ∈ Cand) ∧ (x j ∈ R → ∀ y, (x j, y) ∈ E → y ∈ Cand)

open scoped Classical in
/-- The number of adjacency-list scans of a budgeted walk with `j` moves and budget `k`
(Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), proof of Theorem 6, p.25): one scan per move (of `x 0, …, x (j−1)`), plus one
scan of the final vertex `x j` when it is recognized as an early local minimum (`j < k`) or is a
Steiner vertex at the cutoff. -/
noncomputable def scanCount {d : ℕ} (R : Finset (Pt d)) (k j : ℕ) (x : ℕ → Pt d) : ℕ :=
  if j < k ∨ x j ∈ R then j + 1 else j

end SteinerNav.Supplement


