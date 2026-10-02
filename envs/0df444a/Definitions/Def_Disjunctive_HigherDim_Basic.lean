-- Prove2me | Definitions.Def_Disjunctive_HigherDim_Basic
-- name    : Disjunctive_HigherDim_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:37:28.623577+00:00
-- url     : https://prove2.me/theorems/799bcc06-3ab5-4398-b29f-92bb85b67a6d
-- title:
--   K, K0, the split-convexification step Pj, and its iteration
-- statement:
--   This definition fixes the vocabulary of Section 7.1: the mixed 0-1 program's LP
--   relaxation $K$ and feasible set $K_0$, the one-variable convexification operator $P_j$, and its
--   iteration over a fixed sequence of coordinates.
--
--   `Poly A b` is $K := \{x : \tilde A x \ge \tilde b\}$ (the LP relaxation, after folding bound
--   constraints into $\tilde A, \tilde b$ as the book does). `ZeroOneSet j` is $\{x : x_j \in
--   \{0,1\}\}$. `SplitConvexify S j := \mathrm{conv}(S \cap \{x_j \in \{0,1\}\})$ is one step
--   of sequential convexification — the book's own description of what $P_j$ *is*, before its
--   3-step nonlinear derivation. `IteratedSplit K l` folds `SplitConvexify` left to right over an
--   explicit list `l` of coordinates, giving $P_{i_1,\dots,i_t}(K) := P_{i_t}(P_{i_{t-1}}(\cdots
--   P_{i_1}(K)\cdots))$. `K0Set A b N'` is $K_0 := K \cap \{x_j \in \{0,1\}, j \in N'\}$ for the
--   0-1 index set $N'$.
--
--   `Mj A b j` is the nonlinear lift $M_j(K)$ obtained by multiplying $\tilde A x \ge \tilde b$ by
--   $(1-x_j)$ and $x_j$ (eq. (7.1)) and linearizing $y_i := x_i x_j$ ($i \ne j$), $x_j := x_j^2$: a
--   pair $(x,y)$ with $y_j = x_j$ and the two resulting linearized inequality families. `Pj A b j` is
--   the projection of $M_j(K)$ onto the $x$-space, i.e. $P_j(K) := \{x : \exists y,\ (x,y) \in
--   M_j(K)\}$ — the literal 3-step construction that Theorem 7.1 identifies with `SplitConvexify`.
--
--   **Formalization Note.** `SplitConvexify`/`IteratedSplit`/`K0Set` restate `03-sequential-convex`'s
--   and `02a-convex-hull`'s vocabulary locally (per the series convention that a draft mission cannot
--   import another draft mission's definitions), specialized to the split disjunction $x_j \in
--   \{0,1\}$ that this chapter always disjoins on.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 91-92, Section 7.1

import Mathlib

namespace Disjunctive.HigherDim

/-- The polyhedron `{x : A x ≥ b}` (restated locally, as in earlier chunks of the series). -/
def Poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, b i ≤ (A.mulVec x) i}

/-- `{x : x_j ∈ {0,1}}` (Balas §7.1, p. 91). -/
def ZeroOneSet {n : ℕ} (j : Fin n) : Set (Fin n → ℝ) := {x | x j = 0 ∨ x j = 1}

/-- One step of sequential convexification, `conv(S ∩ {x_j ∈ {0,1}})` (Balas §7.1, p. 91-92,
the simple description of `P_j` that Theorem 7.1 identifies with the nonlinear 3-step
construction). -/
def SplitConvexify {n : ℕ} (S : Set (Fin n → ℝ)) (j : Fin n) : Set (Fin n → ℝ) :=
  convexHull ℝ (S ∩ ZeroOneSet j)

/-- `P_{i1,...,it}(K) := P_it(P_{it-1}(⋯(P_i1(K))⋯))` (Balas §7.1, p. 92): iterating
`SplitConvexify` over an explicit sequence of coordinates, applied left to right. -/
def IteratedSplit {n : ℕ} (K : Set (Fin n → ℝ)) (l : List (Fin n)) : Set (Fin n → ℝ) :=
  l.foldl SplitConvexify K

/-- `K₀ := K ∩ {x_j ∈ {0,1}, j ∈ N'}` (Balas §7.1, p. 91), the mixed 0-1 program's feasible set,
for `N'` the 0-1 index set. -/
def K0Set {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  Poly A b ∩ ⋂ j ∈ Nprime, ZeroOneSet j

/-- `M_j(K)`, the lifted polyhedron from multiplying `Ãx ≥ b̃` by `(1-x_j)` and `x_j` and
linearizing `y_i := x_i x_j` (`i ≠ j`), `x_j := x_j²` (Balas §7.1, p. 91-92, eq. (7.1)-(7.2)):
pairs `(x,y)` with `y_j = x_j` and the two linearized inequality families. -/
def Mj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (j : Fin n) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | (∀ i, 0 ≤ (A.mulVec p.1) i - (A.mulVec p.2) i + b i * (p.1 j - 1)) ∧
        (∀ i, 0 ≤ (A.mulVec p.2) i - b i * p.1 j) ∧ p.2 j = p.1 j}

/-- `P_j(K)`, the projection of `M_j(K)` onto the `x`-space (Balas §7.1, p. 91-92, Step 3). -/
def Pj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (j : Fin n) : Set (Fin n → ℝ) :=
  {x | ∃ y, (x, y) ∈ Mj A b j}

end Disjunctive.HigherDim


