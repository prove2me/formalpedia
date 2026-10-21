-- Prove2me | Definitions.Def_HeldKarp_Gap_SubtourLP
-- name    : HeldKarp_Gap_SubtourLP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:23.988221+00:00
-- url     : https://prove2.me/theorems/efa960ea-56c5-4cd0-a696-871de5105a97
-- title:
--   The integer program (3), the polyhedron $A'x\le b'$, $x\ge 0$ and the linear program (4) (§2, pp. 1141–1145)
-- statement:
--   Let $n\ge 3$ and index the edges of $K_n$ by the pairs $1\le i<j\le n$. Vectors $x=(x_{ij})$ and $c=(c_{ij})$ are $\binom n2$-vectors, $cx=\sum_{i<j}c_{ij}x_{ij}$, and the **degree** of vertex $i$ in $x$ is $\sum_{j>i}x_{ij}+\sum_{j<i}x_{ji}$. This item defines the objects of §2 of Held and Karp.
--
--   The **integer program (3)** for the traveling-salesman problem is $\min \sum_{i<j}c_{ij}x_{ij}$ subject to
--
--   1. (i) $\sum_{j>i}x_{ij}+\sum_{j<i}x_{ji}=2$ for $i=1,\dots,n$;
--   2. (ii) $\sum_{i\in S,\,j\in S,\,i<j}x_{ij}\le |S|-1$ for every proper subset $S\subset\{2,3,\dots,n\}$;
--   3. (iii) $0\le x_{ij}\le 1$;
--   4. (iv) $x_{ij}$ integer.
--
--   The rewritten program (3′) replaces (i) by: (i) degree $2$ at $i=2,\dots,n-1$, written $Ax=b$ with $b=(2,\dots,2)\in\mathbb R^{n-2}$; (ii) $\sum_j x_{1j}=2$; (iii) $\sum_{i<j}x_{ij}=n$; (iv) the subtour constraints of (3); (v) $x_{ij}\le 1$; (vi) $x_{ij}\ge 0$; (vii) $x_{ij}$ integer. The paper writes (ii)–(v) as $A'x\le b'$. This item defines:
--
--   1. the **polyhedron** $\{x : A'x\le b',\ x\ge 0\}$, the points satisfying (ii)–(vi) of (3′);
--   2. the **feasible region of the linear program (4)**, $\{x : Ax=b,\ A'x\le b',\ x\ge 0\}$, the points satisfying (i)–(vi) of (3′);
--   3. an **optimal solution of (4)**: a feasible point $\bar x$ with $c\bar x\le cy$ for every real feasible point $y$ of
--   $$
--   v=\min_x\{cx \mid Ax=b,\ A'x\le b',\ x\ge 0\};
--   $$
--   4. the set of feasible solutions of the integer program (3);
--   5. the **incidence vector** $(e_{ij})$ of a graph: $1$ on its edges and $0$ on the other edges of $K_n$.
--
--   These are the programs whose relation to the gap function is the subject of §2.
--
--   **Formalization Note** Vertices are `Fin n`; the paper's vertex $1$ is `0 : Fin n` and its vertex $n$ is `lastV n` $= n-1$. A $\binom n2$-vector is a function on `Edge n`, the unordered pairs $\{i,j\}$ with $i\ne j$, so there are no diagonal coordinates. Constraints (ii) $\sum_j x_{1j}=2$ and (iii) $\sum_{i<j}x_{ij}=n$ are **equalities**, as printed in (3′); the paper's shorthand $A'x\le b'$ is not read as turning them into inequalities (with that reading Theorems 1 and 2 of the paper fail). The subtour constraints range over the **nonempty** proper subsets $S\subsetneq\{2,\dots,n\}$; for $S=\emptyset$ the constraint would read $0\le -1$ and every program would be infeasible. "Integer" means every coordinate is an integer. Optimality in (4) is over all real feasible points.
-- source:
--   Held & Karp, The Traveling-Salesman Problem and Minimum Spanning Trees, Operations Research 18(6) 1970, pp. 1141–1145, §2, programs (3) (pp. 1141–1142), (3′) and the notation Ax = b, A′x ≤ b′ (p. 1143), the vectors (e^k_ij) (Theorem 1, p. 1144), program (4) (p. 1145)

import Mathlib

open Classical

namespace HeldKarp.Gap

/-- **The edges of `K_n`**: the unordered pairs `{i, j}` with `i ≠ j`. The `(n choose 2)`-vectors
of programs (3), (3′) and (4) (§2, p. 1143) are the functions `Edge n → ℝ`, with component `x_ij`
at the edge `{i, j}`. -/
abbrev Edge (n : ℕ) : Type := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- The paper's vertex `n`, the last vertex `n - 1 : Fin n` (vertex `i` of the paper is
`i - 1 : Fin n`; vertex 1 is `0`). -/
def lastV (n : ℕ) [NeZero n] : Fin n :=
  ⟨n - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne n)) Nat.one_pos⟩

/-- The objective `cx = Σ_{1≤i<j≤n} c_ij x_ij` (§2, pp. 1141–1143). -/
noncomputable def cost {n : ℕ} (c : Sym2 (Fin n) → ℝ) (x : Edge n → ℝ) : ℝ :=
  ∑ e : Edge n, c e.1 * x e

/-- The degree of vertex `i` in `x`, `Σ_{j>i} x_ij + Σ_{j<i} x_ji`: the sum of `x` over the edges
incident with `i`. -/
noncomputable def deg {n : ℕ} (x : Edge n → ℝ) (i : Fin n) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e : Edge n => i ∈ e.1), x e

/-- `Σ_{i∈S, j∈S, i<j} x_ij`: the sum of `x` over the edges with both ends in `S`. -/
noncomputable def insideSum {n : ℕ} (x : Edge n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e : Edge n => ∀ v ∈ e.1, v ∈ S), x e

/-- `Σ_{1≤i<j≤n} x_ij`: the sum of `x` over all edges. -/
noncomputable def total {n : ℕ} (x : Edge n → ℝ) : ℝ :=
  ∑ e : Edge n, x e

/-- **The subtour constraints** ((3)(ii), p. 1142; (3′)(iv), p. 1143):
`Σ_{i∈S, j∈S, i<j} x_ij ≤ |S| − 1` for every nonempty proper subset `S ⊂ {2, 3, …, n}`. -/
def SubtourConstraints {n : ℕ} [NeZero n] (x : Edge n → ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ⊂ Finset.univ.erase 0 →
    insideSum x S ≤ (S.card : ℝ) - 1

/-- **Feasible solutions of the integer program (3)** (§2, pp. 1141–1142):
(i) every vertex has degree 2; (ii) the subtour constraints; (iii) `0 ≤ x_ij ≤ 1`;
(iv) every `x_ij` is an integer. -/
def Feasible3 {n : ℕ} [NeZero n] (x : Edge n → ℝ) : Prop :=
  (∀ i : Fin n, deg x i = 2) ∧
  SubtourConstraints x ∧
  (∀ e : Edge n, 0 ≤ x e ∧ x e ≤ 1) ∧
  (∀ e : Edge n, ∃ z : ℤ, x e = z)

/-- **The polyhedron `A′x ≤ b′, x ≥ 0`** (§2, pp. 1143–1144): constraints (ii)–(vi) of (3′),
(ii) `Σ_j x_1j = 2`, (iii) `Σ_{1≤i<j≤n} x_ij = n` (both equalities, as printed in (3′)),
(iv) the subtour constraints, (v) `x_ij ≤ 1`, (vi) `x_ij ≥ 0`. -/
def OneTreePolyhedron (n : ℕ) [NeZero n] : Set (Edge n → ℝ) :=
  {x | deg x 0 = 2 ∧ total x = n ∧ SubtourConstraints x ∧
    (∀ e : Edge n, x e ≤ 1) ∧ (∀ e : Edge n, 0 ≤ x e)}

/-- **The constraints `Ax = b`** ((3′)(i), p. 1143): degree 2 at every vertex `i = 2, …, n − 1`. -/
def DegreeConstraints {n : ℕ} [NeZero n] (x : Edge n → ℝ) : Prop :=
  ∀ i : Fin n, i ≠ 0 → i ≠ lastV n → deg x i = 2

/-- **The feasible region of the linear program (4)** (§2, p. 1145):
`Ax = b, A′x ≤ b′, x ≥ 0`, i.e. constraints (i)–(vi) of (3′) without (vii). -/
def LP4Feasible (n : ℕ) [NeZero n] : Set (Edge n → ℝ) :=
  {x | x ∈ OneTreePolyhedron n ∧ DegreeConstraints x}

/-- **An optimal solution of the linear program (4)** `min_x {cx | Ax = b, A′x ≤ b′, x ≥ 0}`:
a feasible point whose objective value is at most that of every real feasible point. -/
def IsOptimal4 {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (x : Edge n → ℝ) : Prop :=
  x ∈ LP4Feasible n ∧ ∀ y ∈ LP4Feasible n, cost c x ≤ cost c y

/-- **The incidence vector** `(e_ij)` of a graph `G` (§2, p. 1144): `1` on the edges of `G`, `0`
on the other edges of `K_n`. -/
noncomputable def incidence {n : ℕ} (G : SimpleGraph (Fin n)) : Edge n → ℝ :=
  fun e => if e.1 ∈ G.edgeSet then 1 else 0

end HeldKarp.Gap


