-- Prove2me | Definitions.Def_ProductFraming_Nest_Algorithm
-- name    : ProductFraming_Nest_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:08:17.850813+00:00
-- url     : https://prove2.me/theorems/9355c35d-d67b-4566-a334-4fc6e0bc972d
-- title:
--   The NEST(y) algorithm, the framing it displays, $V^{NEST(y)}$ and $V^{NEST}$
-- statement:
--   Fix $y\in[m]$. For $x\in[m]$, $S(x)\subseteq[n]$ denotes the set of products displayed on the first $x$ pages. The algorithm NEST($y$) works as follows.
--
--   1. Solve problem (2) with cardinality bound $c=y\cdot p$ and let $S(y)$ be an optimal assortment, so $|S(y)|\le yp$ and $R(S(y))=U(y)$.
--   2. For $x=y-1$ down to $1$, choose $S(x)\subseteq S(x+1)$ with $|S(x)|=\min(|S(x+1)|,x\cdot p)$ such that
--   $$\frac{R(S(x))}{|S(x)|}\ \ge\ \frac{R(S(x+1))}{|S(x+1)|}.\qquad(4)$$
--   3. Leave pages $y+1,\dots,m$ blank.
--
--   Since the algorithm makes choices, a **run** of NEST($y$) is any family $S(1),\dots,S(y)$ satisfying 1 and 2. The framing a run displays puts product $i$ on the first page $x\le y$ with $i\in S(x)$, and does not display products outside $S(1)\cup\dots\cup S(y)$. $V^{NEST(y)}$ is the expected revenue (objective of (1)) of this framing, and for a family of runs, one for each $y\in[m]$,
--   $$V^{NEST}=\max_{y\in[m]}V^{NEST(y)}.$$
--
--   These objects are what the approximation guarantee (Theorem 3) is about.
--
--   **Formalization Note** A run is the predicate `IsNestRun` on `S : ℕ → Finset (Fin n)`; only $S(1),\dots,S(y)$ are constrained. In (4), cardinalities are cast to $\mathbb R$; when a set is empty the quotient is $0$. $V^{NEST(y)}$ is defined as the revenue of the displayed framing, not by the formula $\sum_x\lambda(x)R(S(\min(x,y)))$, whose equality with it is part of the proof of Proposition 1.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, §4.2, p. 9, NEST(y) Algorithm, (4)

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model

namespace ProductFraming.Nest

open Finset

/-! The NEST(y) algorithm of Gallego, Li, Truong, Wang (2020), authors' accepted manuscript, §4.2,
p. 9. NEST(y) makes arbitrary choices (which optimal assortment, which subset satisfying (4)), so a run
is described by a predicate on its output `S : ℕ → Finset (Fin n)`, where `S x` is the set `S(x)` of
products displayed in the first `x` pages; only `S 1, …, S y` matter. -/

/-- `S` is an output of NEST(y) (p. 9), with an exact solution of (2) (`ε = 0`):
1. `S(y)` is an optimal solution of (2) with cardinality bound `c = y · p`;
2. for `x = y − 1, …, 1`: `S(x) ⊆ S(x + 1)`, `|S(x)| = min(|S(x + 1)|, x · p)` and
   `R(S(x)) / |S(x)| ≥ R(S(x + 1)) / |S(x + 1)|`, which is (4). -/
def IsNestRun {n : ℕ} (p : ℕ) (r : Fin n → ℝ) (P : Fin n → Finset (Fin n) → ℝ) (y : ℕ)
    (S : ℕ → Finset (Fin n)) : Prop :=
  ((S y).card ≤ y * p ∧ R r P (S y) = U p r P y) ∧
  ∀ x, 1 ≤ x → x < y →
    S x ⊆ S (x + 1) ∧
    (S x).card = min (S (x + 1)).card (x * p) ∧
    R r P (S (x + 1)) / ((S (x + 1)).card : ℝ) ≤ R r P (S x) / ((S x).card : ℝ)

/-- The framing NEST(y) displays: product `i` goes on the first page `x ∈ [1, y]` with `i ∈ S(x)`
(so `S(x)` is exactly the content of pages `1, …, x`); a product in no `S(x)`, `x ≤ y`, is not
displayed (page `0`). Pages `y + 1, …, m` are left blank (step 3). -/
def nestFraming {n : ℕ} (y : ℕ) (S : ℕ → Finset (Fin n)) (i : Fin n) : ℕ :=
  if h : ((Icc 1 y).filter (fun x => i ∈ S x)).Nonempty then
    ((Icc 1 y).filter (fun x => i ∈ S x)).min' h
  else 0

/-- `V^{NEST(y)}`: the expected revenue (objective of (1)) of the framing a NEST(y) run displays. -/
def VNest {n : ℕ} (m : ℕ) (r : Fin n → ℝ) (P : Fin n → Finset (Fin n) → ℝ) (lam : ℕ → ℝ)
    (y : ℕ) (S : ℕ → Finset (Fin n)) : ℝ :=
  V m r P lam (nestFraming y S)

/-- `V^{NEST} = max_{y ∈ [m]} V^{NEST(y)}` (p. 9), for a family `runs y` of NEST(y) runs. -/
noncomputable def VNEST {n m : ℕ} (hm : 1 ≤ m) (r : Fin n → ℝ) (P : Fin n → Finset (Fin n) → ℝ)
    (lam : ℕ → ℝ) (runs : ℕ → ℕ → Finset (Fin n)) : ℝ :=
  (Icc 1 m).sup' ⟨1, mem_Icc.mpr ⟨le_refl 1, hm⟩⟩ (fun y => VNest m r P lam y (runs y))

end ProductFraming.Nest


