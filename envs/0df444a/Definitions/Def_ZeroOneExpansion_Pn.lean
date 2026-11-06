-- Prove2me | Definitions.Def_ZeroOneExpansion_Pn
-- name    : ZeroOneExpansion_Pn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:28.416532+00:00
-- url     : https://prove2.me/theorems/c3bd7f23-d09e-4ecc-b497-0a2ecc3cb8cc
-- title:
--   The polytope $P_n=X_n*Y_n\subseteq\mathbb R^{4n+1}$, its graph $G_n$, and the active-block sets $I(u)$, $J(u)$
-- statement:
--   Let $C=\{0,1\}^2=\{00,01,10,11\}$ and $D=\{0,e_1,e_2\}=\{00,10,01\}$, where $10=(1,0)=e_1$ and $01=(0,1)=e_2$. Let $Q=\operatorname{conv}(C)=[0,1]^2$ be the unit square and $\Delta=\operatorname{conv}(D)$ the standard 2-simplex. A point of $\mathbb R^{4n}=(\mathbb R^2)^{2n}$ is written $x=(x_1,\dots,x_{2n})$ with blocks $x_k\in\mathbb R^2$; blocks $1,\dots,n$ form the **first group** and blocks $n+1,\dots,2n$ the **second group**. Set
--   $$X_n=C^n\times D^n,\qquad Y_n=D^n\times C^n,\qquad P_n=X_n*Y_n=\operatorname{conv}\big(X_n\times\{0\}\cup Y_n\times\{1\}\big)\subseteq\mathbb R^{4n+1},$$
--   and $V_n=X_n\times\{0\}\cup Y_n\times\{1\}$. $G_n$ is the graph (1-skeleton) of $P_n$. For $u=(u_1,\dots,u_{2n};t)$, a block is **active** if it is nonzero, and
--   $$I(u)=\{i\in[n]: u_i\neq 0\},\qquad J(u)=\{j\in[n]: u_{n+j}\neq0\}.$$
--
--   These are the objects of §§3–4: $P_n$ is the family of 0/1-polytopes of Theorem 1.
--
--   **Formalization Note** Block $k$ ($1\le k\le 2n$) occupies coordinates $2k-2,2k-1$ of $\mathbb R^{4n+1}$ and the layer coordinate $t$ is the last coordinate. Blocks are indexed by two copies of $\{0,\dots,n-1\}$ (first and second group), so $[n]$ is 0-based. $G_n$ is the published `Grunbaum2003.polytopeGraph` of $P_n$, whose vertex set is the set of vertices of $P_n$ (equal to $V_n$ by Fact 3).
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), §3, pp.4–6 (C, D, Q, ∆, Xn, Yn, Pn, Vn, I, J) and §4, p.7 (Gn)

import Mathlib
import Definitions.Def_Grunbaum2003_polytopeGraph
import Definitions.Def_ZeroOneExpansion_cayleySum

set_option autoImplicit false

namespace ZeroOneExpansion

open Matrix

/-- `C := {0, 1}^2 = {00, 01, 10, 11}` (arXiv:2608.01870, §3, p.4). The label `10` is the point
`(1, 0) = e₁` and `01` is `(0, 1) = e₂`. -/
def C : Set (Fin 2 → ℝ) := {![0, 0], ![0, 1], ![1, 0], ![1, 1]}

/-- `D := {0, e1, e2} = {00, 10, 01}` (arXiv:2608.01870, §3, p.4). -/
def D : Set (Fin 2 → ℝ) := {![0, 0], ![1, 0], ![0, 1]}

/-- `Q := conv(C) = [0, 1]^2`, the unit square (arXiv:2608.01870, §3, p.4). -/
def Qsq : Set (Fin 2 → ℝ) := convexHull ℝ C

/-- `∆ := conv(D)`, the standard 2-simplex in `ℝ^2` (arXiv:2608.01870, §3, pp.4–5). -/
def Delta : Set (Fin 2 → ℝ) := convexHull ℝ D

/-- Coordinates of the blocks of a point of `ℝ^{4n} = (ℝ^2)^{2n}`. The first-group block `i`
(`Sum.inl i`, the paper's block `i + 1`) occupies coordinates `2i, 2i+1`; the second-group block `j`
(`Sum.inr j`, the paper's block `n + j + 1`) occupies coordinates `2n + 2j, 2n + 2j + 1`. -/
def blockIdx (n : ℕ) : Fin n ⊕ Fin n → Fin 2 → Fin (4 * n)
  | Sum.inl i, j => ⟨2 * i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩
  | Sum.inr i, j => ⟨2 * n + 2 * i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩

/-- The block `k ∈ ℝ^2` of a point `x ∈ ℝ^{4n}`: `x = (x_1, …, x_{2n})` with `x_k ∈ ℝ^2`
(arXiv:2608.01870, §3, p.5). -/
def blk (n : ℕ) (x : Fin (4 * n) → ℝ) (k : Fin n ⊕ Fin n) : Fin 2 → ℝ :=
  fun j => x (blockIdx n k j)

/-- `Xn := C^n × D^n ⊆ ℝ^{4n}` (arXiv:2608.01870, §3, p.5): first-group blocks in `C`,
second-group blocks in `D`. -/
def Xn (n : ℕ) : Set (Fin (4 * n) → ℝ) :=
  {x | ∀ i : Fin n, blk n x (Sum.inl i) ∈ C ∧ blk n x (Sum.inr i) ∈ D}

/-- `Yn := D^n × C^n ⊆ ℝ^{4n}` (arXiv:2608.01870, §3, p.5). -/
def Yn (n : ℕ) : Set (Fin (4 * n) → ℝ) :=
  {x | ∀ i : Fin n, blk n x (Sum.inl i) ∈ D ∧ blk n x (Sum.inr i) ∈ C}

/-- `Vn := Xn × {0} ∪ Yn × {1} ⊆ ℝ^{4n+1}` (arXiv:2608.01870, §3, p.5). -/
def Vn (n : ℕ) : Set (Fin (4 * n + 1) → ℝ) :=
  (fun x => withLast x 0) '' Xn n ∪ (fun y => withLast y 1) '' Yn n

/-- The polytope `Pn := Xn ∗ Yn = conv(Xn × {0} ∪ Yn × {1}) ⊆ ℝ^{4n+1}` (arXiv:2608.01870, §3,
p.5).

**Formalization Note** Coordinate layout of `ℝ^{4n+1}`: block `k` of the paper (1-based,
`1 ≤ k ≤ 2n`) is coordinates `2k − 2, 2k − 1` (`blockIdx`), and the layer coordinate `t` is the last
coordinate `4n`. -/
def Pn (n : ℕ) : Set (Fin (4 * n + 1) → ℝ) := cayleySum (Xn n) (Yn n)

/-- `Gn`, the graph (1-skeleton) of `Pn` (arXiv:2608.01870, §4, p.7: "Gn := (Vn, En), i.e., the
1-skeleton of Pn"), as the published `Grunbaum2003.polytopeGraph`. Its vertex type is the set of
vertices of `Pn`, which is `Vn` by Fact 3. -/
noncomputable def Gn (n : ℕ) : SimpleGraph (Grunbaum2003.PolytopeVertex (Pn n)) :=
  Grunbaum2003.polytopeGraph (Pn n)

/-- The layer coordinate `t` of `u = (u_1, …, u_{2n}; t) ∈ ℝ^{4n+1}`. -/
def layer (n : ℕ) (u : Fin (4 * n + 1) → ℝ) : ℝ := u (Fin.last (4 * n))

/-- The block `u_k ∈ ℝ^2` of `u = (u_1, …, u_{2n}; t) ∈ ℝ^{4n+1}`. -/
def ublk (n : ℕ) (u : Fin (4 * n + 1) → ℝ) (k : Fin n ⊕ Fin n) : Fin 2 → ℝ :=
  blk n (Fin.init u) k

open Classical in
/-- `I(u) := {i ∈ [n] : u_i ≠ 0}`, the active first-group blocks (arXiv:2608.01870, §3, p.6).

**Formalization Note** `[n]` is `Fin n` (0-based): `i : Fin n` stands for the paper's `i + 1`. -/
noncomputable def Iset (n : ℕ) (u : Fin (4 * n + 1) → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => ublk n u (Sum.inl i) ≠ 0

open Classical in
/-- `J(u) := {j ∈ [n] : u_{n+j} ≠ 0}`, the active second-group blocks (arXiv:2608.01870, §3, p.6),
re-indexed to `[n]` (0-based `Fin n`). -/
noncomputable def Jset (n : ℕ) (u : Fin (4 * n + 1) → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun j => ublk n u (Sum.inr j) ≠ 0

end ZeroOneExpansion


