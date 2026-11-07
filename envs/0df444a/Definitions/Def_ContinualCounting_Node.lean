-- Prove2me | Definitions.Def_ContinualCounting_Node
-- name    : ContinualCounting_Node
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:04.545841+00:00
-- url     : https://prove2.me/theorems/b6a63038-95ac-4b1e-ba94-77d1d85175c2
-- title:
--   The binary tree $\mathcal T$, the nodes $\mathcal V(\mathcal T)$ and the tree-basis coefficients
-- statement:
--   Let $n=2^h$ and let $\mathcal T$ be the perfect binary tree of height $h$, its leaves being the coordinates $i$ of $\mathbb R^n$. A node is a pair (depth $d\le h$, index $k<2^d$), with children $\ell(d,k)=(d+1,2k)$ and $r(d,k)=(d+1,2k+1)$. $\mathcal V(\mathcal T)$ is the set consisting of the root $\rho$ and every right child; $\mathcal V(\mathcal T^u)$ is the part of it in the subtree $\mathcal T^u$ rooted at $u$; and $\mathcal L(\mathcal T^u)$ is the set of leaves under $u$.
--
--   For $u\in\mathcal V(\mathcal T)$, $\chi^u$ is the indicator vector of $\mathcal L(\mathcal T^u)$, and these $n$ vectors form a basis of $\mathbb R^n$. Writing $y=\sum_{u\in\mathcal V(\mathcal T)}\mathrm{coef}_u(y)\chi^u$, the coefficients are
--   $$\mathrm{coef}_\rho(y)=y_{\mathrm{lm}(\rho)},\qquad \mathrm{coef}_{r(p)}(y)=y_{\mathrm{lm}(r(p))}-y_{\mathrm{lm}(p)},$$
--   where $\mathrm{lm}(u)$ is the leftmost leaf under $u$. In the paper's notation, $b_u=\mathrm{coef}_u(z)$ and $a_u=\mathrm{coef}_u(Ax)$.
--
--   **Formalization Note** Nodes are plain pairs of naturals with total child maps, and `IsNode h` selects the valid ones. The explicit formula replaces the abstract basis; the identity $y_i=\sum_{u\in\mathrm{Anc}(i)\cap\mathcal V(\mathcal T)}\mathrm{coef}_u(y)$ is what makes it the basis expansion.
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), §5, pp.17–18 (PDF pp.18–19), and the coefficient formula of p.31 (PDF p.32)

import Mathlib

set_option autoImplicit false

namespace ContinualCounting

/-- A node of the perfect binary tree `T`, as (depth, index at that depth). Bairaktari, Dahl, Larsen,
arXiv:2607.00876 (sha256 986e6426…), §5, p.17.

**Formalization Note.** Plain pairs of naturals: the child maps are total, and `IsNode h` says
which pairs are nodes of the tree of height `h`. The `n = 2^h` leaves are `(h, i)`, `i : Fin (2^h)`,
coordinate `i` being leaf `i` (`0`-based). Statements only use valid nodes; `nodes h` and `treeV` filter
to them. -/
abbrev Node := ℕ × ℕ

/-- The left child `ℓ(u)`. -/
def left (u : Node) : Node := (u.1 + 1, 2 * u.2)

/-- The right child `r(u)`. -/
def right (u : Node) : Node := (u.1 + 1, 2 * u.2 + 1)

/-- The root `ρ`. -/
def root : Node := (0, 0)

/-- `u` is a node of the tree of height `h`. -/
def IsNode (h : ℕ) (u : Node) : Prop := u.1 ≤ h ∧ u.2 < 2 ^ u.1

instance (h : ℕ) : DecidablePred (IsNode h) := fun u => by unfold IsNode; infer_instance

/-- All nodes of the tree of height `h`. -/
def nodes (h : ℕ) : Finset Node :=
  (Finset.range (h + 1) ×ˢ Finset.range (2 ^ h)).filter (IsNode h)

/-- `u` lies in `V(T)`: it is the root or the right child of its parent. -/
def InV (u : Node) : Prop := u = root ∨ u.2 % 2 = 1

instance : DecidablePred InV := fun u => by unfold InV; infer_instance

/-- `v` lies in the subtree `T^u` rooted at `u` (`v = u` allowed). -/
def Desc (u v : Node) : Prop := u.1 ≤ v.1 ∧ v.2 / 2 ^ (v.1 - u.1) = u.2

instance (u : Node) : DecidablePred (Desc u) := fun v => by unfold Desc; infer_instance

/-- `V(T^u) := V(T) ∩ T^u`, p.17. -/
def treeV (h : ℕ) (u : Node) : Finset Node :=
  (nodes h).filter fun v => InV v ∧ Desc u v

/-- `i ∈ L(T^u)`: leaf `i` lies below `u`, equivalently `u ∈ Anc(i)`. -/
def IsUnder (h : ℕ) (u : Node) (i : Fin (2 ^ h)) : Prop :=
  u.1 ≤ h ∧ i.val / 2 ^ (h - u.1) = u.2

instance (h : ℕ) (u : Node) : DecidablePred (IsUnder h u) := fun i => by
  unfold IsUnder; infer_instance

/-- The coordinate of `y` at the natural index `j` (`0` off the range, never reached by a node). -/
def readLeaf {h : ℕ} (y : Fin (2 ^ h) → ℝ) (j : ℕ) : ℝ :=
  if hj : j < 2 ^ h then y ⟨j, hj⟩ else 0

/-- The leftmost leaf under `u`, `lm(d, k) = k · 2^{h−d}`. -/
def leftmost (h : ℕ) (u : Node) : ℕ := u.2 * 2 ^ (h - u.1)

/-- The parent of a non-root node. -/
def parent (u : Node) : Node := (u.1 - 1, u.2 / 2)

/-- **The coefficient of `χ^u` in the tree basis.** Bairaktari, Dahl, Larsen, arXiv:2607.00876
(sha256 986e6426…), §5, p.18: `z = ∑_{u∈V(T)} b_u χ^u`, `Ax = ∑_{u∈V(T)} a_u χ^u`, with `χ^u` the indicator
of the leaves under `u`. Explicitly (p.31): "The coefficient of a right child is the difference
between the prefix sums at the leftmost leaves of that child and its parent". So
`coef_ρ(y) = y_{lm(ρ)}` and `coef_{r(p)}(y) = y_{lm(r(p))} − y_{lm(p)}`, and `b_u = coef h u z`,
`a_u = coef h u (A x)`.

**Formalization Note.** The explicit formula replaces a `Basis` construction; it is the unique
expansion because `y_i = ∑_{u ∈ Anc(i) ∩ V(T)} coef_u(y)` telescopes along the path to leaf `i` (proved
in the verification file). A node outside `V(T)` has coefficient `0`. -/
def coef (h : ℕ) (u : Node) (y : Fin (2 ^ h) → ℝ) : ℝ :=
  if u = root then readLeaf y 0
  else if u.2 % 2 = 1 then readLeaf y (leftmost h u) - readLeaf y (leftmost h (parent u))
  else 0

end ContinualCounting


