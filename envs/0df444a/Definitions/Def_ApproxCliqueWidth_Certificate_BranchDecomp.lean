-- Prove2me | Definitions.Def_ApproxCliqueWidth_Certificate_BranchDecomp
-- name    : ApproxCliqueWidth_Certificate_BranchDecomp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:30:05.978714+00:00
-- url     : https://prove2.me/theorems/19644423-9da2-4afc-9575-c1617015643c
-- title:
--   Branch-decomposition, width of an edge, and the predicate $\mathrm{bw}(f) \le k$
-- statement:
--   Let $V$ be a finite set. A **subcubic tree** is a tree with at least two vertices in which every vertex is incident with at most three edges; a **leaf** is a vertex incident with exactly one edge. A **branch-decomposition** $(T, L)$ of a set function on $V$ consists of a subcubic tree $T$ and a bijection $L$ from $V$ onto the set of leaves of $T$.
--
--   For an edge $e = uw$ of $T$, the two components of $T \setminus e$ split the leaves into two sides; let $A_{uw} = \{x \in V : L(x) \text{ lies in the component of } T \setminus e \text{ containing } u\}$. The **width** of $e$ with respect to $f : 2^V \to \mathbb{Z}$ is $f(A_{uw})$, and $(T, L)$ has width at most $k$ if every edge has width at most $k$. The **branch-width** $\mathrm{bw}(f)$ is the minimum width of a branch-decomposition, and $\mathrm{bw}(f) = f(\emptyset)$ when $|V| \le 1$ (where no branch-decomposition exists). Accordingly,
--   $$\mathrm{bw}(f) \le k \iff \big(|V| \le 1 \text{ and } f(\emptyset) \le k\big) \text{ or } f \text{ has a branch-decomposition of width at most } k.$$
--
--   Branch-width measures how well $V$ can be recursively split along cuts of small $f$-value; applied to the cut-rank function of a graph it gives rank-width.
--
--   **Formalization Note** $T$ is a `SimpleGraph (Fin n)` for some $n \ge 2$ with `IsTree`; degree is the cardinality of the neighbour set. The side of an edge $uw$ is computed by reachability from $u$ in $T$ with the edge $uw$ deleted. The width condition is imposed for both orientations of each edge, i.e. on both sides; for the symmetric functions the paper considers the two sides have equal value. Branch-width is expressed only through the predicate $\mathrm{bw}(f)\le k$ (and "every branch-decomposition has an edge of width $\ge m$" for lower bounds), so no minimum over a possibly empty family is ever taken.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 516, Section 2 (subcubic tree, branch-decomposition, width, bw(f))

import Mathlib

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour p. 516: a branch-decomposition `(T, L)` of a set function on the finite ground set
`V`. `T` is a subcubic tree — a tree with at least two vertices, every vertex incident with at most
three edges — here on the vertex set `Fin n`; `L` is a bijection from `V` onto the set of leaves
(vertices incident with exactly one edge) of `T`. -/
structure BranchDecomp (V : Type*) where
  /-- number of vertices of the tree `T` -/
  n : ℕ
  /-- the tree -/
  T : SimpleGraph (Fin n)
  isTree : T.IsTree
  two_le : 2 ≤ n
  subcubic : ∀ t : Fin n, (T.neighborSet t).ncard ≤ 3
  /-- the labelling of the leaves by elements of `V` -/
  L : V → Fin n
  L_leaf : ∀ v : V, (T.neighborSet (L v)).ncard = 1
  L_injective : Function.Injective L
  L_surjective : ∀ t : Fin n, (T.neighborSet t).ncard = 1 → ∃ v : V, L v = t

namespace BranchDecomp

variable {V : Type*} [Fintype V]

/-- For an edge `uw` of `T`, the set `L⁻¹(X)` of elements of `V` whose leaf lies in the component
of `T \ uw` containing `u`. -/
noncomputable def side (D : BranchDecomp V) (u w : Fin D.n) : Finset V := by
  classical
  exact Finset.univ.filter (fun x : V => (D.T.deleteEdges {s(u, w)}).Reachable u (D.L x))

/-- Oum–Seymour p. 516: `(T, L)` has width at most `k` with respect to `f`: for every edge `uw`
of `T`, the width `f(L⁻¹(X))` of the edge is at most `k`, where `X` is the set of leaves on
either side of the edge (both sides are constrained, so no side is privileged). -/
def WidthLE (D : BranchDecomp V) (f : Finset V → ℤ) (k : ℤ) : Prop :=
  ∀ u w : Fin D.n, D.T.Adj u w → f (D.side u w) ≤ k

end BranchDecomp

/-- `bw(f) ≤ k`, Oum–Seymour p. 516: either `|V| ≤ 1`, where the paper sets `bw(f) = f(∅)`, and
`f(∅) ≤ k`; or `f` has a branch-decomposition of width at most `k`. Stated as a predicate so that
no minimum over a possibly empty family is ever taken. -/
def BwLE {V : Type*} [Fintype V] (f : Finset V → ℤ) (k : ℤ) : Prop :=
  (Fintype.card V ≤ 1 ∧ f ∅ ≤ k) ∨ ∃ D : BranchDecomp V, D.WidthLE f k

end ApproxCliqueWidth.Certificate


