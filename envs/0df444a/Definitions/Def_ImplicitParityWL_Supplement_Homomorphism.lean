-- Prove2me | Definitions.Def_ImplicitParityWL_Supplement_Homomorphism
-- name    : ImplicitParityWL_Supplement_Homomorphism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:26:37.499668+00:00
-- url     : https://prove2.me/theorems/69b76f6c-c281-4597-a5bc-3769ff1349b2
-- title:
--   Homomorphism counts and one-vertex tree decompositions
-- statement:
--   Let $F$ and $G$ be colored graphs with colors in the same set $K$.
--
--   1. A **homomorphism** $\varphi:F\to G$ is a map $V(F)\to V(G)$ that maps edges to edges and preserves colors, and $\hom(F,G)$ is the number of homomorphisms.
--   2. A **tree decomposition** of $F$ is a finite tree $T$ with bags $\beta(t)\subseteq V(F)$ such that every edge of $F$ lies in some bag and, for every $p\in V(F)$, the nodes $t$ with $p\in\beta(t)$ induce a nonempty subtree; its width is $\max_t|\beta(t)|-1$, and $\mathrm{tw}(F)\le k$ means that some tree decomposition has width at most $k$.
--   3. Rooted at $\rho\in V(T)$, a tree decomposition is **one-vertex** if $\beta(\rho)=\emptyset$ and every other node $t$, with parent $s$, satisfies $\beta(t)\setminus\beta(s)=\{p_t\}$ for a single vertex $p_t$.
--
--   By Dvořák's theorem, $k$-WL distinguishes $G$ and $H$ iff $\hom(F,G)\ne\hom(F,H)$ for some $F$ of treewidth at most $k$; such an $F$ is a witness. These notions state Theorems 1.4, 10.6 and 10.11.
--
--   **Formalization Note** Tree decompositions and $\mathrm{tw}(F)\le k$ are the published `RobersonCx.IsTreeDecomp` and `RobersonCx.TwLE` (bags of at most $k+1$ vertices). The parent of a node $t\ne\rho$ is its neighbour closer to $\rho$. $\hom(F,G)$ is the cardinality of the set of homomorphisms, which is their number for finite graphs.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), §1.3, p.3; §10, p.53; Definition 10.4, p.56

import Mathlib
import Definitions.Def_ImplicitParityWL_ColoredGraph
import Definitions.Def_RobersonCx_TwLE

namespace ImplicitParityWL

namespace Supplement

/-- `φ : V(F) → V(G)` is a **homomorphism of colored graphs** (Curticapean, Liu, Neuen, Seppelt,
*Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of
November 3, 2026, §1.3, p.3 and §10, p.53): it maps edges to edges and preserves colors. -/
def IsHom {K U V : Type*} (F : ColoredGraph K U) (G : ColoredGraph K V) (φ : U → V) : Prop :=
  (∀ x y, F.graph.Adj x y → G.graph.Adj (φ x) (φ y)) ∧ ∀ x, G.χ (φ x) = F.χ x

/-- `hom(F, G)`, the number of color-preserving homomorphisms `F → G` (§10, p.53).

**Formalization Note** `Nat.card` of the subtype of maps; it is the number of homomorphisms when the
vertex types are finite, which every use assumes. -/
noncomputable def homCount {K U V : Type*} (F : ColoredGraph K U) (G : ColoredGraph K V) : ℕ :=
  Nat.card {φ : U → V // IsHom F G φ}

/-- `F` has a **one-vertex tree decomposition of width at most `k`** (Definition 10.4, p.56): a tree
decomposition `(T, β)` (every edge in some bag; the nodes whose bag contains a vertex induce a
nonempty subtree) with all bags of size at most `k + 1`, and a root `ρ` with `β(ρ) = ∅` such that every
other node `t` with parent `s` has `β(t) ∖ β(s) = {p_t}` for a single vertex `p_t`.

**Formalization Note** The tree decomposition is the published `RobersonCx.IsTreeDecomp` (finite tree in
`Type`, every vertex in some bag, every edge in some bag, connected occurrence sets), which is
Definition 10.4 (i)–(ii). The parent of `t` is its neighbour closer to `ρ`: `s` adjacent to `t` with
`dist(ρ, s) < dist(ρ, t)`. -/
def HasOneVertexTD {K U : Type*} (F : ColoredGraph K U) (k : ℕ) : Prop :=
  ∃ (T : Type) (_ : Finite T) (TG : SimpleGraph T) (bag : T → Set U) (ρ : T),
    RobersonCx.IsTreeDecomp F.graph TG bag ∧ (∀ t, (bag t).encard ≤ ((k + 1 : ℕ) : ℕ∞)) ∧
    bag ρ = ∅ ∧ ∀ s t, TG.Adj s t → TG.dist ρ s < TG.dist ρ t → ∃ p, bag t \ bag s = {p}

end Supplement

end ImplicitParityWL


