-- Prove2me | Definitions.Def_SnarlSPQR_Snarls_SignCut
-- name    : SnarlSPQR_Snarls_SignCut
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:29:21.742941+00:00
-- url     : https://prove2.me/theorems/b4123df3-b769-440b-9d5a-4c45641a86b1
-- title:
--   Sign-consistent vertices, sign-cut graphs (Definition 4) and dangling blocks
-- statement:
--   Let $G$ be a bidirected graph.
--
--   **Sign-consistent vertices.** Let $x$ be a cutvertex of $G$ and let $C_1,\dots,C_\ell$ be the components of $G-x$. Then $x$ is **sign-consistent** if, for every $i$, $x$ is a tip in the induced subgraph $G[V(C_i)+x]$.
--
--   **Sign-cut graphs (Definition 4).** Split every sign-consistent vertex $y$ (with either sign), then relabel each new vertex $y'$ as $y$. The connected components of the resulting graph, each read as a subgraph of $G$, are the **sign-cut graphs** of $G$. A sign-cut graph's vertex set is the relabelled component, and its edges are the edges of $G$ that lie in that component. Sign-cut graphs partition $E(G)$. A sign-consistent vertex belongs to exactly two of them.
--
--   **Dangling blocks.** For a vertex $v$ of a block $H$ of $G$, a block $H'\neq H$ of $G$ that contains $v$ and has vertex-sides of both signs at $v$ is a **dangling block** of $v$ with respect to $H$.
--
--   **Formalization Note.** Every sign-consistent vertex is split with sign $+$. Splitting with $-$ only exchanges the names $y$ and $y'$, which the relabelling erases, so this changes no sign-cut graph. A vertex left isolated by the split, such as the copy of a sign-consistent vertex that is a tip of $G$, gives the one-vertex sign-cut graph $(\{y\},\emptyset)$. `IsSignCut G F` holds when $F$ is the relabelled component of some vertex of the split graph.
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), pp. 29–31, §5.2 (sign-consistent vertices p. 29, Definition 4 p. 30, dangling blocks p. 31)

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_Snarl

open Classical

namespace SnarlSPQR.Snarls

/-!
# Sign-consistent vertices, sign-cut graphs and dangling blocks (§5.2, pp. 29–31)

Sena et al., arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), §5.2: the definition of
sign-consistent vertices (p. 29), Definition 4 (p. 30) and dangling blocks (p. 31).

* A cutvertex `x` of `G` (of `U(G)`), with `C₁, …, C_ℓ` the components of `G − x`, is
  **sign-consistent** if `x` is a tip in `G[V(C_i) + x]` for every `i`.
* **Definition 4.** The **sign-cut graphs** of `G` are the graphs resulting from splitting each
  sign-consistent vertex `y` with any sign and relabelling each new vertex `y'` as `y`. Here every
  sign-consistent `y` is split with sign `+` (the result does not depend on the sign, up to
  exchanging the names `y` and `y'`, which the relabelling erases); the sign-cut graphs are the
  connected components of the split graph, each relabelled (`(v, b) ↦ v`) into a subgraph of `G`
  whose vertex set is the relabelled component and whose edges are the edges of `G` lying in it.
  An isolated vertex of the split graph (for instance the copy `y'` of a sign-consistent `y` that
  is a tip of `G`) gives the one-vertex sign-cut graph `({y}, ∅)`.
* For a vertex `v` of a block `H` of `G`, a block `H' ≠ H` of `G` containing `v` and having
  vertex-sides of opposite signs at `v` is a **dangling block** of `v` with respect to `H`.
-/

namespace BiGraph

variable {V : Type*}

/-- `x` is a sign-consistent vertex of `G` (p. 29): a cutvertex of `G` that is a tip in
`G[V(C) + x]` for every component `C` of `G − x`. -/
def SignConsistent (G : BiGraph V) (x : V) : Prop :=
  G.U.IsCutvertex x ∧
    ∀ w ∈ G.verts, w ≠ x → (G.induce (insert x ((G.U.deleteVert x).compOf w))).IsTip x

/-- The sign-consistent vertices of `G`. -/
noncomputable def signConsistentSet (G : BiGraph V) : Finset V := G.verts.filter G.SignConsistent

/-- The graph obtained by splitting every sign-consistent vertex `y` (with sign `+`). -/
noncomputable def signCutSplit (G : BiGraph V) : BiGraph (V × Bool) :=
  G.split (G.signConsistentSet.image fun y => (y, Sign.pos))

/-- The sign-cut graph containing the vertex `w` of the split graph: its component, relabelled
`(v, b) ↦ v`, with the edges of `G` that lie in that component. -/
noncomputable def signCutOf (G : BiGraph V) (w : V × Bool) : BiGraph V where
  verts := ((G.signCutSplit).U.compOf w).image Prod.fst
  edges := G.edges.filter fun e =>
    ∃ p ∈ e, (G.signCutSplit).U.Reach w
      (splitSide (G.signConsistentSet.image fun y => (y, Sign.pos)) p).1

/-- `F` is a sign-cut graph of `G` (Definition 4). -/
def IsSignCut (G F : BiGraph V) : Prop := ∃ w ∈ (G.signCutSplit).verts, F = G.signCutOf w

/-- `H'` is a dangling block of `v` with respect to the block `H` of `G` (p. 31). -/
def IsDangling (G H H' : BiGraph V) (v : V) : Prop :=
  G.IsBlock H' ∧ H' ≠ H ∧ v ∈ H'.verts ∧ H'.HasSide v .pos ∧ H'.HasSide v .neg

/-- `v` has a dangling block with respect to `H` in `G`. -/
def HasDangling (G H : BiGraph V) (v : V) : Prop := ∃ H', G.IsDangling H H' v

end BiGraph

end SnarlSPQR.Snarls


