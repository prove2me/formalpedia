-- Prove2me | Definitions.Def_MISInducedMinor_InducedMinorModel
-- name    : MISInducedMinor_InducedMinorModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:21.200554+00:00
-- url     : https://prove2.me/theorems/27c39ffd-f010-492e-9370-c0cd020d8eb1
-- title:
--   Induced-minor models and the induced-minor relation
-- statement:
--   Let $H$ and $G$ be graphs. An **induced-minor model** of $H$ in $G$ consists of branch sets $B_w\subseteq V(G)$, one for every vertex $w\in V(H)$, such that
--
--   1. every $B_w$ is nonempty and the branch sets are pairwise disjoint;
--   2. every $B_w$ induces a connected subgraph $G[B_w]$;
--   3. for distinct $u,w\in V(H)$, some edge of $G$ joins $B_u$ and $B_w$ **if and only if** $uw\in E(H)$.
--
--   $H$ is an **induced minor** of $G$ if there is an induced-minor model of $H$ in $G$; this is the same as obtaining $H$ from $G$ by removing vertices and contracting edges. If $H$ is not an induced minor of $G$, then $G$ is **$H$-induced-minor-free**.
--
--   The "only if" in item 3 is what distinguishes induced minors from ordinary minors: two branch sets of nonadjacent vertices of $H$ must not touch. Excluding a planar graph as an induced minor defines the graph classes on which the paper studies Max Independent Set.
--
--   **Formalization Note** No finiteness is assumed. Connectedness of the induced subgraph is Mathlib's `Connected`, which already includes nonemptiness; nonemptiness is also a separate field.
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), §2.1, p.5

import Mathlib

set_option autoImplicit false

namespace MISInducedMinor

/-- An **induced-minor model** of `H` in `G`: pairwise disjoint nonempty branch sets `B w`
(`w ∈ V(H)`), each inducing a connected subgraph of `G`, such that two distinct branch sets
`B u`, `B w` are joined by an edge of `G` **if and only if** `uw ∈ E(H)`. Bonnet, Chang, *Max
Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More)*,
arXiv:2609.11285 (sha256 e378b906…), §2.1, p.5.

**Formalization Note.** `G.induce (B w)` is the subgraph of `G` induced by `B w`, and Mathlib's
`Connected` includes nonemptiness; `nonempty` is stated separately anyway, as on the page. The
`adj_iff` field is the "if and only if" of p.5: with only one direction it would be an ordinary
minor model. No finiteness is assumed. -/
structure InducedMinorModel {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch set of the vertex `w` of `H`. -/
  B : W → Set V
  /-- Branch sets are nonempty. -/
  nonempty : ∀ w, (B w).Nonempty
  /-- Branch sets are pairwise disjoint. -/
  disjoint : Pairwise (Function.onFun Disjoint B)
  /-- Each branch set induces a connected subgraph of `G`. -/
  connected : ∀ w, (G.induce (B w)).Connected
  /-- Distinct branch sets are adjacent in `G` exactly when their vertices are adjacent in `H`. -/
  adj_iff : ∀ u w, u ≠ w → ((∃ x ∈ B u, ∃ y ∈ B w, G.Adj x y) ↔ H.Adj u w)

/-- `H` is an **induced minor** of `G`: there is an induced-minor model of `H` in `G`
(arXiv:2609.11285, §2.1, p.5: "H is an induced minor of G if and only if there is an
induced-minor model of H in G"). `G` is `H`-induced-minor-free when this fails. -/
def IsInducedMinor {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (InducedMinorModel H G)

end MISInducedMinor


