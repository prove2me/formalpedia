-- Prove2me | Definitions.Def_VDCyclePack_IsAPath
-- name    : VDCyclePack_IsAPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:11.937429+00:00
-- url     : https://prove2.me/theorems/733cb1cd-397f-4851-a664-dae5e8460fcd
-- title:
--   $A$-path
-- statement:
--   For a graph $F$ and $A\subseteq V(F)$, an **$A$-path** is a path of $F$ with two distinct ends in $A$ and all internal vertices outside $A$. Such a path has at least one edge.
--
--   For a marked packing $H$ with $A=V(H)$, the paper's $A$-paths are taken in $F=G-E(H)$ (p.11): a single edge of $G$ between two vertices of $A$ is an $A$-path when it is not an edge of $H$.
--
--   **Formalization Note** A walk with `IsPath`, distinct ends in $A$, and every other vertex outside $A$.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 3, p.10

import Mathlib

namespace VDCyclePack

/-- **A-path.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 3, p.10: "For a graph F and a set A ⊆ V(F), an A-path is a path with two
distinct ends in A and all internal vertices outside A. Such a path has at least one edge."

`IsAPath F A p` says the walk `p` from `u` to `v` in `F` is a path, `u ≠ v`, `u, v ∈ A`, and every
other vertex of `p` lies outside `A`.

**Formalization Note.** For a marked packing `H` the paper's A-paths live in `G − E(H)` (p.11:
"the A-paths may use no edge of H"); the theorems apply this definition to
`F = G.deleteEdges H.edgeSet`, or state the no-`H`-edge condition next to it. -/
def IsAPath {V : Type*} (F : SimpleGraph V) (A : Set V) {u v : V} (p : F.Walk u v) : Prop :=
  p.IsPath ∧ u ≠ v ∧ u ∈ A ∧ v ∈ A ∧ ∀ w ∈ p.support, w ≠ u → w ≠ v → w ∉ A

end VDCyclePack


