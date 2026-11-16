-- Prove2me | Definitions.Def_MISInducedMinor_Supplement_redGraph
-- name    : MISInducedMinor_Supplement_redGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:38:11.397181+00:00
-- url     : https://prove2.me/theorems/74b8f37d-28b5-432d-b877-e2216c988cd9
-- title:
--   The red graph of a partition
-- statement:
--   Let $G$ be a finite simple graph and $\mathcal P$ a partition of $V(G)$. Two parts $X,Y$ of $\mathcal P$ are joined by a **black edge** if they are complete to one another (every $x\in X$ is adjacent to every $y\in Y$), by **no edge** if they are anti-complete, and by a **red edge** otherwise. The **red graph** of $\mathcal P$ is the graph whose vertices are the parts of $\mathcal P$ and whose edges are the red edges:
--   $$X \sim Y \iff X\neq Y \text{ and } X,Y \text{ are neither complete nor anti-complete}.$$
--   The red neighbours and red degree of a part are its neighbours and degree in this graph.
--
--   Red graphs are the objects whose degree (twin-width) or component max-leaf (reduced component max-leaf) is bounded along a contraction sequence.
--
--   **Formalization Note** "Complete or anti-complete" is the published `TwinWidthI.BoolWidth.Homogeneous`. The graph is built with `SimpleGraph.fromRel`, which adds $X\neq Y$ and symmetrizes; non-homogeneity is already symmetric.
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), §2.2, p.5

import Definitions.Def_TwinWidthI_BoolWidth_Setting

set_option autoImplicit false

namespace MISInducedMinor.Supplement

/-- The **red graph** of a partition `P` of the vertex set of `G`: its vertices are the parts of
`P`, and two distinct parts `X`, `Y` are joined by a red edge iff they are neither complete nor
anti-complete to each other in `G` (`¬ Homogeneous G X Y`). Bonnet, Chang, *Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More)*, arXiv:2609.11285 (sha256 e378b906…), §2.2, p.5.

**Formalization Note.** `Homogeneous` is the published `TwinWidthI.BoolWidth.Homogeneous` (all
pairs adjacent, or no pair adjacent). `SimpleGraph.fromRel` adds `X ≠ Y` and symmetrizes; since
non-homogeneity is symmetric, the adjacency is exactly "`X ≠ Y` and `X`, `Y` not homogeneous".
The contracted parts need not be adjacent; red edges do not require any edge of `G` between
them beyond non-homogeneity. -/
def redGraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : Finpartition (Finset.univ : Finset V)) : SimpleGraph {X : Finset V // X ∈ P.parts} :=
  SimpleGraph.fromRel fun X Y => ¬ TwinWidthI.BoolWidth.Homogeneous G X.1 Y.1

end MISInducedMinor.Supplement


