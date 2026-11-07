-- Prove2me | Definitions.Def_ForestBackdoorFPT_core2Set
-- name    : ForestBackdoorFPT_core2Set
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:35.343029+00:00
-- url     : https://prove2.me/theorems/98c8e212-e79e-4265-899d-438105accd8d
-- title:
--   The 2-core $\mathrm{core}_2(G)$
-- statement:
--   The **2-core** $\mathrm{core}_2(G)$ of a graph $G$ is the unique maximal induced subgraph in which every vertex has degree at least two. It may be empty. Every cycle of $G$ lies in it, and it has the same cyclomatic number as $G$.
--
--   Lemma 2.2 counts the cycles of the 2-core, and Lemma 4.5 restricts strong forest backdoors to the variables in it.
--
--   **Formalization Note** The vertex set is the union of all vertex sets $S$ in which every vertex has at least two neighbours inside $S$. That family is closed under unions, so the union is its unique maximal member. The 2-core is the subgraph induced on this set, as a graph on the corresponding subtype.
-- source:
--   Bilyk–Munduzbaev–Sharma–Siam, Strong Backdoor to Forests is FPT: Tight Linear-Time FPT for Essentially General SAT, STOC 2027 submission (manuscript sha256 7fd1a7a8…), §2, p.5 (PDF p.6)

import Mathlib

set_option autoImplicit false

namespace ForestBackdoorFPT

/-- The vertex set of the **2-core** (Bilyk–Munduzbaev–Sharma–Siam, *Strong Backdoor to Forests is
FPT*, STOC 2027 submission (manuscript sha256 7fd1a7a8…), §2, p.5 (PDF p.6)): "The 2-core of G,
denoted by core₂(G), is the unique maximal induced subgraph in which every vertex has degree at least
two."

**Formalization Note** It is the union of all vertex sets `S` such that every vertex of `S` has at
least two neighbours inside `S`. This family is closed under unions, so the union is its unique
maximal member (and may be empty). Degrees are taken inside `S`, i.e. in the induced subgraph. -/
def core2Set {W : Type*} (G : SimpleGraph W) : Set W :=
  {v | ∃ S : Set W, v ∈ S ∧ ∀ u ∈ S, 2 ≤ (G.neighborSet u ∩ S).ncard}

/-- The **2-core** `core₂(G)` (p.5): the subgraph of `G` induced by `core2Set G`, on the subtype of
its vertices. -/
def core2 {W : Type*} (G : SimpleGraph W) : SimpleGraph (core2Set G) :=
  G.induce (core2Set G)

end ForestBackdoorFPT


