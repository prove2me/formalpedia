-- Prove2me | Definitions.Def_ClawFreeChoosable_IsRichCliqueCutset
-- name    : ClawFreeChoosable_IsRichCliqueCutset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:46.013732+00:00
-- url     : https://prove2.me/theorems/fc20d3f7-08c1-47c5-bdcb-4aa633f0efec
-- title:
--   Rich clique cutset
-- statement:
--   A clique $K$ of a graph $G$ is a **rich clique cutset** if $V(G) \setminus K$ can be partitioned into anticomplete sets $A, B$ each of which contains two distinct vertices that are not true twins in $G$ (in particular $A, B \ne \emptyset$).
--
--   Chudnovsky and Seymour showed that a connected claw-free graph with a rich clique cutset is of interval type or has a double clique cutset (Theorem 12.2).
--
--   **Formalization Note** The paper defines richness for clique cutsets of a connected graph; connectivity is a separate hypothesis wherever the notion is used.
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, §12.1 p.32, "rich"

import Mathlib
import Definitions.Def_ClawFreeChoosable_IsAnticomplete
import Definitions.Def_ClawFreeChoosable_TrueTwins

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Rich clique cutset** (arXiv:2611.01068v1, §12.1 p.32): a clique `K` of `G` such that
`V(G) \ K` can be partitioned into nonempty anticomplete sets `A, B` each of which contains two
(distinct) vertices that are not true twins in `G`.

**Formalization Note.** The paper defines richness for clique cutsets of a connected graph; the
connectivity of `G` is a separate hypothesis wherever the notion is used. Nonemptiness of `A`
and `B` follows from the two vertices each contains. -/
def IsRichCliqueCutset {V : Type} (G : SimpleGraph V) (K : Set V) : Prop :=
  G.IsClique K ∧ ∃ A B : Set V, Disjoint A B ∧ A ∪ B = Kᶜ ∧ IsAnticomplete G A B ∧
    (∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ ¬ TrueTwins G x y) ∧
    (∃ x ∈ B, ∃ y ∈ B, x ≠ y ∧ ¬ TrueTwins G x y)

end ClawFreeChoosable


