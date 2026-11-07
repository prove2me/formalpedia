-- Prove2me | Definitions.Def_ClawFreeChoosable_IsClawFree
-- name    : ClawFreeChoosable_IsClawFree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:33.88756+00:00
-- url     : https://prove2.me/theorems/280ec595-1b6a-496e-84c7-976dd4c64c9c
-- title:
--   Claw-free graph
-- statement:
--   All graphs are finite and simple. A graph $G$ is **claw-free** if it has no induced subgraph isomorphic to the claw $K_{1,3}$: there are no four vertices $c, a_1, a_2, a_3$ such that $c$ is adjacent to each of $a_1, a_2, a_3$ while $a_1, a_2, a_3$ are pairwise distinct and pairwise nonadjacent.
--
--   Claw-freeness is the hereditary class in which the Gravier–Maffray conjecture (every claw-free graph is chromatic-choosable) is posed; every statement of this mission about claw-free graphs uses this predicate.
--
--   **Formalization Note** The induced $K_{1,3}$ is written out by its four vertices; $c \ne a_i$ follows from the irreflexivity of adjacency.
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, §1 p.1 and §7.1 p.9, "claw-free"

import Mathlib

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Claw-free graph** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are
chromatic-choosable*, arXiv:2611.01068v1, §1 p.1 and §7.1 p.9): `G` has no induced subgraph
isomorphic to `K1,3`, i.e. there are no vertices `c, a₁, a₂, a₃` with `c` adjacent to each `aᵢ`
and the `aᵢ` pairwise distinct and pairwise nonadjacent.

**Formalization Note.** An induced `K1,3` is written out as its four vertices; `c ≠ aᵢ` follows
from the irreflexivity of adjacency. -/
def IsClawFree {V : Type} (G : SimpleGraph V) : Prop :=
  ¬ ∃ c a₁ a₂ a₃ : V, G.Adj c a₁ ∧ G.Adj c a₂ ∧ G.Adj c a₃ ∧
    a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ ∧
    ¬ G.Adj a₁ a₂ ∧ ¬ G.Adj a₁ a₃ ∧ ¬ G.Adj a₂ a₃

end ClawFreeChoosable


