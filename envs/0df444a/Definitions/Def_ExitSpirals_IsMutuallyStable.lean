-- Prove2me | Definitions.Def_ExitSpirals_IsMutuallyStable
-- name    : ExitSpirals_IsMutuallyStable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:21.919597+00:00
-- url     : https://prove2.me/theorems/1452d5cd-cbfa-41ba-8b8a-81afb7806eee
-- title:
--   Stable and mutually stable sets of agents (Definitions 4.1, 4.2)
-- statement:
--   Let $E$ be a directed network on $N$. A set $V\subseteq N$ is **stable** in $E$ if every $i\in V$ has an in-neighbour in $V$:
--   $$\forall i\in V\ \exists j\in V:\ (j\to i)\in E.$$
--   For two networks $E_R, E_C$ on the same agents, $V$ is **mutually stable** if it is stable in both.
--
--   The empty set is stable. By Proposition 2 the active agents of the maximal equilibrium form the largest mutually stable set of the stripped networks, so these sets are the graph-theoretic description of equilibrium activity.
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Definitions 4.1 and 4.2, p.23

import Mathlib
import Definitions.Def_ExitSpirals_Network

namespace ExitSpirals

/-- **Stable subset** (Definition 4.1).
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Definition 4.1,
p.23: "In a network G = (V, E), a subset V′ ⊂ V is stable if, for each i ∈ V′, there is a j ∈ V′
such that (j, i) ∈ E. That is, every node in V′ has an incoming edge from V′."

**Formalization Note.** As on the page, the empty set is stable. -/
def IsStable {n : ℕ} (E : Network n) (V : Finset (Fin n)) : Prop :=
  ∀ i ∈ V, ∃ j ∈ V, (j, i) ∈ E

/-- **Mutually stable subset** (Definition 4.2, p.23): "A mutually stable subset of the coupled
network (G_R, G_C) is a set V′ of nodes that is stable in G_µ for all µ ∈ {R, C}." -/
def IsMutuallyStable {n : ℕ} (ER EC : Network n) (V : Finset (Fin n)) : Prop :=
  IsStable ER V ∧ IsStable EC V

end ExitSpirals


