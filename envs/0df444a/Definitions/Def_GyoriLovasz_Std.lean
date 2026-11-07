-- Prove2me | Definitions.Def_GyoriLovasz_Std
-- name    : GyoriLovasz_Std
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:10.496345+00:00
-- url     : https://prove2.me/theorems/2381a30f-7b93-4250-acb9-7327570e553a
-- title:
--   Standing assumption of §2: no loops, terminals have no outgoing edges
-- statement:
--   The paper assumes throughout §§2–4, without loss of generality, that the graph has no self-loops or parallel edges and that terminals have no outgoing edges. This item records the two conditions not already built into a directed graph: every edge $(x,y)$ has $x\neq y$, and no edge leaves a terminal.
--
--   **Formalization Note** It is a hypothesis of the lemmas of §§2–4, not of Theorems 1 and 2, whose statements speak of an arbitrary directed graph.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), §2, p.14

import Mathlib
import Definitions.Def_GyoriLovasz_DG

namespace GyoriLovasz

/-- **The standing assumption of §2.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), §2, p.14: "We assume without loss of generality that the
graph has no self-loops or parallel edges, and that terminals have no outgoing edges."

**Formalization Note.** Parallel edges are excluded by `DG`. This is a hypothesis of the lemmas of
§§2–4, as the paper's assumption is, and not of `theorem_1`, `theorem_2`, whose printed statements
speak of an arbitrary directed graph. -/
def Std {V : Type*} (G : DG V) (T : Finset V) : Prop :=
  (∀ a ∈ G.arcs, a.1 ≠ a.2) ∧ ∀ a ∈ G.arcs, a.1 ∉ T

end GyoriLovasz


