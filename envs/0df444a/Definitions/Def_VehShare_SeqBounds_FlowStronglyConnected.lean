-- Prove2me | Definitions.Def_VehShare_SeqBounds_FlowStronglyConnected
-- name    : VehShare_SeqBounds_FlowStronglyConnected
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:42:26.359128+00:00
-- url     : https://prove2.me/theorems/01c3ef03-bbf6-4421-ae76-2b85f49b6415
-- title:
--   $q^s$ induces a strongly connected network
-- statement:
--   A price vector $q^s=(q^s_{ij})$ **induces a strongly connected network** if, in the directed graph on the locations $\mathcal N$ with an arc $a\to b$ whenever the induced demand flow is positive,
--
--   $$
--   a\to b\quad\Longleftrightarrow\quad \Lambda_{ab}\,q^s_{ab}>0,
--   $$
--
--   every location can be reached from every location by a directed path (of length $0$ or more). This is the standing assumption "We assume $q^s$ induces a strongly connected network" (p. 6).
--
--   **Formalization Note** Strong connectivity is required on all of $\mathcal N$. With a single location it holds trivially, even with no flow. Under the balance constraint of Problem (2), weak and strong connectivity of this graph coincide.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, p. 6 (unnumbered)

import Mathlib
import Definitions.Def_VehShare_SeqBounds_Instance

namespace VehShare.SeqBounds

/-- **`q^s` induces a strongly connected network.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), p. 6 (unnumbered): "We assume `q^s` induces a strongly connected network."

In the digraph on the locations with an arc `a → b` whenever the induced demand flow
`Λ_ab q_ab` is positive, every location reaches every location.

**Formalization Note.** Reading 12: the network induced by `q^s` is the digraph of its positive
demand flows, and strong connectivity is required on all of `𝒩`. With one location it holds
trivially (`ReflTransGen` is reflexive), even with no flow. -/
def FlowStronglyConnected (P : Instance) (qs : P.L → P.L → ℝ) : Prop :=
  ∀ i j : P.L, Relation.ReflTransGen (fun a b => 0 < P.Λ a b * qs a b) i j

end VehShare.SeqBounds


