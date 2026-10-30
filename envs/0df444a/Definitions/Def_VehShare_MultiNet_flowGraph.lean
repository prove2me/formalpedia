-- Prove2me | Definitions.Def_VehShare_MultiNet_flowGraph
-- name    : VehShare_MultiNet_flowGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:44:44.178405+00:00
-- url     : https://prove2.me/theorems/cf998d3f-339f-49e4-bb80-6c2585127927
-- title:
--   The networks induced by $q^s$
-- statement:
--   For a static vector $q^s$, the **flow graph** is the simple graph on the locations with an edge $\{i,j\}$, $i\neq j$, whenever $\Lambda_{ij}q^s_{ij}>0$ or $\Lambda_{ji}q^s_{ji}>0$. Its connected components are the **networks** $\mathcal N_c$, $c=1,\dots,C$, that $q^s$ induces (§6, p. 17): they partition the locations, $\sum_c N_c=N$.
--
--   **Formalization Note** Every location lies in exactly one network (a location without flow is a network by itself). Under balanced flows, weak and strong connectivity of the components agree.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, §6, p. 17

import Mathlib
import Definitions.Def_VehShare_MultiNet_Instance

namespace VehShare.MultiNet

/-- **The flow graph of a static price vector; its components are the networks.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), §6, p. 17: "Consider the case where the optimal pricing policy `q^s` induces `C > 1` connected
networks. Let `𝒩_c`, `N_c` and `𝒜_c` denote the set of locations, the number of locations, and the set
of location pairs respectively that are associated with network `c` ... `∑ N_c = N`, `∪ 𝒩_c = 𝒩` and
`𝒩_c ∩ 𝒩_l = ∅`".

The simple graph on the locations with an edge `{i, j}` (`i ≠ j`) whenever `Λ_ij q_ij > 0` or
`Λ_ji q_ji > 0`. The networks are its connected components
`(flowGraph P qs).ConnectedComponent` (a finite type).

**Formalization Note.** Reading 4: every location lies in exactly one network (singletons
included). Under the balance constraint of Problem (2) weakly and strongly connected components
coincide. Self-pairs `(i, i)` give no edge, which does not change the components. -/
def flowGraph (P : Instance) (qs : P.L → P.L → ℝ) : SimpleGraph P.L :=
  SimpleGraph.fromRel fun i j => 0 < P.Λ i j * qs i j

end VehShare.MultiNet


