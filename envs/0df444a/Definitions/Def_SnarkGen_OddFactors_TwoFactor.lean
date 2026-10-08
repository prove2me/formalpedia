-- Prove2me | Definitions.Def_SnarkGen_OddFactors_TwoFactor
-- name    : SnarkGen_OddFactors_TwoFactor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:02:58.220746+00:00
-- url     : https://prove2.me/theorems/dde53754-b8d3-4820-9c8c-ced6e19f79a1
-- title:
--   2-factors, and graphs all of whose 2-factors consist of odd cycles (Section 2, §4.4)
-- statement:
--   Let $G$ be a finite simple graph on a vertex set $V$.
--
--   1. A **2-factor** of $G$ is a spanning 2-regular subgraph of $G$: a subgraph $F \subseteq G$ on the whole vertex set $V$ in which every vertex has degree exactly 2. Each connected component of a 2-factor is a cycle, and the length of that cycle is its number of vertices.
--   2. **All 2-factors of $G$ consist of only odd cycles** if for every 2-factor $F$ of $G$ every component of $F$ has an odd number of vertices:
--   $$\forall F \text{ 2-factor of } G,\ \ \forall C \text{ component of } F:\quad |V(C)| \text{ is odd}.$$
--
--   The second notion is the one in Conjecture 4.11 of the paper (Abreu, Labbate, Sheehan). For cubic graphs it is a strong form of uncolourability: the union of two colour classes of a 3-edge-colouring is a 2-factor all of whose cycles are even.
--
--   **Formalization Note** A 2-factor is a graph `F` on the same vertex type as `G` (hence spanning) with `F ≤ G` and `F.IsRegularOfDegree 2` (degrees computed with classical decidability). Component sizes are `Nat.card c.supp`. The property quantifies over all 2-factors and is vacuously true for a graph without 2-factors; the mission's goal pairs it with the snark property, and a supporting theorem shows that the witness graph has a 2-factor.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 4, Section 2 (2-factor); p. 11, §4.4, Refuted Conjecture 4.11; p. 29, Appendix 8.1 (heading)

import Mathlib
import Definitions.Def_SnarkGen_EdgeInsertion_EvenTwoFactor

namespace SnarkGen.OddFactors

variable {V : Type*}

open Classical in

/-- **All 2-factors of `G` consist of only odd cycles** (arXiv:1206.6690v3, p. 11, §4.4 and
Appendix 8.1, p. 29): for every 2-factor `F` of `G`, every connected component of `F` (a cycle,
whose length is its number of vertices) has an odd number of vertices. -/
def AllTwoFactorsOdd [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ F : SimpleGraph V, SnarkGen.EdgeInsertion.IsTwoFactor G F → ∀ c : F.ConnectedComponent, Odd (Nat.card c.supp)

end SnarkGen.OddFactors


