-- Prove2me | Definitions.Def_SnarkGen_Zhang_ZhangConjecture
-- name    : SnarkGen_Zhang_ZhangConjecture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:21.845975+00:00
-- url     : https://prove2.me/theorems/14cef5e2-9a00-4eca-a0b4-6b03170d0ebc
-- title:
--   Zhang's Conjecture 4.1: the Petersen graph is the only cyclically 5-edge-connected permutation snark
-- statement:
--   **Conjecture 4.1 (Zhang).** Let $G$ be a cubic cyclically $5$-edge-connected permutation graph. If $G$ is a snark, then $G$ must be the Petersen graph.
--
--   This definition is the proposition that the conjecture holds: for every finite simple graph $H$,
--   $$
--   H \text{ cubic},\ H \text{ cyclically 5-edge connected},\ H \text{ a permutation graph},\ H \text{ a snark} \;\Longrightarrow\; H \cong P,
--   $$
--   where $P$ is the Petersen graph and $\cong$ denotes graph isomorphism. The paper refutes the conjecture (Observation 4.2); the mission's goal is the negation of this proposition.
--
--   All hypotheses of the printed conjecture are kept, including "cubic", which is already implied by "permutation graph" and by "snark".
--
--   **Formalization Note** The quantifier ranges over all finite vertex types `W : Type` (universe 0, which contains `Fin n` for every $n$) and all simple graphs on them. "Must be the Petersen graph" is read as `Nonempty (H ≃g petersen)`, the existence of a graph isomorphism, since $H$ and $P$ live on different vertex types. Degrees use classical decidability.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 9, Refuted Conjecture 4.1 (Zhang [52])

import Mathlib
import Definitions.Def_SnarkGen_Zhang_CyclicallyEdgeConnected
import Definitions.Def_SnarkGen_Zhang_IsSnark
import Definitions.Def_SnarkGen_Zhang_IsPermutationGraph
import Definitions.Def_SnarkGen_Zhang_petersen

namespace SnarkGen.Zhang

open Classical in
/-- Zhang's Conjecture 4.1 (p. 9): every cubic cyclically 5-edge-connected permutation graph
that is a snark is isomorphic to the Petersen graph. -/
def ZhangConjecture : Prop :=
  ∀ (W : Type) [Fintype W] (H : SimpleGraph W),
    H.IsRegularOfDegree 3 → CyclicallyEdgeConnected H 5 → IsPermutationGraph H → IsSnark H →
      Nonempty (H ≃g petersen)

end SnarkGen.Zhang


