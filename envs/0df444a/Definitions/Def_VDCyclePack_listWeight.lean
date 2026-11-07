-- Prove2me | Definitions.Def_VDCyclePack_listWeight
-- name    : VDCyclePack_listWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:10:26.692304+00:00
-- url     : https://prove2.me/theorems/1a0fefc6-dcae-4b9b-a286-d7f81b041d3f
-- title:
--   The weighting given by an explicit weighted list of cycles
-- statement:
--   For a list of (vertex list, rational weight) entries, the weight of a subgraph $C$ is the sum of the weights of the entries whose vertex list represents $C$, and $0$ if there is none.
--
--   This turns the explicit output of Lemma 4.1 and the input of Theorem 4.2 into a weighting $x$ of the cycles.
--
--   **Formalization Note** A cycle listed several times receives the sum of its weights.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 4.1, p.11

import Mathlib
import Definitions.Def_VDCyclePack_Represents

namespace VDCyclePack

open Classical in
/-- **The weighting given by an explicit weighted list of cycles.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 4.1, p.11: "an optimal fractional packing of G, given as an explicit list of
polynomially many cycles with positive rational weights".

For a list `ws` of (vertex list, rational weight) entries, `listWeight I ws C` is the sum of the
weights of the entries whose vertex list represents the subgraph `C`.

**Formalization Note.** If a cycle is listed several times its weights add up; a subgraph that no
entry represents gets weight `0`. -/
noncomputable def listWeight (I : GraphInst) (ws : List (List ℕ × ℚ)) (C : I.toGraph.Subgraph) : ℝ :=
  ((ws.filter fun e => decide (Represents I e.1 C)).map fun e => (e.2 : ℝ)).sum

end VDCyclePack


