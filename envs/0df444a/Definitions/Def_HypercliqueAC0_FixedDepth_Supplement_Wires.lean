-- Prove2me | Definitions.Def_HypercliqueAC0_FixedDepth_Supplement_Wires
-- name    : HypercliqueAC0_FixedDepth_Supplement_Wires
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:26:26.958735+00:00
-- url     : https://prove2.me/theorems/df2ac3a7-b4fa-4ca4-9d13-4cbff5ba5d09
-- title:
--   The wire size $W(C)$ of a De Morgan circuit
-- statement:
--   Let $C$ be a De Morgan circuit: a directed acyclic graph whose inputs are literals and constants and whose gates compute AND or OR of arbitrary fan-in. Its **wire size** $W(C)$ is the number of edges of the underlying graph, that is, the total fan-in
--
--   $$W(C)=\sum_{\alpha\text{ gate of }C}\operatorname{fan\text{-}in}(\alpha).$$
--
--   Every input of a gate, whether a literal, a constant or another gate, contributes one wire. The gates themselves are not counted, so $W(C)$ differs from the size "gates plus wires". The wire size is the complexity measure of the depth-three lower bound for $2\text{-}\mathsf{OV}$.
--
--   **Formalization Note** The circuit is the published `MantriCVQ.ACCircuit`, a list of gates each with a list of inputs; $W(C)$ is the sum of the lengths of these input lists. A repeated entry in an input list counts as a separate wire.
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.10 (PDF p.12), §3.2 Boolean Circuits (wire size W(C))

import Mathlib
import Definitions.Def_MantriCVQ_ACCircuit

namespace HypercliqueAC0.FixedDepth.Supplement

/-- The wire size `W(C)` (§3.2, p. 10, PDF 12): the number of edges of the circuit's underlying
graph, i.e. the total fan-in of its gates. Every entry of a gate's input list (a literal, a
constant or an earlier gate) is one wire. Unlike `MantriCVQ.ACCircuit.size`, the gates themselves
are not counted. -/
def wires {V : Type} (C : MantriCVQ.ACCircuit V) : ℕ :=
  (C.gates.map (fun g => g.inputs.length)).sum

end HypercliqueAC0.FixedDepth.Supplement


