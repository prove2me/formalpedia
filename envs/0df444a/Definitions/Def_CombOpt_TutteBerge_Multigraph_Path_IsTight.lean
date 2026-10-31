-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsTight
-- name    : CombOpt_TutteBerge_Multigraph_Path_IsTight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:40.359356+00:00
-- url     : https://prove2.me/theorems/ba6a4421-bb2e-4535-b8ee-8b1eeaa588f6
-- title:
--   Tight odd circuit
-- statement:
--   An odd circuit $C$ of $G$ is **tight** if
--   $$
--   \nu(G)=\nu(G\times C)+\frac{|V(C)|-1}{2},
--   $$
--   that is, if inequality (5.2) holds with equality.
--
--   **Formalization Note** The equation is stated in $\mathbb Q$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 132 (PDF p. 140)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsOddCircuit
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_nodeSet
import Definitions.Def_CombOpt_TutteBerge_Multigraph_matchingNumber
import Definitions.Def_CombOpt_TutteBerge_Multigraph_shrink

namespace CombOpt.TutteBerge

/-- **A tight odd circuit.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 132 (PDF p. 140): "Let us call an odd circuit C of G *tight* if (5.2) holds with
equality", (5.2) being ν(G) ≥ ν(G × C) + (|V(C)| − 1)/2.

**Formalization Note.** The equation is stated in `ℚ` after casting, so `(|V(C)| − 1)/2` does not
truncate. For an odd circuit it is an integer anyway. -/
noncomputable def Multigraph.Path.IsTight {V E : Type*} {G : Multigraph V E} {x : V}
    (C : G.Path x x) : Prop :=
  C.IsOddCircuit ∧
    (G.matchingNumber : ℚ) =
      ((G.shrink C.nodeSet).matchingNumber : ℚ) + ((C.nodeSet.ncard : ℚ) - 1) / 2

end CombOpt.TutteBerge


