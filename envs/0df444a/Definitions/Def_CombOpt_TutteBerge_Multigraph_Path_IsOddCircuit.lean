-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsOddCircuit
-- name    : CombOpt_TutteBerge_Multigraph_Path_IsOddCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:41.542604+00:00
-- url     : https://prove2.me/theorems/6f0ee97f-86e4-4c7b-ba2e-2d95e1bbc2c7
-- title:
--   Odd circuit
-- statement:
--   An **odd circuit** is a circuit of odd length.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 130 (PDF p. 138)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsCircuit
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_length

namespace CombOpt.TutteBerge

/-- **An odd circuit.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 130 (PDF p. 138): the circuits of odd length ("a circuit of odd length 2k + 1"). -/
def Multigraph.Path.IsOddCircuit {V E : Type*} {G : Multigraph V E} {x : V} (C : G.Path x x) :
    Prop :=
  C.IsCircuit ∧ Odd C.length

end CombOpt.TutteBerge


