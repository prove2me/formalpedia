-- Prove2me | solution 1 for AME125.toZ_combineFirst_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:04:41.292921+00:00
-- url     : https://prove2.me/submissions/840d0ca2-0d92-48a5-8cb5-7ed3a1f0c855

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_rightIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_rightIndex



set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix
namespace AME125
theorem _root_.solution {n m : ℕ} (hm : m ≤ n) (a : Config m 5) (z : Config (n - m) 5)
    (j : Fin (n - m)) : toZ (combineFirst m hm a z) (rightIndex hm j) = toZ z j :=
  combineFirst_rightIndex hm a z j
end AME125
