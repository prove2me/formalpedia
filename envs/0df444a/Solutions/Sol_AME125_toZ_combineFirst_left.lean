-- Prove2me | solution 1 for AME125.toZ_combineFirst_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:03:45.911301+00:00
-- url     : https://prove2.me/submissions/e1c0114d-316f-421a-80b3-7d9796c97ce4

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
public import Theorems.Thm_OpenQuantumProblem35_combineFirst_leftIndex
attribute [local simp] OpenQuantumProblem35.combineFirst_leftIndex



set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix
namespace AME125
theorem _root_.solution {n m : ℕ} (hm : m ≤ n) (a : Config m 5) (z : Config (n - m) 5)
    (i : Fin m) : toZ (combineFirst m hm a z) (leftIndex hm i) = toZ a i :=
  combineFirst_leftIndex hm a z i
end AME125
