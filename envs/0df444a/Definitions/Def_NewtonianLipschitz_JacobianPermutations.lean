-- Prove2me | Definitions.Def_NewtonianLipschitz_JacobianPermutations
-- name    : NewtonianLipschitz_JacobianPermutations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:25:41.96854+00:00
-- url     : https://prove2.me/theorems/d9b90397-6156-449e-bae4-698ec6c98a73
-- title:
--   Jacobian Permutations
-- statement:
--   Definitions and structural lemmas for Jacobian Permutations, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NewtonianLipschitz
def cycleIndex (i : Fin 3) : Fin 3 :=
  if i = 0 then 1 else if i = 1 then 2 else 0
def cycleVec (x : Vec3) : Vec3 := ![x 1, x 2, x 0]
def swapYZIndex (i : Fin 3) : Fin 3 :=
  if i = 0 then 0 else if i = 1 then 2 else 1
def swapYZVec (x : Vec3) : Vec3 := ![x 0, x 2, x 1]
end NewtonianLipschitz


