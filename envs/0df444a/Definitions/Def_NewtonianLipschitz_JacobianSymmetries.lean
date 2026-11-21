-- Prove2me | Definitions.Def_NewtonianLipschitz_JacobianSymmetries
-- name    : NewtonianLipschitz_JacobianSymmetries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:24:35.953004+00:00
-- url     : https://prove2.me/theorems/a44b32d6-b57e-403b-bdeb-dafa59f8bfd6
-- title:
--   Jacobian Symmetries
-- statement:
--   Definitions and structural lemmas for Jacobian Symmetries, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSymmetries.lean

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NewtonianLipschitz
def coordinateAbs (x : Vec3) : Vec3 := fun i => |x i|
end NewtonianLipschitz


