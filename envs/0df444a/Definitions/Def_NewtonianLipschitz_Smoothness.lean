-- Prove2me | Definitions.Def_NewtonianLipschitz_Smoothness
-- name    : NewtonianLipschitz_Smoothness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:21:04.186411+00:00
-- url     : https://prove2.me/theorems/533399b3-7b0f-41b5-a32e-1456973fc0d7
-- title:
--   Smoothness
-- statement:
--   Definitions and structural lemmas for Smoothness, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Smoothness.lean

module
public import Definitions.Def_NewtonianLipschitz_Field
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped NNReal Topology InnerProductSpace
namespace NewtonianLipschitz
noncomputable def physicalNewtonianAcceleration
    (μ : ℝ) (q : PhysicalVec3) : PhysicalVec3 :=
  (-(μ) / ‖q‖ ^ 3) • q
end NewtonianLipschitz


