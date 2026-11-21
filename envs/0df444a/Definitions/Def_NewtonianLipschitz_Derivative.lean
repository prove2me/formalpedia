-- Prove2me | Definitions.Def_NewtonianLipschitz_Derivative
-- name    : NewtonianLipschitz_Derivative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:21:41.150032+00:00
-- url     : https://prove2.me/theorems/773922b3-9f92-44da-b349-dce16e861bc7
-- title:
--   Derivative
-- statement:
--   Definitions and structural lemmas for Derivative, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped NNReal Topology InnerProductSpace
namespace NewtonianLipschitz
noncomputable def NewtonianPointSource.radialCoefficient
    (c : NewtonianPointSource) (x : Vec3) : ℝ :=
  -(c.gravitationalParameter) / euclideanRadius x ^ 3
end NewtonianLipschitz


