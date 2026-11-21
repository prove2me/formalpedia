-- Prove2me | Definitions.Def_NewtonianLipschitz_SafePlaneReduction
-- name    : NewtonianLipschitz_SafePlaneReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:48:10.883956+00:00
-- url     : https://prove2.me/theorems/c8f6e927-a500-4ebc-a88c-64c536d953ac
-- title:
--   Safe Plane Reduction
-- statement:
--   Definitions and structural lemmas for Safe Plane Reduction, from alexodas and contributors's pinned Sharp Newtonian field Lipschitz bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/SafePlaneReduction.lean

module
public import Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NewtonianLipschitz
abbrev oneSourceSafePlaneFiveFourthBound : Prop :=
  ∀ (c : NewtonianPointSource) (x y : Vec3)
    (d : ℝ) (i : Fin 3),
    0 < d →
    x i = y i →
    (d ≤ x i ∨ x i ≤ -d) →
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) *
        (c.gravitationalParameter * (5 / 4 : ℝ))) * ‖x - y‖
end NewtonianLipschitz


