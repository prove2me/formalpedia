-- Prove2me | Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
-- name    : QEC_Distillation_Universality_SU2GeneratedDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:03:20.152572+00:00
-- url     : https://prove2.me/theorems/d006c14c-c206-4c1d-b219-67406eee143d
-- title:
--   SU2 Generated Density
-- statement:
--   Definitions and structural lemmas for SU2 Generated Density, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/SU2GeneratedDensity.lean

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Theorems.Thm_QEC_Distillation_axisCircle_add

set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
open GeneratedUniversality
def specialUnitaryGeneratedClosure (generators : Set SingleQubitGate) :
    Subgroup SingleQubitSpecialUnitary :=
  (generatedUnitarySubgroup generators).topologicalClosure.comap
    determinantOneSubgroup.subtype
noncomputable def axisCircleAddHom (axis : UnitBlochAxis) :
    AddMonoidHom (AddCircle (2 * Real.pi)) (Additive SingleQubitGate) where
  toFun t := Additive.ofMul (axisCircle axis t)
  map_zero' := by
    change Additive.ofMul (axisCircle axis 0) = Additive.ofMul 1
    rw [axisCircle_zero]
  map_add' t u := by
    change Additive.ofMul (axisCircle axis (t + u)) =
      Additive.ofMul (axisCircle axis t * axisCircle axis u)
    rw [axisCircle_add]
end Distillation
end QEC


