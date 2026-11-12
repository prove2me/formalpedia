-- Prove2me | Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
-- name    : QEC_Distillation_Universality_HAngleUniversality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T15:04:26.6302+00:00
-- url     : https://prove2.me/theorems/1894ebdb-e434-4b52-82ea-b637ca9fe659
-- title:
--   HAngle Universality
-- statement:
--   Definitions and structural lemmas for HAngle Universality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/HAngleUniversality.lean

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Distillation
namespace OneQubitMagic
open GeneratedUniversality
theorem sqrt_seven_pos : 0 < Real.sqrt 7 :=
  Real.sqrt_pos.2 (by norm_num)
theorem sqrt_seven_sq : Real.sqrt 7 ^ 2 = 7 :=
  Real.sq_sqrt (by norm_num)
noncomputable def hAngle : Real :=
  Real.arccos (3 / 4)
noncomputable def hAngleAxis : UnitBlochAxis where
  x := -(Real.sqrt 2 + 1) / Real.sqrt 7
  y := 1 / Real.sqrt 7
  z := (1 - Real.sqrt 2) / Real.sqrt 7
  norm_sq := by
    field_simp [sqrt_seven_pos.ne']
    nlinarith [sqrt_two_mul_self, sqrt_seven_sq]
noncomputable def hAngleConjugateAxis : UnitBlochAxis where
  x := -hAngleAxis.y
  y := hAngleAxis.x
  z := hAngleAxis.z
  norm_sq := by
    nlinarith [hAngleAxis.norm_sq]
noncomputable def hAngleWord : SingleQubitGate :=
  ((hadamardGate * phaseGate) ^ 3) *
    ((hadamardGate * phaseShiftGate (-Real.pi / 4)) ^ 4) * phaseGate
noncomputable def hAngleConjugateWord : SingleQubitGate :=
  phaseGate * hAngleWord * phaseGate⁻¹
end OneQubitMagic
end Distillation
end QEC


