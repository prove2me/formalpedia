-- Prove2me | Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
-- name    : QEC_Semantics_ErrorCorrection_KnillLaflamme
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:00:50.891251+00:00
-- url     : https://prove2.me/theorems/0b6c5a6e-ae92-4b7a-95a7-9e2915a99429
-- title:
--   Knill Laflamme
-- statement:
--   Definitions and structural lemmas for Knill Laflamme, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KnillLaflamme.lean

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
noncomputable section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
def KnillLaflammeMatrixConditionWithScalar
    (C : QuantumCode H) (errors : Set (Operator H))
    (scalar : Operator H → Operator H → Complex) : Prop :=
  ∀ ⦃E : Operator H⦄, E ∈ errors →
    ∀ ⦃F : Operator H⦄, F ∈ errors →
      ∀ x : H, x ∈ C.carrier →
        ∀ y : H, y ∈ C.carrier →
          inner Complex (E x) (F y) = scalar E F * inner Complex x y
def KnillLaflammeProjectorConditionWithScalar
    (C : QuantumCode H) (errors : Set (Operator H))
    (scalar : Operator H → Operator H → Complex) : Prop :=
  ∀ ⦃E : Operator H⦄, E ∈ errors →
    ∀ ⦃F : Operator H⦄, F ∈ errors →
      (C.projector.comp ((LinearMap.adjoint E).comp F)).comp C.projector =
        scalar E F • C.projector
def KnillLaflammeProjectorEquation
    (C : QuantumCode H) (errors : Set (Operator H)) : Prop :=
  ∃ scalar : Operator H → Operator H → Complex,
    KnillLaflammeProjectorConditionWithScalar C errors scalar
namespace KnillLaflamme
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
end KnillLaflamme
end
end Semantics
end QEC


