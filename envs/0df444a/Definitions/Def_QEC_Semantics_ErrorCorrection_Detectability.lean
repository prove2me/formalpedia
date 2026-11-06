-- Prove2me | Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
-- name    : QEC_Semantics_ErrorCorrection_Detectability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:01:02.271492+00:00
-- url     : https://prove2.me/theorems/0c6ea6a3-3683-4dd9-adcb-80716189238c
-- title:
--   Detectability
-- statement:
--   Definitions and structural lemmas for Detectability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/Detectability.lean

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
noncomputable section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
def DetectableOnWithScalar
    (C : QuantumCode H) (E : Operator H) (c : Complex) : Prop :=
  ∀ x : H, x ∈ C.carrier →
    ∀ y : H, y ∈ C.carrier →
      inner Complex x (E y) = c * inner Complex x y
def DetectableOn (C : QuantumCode H) (E : Operator H) : Prop :=
  ∃ c : Complex, DetectableOnWithScalar C E c
end
end Semantics
end QEC


