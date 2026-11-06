-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_Distance
-- name    : QEC_Coding_Stabilizer_Distance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:44:21.237023+00:00
-- url     : https://prove2.me/theorems/27bde072-b9a1-4fa4-9c12-49cf7b92a479
-- title:
--   Distance
-- statement:
--   Definitions and structural lemmas for Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Distance.lean

import Definitions.Def_QEC_Coding_Stabilizer_Detectability
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace StabilizerCode
universe u
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def SemanticStabilizerDistance (Q : SourceValidBinary ι) (d : Nat) : Prop :=
  ∃ E : Binary ι,
    ¬ Semantics.DetectableOn Q.1.code (toQubitOperator E) ∧
    weight E = d ∧
    ∀ F : Binary ι,
      ¬ Semantics.DetectableOn Q.1.code (toQubitOperator F) →
      d ≤ weight F
end StabilizerCode
end Coding
end QEC


