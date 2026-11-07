-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_Degeneracy
-- name    : QEC_Coding_Stabilizer_Degeneracy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:10:31.446446+00:00
-- url     : https://prove2.me/theorems/433154ab-f7c6-4fad-9f7a-811c2d3e6a19
-- title:
--   Degeneracy
-- statement:
--   Definitions and structural lemmas for Degeneracy, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Degeneracy.lean

import Definitions.Def_QEC_Coding_Stabilizer_Distance
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace StabilizerCode
universe u
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def SemanticallyDegenerateAtDistance
    (Q : SourceValidBinary ι) (d : Nat) : Prop :=
  SemanticStabilizerDistance Q d ∧
  ∃ E : Binary ι, ∃ c : Complex,
    ¬ BinaryUpToSign E (binaryOne (ι := ι)) ∧
    weight E < d ∧ c ≠ 0 ∧
    Semantics.DetectableOnWithScalar Q.1.code (toQubitOperator E) c
end StabilizerCode
end Coding
end QEC


