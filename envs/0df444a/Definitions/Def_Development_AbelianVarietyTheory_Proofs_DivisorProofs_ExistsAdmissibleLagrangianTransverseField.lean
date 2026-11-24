-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleLagrangianTransverseField
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleLagrangianTransverseField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:29.190452+00:00
-- url     : https://prove2.me/theorems/85c50abf-569f-4194-bd15-9bdb985e82f9
-- title:
--   Exists Admissible Lagrangian Transverse Field
-- statement:
--   Definitions and structural lemmas for Exists Admissible Lagrangian Transverse Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdmissibleLagrangianTransverseField.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory
def lagrRankOne {k : Type} [Field k] {n : ℕ} (S : Matrix (Fin n) (Fin n) k) (j : Fin n) :
    Matrix (Fin n) (Fin n) k :=
  Matrix.of fun a b => if a = j then S b j else 0
end GlobalTheory


