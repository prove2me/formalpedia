-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:23.916296+00:00
-- url     : https://prove2.me/theorems/4b39fbed-7cdd-47da-925d-c93b143aa2e5
-- title:
--   Diag Part Mul Diag Part
-- statement:
--   Definitions and structural lemmas for Diag Part Mul Diag Part, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DiagPartMulDiagPart.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
namespace GlobalTheory.RootEx.BlockLevi
variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
def diagPart (f : ι → ℕ) (A : Matrix ι ι k) : Matrix ι ι k :=
  Matrix.of fun r s => if f r = f s then A r s else 0
end GlobalTheory.RootEx.BlockLevi


