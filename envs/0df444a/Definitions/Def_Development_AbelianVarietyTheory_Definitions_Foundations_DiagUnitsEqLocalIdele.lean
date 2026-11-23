-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:31.52918+00:00
-- url     : https://prove2.me/theorems/318f5474-0ef5-4f1f-9d7c-31976679b04a
-- title:
--   Diag Units Eq Local Idele
-- statement:
--   Definitions and structural lemmas for Diag Units Eq Local Idele, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
namespace GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]
example : IsTopologicalGroup (Ideles L) := inferInstance
example : CommGroup (Ideles L) := inferInstance
end GlobalTheory.Mem.Chr.Model


