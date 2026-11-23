-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousRhoApply
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousRhoApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:52.601019+00:00
-- url     : https://prove2.me/theorems/00849b7e-94f7-4056-87ac-16dfbd2f5bac
-- title:
--   Continuous Rho Apply
-- statement:
--   Definitions and structural lemmas for Continuous Rho Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousRhoApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open scoped Matrix Real RealInnerProductSpace InnerProductSpace
namespace GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
end GlobalTheory.RealWeil


