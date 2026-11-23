-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:07.925405+00:00
-- url     : https://prove2.me/theorems/29e7ab47-d052-484e-8b89-97b9b21af78f
-- title:
--   Exists Schwartz Translate
-- statement:
--   Definitions and structural lemmas for Exists Schwartz Translate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSchwartzTranslate.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace
namespace GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
def rhoSch (w : l ⊕ l → ℝ) : Sch l →L[ℂ] Sch l :=
  SchwartzMap.smulLeftCLM ℂ (phase w) ∘L SchwartzMap.compSubConstCLM ℂ (-pPart w)
end GlobalTheory.RealWeil


