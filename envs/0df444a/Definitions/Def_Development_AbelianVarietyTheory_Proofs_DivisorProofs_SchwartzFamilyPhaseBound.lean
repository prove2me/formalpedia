-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFamilyPhaseBound
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFamilyPhaseBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:03.3889+00:00
-- url     : https://prove2.me/theorems/eb92a662-de9e-4566-930c-b8ed99fb5f1b
-- title:
--   Schwartz Family Phase Bound
-- statement:
--   Definitions and structural lemmas for Schwartz Family Phase Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFamilyPhaseBound.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
namespace GlobalTheory.CharFamily
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
end GlobalTheory.CharFamily


