-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuousStatement
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuousStatement
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:49:50.360927+00:00
-- url     : https://prove2.me/theorems/9a7c85ae-2baf-5b16-95ab-a4d2a3e7957f
-- title:
--   Gram Positive Volume Continuous Statement
-- statement:
--   Definitions and structural lemmas for Gram Positive Volume Continuous Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GramPositiveVolumeContinuousStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder


