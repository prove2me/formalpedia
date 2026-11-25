-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsCompactHaarMeasure
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsCompactHaarMeasure
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:57:42.66932+00:00
-- url     : https://prove2.me/theorems/2c22f8b0-5f96-5962-b1c1-e996dc65493c
-- title:
--   Exists Compact Haar Measure
-- statement:
--   Definitions and structural lemmas for Exists Compact Haar Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsCompactHaarMeasure.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupPropertiesStatement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
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
namespace GlobalTheory.HCXi
end GlobalTheory.HCXi


