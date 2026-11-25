-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExistsStatement
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExistsStatement
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:03:37.088504+00:00
-- url     : https://prove2.me/theorems/15d23266-e72b-5a57-bd52-39f87c4077f8
-- title:
--   Local Field Selfdual Measure Exists Statement
-- statement:
--   Definitions and structural lemmas for Local Field Selfdual Measure Exists Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalFieldSelfdualMeasureExistsStatement.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExists
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix


