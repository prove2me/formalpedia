-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExists
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExists
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:39.62917+00:00
-- url     : https://prove2.me/theorems/cd23844b-bdf1-41c7-8a83-5cc1edafa695
-- title:
--   Local Field Selfdual Measure Exists
-- statement:
--   Definitions and structural lemmas for Local Field Selfdual Measure Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalFieldSelfdualMeasureExists.lean

import Mathlib
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
set_option maxSynthPendingDepth 1
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.LocInv
open GroundTheory.LocalField ValuativeRel MeasureTheory Topology Filter
open scoped NNReal ENNReal
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
end GlobalTheory.CompanionTheory.SW.LocInv
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix


