-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PoissonSummationGaussian
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PoissonSummationGaussian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:34.683733+00:00
-- url     : https://prove2.me/theorems/7259b177-5f4c-4fe8-9fb7-c21716ceff97
-- title:
--   Poisson Summation Gaussian
-- statement:
--   Definitions and structural lemmas for Poisson Summation Gaussian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PoissonSummationGaussian.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Core.PoiLat
variable {κ : Type} [Fintype κ] [DecidableEq κ]
end GlobalTheory.CompanionTheory.SW.Core.PoiLat


