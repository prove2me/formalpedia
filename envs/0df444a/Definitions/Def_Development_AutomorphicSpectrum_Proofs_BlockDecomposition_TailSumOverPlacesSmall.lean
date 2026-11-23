-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmall
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmall
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:13.951136+00:00
-- url     : https://prove2.me/theorems/d2fce4c1-6ec9-4770-95c4-d371a582296d
-- title:
--   Tail Sum Over Places Small
-- statement:
--   Definitions and structural lemmas for Tail Sum Over Places Small, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TailSumOverPlacesSmall.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SummableOneDivAbsNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
namespace GlobalTheory.CompanionTheory.Mass.MeanV
end GlobalTheory.CompanionTheory.Mass.MeanV


