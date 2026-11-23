-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIntegralMultipleBoundedPlaces
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIntegralMultipleBoundedPlaces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:00.829113+00:00
-- url     : https://prove2.me/theorems/0abc50da-0944-4c20-8087-5af919cdd3fc
-- title:
--   Exists Integral Multiple Bounded Places
-- statement:
--   Definitions and structural lemmas for Exists Integral Multiple Bounded Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIntegralMultipleBoundedPlaces.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
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
namespace GlobalTheory.CompanionTheory.Mass.MeanV.Den
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.CompanionTheory.Mass.MeanV.Den


