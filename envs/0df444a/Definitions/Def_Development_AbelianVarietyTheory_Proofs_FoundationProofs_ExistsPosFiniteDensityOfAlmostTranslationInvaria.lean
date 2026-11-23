-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsPosFiniteDensityOfAlmostTranslationInvaria
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsPosFiniteDensityOfAlmostTranslationInvaria
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:50.1152+00:00
-- url     : https://prove2.me/theorems/4cfa1440-1a3a-42d5-8b5e-71a5f682f37e
-- title:
--   Exists Pos Finite Density Of Almost Translation Invaria
-- statement:
--   Definitions and structural lemmas for Exists Pos Finite Density Of Almost Translation Invaria, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsPosFiniteDensityOfAlmostTranslationInvaria.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Metric Set
namespace GlobalTheory
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
end
end GlobalTheory


