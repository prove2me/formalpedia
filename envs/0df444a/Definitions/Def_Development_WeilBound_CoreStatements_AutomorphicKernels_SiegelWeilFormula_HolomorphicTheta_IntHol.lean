-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_HolomorphicTheta_IntHol
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_HolomorphicTheta_IntHol
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:11:59.545894+00:00
-- url     : https://prove2.me/theorems/2219ab59-e6b6-4a51-bc52-bfef886f8262
-- title:
--   Int Hol
-- statement:
--   Definitions and structural lemmas for Int Hol, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/HolomorphicTheta/IntHol.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Set
namespace PositivityTheory.SiegelWeilFormula.Holtb
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
end PositivityTheory.SiegelWeilFormula.Holtb


