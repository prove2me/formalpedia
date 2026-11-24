-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_VolumeIsAddHaar
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_VolumeIsAddHaar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:15.35639+00:00
-- url     : https://prove2.me/theorems/ea44a72f-b73c-41f2-b850-c5d4fd9bfe3e
-- title:
--   Volume Is Add Haar
-- statement:
--   Definitions and structural lemmas for Volume Is Add Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/FockSpaces/VolumeIsAddHaar.lean

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
open MeasureTheory
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {G H K : Type}
  [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace K] [AddCommGroup K] [IsTopologicalAddGroup K] [LocallyCompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K]
end PositivityTheory.SiegelWeilFormula.KFock
end


