-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg
-- name    : Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:10.9028+00:00
-- url     : https://prove2.me/theorems/62b9b824-e414-419d-ab3c-7e7e4ebab2ea
-- title:
--   Siegel Transport Alg
-- statement:
--   Definitions and structural lemmas for Siegel Transport Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAlg.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β ν ν' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν]
  [Fintype ν'] [DecidableEq ν']
end PositivityTheory.ThK.SiegelT


