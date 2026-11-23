-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:14.138741+00:00
-- url     : https://prove2.me/theorems/8f83a411-18e1-4264-8400-10a04391504f
-- title:
--   Haar Product Closed Compact Holds
-- statement:
--   Definitions and structural lemmas for Haar Product Closed Compact Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Pointwise
namespace GlobalTheory.CompanionTheory.HaarPK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
def transl (M : Subgroup G) (η : Measure M) (x : G) : Measure G := η.map (fun m : M => x * m)
end GlobalTheory.CompanionTheory.HaarPK
end


