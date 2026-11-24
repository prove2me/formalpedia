-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_ExistsVBallSubset
-- name    : Development_WeilBound_ThetaLifts_SphericalLattices_ExistsVBallSubset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:06.844732+00:00
-- url     : https://prove2.me/theorems/8e34ec9b-6b3b-4bb8-8ef4-ba72cfa1a1d8
-- title:
--   Exists VBall Subset
-- statement:
--   Definitions and structural lemmas for Exists VBall Subset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/ExistsVBallSubset.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_LatDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.Sph
open ValuativeRel Topology
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def vBall {m p : Type} (r : k) : Set (Matrix m p k) :=
  {Z | ∀ i j, valuation k (Z i j) ≤ valuation k r}
end PositivityTheory.Sph
end


