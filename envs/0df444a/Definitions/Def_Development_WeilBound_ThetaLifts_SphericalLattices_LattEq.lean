-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_LattEq
-- name    : Development_WeilBound_ThetaLifts_SphericalLattices_LattEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:54.294032+00:00
-- url     : https://prove2.me/theorems/35699d09-ff4d-4d34-9474-defdab5b51f5
-- title:
--   Latt Eq
-- statement:
--   Definitions and structural lemmas for Latt Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/LattEq.lean

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
open ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end PositivityTheory.Sph
end


