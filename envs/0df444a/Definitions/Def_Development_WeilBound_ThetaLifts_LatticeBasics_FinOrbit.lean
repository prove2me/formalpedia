-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_FinOrbit
-- name    : Development_WeilBound_ThetaLifts_LatticeBasics_FinOrbit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:57:36.399431+00:00
-- url     : https://prove2.me/theorems/7a1ee451-1924-4c36-8103-a8f59d5356fd
-- title:
--   Fin Orbit
-- statement:
--   Definitions and structural lemmas for Fin Orbit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/FinOrbit.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_HermAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThK.Dbl.Herm
open scoped InnerProductSpace Cardinal
open PositivityTheory.ThKF.Abs Topology
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {P : Type} [AddCommGroup P] [Module ℂ P]
end GlobalTheory.ThK.Dbl.Herm
end


