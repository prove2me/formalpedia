-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_LandauIteratedDerivatives_LandauL
-- name    : Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_LandauIteratedDerivatives_LandauL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:28.697384+00:00
-- url     : https://prove2.me/theorems/a838eca5-3a01-4ce7-a6a8-a05bbae93adb
-- title:
--   Landau L
-- statement:
--   Definitions and structural lemmas for Landau L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/LandauIteratedDerivatives/LandauL.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
namespace PositivityTheory.RgJS.LandauNonnegativeDirichletSeries
end PositivityTheory.RgJS.LandauNonnegativeDirichletSeries
namespace PositivityTheory.RgJS
open LandauNonnegativeDirichletSeries
end PositivityTheory.RgJS


