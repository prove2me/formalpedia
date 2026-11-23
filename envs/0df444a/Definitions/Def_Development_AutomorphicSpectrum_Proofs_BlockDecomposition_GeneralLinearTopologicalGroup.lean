-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GeneralLinearTopologicalGroup
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GeneralLinearTopologicalGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:28.56978+00:00
-- url     : https://prove2.me/theorems/caae0038-c5fd-48ae-94db-a6c9d9ff8d3c
-- title:
--   General Linear Topological Group
-- statement:
--   Definitions and structural lemmas for General Linear Topological Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GeneralLinearTopologicalGroup.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology
namespace GlobalTheory.CompanionTheory.RgEisTop
section Units
variable {M : Type} [TopologicalSpace M] [Monoid M] [ContinuousMul M] [T2Space M]
end Units
section Mat
variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  (ι : Type) [Fintype ι] [DecidableEq ι]
end Mat
open PositivityTheory.RgEis
end GlobalTheory.CompanionTheory.RgEisTop


