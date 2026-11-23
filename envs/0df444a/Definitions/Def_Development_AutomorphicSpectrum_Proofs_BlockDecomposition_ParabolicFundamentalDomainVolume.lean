-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicFundamentalDomainVolume
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicFundamentalDomainVolume
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:12.392803+00:00
-- url     : https://prove2.me/theorems/1bcec3e9-cda5-4b0b-ad64-4b4228c7f75c
-- title:
--   Parabolic Fundamental Domain Volume
-- statement:
--   Definitions and structural lemmas for Parabolic Fundamental Domain Volume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ParabolicFundamentalDomainVolume.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
namespace GlobalTheory.CompanionTheory.SplitExtLat
end GlobalTheory.CompanionTheory.SplitExtLat


