-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_MemOrbitSelf
-- name    : Development_AutomorphicSpectrum_Proofs_AlgebraProofs_MemOrbitSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:34.947526+00:00
-- url     : https://prove2.me/theorems/c4452f0f-63ed-4433-a659-ff5a445465a2
-- title:
--   Mem Orbit Self
-- statement:
--   Definitions and structural lemmas for Mem Orbit Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/MemOrbitSelf.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
namespace GlobalTheory.CompanionTheory.FreeQuotProof
end GlobalTheory.CompanionTheory.FreeQuotProof


