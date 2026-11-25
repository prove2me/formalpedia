-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_QwBound
-- name    : CompanionTheory_AutomorphicTheory_BesselWaveGrids_QwBound
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T03:07:30.07881+00:00
-- url     : https://prove2.me/theorems/638ca310-e207-41e3-b7e7-a11b9edebbf2
-- title:
--   Qw Bound
-- statement:
--   Definitions and structural lemmas for Qw Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/QwBound.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt
noncomputable def fac (l : C.Letter) (y : ℝ) : ℝ :=
  if l.1 then (y - l.2 + 1) / (y - l.2) else (l.2 - y) / (l.2 - y - 1)
noncomputable def facW {S : Type} (l : Wd.Letter ℂ S) (Y : ℂ) : ℂ :=
  if l.plus then (Y - l.pt + 1) / (Y - l.pt) else (l.pt - Y) / (l.pt - Y - 1)
end CompanionTheory.WaveGrid


