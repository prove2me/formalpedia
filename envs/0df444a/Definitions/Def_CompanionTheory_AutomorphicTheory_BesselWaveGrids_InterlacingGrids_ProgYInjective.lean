-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_ProgYInjective
-- name    : CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_ProgYInjective
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:08:28.690195+00:00
-- url     : https://prove2.me/theorems/044f7a0e-9a98-4c98-b9fa-d160c8dc158f
-- title:
--   Prog YInjective
-- statement:
--   Definitions and structural lemmas for Prog YInjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/ProgYInjective.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
open Finset
noncomputable def progY (y0 : ℝ) (M : ℕ) : Finset ℝ := (range M).image fun i : ℕ => y0 + 5 * (i : ℝ)
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid


