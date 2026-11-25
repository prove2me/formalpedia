-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PairOKOfInterlace
-- name    : CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PairOKOfInterlace
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T03:08:19.315081+00:00
-- url     : https://prove2.me/theorems/794bc5ed-758c-4ec0-9f4f-e17874674cad
-- title:
--   Pair OKOf Interlace
-- statement:
--   Definitions and structural lemmas for Pair OKOf Interlace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/InterlacingGrids/PairOKOfInterlace.lean

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
def Pst (k r : ℕ) (lam : ℕ → ℝ) (c Y : ℝ) : ℝ := ∏ s ∈ Icc 1 (k + 2 * r + 1), (|Y + lam s| + c)
def PairOK (k : ℕ) (lam v : ℕ → ℝ) (e : ℕ) (x : ℝ) : Prop :=
  ∀ s, 1 ≤ s → s ≤ k - 1 → s ≠ e →
    (x < lam s → lam s + 1 / 2 ≤ v s) ∧ (lam s ≤ x → v (s + 1) ≤ lam s - 1 / 2)
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid


