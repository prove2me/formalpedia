-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqOfLamData
-- name    : CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqOfLamData
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:58:28.340364+00:00
-- url     : https://prove2.me/theorems/d85b41eb-02d9-5121-8551-ee1c94af2b52
-- title:
--   Nq Of Lam Data
-- statement:
--   Definitions and structural lemmas for Nq Of Lam Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/NqOfLamData.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace CompanionTheory.WaveGrid.Inhab
open Formalism.FourierDecayAlt Finset CompanionTheory.WaveGrid GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
def uP (u : ℕ → ℝ) (l n₀ : ℕ) : ℕ → ℝ := fun i => if i = l + 1 then u i + n₀ else u i
def uM (u : ℕ → ℝ) (l n₀ : ℕ) : ℕ → ℝ := fun i => if i = l then u i - n₀ else u i
noncomputable def lamX (x : ℤ) : Fin (2 * 0 + 3 + 1) → ℝ := ![(x : ℝ) + 1 / 2, -79 / 2, -119 / 2, -159 / 2]
noncomputable def uX : ℕ → ℝ := fun i => if i = 1 then 80 else if i = 2 then 0 else -50
noncomputable def cfg₁ : Sz.Cfg := { cfg₀ with a := 801 / 2 }
noncomputable def Pc : M.Par := cfgPar cfg₁ 0 1 1 (fun _ => 0) (fun i => if i = 1 then 1 else 0)
end CompanionTheory.WaveGrid.Inhab


