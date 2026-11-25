-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
-- name    : CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:36:04.289797+00:00
-- url     : https://prove2.me/theorems/fd4285ec-297c-590b-853e-7d86c853c112
-- title:
--   Cfg Tie
-- statement:
--   Definitions and structural lemmas for Cfg Tie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset
noncomputable def cfgPar (c : Sz.Cfg) (r : ℕ) (T T' : ℝ) (de de' : ℕ → ℝ) : M.Par := ⟨c.k, r, T, T', c.u de, c.u de'⟩
section cfg
variable (c : Sz.Cfg)
end cfg
noncomputable def cfg₀ : Sz.Cfg where
  k := 4
  m := 2
  Del := 15
  vlast := 0
  b := fun j => (j : ℝ) + 1
  a := 400
  top := false
  bp := 0
end CompanionTheory.WaveGrid


