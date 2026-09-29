-- Prove2me | Definitions.Def_TarchaBraids_right_interp_config_data_v1
-- name    : TarchaBraids_right_interp_config_data_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-21T11:31:02.600113+00:00
-- url     : https://prove2.me/theorems/1332790f-f84c-4c64-8308-e290a27f502a
-- title:
--   Tarcha right adjacent interpolation as an ordered configuration
-- statement:
--   The collision-free right interpolation between the adjacent three-half-twist word and the common outer-rotation path, packaged as an ordered configuration using the accepted injectivity theorem.
-- source:
--   Modular ordered-configuration layer for Tarcha's explicit adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_interp_injective_v1

namespace TarchaBraids

noncomputable section

open BraidsLinksMCG

def rightOuterInterpConfig {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : unitInterval) : OrderedConfig n :=
  ⟨rightOuterInterpFun n i j (u : ℝ) (q : ℝ),
    thm_3_15_adjacent_right_interp_injective_v1
      i j hji (u : ℝ) (q : ℝ) u.2.1 u.2.2 q.2.1 q.2.2⟩

end

end TarchaBraids


