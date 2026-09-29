-- Prove2me | Definitions.Def_TarchaBraids_left_interp_config_data_v1
-- name    : TarchaBraids_left_interp_config_data_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-21T09:11:37.332761+00:00
-- url     : https://prove2.me/theorems/01113162-c3ad-4b93-90be-1b3ac96b1f9f
-- title:
--   Tarcha left adjacent interpolation as an ordered configuration
-- statement:
--   The collision-free left interpolation between the adjacent three-half-twist word and the common outer-rotation path, packaged as an ordered configuration using the accepted injectivity theorem.
-- source:
--   Modular ordered-configuration layer for Tarcha's explicit adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_interp_injective_v1

namespace TarchaBraids

noncomputable section

open BraidsLinksMCG

def leftOuterInterpConfig {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : unitInterval) : OrderedConfig n :=
  ⟨leftOuterInterpFun n i j (u : ℝ) (q : ℝ),
    thm_3_15_adjacent_left_interp_injective_v1
      i j hji (u : ℝ) (q : ℝ) u.2.1 u.2.2 q.2.1 q.2.2⟩

end

end TarchaBraids


