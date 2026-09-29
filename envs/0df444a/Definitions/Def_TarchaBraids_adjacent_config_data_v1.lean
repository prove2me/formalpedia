-- Prove2me | Definitions.Def_TarchaBraids_adjacent_config_data_v1
-- name    : TarchaBraids_adjacent_config_data_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-21T08:24:33.5028+00:00
-- url     : https://prove2.me/theorems/11619c5c-0742-4a1f-b1ce-b4f3762162bc
-- title:
--   Tarcha adjacent braid ordered configuration paths
-- statement:
--   Ordered-configuration lifts of the left and right adjacent braid words and the common outer-rotation path, using the accepted raw-map injectivity theorem.
-- source:
--   Modular configuration layer for the explicit proof of Tarcha's adjacent Artin braid relation.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_injective_v1

namespace TarchaBraids

noncomputable section

open BraidsLinksMCG

def leftBraidConfig (n : ℕ) (i j : Fin (n - 1)) (q : ℝ) : OrderedConfig n :=
  ⟨leftBraidFun n i j q,
    thm_3_15_adjacent_raw_injective_v1.1 i j q⟩

def rightBraidConfig (n : ℕ) (i j : Fin (n - 1)) (q : ℝ) : OrderedConfig n :=
  ⟨rightBraidFun n i j q,
    thm_3_15_adjacent_raw_injective_v1.2.1 i j q⟩

def outerRotateConfig {n : ℕ} (i : Fin (n - 1)) (hi2 : (i : ℕ) + 2 < n)
    (q : ℝ) : OrderedConfig n :=
  ⟨outerRotateFun n i q,
    thm_3_15_adjacent_raw_injective_v1.2.2 i q hi2⟩

end

end TarchaBraids


