-- Prove2me | Definitions.Def_TarchaBraids_adjacent_outer_loop_v1
-- name    : TarchaBraids_adjacent_outer_loop_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-21T09:39:29.011774+00:00
-- url     : https://prove2.me/theorems/43d08bdb-9107-4f25-8d53-46d0542cdab9
-- title:
--   Tarcha adjacent common outer-rotation loop
-- statement:
--   The common outer-rotation loop used as the comparison path for the two adjacent three-half-twist words.
-- source:
--   Modular common-loop layer extracted from Tarcha's adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_config_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_config_continuous_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_zero_endpoints_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_one_endpoint_v1

namespace TarchaBraids

noncomputable section

open BraidsLinksMCG

def outerRotateLoop {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) : Path (baseUnordered n) (baseUnordered n) := by
  have hi2 : (i : ℕ) + 2 < n := by
    have hj := j.isLt
    omega
  exact
    { toFun := fun q => configProj n (outerRotateConfig i hi2 (q : ℝ))
      continuous_toFun :=
        (configProj n).continuous.comp
          ((thm_3_15_adjacent_config_continuous_v1.2.2 i hi2).comp continuous_subtype_val)
      source' := by
        change configProj n (outerRotateConfig i hi2 0) = configProj n (baseOrdered n)
        apply congrArg (configProj n)
        apply Subtype.ext
        exact thm_3_15_adjacent_raw_zero_endpoints_v1.2.2 n i
      target' := by
        change configProj n (outerRotateConfig i hi2 1) = configProj n (baseOrdered n)
        have hfun := thm_3_15_adjacent_outer_one_endpoint_v1 i j hji hi2
        have h : configProj n (baseOrdered n) =
            configProj n (outerRotateConfig i hi2 1) := by
          apply Quotient.sound
          refine ⟨Equiv.swap (strandIdx i) (strandIdxSucc j), ?_⟩
          exact hfun
        exact h.symm }

end

end TarchaBraids


