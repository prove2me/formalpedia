-- Prove2me | Definitions.Def_ZZ_SegProbe2
-- name    : ZZ_SegProbe2
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-26T13:59:53.874312+00:00
-- url     : https://prove2.me/theorems/8c90253a-0f63-4263-aaf9-73a22d1a7103
-- title:
--   seg probe 2
-- statement:
--   probe

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_Thm_BraidsLinksMCG_segment_coords

open BraidsLinksMCG
namespace BraidsLinksMCG

example (m : ℝ) (z : ℂ) (w : ℂ)
    (hw : w ∈ segment ℝ z (m + z.im * Complex.I)) : w.im = z.im := by
  have himxy : z.im = (m + z.im * Complex.I).im := by simp
  exact segment_const_im himxy w hw

end BraidsLinksMCG


