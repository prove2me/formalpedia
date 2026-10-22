-- Prove2me | solution 1 for AlliancePortfolio.Sharing.single_alliance_only_if
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:53:13.298591+00:00
-- url     : https://prove2.me/submissions/1633faf1-c805-4582-99b2-4b760c09f0b4

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_AlliancePortfolio_Sharing_Model
set_option autoImplicit false

open AlliancePortfolio.Sharing

theorem solution (V I πF : ℝ) (hI : 0 < I) (hπF : 0 ≤ πF) (hV : πF ≤ V) :
    SingleFeasible V I πF 0 → πF ≤ V - I := by
  rintro ⟨_, h⟩
  unfold singlePayoff at h
  linarith
