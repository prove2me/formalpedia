-- Prove2me | solution 1 for AlliancePortfolio.Sharing.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:11:36.998625+00:00
-- url     : https://prove2.me/submissions/9f425937-ba03-4481-94b3-65c95105b587

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_AlliancePortfolio_Sharing_Model
set_option autoImplicit false
open AlliancePortfolio.Sharing

theorem solution (V I πF πA : ℝ) (hI : 0 < I) (hV : πF + πA ≤ V) :
    SingleFeasible V I πF πA ↔ |πF - πA| ≤ V - I := by
  unfold SingleFeasible singlePayoff
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith
