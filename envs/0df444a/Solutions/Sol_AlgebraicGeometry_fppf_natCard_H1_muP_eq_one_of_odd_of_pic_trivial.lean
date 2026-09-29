-- Prove2me | solution 1 for AlgebraicGeometry.fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6f58a2b6-3b56-5fde-a671-4aa3e313e003

import Definitions.Def_AlgebraicGeometry_FppfKummerCalculus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial
p2m_open "CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry"
theorem solution (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hH1Gm : Nat.card (FppfCohomologyLES.FppfH FppfKummerSES.GmAbelianSheafLifted.{0} 1) = 1) :
    Nat.card (FppfCohomologyLES.FppfH (FppfKummerSES.muPAbelianSheafLifted.{0} p) 1) = 1 := by
  have hne : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hodd
    omega
  have h := FppfBigSiteH0Gm.kummer_h1_card_value_of_pic_trivial p hp hH1Gm
  rw [if_neg hne] at h
  exact h

end S_AlgebraicGeometry_fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial
end P2MW
export P2MW.S_AlgebraicGeometry_fppf_natCard_H1_muP_eq_one_of_odd_of_pic_trivial (solution)
