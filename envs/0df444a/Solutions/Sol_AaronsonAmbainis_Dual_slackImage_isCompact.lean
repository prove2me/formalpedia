-- Prove2me | solution 1 for AaronsonAmbainis.Dual.slackImage_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:07.726512+00:00
-- url     : https://prove2.me/submissions/cdd4609c-511c-4b60-b3e3-032f8b93dbaa

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets
import Theorems.Thm_AaronsonAmbainis_Dual_massSet_isCompact
import Theorems.Thm_AaronsonAmbainis_Dual_slack_continuous

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (t : Finset ι → ℝ) (K : ℝ) :
    IsCompact (slack t '' massSet ι K) :=
  (massSet_isCompact K).image (slack_continuous t)
end AaronsonAmbainis.Dual
