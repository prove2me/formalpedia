-- Prove2me | solution 1 for AaronsonAmbainis.Level.four_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:35:54.63781+00:00
-- url     : https://prove2.me/submissions/44e2978f-51c2-45eb-b0e9-36d682ba48d9

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution [Nonempty ι] :
    (4 : ℝ) ^ Fintype.card ι = 4 * 4 ^ (Fintype.card ι - 1) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  rw [← pow_succ']
  congr 1
  omega
end AaronsonAmbainis.Level
