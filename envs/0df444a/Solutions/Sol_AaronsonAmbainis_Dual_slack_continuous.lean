-- Prove2me | solution 1 for AaronsonAmbainis.Dual.slack_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:48.806801+00:00
-- url     : https://prove2.me/submissions/ba661068-6aed-40e1-a722-fc343be5670e

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Sets

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (t : Finset ι → ℝ) : Continuous (slack t) :=
  continuous_pi fun _ =>
    (continuous_finsetSum _ fun i _ => continuous_apply i).sub continuous_const
end AaronsonAmbainis.Dual
