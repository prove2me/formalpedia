-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.sg_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:20:33.751777+00:00
-- url     : https://prove2.me/submissions/deea57f9-dbbf-431f-9155-3c76703981e2

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (b : Bool) : sg (!b) = -sg b := by
  cases b <;> simp [sg]
end AaronsonAmbainis.Bridge
