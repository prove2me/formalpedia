-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.sg_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:57:32.088138+00:00
-- url     : https://prove2.me/submissions/88fbd099-f235-42dc-b95c-88c238f0ef72

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (b : Bool) : sg b * sg b = 1 := by
  cases b <;> simp [sg]
end AaronsonAmbainis.Bridge
