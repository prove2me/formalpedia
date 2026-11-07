-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.sg_mul_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:20:48.076731+00:00
-- url     : https://prove2.me/submissions/3bb0fdc3-8cfd-4b49-b0f7-79bb1ef12667

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {a b : Bool} (h : a ≠ b) : sg a * sg b = -1 := by
  cases a <;> cases b <;> simp_all [sg]
end AaronsonAmbainis.Bridge
