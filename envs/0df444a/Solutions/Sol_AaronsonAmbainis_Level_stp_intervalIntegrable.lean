-- Prove2me | solution 1 for AaronsonAmbainis.Level.stp_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:20:24.241234+00:00
-- url     : https://prove2.me/submissions/945ffe1f-a2c4-461b-a8b1-b79fbfd34356

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral
import Theorems.Thm_AaronsonAmbainis_Level_stp_mono

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
namespace AaronsonAmbainis.Level
theorem _root_.solution (c a b : ℝ) :
    IntervalIntegrable (stp c) MeasureTheory.volume a b :=
  (stp_mono c).intervalIntegrable
end AaronsonAmbainis.Level
