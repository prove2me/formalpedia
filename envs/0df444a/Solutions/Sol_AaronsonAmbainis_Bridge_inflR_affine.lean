-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.inflR_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:12.057797+00:00
-- url     : https://prove2.me/submissions/eb959a69-e609-423e-98a8-10650a4cb3ed

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Affine

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (a b : ℝ) (g : Cube ι → ℝ) (j : ι) :
    inflR (fun x => a + b * g x) j = b ^ 2 * inflR g j := by
  have h : ∀ x : Cube ι, ((a + b * g x - (a + b * g (flipSet x {j}))) / 2) ^ 2
      = b ^ 2 * ((g x - g (flipSet x {j})) / 2) ^ 2 := fun x => by ring
  simp only [inflR, h]
  rw [← Finset.mul_sum, mul_div_assoc]
end AaronsonAmbainis.Bridge
