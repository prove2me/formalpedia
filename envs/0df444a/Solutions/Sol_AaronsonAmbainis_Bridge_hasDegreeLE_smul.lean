-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:02:10.72864+00:00
-- url     : https://prove2.me/submissions/3a92b603-c72f-4a9c-a3ed-7e4d5a63380e

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (r : ℝ) {f : Cube ι → ℝ} {d : ℕ} (hf : HasDegreeLE f d) :
    HasDegreeLE (fun x => r * f x) d := by
  obtain ⟨a, ha, hfa⟩ := hf
  refine ⟨fun S => r * a S, fun S hS => by show r * a S = 0; rw [ha S hS, mul_zero], fun x => ?_⟩
  show r * f x = ∑ S, r * a S * chi S x
  rw [hfa x, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  ring
end AaronsonAmbainis.Bridge
