-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:00:59.37813+00:00
-- url     : https://prove2.me/submissions/952a6dc1-d08d-4e32-aace-b1e1485abc9a

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f g : Cube ι → ℝ} {d : ℕ} (hf : HasDegreeLE f d)
    (hg : HasDegreeLE g d) : HasDegreeLE (fun x => f x + g x) d := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  refine ⟨fun S => a S + b S, fun S hS => by show a S + b S = 0; rw [ha S hS, hb S hS, add_zero], fun x => ?_⟩
  show f x + g x = ∑ S, (a S + b S) * chi S x
  simp only [add_mul, Finset.sum_add_distrib]
  rw [← hfa x, ← hgb x]
end AaronsonAmbainis.Bridge
