-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.printedConcl_of_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:22:07.332667+00:00
-- url     : https://prove2.me/submissions/cafa78f3-c5e5-433f-9a59-6d8ede15bd2a

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {n : ℕ} {f : (Fin n → Bool) → ℝ} (h : ∀ x y, f x = f y) (d : ℕ) :
    PrintedConcl f d := by
  refine ⟨fun _ _ => 0, fun x y => ?_, fun x => ?_⟩
  · rw [h x y, sub_self, abs_zero]
    simp
  · simp only [Finset.sum_const_zero]
    positivity
end AaronsonAmbainis.Bridge
