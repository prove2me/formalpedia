-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:59:36.729214+00:00
-- url     : https://prove2.me/submissions/b38fdf78-72f1-4bc2-9a32-79beda97391c

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {β : Type*} [Fintype β]
namespace AaronsonAmbainis.Row
theorem _root_.solution {f g : Cube β → ℝ} {k : ℕ} (h : HasDegreeLE f k)
    (hfg : ∀ w, g w = f w) : HasDegreeLE g k := by
  obtain ⟨c, hc, hf⟩ := h
  exact ⟨c, hc, fun w => (hfg w).trans (hf w)⟩
end AaronsonAmbainis.Row
