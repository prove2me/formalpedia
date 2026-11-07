-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:02:31.721194+00:00
-- url     : https://prove2.me/submissions/d467e329-5e89-4ac5-86bf-2f50d62f9c94

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {β : Type*} [Fintype β]
namespace AaronsonAmbainis.Row
theorem _root_.solution {f : Cube β → ℝ} {k l : ℕ} (hkl : k ≤ l) (hf : HasDegreeLE f k) :
    HasDegreeLE f l := by
  obtain ⟨c, hc, hf⟩ := hf
  exact ⟨c, fun T hT => hc T (lt_of_le_of_lt hkl hT), hf⟩
end AaronsonAmbainis.Row
