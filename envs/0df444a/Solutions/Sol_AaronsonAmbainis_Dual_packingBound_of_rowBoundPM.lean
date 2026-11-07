-- Prove2me | solution 1 for AaronsonAmbainis.Dual.packingBound_of_rowBoundPM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:08:17.489596+00:00
-- url     : https://prove2.me/submissions/56fa2590-c604-48ef-b2f3-58ab1c5974b3

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
import Theorems.Thm_AaronsonAmbainis_Dual_packing_le_of_cover
import Theorems.Thm_AaronsonAmbainis_diffSet_flipSet


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
namespace AaronsonAmbainis.Dual
theorem _root_.solution : RowBoundPM → PackingBound := by
  intro hRB ι _ _ d f hf hdeg x κ hκ hload
  obtain ⟨a, ha0, haK, hacov⟩ := hRB ι d f hf hdeg
  refine packing_le_of_cover (fun S => |f x - f (flipSet x S)|) _ (a x) (ha0 x) (haK x)
    (fun S => ?_) κ hκ hload
  have h := hacov x (flipSet x S)
  rwa [diffSet_flipSet] at h
end AaronsonAmbainis.Dual
