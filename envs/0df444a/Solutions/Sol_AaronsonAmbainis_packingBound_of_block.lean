-- Prove2me | solution 1 for AaronsonAmbainis.packingBound_of_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:19:09.424319+00:00
-- url     : https://prove2.me/submissions/6f383d93-7f65-4dc0-a7bb-c9c07c5291a6

import Definitions.Def_AaronsonAmbainis_Pack_Scaled
import Definitions.Def_AaronsonAmbainis_Pack_Packing
import Theorems.Thm_AaronsonAmbainis_Pack_le_of_scaled
import Theorems.Thm_AaronsonAmbainis_Pack_scaled_bound


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : BlockInequality → PackingBound := by
  intro hB ι _ _ d f hf hd x κ hκ hpack
  exact Pack.le_of_scaled _ (∑ S, |f x - f (flipSet x S)|) d
    (fun M hM => Pack.scaled_bound hB ι d f hf hd x κ hκ hpack M hM)
end AaronsonAmbainis
