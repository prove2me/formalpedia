-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.chi_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:49:34.018752+00:00
-- url     : https://prove2.me/submissions/95285d1e-0fab-48de-a300-e200ff0fac5a

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (e : ι ≃ κ) (S : Finset ι) (y : Cube κ) :
    chi S (fun i => y (e i)) = chi (S.map e.toEmbedding) y := by
  simp [chi, Finset.prod_map]
end AaronsonAmbainis.Bridge
