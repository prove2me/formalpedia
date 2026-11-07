-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.chi_eq_prod_sg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:57:01.821034+00:00
-- url     : https://prove2.me/submissions/0ccdc0de-c88b-47ab-b651-70a8b407c502

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {ι : Type*} (S : Finset ι) (x : Cube ι) : chi S x = ∏ i ∈ S, sg (x i) :=
  rfl
end AaronsonAmbainis.Bridge
