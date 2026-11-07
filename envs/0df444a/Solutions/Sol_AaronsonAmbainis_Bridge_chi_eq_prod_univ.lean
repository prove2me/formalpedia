-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.chi_eq_prod_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:20:56.796719+00:00
-- url     : https://prove2.me/submissions/62039930-a9f6-49d9-a65b-cccb5de94a31

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_chi_eq_prod_sg

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (S : Finset ι) (x : Cube ι) :
    chi S x = ∏ i, (if i ∈ S then sg (x i) else 1) := by
  rw [chi_eq_prod_sg, Fintype.prod_ite_mem]
end AaronsonAmbainis.Bridge
