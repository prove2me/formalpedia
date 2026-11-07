-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.chi_flip_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:21:52.909536+00:00
-- url     : https://prove2.me/submissions/363ab58f-8df8-44c9-9ab6-e38e1e6f230a

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_sg_not
import Theorems.Thm_AaronsonAmbainis_Bridge_chi_eq_prod_sg
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_singleton_ne
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_singleton_self


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {U : Finset ι} {j : ι} (hj : j ∈ U) (x : Cube ι) :
    chi U (flipSet x {j}) = -chi U x := by
  have h : ∏ i ∈ U.erase j, sg (flipSet x {j} i) = ∏ i ∈ U.erase j, sg (x i) :=
    Finset.prod_congr rfl
      (fun i hi => by rw [flipSet_singleton_ne x (Finset.ne_of_mem_erase hi)])
  rw [chi_eq_prod_sg, chi_eq_prod_sg,
    ← Finset.mul_prod_erase U (fun i => sg (flipSet x {j} i)) hj,
    ← Finset.mul_prod_erase U (fun i => sg (x i)) hj, h, flipSet_singleton_self, sg_not, neg_mul]
end AaronsonAmbainis.Bridge
