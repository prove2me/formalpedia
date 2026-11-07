-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.diffSet_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:49:36.726202+00:00
-- url     : https://prove2.me/submissions/f0717c8d-98a6-4cf9-be96-0f92f8330017

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι] [DecidableEq κ]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (e : ι ≃ κ) (x y : Cube ι) :
    diffSet (fun k => x (e.symm k)) (fun k => y (e.symm k))
      = (diffSet x y).map e.toEmbedding := by
  ext k
  simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.coe_toEmbedding]
  constructor
  · intro h
    exact ⟨e.symm k, h, e.apply_symm_apply k⟩
  · rintro ⟨i, hi, rfl⟩
    simpa using hi
end AaronsonAmbainis.Bridge
