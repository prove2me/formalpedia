-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.agCount_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:22:36.466393+00:00
-- url     : https://prove2.me/submissions/30a35c00-53f5-4659-9171-b6f2a8513037

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (x z : Cube ι) (h : x ≠ z) : agCount x z < Fintype.card ι := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  unfold agCount
  rw [← Finset.card_univ]
  apply Finset.card_lt_card
  rw [Finset.filter_ssubset]
  exact ⟨i, mem_univ i, hi⟩
end AaronsonAmbainis.DetLow
