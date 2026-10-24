-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part5
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part5
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T08:05:26.754366+00:00
-- url     : https://prove2.me/theorems/e78835b2-0c27-459c-85bb-dace9faf8bc8
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part5
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShape3DM

open Hardness Hardness.Cert Hardness.Sat3dm

def wMap (input : List CLRS.Chapter34.CNFSym)
    (e : Sat3dm.Ext (variableList input).length (paddedCNF input).length) :
    Fin (dimension input) :=
  ⟨SatToMatching3DCode.extIdx e, by
    rw [← ext_card_eq_dimension input]
    exact SatToMatching3DCode.extIdx_lt e⟩

def slotMap (input : List CLRS.Chapter34.CNFSym)
    (s : Sat3dm.Slot (variableList input).length (paddedCNF input).length) :
    Fin (dimension input) :=
  ⟨SatToMatching3DCode.slotIdx s, by
    rw [← slot_card_eq_dimension input]
    exact SatToMatching3DCode.slotIdx_lt s⟩

noncomputable def wEquiv (input : List CLRS.Chapter34.CNFSym) :
    Sat3dm.Ext (variableList input).length (paddedCNF input).length ≃
      Fin (dimension input) :=
  (SatToMatching3DCode.extEquivFin _ _).trans
    (finCongr (ext_card_eq_dimension input))

noncomputable def slotEquiv (input : List CLRS.Chapter34.CNFSym) :
    Sat3dm.Slot (variableList input).length (paddedCNF input).length ≃
      Fin (dimension input) :=
  (SatToMatching3DCode.slotEquivFin _ _).trans
    (finCongr (slot_card_eq_dimension input))
end PricingWithTips.FixedShape3DM


