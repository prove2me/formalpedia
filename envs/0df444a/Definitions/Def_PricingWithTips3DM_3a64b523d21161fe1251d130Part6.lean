-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part6
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part6
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T08:10:40.741493+00:00
-- url     : https://prove2.me/theorems/65b96fdc-2182-4a5e-bc2d-bff28e70fd66
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part6
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part5
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShape3DM

open Hardness Hardness.Cert Hardness.Sat3dm

def normalizedTriples (input : List CLRS.Chapter34.CNFSym) :
    Finset (ThreeDMTriple (dimension input)) :=
  (triples input).image
    (fun t => (wMap input t.1,
      (slotMap input t.2.1, slotMap input t.2.2)))

def reduction (input : List CLRS.Chapter34.CNFSym) : ThreeDMInstance :=
  ⟨dimension input,
    fun b s d => decide ((b, s, d) ∈ normalizedTriples input)⟩

def abstractInstance (input : List CLRS.Chapter34.CNFSym) : Matching3DInstance where
  W := Sat3dm.Ext (variableList input).length (paddedCNF input).length
  X := Sat3dm.Slot (variableList input).length (paddedCNF input).length
  Y := Sat3dm.Slot (variableList input).length (paddedCNF input).length
  triples := triples input

def normalizedInstance (input : List CLRS.Chapter34.CNFSym) : Matching3DInstance where
  W := Fin (dimension input)
  X := Fin (dimension input)
  Y := Fin (dimension input)
  triples := normalizedTriples input
end PricingWithTips.FixedShape3DM


