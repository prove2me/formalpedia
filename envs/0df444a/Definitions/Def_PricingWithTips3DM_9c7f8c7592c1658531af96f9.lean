-- Prove2me | Definitions.Def_PricingWithTips3DM_9c7f8c7592c1658531af96f9
-- name    : PricingWithTips3DM_9c7f8c7592c1658531af96f9
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:30:09.33385+00:00
-- url     : https://prove2.me/theorems/fc656ae8-7254-47f4-8690-b2f2beb53690
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft.Basic
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_dea1a793ff7c6a92846a13d9
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
import Mathlib.Tactic.DeriveFintype
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Formatting the left half of an option-separated pair
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder.OptionPairLeft

/-- Embed a raw stream as the left component and append the `none` separator. -/
def format {Γ : Type} (input : List Γ) : List (Option Γ) :=
  input.map some ++ [none]

inductive Label (Γ : Type)
  | scan | emit (symbol : Γ) | separator | halt
deriving Fintype

/-- Reversed-output formatter. -/
def program (Γ : Type) [Fintype Γ] : Program Γ (Option Γ) where
  Label := Label Γ
  labelDecidableEq := Classical.decEq _
  labelFintype := inferInstance
  main := .scan
  op
    | .scan => .popInput .separator .emit
    | .emit symbol => .pushOutput (some symbol) .scan
    | .separator => .pushOutput none .halt
    | .halt => .halt

def cfg (Γ : Type) [Fintype Γ] (label : Label Γ)
    (buffer₁ buffer₂ : Option Γ) (test : Bool)
    (input : List Γ) (output : List (Option Γ)) : BuilderCfg (program Γ) where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := []
  counter₂ := []
  counter₃ := []

end CLRS.Chapter34.Turing.PolyBuilder.OptionPairLeft


