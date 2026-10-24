-- Prove2me | Definitions.Def_PricingWithTips3DM_94ae945174b1f30ac1acaa8b
-- name    : PricingWithTips3DM_94ae945174b1f30ac1acaa8b
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:20:08.515081+00:00
-- url     : https://prove2.me/theorems/142c0821-21d2-4718-80e7-60e0006006a8
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairFirstProjection.Basic
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_dea1a793ff7c6a92846a13d9
import Definitions.Def_PricingWithTips3DM_a6f12e82e39df26683946dd8
import Mathlib.Tactic.DeriveFintype
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# First projection of a separator-encoded pair

This is the reusable counterpart of `Turing.Prj`: it retains the symbols
before the unique `none` separator and discards the right component.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder.PairFirstProjection

/-- Finite control for copying the first component in forward order. -/
inductive Label (Γ : Type)
  | scan | save (symbol : Γ) | discard | restore | emit (symbol : Γ) | halt
deriving Fintype

/-- Fixed first-projection controller. -/
def program (Γ : Type) [Fintype Γ] : Program (Option Γ) Γ where
  Label := Label Γ
  labelDecidableEq := Classical.decEq _
  labelFintype := inferInstance
  main := .scan
  op
    | .scan => .popInput .restore fun
        | none => .discard
        | some symbol => .save symbol
    | .save symbol => .pushWork₁ (some symbol) .scan
    | .discard => .popInput .restore fun _ => .discard
    | .restore => .popWork₁ .halt fun
        | none => .restore
        | some symbol => .emit symbol
    | .emit symbol => .pushOutput symbol .restore
    | .halt => .halt

/-- Proof-facing configuration. -/
def cfg (Γ : Type) [Fintype Γ] (label : Label Γ)
    (buffer₁ buffer₂ : Option (Option Γ)) (test : Bool)
    (input : List (Option Γ)) (output : List Γ)
    (work₁ work₂ : List (Option Γ)) : BuilderCfg (program Γ) where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := []
  counter₂ := []
  counter₃ := []

end CLRS.Chapter34.Turing.PolyBuilder.PairFirstProjection


