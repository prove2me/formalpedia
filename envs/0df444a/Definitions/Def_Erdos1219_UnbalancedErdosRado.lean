-- Prove2me | Definitions.Def_Erdos1219_UnbalancedErdosRado
-- name    : Erdos1219_UnbalancedErdosRado
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:39:50.947315+00:00
-- url     : https://prove2.me/theorems/6637694b-a399-445e-a62e-35c67d7fa264
-- title:
--   Unbalanced Erdos Rado
-- statement:
--   Definitions and structural lemmas for Unbalanced Erdos Rado, from Ji Ho Bae (jbaelaw/erdos1219-lean; see pinned Apache-2.0 LICENSE and source headers)'s pinned Erdos Problem 1219 on cardinal partition relations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
set_option autoImplicit false
open Cardinal Ordinal Set
namespace Erdos1219
universe u
section WellOrder
variable {X : Type u} [LinearOrder X] [WellFoundedLT X]
end WellOrder
section Main
variable {W : Type u} [LinearOrder W] [WellFoundedLT W]
def nbr (f : W → W → Bool) (c : Bool) (α : W) : Set W := {γ | γ < α ∧ f γ α = !c}
def common (f : W → W → Bool) (c : Bool) (Z : Set W) : Set W := {γ | ∀ z ∈ Z, f z γ = !c}
def bigCof (μ : Cardinal.{u}) : Set W :=
  {α | ∀ Z : Set W, Z ⊆ Iio α → #Z ≤ μ → ∃ β < α, Z ⊆ Iio β}
def IsGood (f : W → W → Bool) (c : Bool) (μ : Cardinal.{u}) (α : W) : Prop :=
  α ∈ bigCof μ ∧ ∀ Z ⊆ nbr f c α, Homog f (!c) Z → #Z ≤ μ →
    ∀ β < α, Z ⊆ Iio β → ∃ γ ∈ nbr f c α ∩ common f c Z, β ≤ γ
end Main
end Erdos1219


