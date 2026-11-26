-- Prove2me | Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
-- name    : KrohnRhodes_Foundations_MonoidWreathBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:53:14.40788+00:00
-- url     : https://prove2.me/theorems/ddf25513-342a-4f6e-931f-6459a59270cc
-- title:
--   Monoid Wreath Bridge
-- statement:
--   Definitions and structural lemmas for Monoid Wreath Bridge, from Aditya Rao (adii800/krohn-rhodes-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Krohn-Rhodes prime decomposition of finite monoids into aperiodic and simple-group factors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/MonoidWreathBridge.lean

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib.GroupTheory.RegularWreathProduct
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace KrohnRhodes
universe u
variable (D Q : Type u) [Group D] [Group Q]
def regularWreathToMonoidWreathFun (a : D ≀ᵣ Q) :
    WreathProduct D Q Q :=
  ⟨fun x => a.left (a.right * x), a.right⟩
def regularWreath_to_monoidWreath :
    (D ≀ᵣ Q) →* WreathProduct D Q Q where
  toFun := regularWreathToMonoidWreathFun D Q
  map_one' := by
    -- φ(1) has decoration `x ↦ 1.left (1.right * x) = 1` and base `1.right = 1`.
    ext x
    · simp [regularWreathToMonoidWreathFun]
    · simp [regularWreathToMonoidWreathFun]
  map_mul' a b := by
    -- We have to verify
    --   φ(a*b).func x = (φ a * φ b).func x
    --   φ(a*b).base   = (φ a * φ b).base
    -- LHS func: (a*b).left ((a*b).right * x)
    --         = a.left ((a*b).right * x) * b.left (a.right⁻¹ * (a*b).right * x)
    --         = a.left (a.right * b.right * x) * b.left (b.right * x)
    -- RHS func: φ(a).func (φ(b).base • x) * φ(b).func x
    --         = a.left (a.right * (b.right * x)) * b.left (b.right * x)
    -- These agree by associativity.
    ext x
    · -- decoration component
      change (a * b).left ((a * b).right * x)
        = a.left (a.right * (b.right * x)) * b.left (b.right * x)
      simp [RegularWreathProduct.mul_def, mul_assoc]
    · -- base component
      change (a * b).right = a.right * b.right
      rfl
end KrohnRhodes


