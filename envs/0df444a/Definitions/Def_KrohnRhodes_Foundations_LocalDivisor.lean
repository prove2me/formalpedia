-- Prove2me | Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
-- name    : KrohnRhodes_Foundations_LocalDivisor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:53:11.106794+00:00
-- url     : https://prove2.me/theorems/442e9a54-fd8b-52e3-9972-418b1eccd135
-- title:
--   Local Divisor
-- statement:
--   Definitions and structural lemmas for Local Divisor, from Aditya Rao (adii800/krohn-rhodes-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Krohn-Rhodes prime decomposition of finite monoids into aperiodic and simple-group factors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/LocalDivisor.lean

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
set_option autoImplicit true
@[expose] public section
@[expose] public section
open FreeMonoid Computability Pointwise
universe u
variable {α : Type u}
namespace KrohnRhodes
def LocalDivisor (M : Type*) [Monoid M] (c : M) : Type _ :=
  {x : M // (∃ a : M, x = c * a) ∧ (∃ b : M, x = b * c)}
namespace LocalDivisor
variable {M : Type*} [Monoid M] {c : M}
def val (x : LocalDivisor M c) : M := x.1
@[ext] theorem ext {x y : LocalDivisor M c} (h : x.val = y.val) : x = y := Subtype.ext h
theorem mem_left (x : LocalDivisor M c) : ∃ a : M, x.val = c * a := x.2.1
theorem mem_right (x : LocalDivisor M c) : ∃ b : M, x.val = b * c := x.2.2
noncomputable instance : Mul (LocalDivisor M c) where
  mul x y :=
    ⟨x.val * (Classical.choose y.mem_left),
      by
        obtain ⟨a, ha⟩ := x.mem_left
        exact ⟨a * Classical.choose y.mem_left, by rw [ha, mul_assoc]⟩,
      by
        -- x.val * y₀ = (x.val) * y₀, and x.val ∈ Mc gives x.val = b*c, but we need *·c form.
        -- Use that x.val * y₀ = b * c * y₀ = b * (c * y₀) = b * y.val, and y.val ∈ Mc.
        obtain ⟨b, hb⟩ := x.mem_right
        obtain ⟨b', hb'⟩ := y.mem_right
        have hy0 : c * Classical.choose y.mem_left = y.val := (Classical.choose_spec y.mem_left).symm
        refine ⟨b * b', ?_⟩
        rw [hb, mul_assoc, hy0, hb', ← mul_assoc]⟩
theorem mul_val (x y : LocalDivisor M c) :
    (x * y).val = x.val * Classical.choose y.mem_left := rfl
theorem mul_val_of_eq (x y : LocalDivisor M c) {y₀ : M} (hy₀ : y.val = c * y₀) :
    (x * y).val = x.val * y₀ := by
  rw [mul_val]
  obtain ⟨b, hb⟩ := x.mem_right
  have hc : c * Classical.choose y.mem_left = c * y₀ := by
    rw [(Classical.choose_spec y.mem_left).symm, hy₀]
  calc x.val * Classical.choose y.mem_left
      = b * (c * Classical.choose y.mem_left) := by rw [hb, mul_assoc]
    _ = b * (c * y₀) := by rw [hc]
    _ = x.val * y₀ := by rw [hb, mul_assoc]
noncomputable instance : One (LocalDivisor M c) where
  one := ⟨c, ⟨1, (mul_one c).symm⟩, ⟨1, (one_mul c).symm⟩⟩
theorem one_val : (1 : LocalDivisor M c).val = c := rfl
noncomputable instance : Monoid (LocalDivisor M c) where
  mul_assoc x y z := by
    apply LocalDivisor.ext
    -- (x*y)*z and x*(y*z) both equal x.val * y₀ * z₀ where y=c y₀, z=c z₀.
    obtain ⟨z₀, hz₀⟩ := z.mem_left
    obtain ⟨y₀, hy₀⟩ := y.mem_left
    have hyz : (y * z).val = y.val * z₀ := mul_val_of_eq y z hz₀
    have hyz' : (y * z).val = c * (y₀ * z₀) := by rw [hyz, hy₀, mul_assoc]
    -- LHS: ((x*y)*z).val = (x*y).val * z₀ = (x.val*y₀)*z₀
    have hL : (x * y * z).val = x.val * y₀ * z₀ := by
      rw [mul_val_of_eq (x * y) z hz₀, mul_val_of_eq x y hy₀]
    -- RHS: (x*(y*z)).val = x.val*(y₀*z₀)
    have hR : (x * (y * z)).val = x.val * (y₀ * z₀) := mul_val_of_eq x (y * z) hyz'
    rw [hL, hR, mul_assoc]
  one_mul x := by
    apply LocalDivisor.ext
    obtain ⟨a, ha⟩ := x.mem_left
    rw [mul_val_of_eq 1 x ha, one_val, ← ha]
  mul_one x := by
    apply LocalDivisor.ext
    -- 1.val = c = c*1, so (x*1).val = x.val * 1 = x.val.
    rw [mul_val_of_eq x 1 (by rw [one_val, mul_one] : (1 : LocalDivisor M c).val = c * 1),
      mul_one]
noncomputable instance [Finite M] : Finite (LocalDivisor M c) := Subtype.finite
end LocalDivisor
end KrohnRhodes


