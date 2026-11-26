-- Prove2me | Definitions.Def_KrohnRhodes_Foundations_WreathProduct
-- name    : KrohnRhodes_Foundations_WreathProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:52:42.896849+00:00
-- url     : https://prove2.me/theorems/e89f9c30-5cb7-52e8-a553-2c8a9b2965d6
-- title:
--   Wreath Product
-- statement:
--   Definitions and structural lemmas for Wreath Product, from Aditya Rao (adii800/krohn-rhodes-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Krohn-Rhodes prime decomposition of finite monoids into aperiodic and simple-group factors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/WreathProduct.lean

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v w
namespace WreathProduct
variable {A : Type u} {B : Type v} {X : Type w}
variable [Monoid A] [Monoid B] [MulAction B X]
instance : One (WreathProduct A B X) where
  one := ⟨fun _ => 1, 1⟩
@[simp]
theorem mul_func (p q : WreathProduct A B X) (x : X) :
    (p * q).func x = p.func (q.base • x) * q.func x := rfl
@[simp]
theorem mul_base (p q : WreathProduct A B X) :
    (p * q).base = p.base * q.base := rfl
@[simp]
theorem one_func (x : X) : (1 : WreathProduct A B X).func x = 1 := rfl
@[simp]
theorem one_base : (1 : WreathProduct A B X).base = (1 : B) := rfl
instance instMonoid : Monoid (WreathProduct A B X) where
  mul_assoc p q r := by
    ext x
    · -- LHS: ((p*q)*r).func x = (p*q).func (r.base • x) * r.func x
      --     = p.func (q.base • (r.base • x)) * q.func (r.base • x) * r.func x
      -- RHS: (p*(q*r)).func x = p.func ((q*r).base • x) * (q*r).func x
      --     = p.func ((q.base * r.base) • x) * (q.func (r.base • x) * r.func x)
      -- These are equal by mul_smul and mul_assoc
      simp only [mul_func, mul_base, mul_smul, mul_assoc]
    · simp [mul_assoc]
  one_mul p := by
    ext x
    · simp only [mul_func, one_func, one_mul]
    · simp
  mul_one p := by
    ext x
    · simp only [mul_func, one_func, one_base, one_smul, mul_one]
    · simp
instance instFinite [Finite X] [Finite A] [Finite B] : Finite (WreathProduct A B X) := by
  have : Finite ((X → A) × B) := inferInstance
  exact Finite.of_injective (fun w => (w.func, w.base))
    (fun a b h => by
      have h1 : a.func = b.func := (Prod.mk.inj h).1
      have h2 : a.base = b.base := (Prod.mk.inj h).2
      exact WreathProduct.ext h1 h2)
end WreathProduct


