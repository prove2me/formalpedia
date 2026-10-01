-- Prove2me | Definitions.Def_Yukon_70261194b18f9bef5e61baff
-- name    : Yukon_70261194b18f9bef5e61baff
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:38:09.075903+00:00
-- url     : https://prove2.me/theorems/f7573897-4bb1-468b-8913-724b2d7a3125
-- title:
--   YukonModule.PolyFun.Control.Coalgebra.part0
-- statement:
--   Source module PolyFun.Control.Coalgebra.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/Control/Coalgebra.lean
--
--   provider-v8:aa0f196dcc54a9a5b63076857741afb997e0dffdfdef4afd13625afa392bf52e
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODphYTBmMTk2ZGNjNTRhOWE1YjYzMDc2ODU3NzQxYWZiOTk3ZTBkZmZkZmRlZjRhZmQxMzYyNWFmYTM5MmJmNTJlIiwiaGFzaCI6ImEyM2RhNWNmNzIyZTllZWUxOTg0MTc2ZTYwNDFhNDg3MDhmODQ1ZjY0MDA1OTE2MjgxZTk3NzhhZTIxMmFmOTMiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzcwMjYxMTk0YjE4ZjliZWY1ZTYxYmFmZiIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.FunLike.Basic


public import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# F-coalgebras

An `F`-coalgebra for an endofunctor `F` on `Type` is a type `S` together with a
structure map `out : S → F S`.

This is the categorical dual of `MonadAlgebra`: where an algebra collapses a
functor layer, a coalgebra *observes* one layer of structure from a state.

## Main definitions

* `Coalg F S`: typeclass packaging `out : S → F S`.
* `Coalg.Hom S₁ S₂`: a function `S₁ → S₂` that commutes with the structure
  maps (`Functor.map f ∘ out = out ∘ f`). Equipped with coercion, `id`, `comp`.

## Relationship to Mathlib and Poly

`CategoryTheory.Endofunctor.Coalgebra` in Mathlib defines coalgebras for
endofunctors on an arbitrary category. This file instead provides a Lean-native
typeclass for `Type`-endofunctors, following the style of `MonadAlgebra`.
The `Type`-level definition suffices for the polynomial-functor framework:
a `PFunctor.DynSystem S p` is exactly a `p.Obj`-coalgebra on `S` via
`PFunctor.DynSystem.out`, in the sense of the Poly book (Spivak, 2022).
-/

@[expose] public section

universe u v

/-- An `F`-coalgebra on `S` is a structure map `out : S → F S`.

Named `Coalg` to avoid collision with `Mathlib.RingTheory.Coalgebra`.
This is the dual of `MonadAlgebra`. No `[Functor F]` constraint is imposed on the
class itself so that the definition applies to arbitrary type-level maps. -/
class Coalg (F : Type u → Type v) (S : Type u) where
  /-- The structure map of the coalgebra, unfolding a state `S` into one layer of `F`. -/
  out : S → F S

export Coalg (out)

/-! ## Coalg morphisms -/

/-- A coalgebra morphism between `F`-coalgebras on `S₁` and `S₂` is a function
that commutes with the structure maps:
```
      out
  S₁ -----> F S₁
  |          |
  f        F f
  |          |
  v          v
  S₂ -----> F S₂
      out
```
In the interaction framework, coalgebra morphisms between processes correspond
to forward simulations that preserve step structure. -/
structure Coalg.Hom (F : Type u → Type v) [Functor F]
    (S₁ : Type u) (S₂ : Type u) [Coalg F S₁] [Coalg F S₂] where
  /-- The underlying function between state spaces. -/
  toFun : S₁ → S₂
  /-- The commutativity condition: `F.map f ∘ out = out ∘ f`. -/
  comm : Functor.map toFun ∘ (out : S₁ → F S₁) = (out : S₂ → F S₂) ∘ toFun

namespace Coalg.Hom

variable {F : Type u → Type v} [Functor F]
variable {S₁ S₂ S₃ : Type u} [Coalg F S₁] [Coalg F S₂] [Coalg F S₃]

instance  _root_.Coalg.Hom.instFunLike : FunLike (Coalg.Hom F S₁ S₂) S₁ S₂ where
  coe := Coalg.Hom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext]
theorem ext {f g : Coalg.Hom F S₁ S₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

variable [LawfulFunctor F]

/-- The identity coalgebra morphism. -/
def id : Coalg.Hom F S₁ S₁ where
  toFun := _root_.id
  comm := by funext x; simp [Function.comp, id_map]

/-- Composition of coalgebra morphisms. -/
def comp (g : Coalg.Hom F S₂ S₃) (f : Coalg.Hom F S₁ S₂) : Coalg.Hom F S₁ S₃ where
  toFun := g.toFun ∘ f.toFun
  comm := by
    funext x
    have hf := congrFun f.comm x
    have hg := congrFun g.comm (f.toFun x)
    simp only [Function.comp_apply] at hf hg ⊢
    rw [comp_map, hf, hg]

@[simp]
theorem id_apply (x : S₁) : (Coalg.Hom.id : Coalg.Hom F S₁ S₁) x = x := rfl

@[simp]
theorem comp_apply (g : Coalg.Hom F S₂ S₃) (f : Coalg.Hom F S₁ S₂) (x : S₁) :
    (Coalg.Hom.comp g f) x = g (f x) := rfl

end Coalg.Hom


