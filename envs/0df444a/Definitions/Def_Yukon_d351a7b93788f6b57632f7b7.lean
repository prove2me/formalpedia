-- Prove2me | Definitions.Def_Yukon_d351a7b93788f6b57632f7b7
-- name    : Yukon_d351a7b93788f6b57632f7b7
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:54:51.65849+00:00
-- url     : https://prove2.me/theorems/46abb436-d6a8-4ae1-ad29-37adbaa665fe
-- title:
--   YukonModule.PolyFun.PFunctor.SubstMonoid.part0
-- statement:
--   Source module PolyFun.PFunctor.SubstMonoid.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/PFunctor/SubstMonoid.lean
--
--   yukon-proof-operation:9b8578bd03cd93ea633a0163ab41d5e7f0acbdb0e322b837d266dcd7612eaee2
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246OWI4NTc4YmQwM2NkOTNlYTYzM2EwMTYzYWI0MWQ1ZTdmMGFjYmRiMGUzMjJiODM3ZDI2NmRjZDc2MTJlYWVlMiIsImhhc2giOiIzN2VjMmJlNGMzM2VlMjg3MTYzMzI1ZTQwNzcxZmRhZDE0YjE3ZmRhMmFiNWEwYjBjZTlhMWY1OWVlMDU2YWMzIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9kMzUxYTdiOTM3ODhmNmI1NzYzMmY3YjciLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Definitions.Def_Yukon_e69cfa8daa289eb317ddc090

public import Mathlib.CategoryTheory.Category.Basic
import Batteries.Tactic.Lint


public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Init
meta import Definitions.Def_Yukon_e69cfa8daa289eb317ddc090
set_option backward.isDefEq.respectTransparency.types false
/-!
# Monoids for polynomial substitution

A `SubstMonoid` is a monoid object in the composition-monoidal category
`(Poly, ◃, y)`: a polynomial `p`, a unit lens `y ⇆ p`, and a multiplication
lens `p ◃ p ⇆ p` satisfying the two unit laws and associativity. Under
polynomial extension, every substitution monoid induces a monad on `Type`.

The laws are stated directly with the composition unitors and associator from
`PFunctor.Lens.Equiv`. This à-la-carte presentation avoids choosing between the
lens and chart category instances on `PFunctor` and matches the existing
`PFunctor.Comonoid` API.

`SubstMonoid.Hom` packages the polynomial monad morphisms: lenses preserving
the unit and multiplication. They form a category under ordinary lens
composition.

This file records the polynomial-level structure and its morphisms. Packaging
the induced monad on each extension, and constructing the free substitution
monoid, are separate layers.

## References

* Libkind and Spivak, *Pattern Runs on Matter: The Free Monad Monad as a
  Module over the Cofree Comonad Comonad*.
* Niu and Spivak, *Polynomial Functors: A Mathematical Theory of Interaction*,
  Chapter 7.
-/

@[expose] public section

universe uA uB

open CategoryTheory

namespace PFunctor

/-! ## Substitution monoids -/

set_option linter.checkUnivs false in
/-- A monoid object in the composition-monoidal category `(Poly, ◃, y)`.

The unit and multiplication are polynomial lenses. The laws use the explicit
unitors `XComp` and `compX` and associator `compAssoc`; no ambient monoidal
category instance is required. -/
-- The carrier's position and direction universes are independent; `checkUnivs`
-- sees only their joint contribution to the structure's resulting sort.
structure SubstMonoid where
  /-- The carrier polynomial. -/
  carrier : PFunctor.{uA, uB}
  /-- The unit `η : y ⇆ p`. Its universe instance agrees with the composition
  unit appearing beside `carrier ◃ carrier`. -/
  unit : Lens X.{max uA uB, uB} carrier
  /-- The multiplication `μ : p ◃ p ⇆ p`. -/
  mult : Lens (carrier ◃ carrier) carrier
  /-- Left unitality: `μ ∘ (η ◃ id) ∘ λ⁻¹ = id`. -/
  unit_left : mult ∘ₗ (unit ◃ₗ Lens.id carrier) ∘ₗ
      Lens.Equiv.XComp.invLens = Lens.id carrier
  /-- Right unitality: `μ ∘ (id ◃ η) ∘ ρ⁻¹ = id`. -/
  unit_right : mult ∘ₗ (Lens.id carrier ◃ₗ unit) ∘ₗ
      Lens.Equiv.compX.invLens = Lens.id carrier
  /-- Associativity: multiplying the outer pair or the inner pair agrees. -/
  assoc : mult ∘ₗ (mult ◃ₗ Lens.id carrier) =
      mult ∘ₗ (Lens.id carrier ◃ₗ mult) ∘ₗ Lens.Equiv.compAssoc.toLens

namespace SubstMonoid

/-! ## Morphisms -/

/-- A homomorphism of substitution monoids. It is a lens on carriers that
preserves the unit and multiplication. -/
structure Hom (M N : SubstMonoid.{uA, uB}) where
  /-- The underlying lens between carrier polynomials. -/
  toLens : Lens M.carrier N.carrier
  /-- Preservation of the unit. -/
  map_unit : toLens ∘ₗ M.unit = N.unit
  /-- Preservation of multiplication. -/
  map_mult : toLens ∘ₗ M.mult =
    N.mult ∘ₗ (toLens ◃ₗ toLens)

instance  _root_.PFunctor.SubstMonoid.instCoeHomLensCarrier {M N : SubstMonoid.{uA, uB}} :
    Coe (Hom M N) (Lens M.carrier N.carrier) :=
  ⟨Hom.toLens⟩

@[ext]
theorem Hom.ext {M N : SubstMonoid.{uA, uB}} (f g : Hom M N)
    (h : f.toLens = g.toLens) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity substitution-monoid homomorphism. -/
def Hom.id (M : SubstMonoid.{uA, uB}) : Hom M M where
  toLens := Lens.id M.carrier
  map_unit := rfl
  map_mult := by simp

/-- Composition of substitution-monoid homomorphisms, in diagrammatic order. -/
def Hom.comp {M N O : SubstMonoid.{uA, uB}} (f : Hom M N) (g : Hom N O) : Hom M O where
  toLens := g.toLens ∘ₗ f.toLens
  map_unit := by
    rw [Lens.comp_assoc, f.map_unit, g.map_unit]
  map_mult := by
    calc
      (g.toLens ∘ₗ f.toLens) ∘ₗ M.mult =
          g.toLens ∘ₗ (f.toLens ∘ₗ M.mult) := rfl
      _ = g.toLens ∘ₗ (N.mult ∘ₗ (f.toLens ◃ₗ f.toLens)) := by
        rw [f.map_mult]
      _ = (g.toLens ∘ₗ N.mult) ∘ₗ (f.toLens ◃ₗ f.toLens) := rfl
      _ = (O.mult ∘ₗ (g.toLens ◃ₗ g.toLens)) ∘ₗ
          (f.toLens ◃ₗ f.toLens) := by
        rw [g.map_mult]
      _ = O.mult ∘ₗ ((g.toLens ◃ₗ g.toLens) ∘ₗ
          (f.toLens ◃ₗ f.toLens)) := rfl
      _ = O.mult ∘ₗ ((g.toLens ∘ₗ f.toLens) ◃ₗ
          (g.toLens ∘ₗ f.toLens)) := by
        rw [Lens.compMap_comp]

@[simp] theorem Hom.id_toLens (M : SubstMonoid.{uA, uB}) :
    (Hom.id M).toLens = Lens.id M.carrier := rfl

@[simp] theorem Hom.comp_toLens {M N O : SubstMonoid.{uA, uB}}
    (f : Hom M N) (g : Hom N O) :
    (f.comp g).toLens = g.toLens ∘ₗ f.toLens := rfl

@[simp] theorem Hom.id_comp {M N : SubstMonoid.{uA, uB}} (f : Hom M N) :
    (Hom.id M).comp f = f :=
  Hom.ext _ _ (Lens.comp_id f.toLens)

@[simp] theorem Hom.comp_id {M N : SubstMonoid.{uA, uB}} (f : Hom M N) :
    f.comp (Hom.id N) = f :=
  Hom.ext _ _ (Lens.id_comp f.toLens)

theorem Hom.comp_assoc {M N O P : SubstMonoid.{uA, uB}}
    (f : Hom M N) (g : Hom N O) (h : Hom O P) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  Hom.ext _ _ (Lens.comp_assoc h.toLens g.toLens f.toLens)

/-- The category of substitution monoids and their homomorphisms. -/
instance  _root_.PFunctor.SubstMonoid.instCategory : Category SubstMonoid.{uA, uB} where
  Hom := Hom
  id := Hom.id
  comp f g := f.comp g
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

end SubstMonoid

end PFunctor


