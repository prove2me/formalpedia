-- Prove2me | Definitions.Def_Yukon_06171bfbcf8faa33c2404989
-- name    : Yukon_06171bfbcf8faa33c2404989
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:54:06.607694+00:00
-- url     : https://prove2.me/theorems/032d3f2b-eac4-4ed2-bb43-5d83969baf4c
-- title:
--   YukonModule.PolyFun.PFunctor.Lens.Cartesian.part0
-- statement:
--   Source module PolyFun.PFunctor.Lens.Cartesian.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/PFunctor/Lens/Cartesian.lean
--
--   yukon-proof-operation:ee38d0a346bbc141f855a63660a8134a48199c2c3e6e8ed484703ca81938dae5
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZWUzOGQwYTM0NmJiYzE0MWY4NTVhNjM2NjBhODEzNGE0ODE5OWMyYzNlNmU4ZWQ0ODQ3MDNjYTgxOTM4ZGFlNSIsImhhc2giOiI0ZWRiYjE0MGMzMTE0NDZiMjBhOWY2NzM2NmUyNWM2NTEyYTRjNWNlZmRmZGVmZDc1OTc1NGUzZDdjZGNkNDkwIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8wNjE3MWJmYmNmOGZhYTMzYzI0MDQ5ODkiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Definitions.Def_Yukon_e69cfa8daa289eb317ddc090



public import Batteries.Tactic.Lint
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Init
meta import Definitions.Def_Yukon_e69cfa8daa289eb317ddc090
set_option backward.isDefEq.respectTransparency.types false
/-!
# Cartesian Lenses Between Polynomial Functors

A `Lens P Q` between polynomial functors carries a forward map on positions
(`toFunA : P.A → Q.A`) and, for each position `a : P.A`, a backward map on
directions (`toFunB a : Q.B (toFunA a) → P.B a`). We say the lens is
**cartesian** when every backward map `toFunB a` is a bijection.

In the language of the fibration `Poly → Set` that sends a polynomial
functor to its set of positions, cartesian lenses are exactly the
cartesian morphisms: the type-square underlying each fiber is a pullback.
A cartesian lens is a *fiberwise isomorphism* over an arbitrary forward
map on positions.

The two classes in the orthogonal factorization system on `Poly` are captured
separately:

* a **vertical** lens has bijective `toFunA` (it changes position coordinates
  without losing or adding positions); and
* a **cartesian** lens has each `toFunB a` a bijection (each direction fiber is
  rigid over an arbitrary position map).

The canonical vertical leg in the factorization is identity on positions, but
identity is a chosen representative of the more general bijective-on-positions
class. See `PFunctor.Lens.IsVertical` in `Lens/Factorization.lean`.

A `PFunctor.Lens.Equiv` (a categorical isomorphism in the lens category)
is the intersection of the two: `toFunA` is a bijection AND every
`toFunB a` is a bijection. Thus *every* `Equiv` is cartesian, but a
cartesian lens whose position map is not a bijection (e.g.
`Lens.inl : Lens P (P + Q)`) is not an `Equiv`.

The downstream consumer of this file is `LawfulSubSpec` in
`VCVio/OracleComp/Coercions/SubSpec.lean`: a `LawfulSubSpec` is by
definition the predicate "the underlying
`Lens spec.toPFunctor superSpec.toPFunctor` is cartesian", which is the
exact condition needed to pull the uniform distribution on
`superSpec.Range` back through a sub-spec embedding without distortion.
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ uA₃ uB₃ uA₄ uB₄

namespace PFunctor

namespace Lens

variable {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}

/-- A lens `l : Lens P Q` is **cartesian** when every backward fiber
`l.toFunB a : Q.B (l.toFunA a) → P.B a` is a bijection. Equivalently,
`l` is a cartesian morphism in the fibration `Poly → Set` of polynomial
functors over their position sets. -/
def IsCartesian (l : Lens P Q) : Prop :=
  ∀ a, Function.Bijective (l.toFunB a)

namespace IsCartesian

@[simp]
theorem id (P : PFunctor.{uA, uB}) : (Lens.id P).IsCartesian := fun _ => Function.bijective_id

theorem comp {l₁ : Lens Q R} {l₂ : Lens P Q}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) :
    (l₁ ∘ₗ l₂).IsCartesian := fun a => (h₂ a).comp (h₁ (l₂.toFunA a))

end IsCartesian

/-! ## Cartesianness of canonical lens constructors

Most "embedding-shaped" lenses produced by the lens algebra are cartesian.
We collect the witnesses here so that downstream classes (notably
`LawfulSubSpec`) can be discharged uniformly. -/

namespace IsCartesian

theorem inl {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    (Lens.inl : Lens.{uA₁, uB, max uA₁ uA₂, uB} P (P + Q)).IsCartesian := fun _ =>
  Function.bijective_id

theorem inr {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}} :
    (Lens.inr : Lens.{uA₂, uB, max uA₁ uA₂, uB} Q (P + Q)).IsCartesian := fun _ =>
  Function.bijective_id

theorem sumMap {P : PFunctor.{uA₁, uB₁}} {Q : PFunctor.{uA₂, uB₁}}
    {R : PFunctor.{uA₃, uB₃}} {W : PFunctor.{uA₄, uB₃}}
    {l₁ : Lens P R} {l₂ : Lens Q W}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) :
    (l₁ ⊎ₗ l₂).IsCartesian
  | Sum.inl a => h₁ a
  | Sum.inr a => h₂ a

theorem sumPair {P : PFunctor.{uA₁, uB}} {Q : PFunctor.{uA₂, uB}}
    {R : PFunctor.{uA₃, uB₃}} {l₁ : Lens P R} {l₂ : Lens Q R}
    (h₁ : l₁.IsCartesian) (h₂ : l₂.IsCartesian) :
    (Lens.sumPair l₁ l₂).IsCartesian
  | Sum.inl a => h₁ a
  | Sum.inr a => h₂ a

theorem sigmaMap {I : Type v}
    {F : I → PFunctor.{uA₁, uB₁}} {G : I → PFunctor.{uA₂, uB₂}}
    {l : ∀ i, Lens (F i) (G i)} (hl : ∀ i, (l i).IsCartesian) :
    (Lens.sigmaMap l).IsCartesian
  | ⟨i, fa⟩ => hl i fa

theorem sigmaExists {I : Type v}
    {F : I → PFunctor.{uA₁, uB₁}} {R : PFunctor.{uA₂, uB₂}}
    {l : ∀ i, Lens (F i) R} (hl : ∀ i, (l i).IsCartesian) :
    (Lens.sigmaExists l).IsCartesian
  | ⟨i, fa⟩ => hl i fa

end IsCartesian

/-! ## Sigma injection

The natural inclusion of the `j`-th summand into a `sigma`: the unique
lens whose forward action picks the `j`-th tag and whose backward action
is the identity on directions. This is the `Lens` whose corresponding
`MonadLift` underlies `OracleSpec.subSpec_sigma`. -/

/-- Lens injection `Lens (F j) (sigma F)` for a fixed index `j : I`. -/
def sigmaInj {I : Type v} {F : I → PFunctor.{uA, uB}} (j : I) :
    Lens (F j) (sigma F) :=
  (fun fa => ⟨j, fa⟩) ⇆ fun _ => id

namespace IsCartesian

theorem sigmaInj {I : Type v} {F : I → PFunctor.{uA, uB}} (j : I) :
    (Lens.sigmaInj (F := F) j).IsCartesian := fun _ => Function.bijective_id

end IsCartesian

end Lens

end PFunctor


