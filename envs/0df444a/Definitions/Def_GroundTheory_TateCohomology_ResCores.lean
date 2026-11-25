-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_ResCores
-- name    : GroundTheory_TateCohomology_ResCores
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:07:29.666328+00:00
-- url     : https://prove2.me/theorems/da64df23-6e9e-466c-8fde-bb595f57aa58
-- title:
--   Res Cores
-- statement:
--   Definitions and structural lemmas for Res Cores, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCores.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateShapiro
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]
omit [Fintype G] [Fintype S] in

lemma shortExact_map_resFunctor {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    (X.map (resFunctor S.subtype)).ShortExact :=
  (Rep.shortExact_res S.subtype).2 hX
section Res
noncomputable def tateRes (n : ℤ) :
    tateCohomologyFunctor (R := k) (G := G) n ⟶
      resFunctor S.subtype ⋙ tateCohomologyFunctor (R := k) (G := S) n :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (Rep.resCoindAdjunction.{u, u} k S.subtype).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (resFunctor S.subtype) (tateCoindNatIso S n).hom
@[simps]
noncomputable def resCoindUnitShortComplex (X : ShortComplex (Rep.{u} k G)) :
    X ⟶ (X.map (resFunctor S.subtype)).map (coindFunctor k S.subtype) where
  τ₁ := (Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app X.X₁
  τ₂ := (Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app X.X₂
  τ₃ := (Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app X.X₃
  comm₁₂ := ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.naturality X.f).symm
  comm₂₃ := ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.naturality X.g).symm
end Res
section Cores
open scoped Classical in

noncomputable def tateCores (n : ℤ) :
    resFunctor S.subtype ⋙ tateCohomologyFunctor (R := k) (G := S) n ⟶
      tateCohomologyFunctor (R := k) (G := G) n :=
  Functor.whiskerLeft (resFunctor S.subtype) (tateIndNatIso S n).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Rep.indResAdjunction.{u} k S.subtype).counit _ ≫
    (Functor.leftUnitor _).hom
@[simps]
noncomputable def indResCounitShortComplex (X : ShortComplex (Rep.{u} k G)) :
    (X.map (resFunctor S.subtype)).map (indFunctor k S.subtype) ⟶ X where
  τ₁ := (Rep.indResAdjunction.{u} k S.subtype).counit.app X.X₁
  τ₂ := (Rep.indResAdjunction.{u} k S.subtype).counit.app X.X₂
  τ₃ := (Rep.indResAdjunction.{u} k S.subtype).counit.app X.X₃
  comm₁₂ := ((Rep.indResAdjunction.{u} k S.subtype).counit.naturality X.f).symm
  comm₂₃ := ((Rep.indResAdjunction.{u} k S.subtype).counit.naturality X.g).symm
end Cores
end GroundTheory.GroupCoh


