-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_LieModel
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_LieModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:09.710673+00:00
-- url     : https://prove2.me/theorems/1ed0d6fa-cf4b-4d73-b2ca-d6604e761359
-- title:
--   Lie Model
-- statement:
--   Definitions and structural lemmas for Lie Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/LieModel.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
abbrev epsAt (x : Spec (CommRingCat.of R) ⟶ S) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x)
def IsTanAt (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (v : epsAt x ⟶ G) : Prop :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ v.left = (1 : Over.mk x ⟶ G).left
def epsMul (c : R) : DualNumber R →+* DualNumber R :=
  (TrivSqZeroExt.map (c • (LinearMap.id : R →ₗ[R] R))).toRingHom
def dualMap (φ : R →+* R') : DualNumber R →+* DualNumber R' where
  toFun a := TrivSqZeroExt.inl (φ a.fst) + TrivSqZeroExt.inr (φ a.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
structure LieModel (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E]
    [Module R E] where

  pt : E → (epsAt x ⟶ G)
  tan : ∀ e, IsTanAt G x (pt e)
  inj : Function.Injective pt
  onto : ∀ v, IsTanAt G x v → ∃ e, pt e = v
  add : ∀ e e', pt (e + e') = pt e * pt e'
  smul : ∀ (c : R) e, (pt (c • e)).left = Spec.map (CommRingCat.ofHom (epsMul c)) ≫ (pt e).left
def LieModel.IsDiffOf {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E]
    [Module R E] (M : LieModel G x E) (f : G ⟶ G) (A : E →ₗ[R] E) : Prop :=
  ∀ e, M.pt (A e) = M.pt e ≫ f
def LieModel.IsActOf {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E]
    [Module R E] (M : LieModel G x E) {O : Type} [CommRing O] (act : O → (G ⟶ G))
    (ρ : O →+* Module.End R E) : Prop :=
  ∀ a, M.IsDiffOf (act a) (ρ a)
def eigSp {E : Type} [AddCommGroup E] [Module R E] {O : Type} [CommRing O] (ρ : O →+* Module.End R E)
    (σ : O →+* R) : Submodule R E :=
  ⨅ a, LinearMap.ker (ρ a - σ a • LinearMap.id)
end GlobalTheory.CompanionTheory.Ar


