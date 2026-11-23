-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:57.910522+00:00
-- url     : https://prove2.me/theorems/3724e991-c27b-42d2-8624-1810b79f00da
-- title:
--   Eig Lat
-- statement:
--   Definitions and structural lemmas for Eig Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/EigLat.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_LieModel
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
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
namespace LieModel
def Extends (M : LieModel G ξ E) (p : Cpt ξ) (e : E)
    (v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G) : Prop :=
  IsTanAt G _ v ∧ (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ p))) ≫ v.left
def lat (M : LieModel G ξ E) : Lat ξ E := fun p =>
  Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v}
def omLat (M : LieModel G ξ E) : Lat ξ (Module.Dual Ω E) := M.lat.dual
def eigLat (M : LieModel G ξ E) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E) (σ : O →+* Ω) : Lat ξ E :=
  M.lat.inter (eigSp ρ σ)
variable {R : Type} [CommRing R] [IsLocalRing R]
def ValAt (M : LieModel G ξ E) (z : Spec (CommRingCat.of R) ⟶ X) (e : E) (w : epsAt z ⟶ G) : Prop :=
  ∃ (h : genPt ξ ⤳ centre z) (v : epsAt (R := X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) ⟶ G),
    M.Extends ⟨centre z, h⟩ e v ∧
      w.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ v.left
def fibAt (M : LieModel G ξ E) (L : Lat ξ E) (z : Spec (CommRingCat.of R) ⟶ X) {C : Type} [Field C] [Algebra R C]
    {EC : Type} [AddCommGroup EC] [Module C EC] [Module R EC]
    (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC) : Submodule R EC :=
  Submodule.span R {w | ∃ (h : genPt ξ ⤳ centre z) (e : E), e ∈ L ⟨centre z, h⟩ ∧
    M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt w)}
end LieModel
end GlobalTheory.CompanionTheory.Ar


