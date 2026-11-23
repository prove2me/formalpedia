-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:59.384278+00:00
-- url     : https://prove2.me/theorems/52112892-2cc8-4d54-9c19-cc75d11dd6fb
-- title:
--   Structure Hom Apply
-- statement:
--   Definitions and structural lemmas for Structure Hom Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/StructureHomApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
namespace GlobalTheory.SectionsCommRing
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
def structureHom (s : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop ≫
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
theorem map_structureHom (s : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (h : V ≤ U) (r : R) :
    (X.presheaf.map (homOfLE h).op).hom (structureHom s U r) = structureHom s V r := by
  show ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ X.presheaf.map (homOfLE h).op).hom
    (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = _
  rw [← X.presheaf.map_comp]
  rfl
def Sections (_s : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : Type u := Γ(X, U)
namespace Sections
variable (s : X ⟶ Spec (CommRingCat.of R))
instance (U : X.Opens) : CommRing (Sections s U) := inferInstanceAs (CommRing Γ(X, U))
instance (U : X.Opens) : Algebra R (Sections s U) :=
  RingHom.toAlgebra (R := R) (S := Sections s U) (structureHom s U)
def equiv (U : X.Opens) : Sections s U ≃+* Γ(X, U) := RingEquiv.refl _
def restrict {U V : X.Opens} (h : V ≤ U) : Sections s U →ₐ[R] Sections s V where
  toRingHom := (X.presheaf.map (homOfLE h).op).hom
  commutes' r := map_structureHom s h r
end Sections
end GlobalTheory.SectionsCommRing


