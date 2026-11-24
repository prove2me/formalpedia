-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:35.062656+00:00
-- url     : https://prove2.me/theorems/3e7133b0-db6b-4f09-84e1-001b9977469f
-- title:
--   Affine Space Global Sections
-- statement:
--   Definitions and structural lemmas for Affine Space Global Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceGlobalSections.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
abbrev affineSpaceIsoSpecMvPolynomial (k : Type u) [Field k] (v : Type u) :
    affineSpaceIndexedBy k v ≅ Spec (CommRingCat.of (MvPolynomial v k)) :=
  AffineSpace.SpecIso v (CommRingCat.of k)
def mvPolynomialToGlobalSections (k : Type u) [Field k] (v : Type u) :
    MvPolynomial v k →+* Γ(affineSpaceIndexedBy k v, ⊤) :=
  ((affineSpaceIsoSpecMvPolynomial k v).hom.appTop).hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv).hom
def globalSectionsToMvPolynomial (k : Type u) [Field k] (v : Type u) :
    Γ(affineSpaceIndexedBy k v, ⊤) →+* MvPolynomial v k :=
  ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom).hom.comp
    ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop).hom
theorem appTop_inv_hom_apply {X Y : Scheme.{u}} (e : X ≅ Y) (s : Γ(Y, ⊤)) :
    e.inv.appTop (e.hom.appTop s) = s := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.inv_hom_id]
  simp
theorem appTop_hom_inv_apply {X Y : Scheme.{u}} (e : X ≅ Y) (s : Γ(X, ⊤)) :
    e.hom.appTop (e.inv.appTop s) = s := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.hom_inv_id]
  simp
theorem mvPolynomialToGlobalSections_apply (k : Type u) [Field k] (v : Type u)
    (p : MvPolynomial v k) :
    mvPolynomialToGlobalSections k v p =
      (affineSpaceIsoSpecMvPolynomial k v).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := rfl
theorem globalSectionsToMvPolynomial_apply (k : Type u) [Field k] (v : Type u)
    (s : Γ(affineSpaceIndexedBy k v, ⊤)) :
    globalSectionsToMvPolynomial k v s =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom
        ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop s) := rfl
theorem leftInverse_globalSectionsToMvPolynomial (k : Type u) [Field k] (v : Type u) :
    Function.LeftInverse ⇑(globalSectionsToMvPolynomial k v) ⇑(mvPolynomialToGlobalSections k v) := by
  intro p
  rw [mvPolynomialToGlobalSections_apply, globalSectionsToMvPolynomial_apply, appTop_inv_hom_apply]
  simp
theorem rightInverse_globalSectionsToMvPolynomial (k : Type u) [Field k] (v : Type u) :
    Function.RightInverse ⇑(globalSectionsToMvPolynomial k v) ⇑(mvPolynomialToGlobalSections k v) := by
  intro s
  rw [globalSectionsToMvPolynomial_apply, mvPolynomialToGlobalSections_apply, Iso.hom_inv_id_apply,
    appTop_hom_inv_apply]
def mvPolynomialEquivGlobalSections (k : Type u) [Field k] (v : Type u) :
    MvPolynomial v k ≃+* Γ(affineSpaceIndexedBy k v, ⊤) where
  toFun := mvPolynomialToGlobalSections k v
  invFun := globalSectionsToMvPolynomial k v
  left_inv := leftInverse_globalSectionsToMvPolynomial k v
  right_inv := rightInverse_globalSectionsToMvPolynomial k v
  map_mul' := map_mul (mvPolynomialToGlobalSections k v)
  map_add' := map_add (mvPolynomialToGlobalSections k v)
end FunctorialResolution.EmbeddedResolution
end


