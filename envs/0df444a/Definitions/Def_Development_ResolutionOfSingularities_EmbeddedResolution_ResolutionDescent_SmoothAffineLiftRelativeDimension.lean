-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothAffineLiftRelativeDimension
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SmoothAffineLiftRelativeDimension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:15.223323+00:00
-- url     : https://prove2.me/theorems/801f4f80-7ebc-4cf0-8f99-5d67b3789fc7
-- title:
--   Smooth Affine Lift Relative Dimension
-- statement:
--   Definitions and structural lemmas for Smooth Affine Lift Relative Dimension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SmoothAffineLiftRelativeDimension.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StandardSmoothLiftRelativeDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
namespace SmoothChartRelativeDimension
def tensorProductLiftRingHom {S R C T : Type u} [CommRing S] [CommRing R] [CommRing C]
    [CommRing T] [Algebra S R] [Algebra S C] (a : R →+* T) (b : C →+* T)
    (hab : ∀ s : S, a (algebraMap S R s) = b (algebraMap S C s)) : (R ⊗[S] C) →+* T :=
  letI : Algebra S T := (a.comp (algebraMap S R)).toAlgebra
  letI : Algebra R T := a.toAlgebra
  haveI : IsScalarTower S R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom S R T)
      ({ toRingHom := b, commutes' := fun s => (hab s).symm } : C →ₐ[S] T)).toRingHom
end SmoothChartRelativeDimension
end FunctorialResolution.EmbeddedResolution
end


