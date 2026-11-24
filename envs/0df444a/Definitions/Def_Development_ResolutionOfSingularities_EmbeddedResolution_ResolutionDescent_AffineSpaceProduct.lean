-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:14.226264+00:00
-- url     : https://prove2.me/theorems/d6a8c9f7-ddab-4863-a858-c53f14c0b8d8
-- title:
--   Affine Space Product
-- statement:
--   Definitions and structural lemmas for Affine Space Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/AffineSpaceProduct.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineResolutionRule
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def homOfSumCoords {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u}) {X : Scheme.{u}}
    (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S) :
    X ⟶ AffineSpace n S :=
  AffineSpace.homOfVector (f ≫ AffineSpace n₁ S ↘ S)
    (fun i =>
      Sum.elim (fun a => f.appTop (AffineSpace.coord S a))
        (fun b => g.appTop (AffineSpace.coord S b)) (e.symm i))
def sumUliftEquivUliftSum (n m : ℕ) :
    (ULift.{u} (Fin n) ⊕ ULift.{u} (Fin m)) ≃ ULift.{u} (Fin n ⊕ Fin m) where
  toFun := Sum.elim (fun a => ULift.up (Sum.inl a.down)) (fun b => ULift.up (Sum.inr b.down))
  invFun := fun i =>
    Sum.elim (fun a => Sum.inl (ULift.up a)) (fun b => Sum.inr (ULift.up b)) i.down
  left_inv := by rintro (⟨a⟩ | ⟨b⟩) <;> rfl
  right_inv := by rintro ⟨a | b⟩ <;> rfl
def projRight (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)) ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m)) :=
  AffineSpace.reindex (S := Spec (CommRingCat.of k))
    (fun j : ULift.{u} (Fin m) => (ULift.up (Sum.inr j.down) : ULift.{u} (Fin n ⊕ Fin m)))
def projLeft (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)) ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n)) :=
  AffineSpace.reindex (S := Spec (CommRingCat.of k))
    (fun j : ULift.{u} (Fin n) => (ULift.up (Sum.inl j.down) : ULift.{u} (Fin n ⊕ Fin m)))
def prodMapOnPreimage (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))) :
    (projLeft k n m ⁻¹ᵁ U).toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c ⊕ Fin m)) :=
  AffineSpace.homOfVector
    ((projLeft k n m ⁻¹ᵁ U).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)))
    (fun i =>
      Sum.elim
        (fun a : Fin c =>
          (AlgebraicGeometry.morphismRestrict (projLeft k n m) U ≫ φ).appTop
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up a)))
        (fun b : Fin m =>
          ((projLeft k n m ⁻¹ᵁ U).ι).appTop
            (AffineSpace.coord (Spec (CommRingCat.of k))
              (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))))
        i.down)
end FunctorialResolution.EmbeddedResolution
end


