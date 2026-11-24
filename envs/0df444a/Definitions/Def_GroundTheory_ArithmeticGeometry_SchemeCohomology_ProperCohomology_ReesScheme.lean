-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesScheme
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesScheme
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:23.489953+00:00
-- url     : https://prove2.me/theorems/86a15f0f-43eb-4136-8f50-056298fcec0e
-- title:
--   Rees Scheme
-- statement:
--   Definitions and structural lemmas for Rees Scheme, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesScheme.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesSubmodule
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackGamma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
noncomputable section
section Schemes
variable {A : Type u} [CommRing A] (I : Ideal A) (X : Scheme.{u}) [X.Over (Spec (.of A))]
abbrev reesStructure : Spec (.of (reesAlgebra I)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (reesAlgebra I)))
abbrev reesPolyStructure : Spec (.of (Polynomial A)) ⟶ Spec (.of (reesAlgebra I)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (reesAlgebra I) (Polynomial A)))
def reesScheme : Scheme.{u} := pullback (X ↘ Spec (.of A)) (reesStructure I)
def reesPr : reesScheme I X ⟶ X := pullback.fst _ _
def reesSnd : reesScheme I X ⟶ Spec (.of (reesAlgebra I)) := pullback.snd _ _
instance : (reesScheme I X).Over (Spec (.of (reesAlgebra I))) := ⟨reesSnd I X⟩
instance : IsAffineHom (reesPr I X) :=
  isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
instance [IsProper (X ↘ Spec (.of A))] :
    IsProper (reesScheme I X ↘ Spec (.of (reesAlgebra I))) := by
  change IsProper (pullback.snd (X ↘ Spec (.of A)) (reesStructure I))
  infer_instance
def reesPolyScheme : Scheme.{u} := pullback (reesSnd I X) (reesPolyStructure I)
def reesPolyMap : reesPolyScheme I X ⟶ reesScheme I X := pullback.fst _ _
def reesPolySnd : reesPolyScheme I X ⟶ Spec (.of (Polynomial A)) := pullback.snd _ _
instance : IsAffineHom (reesPolyMap I X) :=
  isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
end Schemes
section Rings
variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
variable (X) in

def algV (V : X.Opens) : A →+* Γ(X, V) :=
  ((X ↘ Spec (.of A)).appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom
variable {V : X.Opens} (hV : IsAffineOpen V)
variable (I) in

def reesInr (V : X.Opens) : CommRingCat.of (reesAlgebra I) ⟶ Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) :=
  (Scheme.ΓSpecIso (.of (reesAlgebra I))).inv ≫ (reesSnd I X).appLE ⊤ _ le_top
variable (I) in

def polyInr (V : X.Opens) : CommRingCat.of (Polynomial A) ⟶
    Γ(reesPolyScheme I X, reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V)) :=
  (Scheme.ΓSpecIso (.of (Polynomial A))).inv ≫ (reesPolySnd I X).appLE ⊤ _ le_top
end Rings
end
end GroundTheory.Arith.SchemeCoh


