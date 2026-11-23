-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:29.276714+00:00
-- url     : https://prove2.me/theorems/b7f22c66-efe4-4354-9687-48f8b4d335ae
-- title:
--   Is Quasicoherent Of Forall Exists Affine
-- statement:
--   Definitions and structural lemmas for Is Quasicoherent Of Forall Exists Affine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
namespace GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
abbrev resAlgebra (h : V ≤ U) : Algebra Γ(X, U) Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom.toAlgebra
abbrev resModule (h : V ≤ U) : Module Γ(X, U) Γ(F, V) :=
  Module.compHom Γ(F, V) (X.presheaf.map (homOfLE h).op).hom
theorem res_isScalarTower (h : V ≤ U) :
    letI := resAlgebra h
    letI := resModule F h
    IsScalarTower Γ(X, U) Γ(X, V) Γ(F, V) :=
  letI := resAlgebra h
  letI := resModule F h
  .of_algebraMap_smul fun _ _ ↦ rfl
def resLinear (h : V ≤ U) :
    letI := resModule F h
    Γ(F, U) →ₗ[Γ(X, U)] Γ(F, V) :=
  letI := resModule F h
  { toFun := F.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r s ↦ F.map_smul (homOfLE h) r s }
instance moduleSectionsBasicOpen (f : Γ(X, U)) : Module Γ(X, U) Γ(F, X.basicOpen f) :=
  resModule F (X.basicOpen_le f)
instance isScalarTower_sectionsBasicOpen (f : Γ(X, U)) :
    IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) :=
  res_isScalarTower F (X.basicOpen_le f)
def resBasicOpen (f : Γ(X, U)) : Γ(F, U) →ₗ[Γ(X, U)] Γ(F, X.basicOpen f) :=
  resLinear F (X.basicOpen_le f)
section Spec
variable (hU : IsAffineOpen U)
theorem fromSpec_image_le (W : (Spec Γ(X, U)).Opens) : hU.fromSpec ''ᵁ W ≤ U :=
  (hU.fromSpec.image_le_opensRange W).trans hU.opensRange_fromSpec.le
end Spec
section Elementwise
variable [F.IsQuasicoherent]
end Elementwise
section Algebra
end Algebra
section Stalk
instance stalkModule (x : X) : Module (X.presheaf.stalk x) (F.presheaf.stalk x :) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x
theorem germ_smul (x : X) (hx : x ∈ U) (r : Γ(X, U)) (s : Γ(F, U)) :
    F.presheaf.germ U x hx (r • s) = X.presheaf.germ U x hx r • F.presheaf.germ U x hx s :=
  PresheafOfModules.germ_smul (R := X.presheaf) F.val x U hx r s
instance stalkModuleSections (x : U) : Module Γ(X, U) (F.presheaf.stalk (x : X) :) :=
  Module.compHom _ (X.presheaf.germ U x x.2).hom
instance isScalarTower_stalk (x : U) :
    IsScalarTower Γ(X, U) (X.presheaf.stalk (x : X)) (F.presheaf.stalk (x : X) :) :=
  .of_algebraMap_smul fun _ _ ↦ rfl
def germLinear (x : U) : Γ(F, U) →ₗ[Γ(X, U)] (F.presheaf.stalk (x : X) :) where
  toFun := F.presheaf.germ U x x.2
  map_add' := map_add _
  map_smul' r s := germ_smul F x x.2 r s
end Stalk
end GlobalTheory.QCoh


