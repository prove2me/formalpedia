-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:46.377795+00:00
-- url     : https://prove2.me/theorems/4c7f7026-d4a3-43c8-afe7-6e36e0f8b919
-- title:
--   Torus2 Gamma Bijective
-- statement:
--   Definitions and structural lemmas for Torus2 Gamma Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/Torus2GammaBijective.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj MonObj TensorProduct
open AddMonoidAlgebra
namespace Rosenlicht
section
variable {S : Scheme.{u}}
noncomputable def torusFst (S : Scheme.{u}) (Y : Type u) [AddCommGroup Y] :
    (splitTorus S Y).left ⟶ Spec (torusRing ZU Y) :=
  pullback.fst (splitTorusAff ZU Y).hom (toZ S)
noncomputable def coord {Z : Over S} {Y : Type u} [AddCommGroup Y] (g : Z ⟶ splitTorus S Y) :
    torusRing ZU Y ⟶ Γ(Z.left, ⊤) :=
  (Scheme.ΓSpecIso (torusRing ZU Y)).inv ≫ (g.left ≫ torusFst S Y).appTop
noncomputable def chi (X : Type u) [AddCommGroup X] (a : X) : Γ((splitTorus S X).left, ⊤) :=
  (coord (𝟙 (splitTorus S X))).hom (single a 1)
end
section
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]
noncomputable abbrev zuAlgebra : Algebra ZU K := ULift.algebra' ℤ K
attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra
theorem toZ_eq : toZ (Spec (.of K)) = Spec.map (CommRingCat.ofHom (algebraMap ZU.{u} K)) := by
  first
  | exact specULiftZIsTerminal.hom_ext _ _
  | exact AlgebraicGeometry.specULiftZIsTerminal.hom_ext _ _
  | exact IsTerminal.hom_ext specULiftZIsTerminal _ _
instance isScalarTower_torus :
    IsScalarTower ZU.{u} (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X) :=
  ⟨fun r a b => by
    obtain ⟨n⟩ := r
    show (n • a) • b = n • (a • b)
    simp only [Algebra.smul_def, map_mul, _root_.mul_assoc, eq_intCast, map_intCast]⟩
theorem isPushout_torusRing :
    IsPushout (CommRingCat.ofHom (algebraMap ZU.{u} (AddMonoidAlgebra ZU.{u} X)))
      (CommRingCat.ofHom (algebraMap ZU.{u} K))
      (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X)))
      (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X))) := by
  first
  | exact CommRingCat.isPushout_of_isPushout ZU.{u} (AddMonoidAlgebra ZU.{u} X) K (AddMonoidAlgebra K X)
  | exact (CommRingCat.isPushout_iff_isPushout).2 inferInstance
  | (haveI := Algebra.IsPushout.symm
        (inferInstance : Algebra.IsPushout ZU.{u} K (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X))
     exact CommRingCat.isPushout_of_isPushout ZU.{u} (AddMonoidAlgebra ZU.{u} X) K (AddMonoidAlgebra K X))
theorem isPullback_torus :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X))))
      (splitTorusAff ZU X).hom (toZ (Spec (.of K))) := by
  rw [toZ_eq]
  first
  | exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_torusRing K X)
  | exact isPullback_Spec_map_isPushout _ _ _ _ (isPushout_torusRing K X)
  | exact (isPushout_torusRing K X).op.map Scheme.Spec
  | exact (isPushout_torusRing K X).op.flip.map Scheme.Spec
noncomputable def torusIso :
    Spec (.of (AddMonoidAlgebra K X)) ≅ (splitTorus (Spec (.of K)) X).left :=
  (isPullback_torus K X).isoPullback
theorem torusIso_hom_hom : (torusIso K X).hom ≫ (splitTorus (Spec (.of K)) X).hom =
    Spec.map (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X))) := by
  first
  | exact (isPullback_torus K X).isoPullback_hom_snd
  | (simp [torusIso]; done)
noncomputable def torusGamma :
    Γ((splitTorus (Spec (.of K)) X).left, ⊤) ⟶ CommRingCat.of (AddMonoidAlgebra K X) :=
  (torusIso K X).hom.appTop ≫ (Scheme.ΓSpecIso _).hom
end
section
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]
theorem isPullback_torus2 :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        AddMonoidAlgebra K X →+* AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X)) ≫ (torusIso K X).hom)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        AddMonoidAlgebra K X →ₐ[K] AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X).toRingHom) ≫
          (torusIso K X).hom)
      (splitTorus (Spec (.of K)) X).hom (splitTorus (Spec (.of K)) X).hom := by
  have hp : IsPushout (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X)))
      (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X)))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        AddMonoidAlgebra K X →+* AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        AddMonoidAlgebra K X →ₐ[K] AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X).toRingHom) := by
    first
    | exact CommRingCat.isPushout_tensorProduct K (AddMonoidAlgebra K X) (AddMonoidAlgebra K X)
    | exact CommRingCat.isPushout_of_isPushout K (AddMonoidAlgebra K X) (AddMonoidAlgebra K X)
        (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X)
  have h : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        AddMonoidAlgebra K X →+* AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X)))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        AddMonoidAlgebra K X →ₐ[K] AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X)))) := by
    first
    | exact isPullback_SpecMap_of_isPushout _ _ _ _ hp
    | exact isPullback_Spec_map_isPushout _ _ _ _ hp
    | exact hp.op.map Scheme.Spec
    | exact hp.op.flip.map Scheme.Spec
  refine IsPullback.of_iso h (Iso.refl _) (torusIso K X) (torusIso K X) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp [torusIso_hom_hom]
  · simp [torusIso_hom_hom]
noncomputable def torus2Iso :
    Spec (.of (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X)) ≅
      (splitTorus (Spec (.of K)) X ⊗ splitTorus (Spec (.of K)) X).left :=
  (isPullback_torus2 K X).isoPullback
noncomputable def torus2Gamma :
    Γ((splitTorus (Spec (.of K)) X ⊗ splitTorus (Spec (.of K)) X).left, ⊤) ⟶
      CommRingCat.of (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X) :=
  (torus2Iso K X).hom.appTop ≫ (Scheme.ΓSpecIso _).hom
end
section
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]
end
end Rosenlicht
end ReciprocityTheory.ChartRestriction.G.Semi


