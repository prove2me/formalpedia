-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:13:52.696911+00:00
-- url     : https://prove2.me/theorems/c72d6df4-d5f6-4496-938b-58142ba42e91
-- title:
--   Exists Torus And Quotient Hom
-- statement:
--   Definitions and structural lemmas for Exists Torus And Quotient Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsTorusAndQuotientHom.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SurjectiveAppOfIsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
import Theorems.Thm_GlobalTheory_GroupRingConst_powChar_apply
import Theorems.Thm_GlobalTheory_GroupRingConst_pt_single
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GroupRingConst.powChar_apply
attribute [local simp] GlobalTheory.GroupRingConst.pt_single
attribute [local simp] GlobalTheory.restrictPoints_val


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SemiRigid
open SplitTorus
section Affine
noncomputable def aug (R X : Type) [CommRing R] [AddCommGroup X] : AddMonoidAlgebra R X →+* R :=
  AddMonoidAlgebra.liftNCRingHom (RingHom.id R) 1 fun _ _ ↦ Commute.all _ _
theorem aug_single {R X : Type} [CommRing R] [AddCommGroup X] (a : X) (c : R) :
    aug R X (AddMonoidAlgebra.single a c) = c := by
  simp [aug]
theorem aug_comp (R X : Type) [CommRing R] [AddCommGroup X] :
    (aug R X).comp (algebraMap R _) = RingHom.id R :=
  RingHom.ext fun c ↦ aug_single 0 c
variable {S : Scheme.{0}}
noncomputable def sp {A C : CommRingCat.{0}} (ψ : A ⟶ C) {s : Spec A ⟶ S} {s' : Spec C ⟶ S}
    (h : Spec.map ψ ≫ s = s') : Over.mk s' ⟶ Over.mk s := Over.homMk (Spec.map ψ) h
variable {R : CommRingCat.{0}} (X : Type) [AddCommGroup X] (t : Spec R ⟶ S)
noncomputable abbrev grpSpec : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (torusRing R X))) ≫ t)
noncomputable def unitSec : Over.mk t ⟶ grpSpec X t :=
  sp (A := torusRing R X) (CommRingCat.ofHom (aug R X)) (by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, aug_comp]; simp)
variable [Module.Free ℤ X] [Module.Finite ℤ X] [IsDomain R]
end Affine
section Field
variable {K : Type} [Field K]
end Field
section Descent
variable {S : Scheme.{0}}
theorem isPullback_whiskerRight {G B : Over S} (p : G ⟶ B) (W : Over S) :
    IsPullback (fst G W).left (p ▷ W).left p.left (fst B W).left := by
  refine IsPullback.of_bot ?_ (congrArg (·.left) (whiskerRight_fst p W).symm)
    (IsPullback.of_hasPullback B.hom W.hom)
  rw [show (p ▷ W).left ≫ pullback.snd B.hom W.hom = (snd G W).left from
    congrArg (·.left) (whiskerRight_snd p W), Over.w]
  exact IsPullback.of_hasPullback G.hom W.hom
instance {G B : Over S} (p : G ⟶ B) (W : Over S) [Flat p.left] : Flat (p ▷ W).left :=
  MorphismProperty.of_isPullback (isPullback_whiskerRight p W) ‹_›
instance {G B : Over S} (p : G ⟶ B) (W : Over S) [Surjective p.left] : Surjective (p ▷ W).left :=
  MorphismProperty.of_isPullback (isPullback_whiskerRight p W) ‹_›
instance {G B : Over S} (p : G ⟶ B) (W : Over S) [QuasiCompact p.left] :
    QuasiCompact (p ▷ W).left :=
  MorphismProperty.of_isPullback (isPullback_whiskerRight p W) ‹_›
end Descent
section Main
variable {K : Type} [Field K]
end Main
section Family
variable {S : Scheme.{0}}
end Family
end GlobalTheory.SemiRigid
namespace GlobalTheory
open SemiRigid
end GlobalTheory


