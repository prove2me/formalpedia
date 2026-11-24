-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitDefs
-- name    : GroundTheory_ProfiniteCohomology_ColimitDefs
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:49.255687+00:00
-- url     : https://prove2.me/theorems/c165f282-4cd4-410d-9d46-d14c750b0dcd
-- title:
--   Colimit Defs
-- statement:
--   Definitions and structural lemmas for Colimit Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ColimitDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Theorems.Thm_GroundTheory_ProfCoh_invariants_comp_subtype_antitone
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
theorem isLocallyConstant_comp_quotient_mk [IsTopologicalGroup G] (U : OpenNormalSubgroup G) {n : ℕ} {X : Type*}
    (y : (Fin n → G ⧸ (U : Subgroup G)) → X) :
    IsLocallyConstant fun g : Fin n → G => y fun i => (g i : G ⧸ (U : Subgroup G)) :=
  (IsLocallyConstant.of_discrete y).comp_continuous
    (continuous_pi fun i => continuous_quot_mk.comp (continuous_apply i))
noncomputable abbrev quotientMapOfLE {U V : OpenNormalSubgroup G} (h : V ≤ U) :
    G ⧸ (V : Subgroup G) →* G ⧸ (U : Subgroup G) :=
  QuotientGroup.map _ _ (MonoidHom.id G) fun _ hx => h hx
@[simp]
theorem quotientMapOfLE_mk {U V : OpenNormalSubgroup G} (h : V ≤ U) (g : G) :
    quotientMapOfLE h (g : G ⧸ (V : Subgroup G)) = (g : G ⧸ (U : Subgroup G)) :=
  rfl
section Level
variable (A : Rep.{u} k G)
noncomputable def invariantsInclusion {U V : OpenNormalSubgroup G} (h : V ≤ U) :
    Rep.res (quotientMapOfLE h) (A.quotientToInvariants (U : Subgroup G)) ⟶
      A.quotientToInvariants (V : Subgroup G) :=
  Rep.ofHom ⟨Submodule.inclusion (invariants_comp_subtype_antitone A fun _ hx => h hx),
    fun g => QuotientGroup.induction_on g fun _ => LinearMap.ext fun _ => rfl⟩
@[simp]
theorem invariantsInclusion_hom_apply {U V : OpenNormalSubgroup G} (h : V ≤ U)
    (x : Representation.invariants (A.ρ.comp (U : Subgroup G).subtype)) :
    ((invariantsInclusion A h).hom x : A) = x :=
  rfl
noncomputable abbrev transitionCochains {U V : OpenNormalSubgroup G} (h : V ≤ U) :
    inhomogeneousCochains (A.quotientToInvariants (U : Subgroup G)) ⟶
      inhomogeneousCochains (A.quotientToInvariants (V : Subgroup G)) :=
  groupCohomology.cochainsMap (quotientMapOfLE h) (invariantsInclusion A h)
noncomputable def transition {U V : OpenNormalSubgroup G} (h : V ≤ U) (n : ℕ) :
    groupCohomology (A.quotientToInvariants (U : Subgroup G)) n ⟶
      groupCohomology (A.quotientToInvariants (V : Subgroup G)) n :=
  groupCohomology.map (quotientMapOfLE h) (invariantsInclusion A h) n
theorem transitionCochains_refl (U : OpenNormalSubgroup G) :
    transitionCochains A (le_refl U) = 𝟙 _ := by
  rw [← groupCohomology.cochainsMap_id]
  exact groupCohomology.cochainsMap_congr
    (MonoidHom.ext fun g => QuotientGroup.induction_on g fun _ => rfl) (LinearMap.ext fun _ => rfl)
theorem transitionCochains_trans {U V W : OpenNormalSubgroup G} (hVU : V ≤ U) (hWV : W ≤ V) :
    transitionCochains A (hWV.trans hVU) =
      transitionCochains A hVU ≫ transitionCochains A hWV := by
  rw [← groupCohomology.cochainsMap_comp]
  exact groupCohomology.cochainsMap_congr
    (MonoidHom.ext fun g => QuotientGroup.induction_on g fun _ => rfl) (LinearMap.ext fun _ => rfl)
variable (k G) in

example [Nonempty (OpenNormalSubgroup G)] : IsFiltered (OpenNormalSubgroup G)ᵒᵖ := inferInstance
@[simps]
noncomputable def levelCochains :
    (OpenNormalSubgroup G)ᵒᵖ ⥤ CochainComplex (ModuleCat k) ℕ where
  obj U := inhomogeneousCochains (A.quotientToInvariants (U.unop : Subgroup G))
  map f := transitionCochains A (leOfHom f.unop)
  map_id U := transitionCochains_refl A U.unop
  map_comp f g := transitionCochains_trans A (leOfHom f.unop) (leOfHom g.unop)
noncomputable abbrev levelFunctor (n : ℕ) : (OpenNormalSubgroup G)ᵒᵖ ⥤ ModuleCat k :=
  levelCochains A ⋙ HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n
variable [IsTopologicalGroup G] [IsDiscreteRep A]
noncomputable abbrev infCochains (U : OpenNormalSubgroup G) :
    inhomogeneousCochains (A.quotientToInvariants (U : Subgroup G)) ⟶ inhomogeneousCochains A :=
  groupCohomology.cochainsMap (QuotientGroup.mk' (U : Subgroup G))
    (Rep.ofHom (A.ρ.quotientToInvariants_lift (U : Subgroup G)))
noncomputable def inflationCochainsX (U : OpenNormalSubgroup G) (n : ℕ) :
    (inhomogeneousCochains (A.quotientToInvariants (U : Subgroup G))).X n ⟶
      (cochainsComplex A).X n :=
  ModuleCat.ofHom <| LinearMap.codRestrict (locallyConstantCochains A n)
    ((infCochains A U).f n).hom
    fun x => isLocallyConstant_comp_quotient_mk U fun q => (x q : A)
theorem inflationCochainsX_comp_ι (U : OpenNormalSubgroup G) (n : ℕ) :
    inflationCochainsX A U n ≫ (cochainsComplexι A).f n = (infCochains A U).f n :=
  rfl
noncomputable def inflationCochains (U : OpenNormalSubgroup G) :
    inhomogeneousCochains (A.quotientToInvariants (U : Subgroup G)) ⟶ cochainsComplex A where
  f n := inflationCochainsX A U n
  comm' i j _ := by
    rw [← cancel_mono ((cochainsComplexι A).f j), Category.assoc, Category.assoc,
      ← (cochainsComplexι A).comm i j, ← Category.assoc, inflationCochainsX_comp_ι,
      inflationCochainsX_comp_ι, HomologicalComplex.Hom.comm]
@[simp]
theorem inflationCochains_f_hom_apply (U : OpenNormalSubgroup G) (n : ℕ)
    (x : (Fin n → G ⧸ (U : Subgroup G)) →
      Representation.invariants (A.ρ.comp (U : Subgroup G).subtype)) (g : Fin n → G) :
    ((cochainsComplexι A).f n).hom (((inflationCochains A U).f n).hom x) g =
      (x fun i => (g i : G ⧸ (U : Subgroup G)) : A) :=
  rfl
noncomputable def inflation (U : OpenNormalSubgroup G) (n : ℕ) :
    groupCohomology (A.quotientToInvariants (U : Subgroup G)) n ⟶ cohomology A n :=
  HomologicalComplex.homologyMap (inflationCochains A U) n
theorem transitionCochains_comp_inflationCochains {U V : OpenNormalSubgroup G} (h : V ≤ U) :
    transitionCochains A h ≫ inflationCochains A V = inflationCochains A U := by
  ext n : 1
  rw [← cancel_mono ((cochainsComplexι A).f n), HomologicalComplex.comp_f, Category.assoc]
  ext x : 2
  rfl
@[simps]
noncomputable def inflationCochainsCocone : Limits.Cocone (levelCochains A) where
  pt := cochainsComplex A
  ι :=
    { app U := inflationCochains A U.unop
      naturality U V f := by
        exact (transitionCochains_comp_inflationCochains A (leOfHom f.unop)).trans
          (Category.comp_id _).symm }
noncomputable abbrev inflationCocone (n : ℕ) : Limits.Cocone (levelFunctor A n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).mapCocone
    (inflationCochainsCocone A)
end Level
end GroundTheory.ProfCoh


