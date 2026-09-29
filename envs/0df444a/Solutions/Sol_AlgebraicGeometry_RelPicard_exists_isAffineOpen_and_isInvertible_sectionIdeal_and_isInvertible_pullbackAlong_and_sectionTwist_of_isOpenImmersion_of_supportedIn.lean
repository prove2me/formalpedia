-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_isAffineOpen_and_isInvertible_sectionIdeal_and_isInvertible_pullbackAlong_and_sectionTwist_of_isOpenImmersion_of_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8b30b048-1cfa-5890-b1bc-d8c25336b316

import Mathlib
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_isAffineOpen_of_finset_of_universal_supportedIn
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_le_inf_forall_mem_of_finset
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso_of_range_subset
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_isAffineOpen_and_isInvertible_sectionIdeal_and_isInvertible_pullbackAlong_and_sectionTwist_of_isOpenImmersion_of_supportedIn
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    (hcov : ∀ (V : (Spec (CommRingCat.of R)).affineOpens) (F : Finset ↥U),
      (∀ x ∈ F, (U.ι ≫ c) x ∈ (V : (Spec (CommRingCat.of R)).Opens)) →
      ∃ W : (↑U : Scheme.{u}).Opens, IsAffineOpen W ∧ W ≤ (U.ι ≫ c) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) ∧
        ∀ x ∈ F, x ∈ W)
    (r g e : ℕ)

    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) (Duniv : RelEffCartierDiv c g y) (hDunivU : Duniv.SupportedIn U)
    (huniv : ∀ ⦃T : Scheme.{u}⦄ (g' : T ⟶ Spec (CommRingCat.of R)) (D : RelEffCartierDiv c g g'), D.SupportedIn U →
        ∃! φ : {φ : T ⟶ Y // φ ≫ y = g'}, PullsBackOver Duniv φ.1 φ.2 D)

    {ι : Type u} (X : ι → Scheme.{u})
    (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal)
    (hj : ∀ i, ∃ j : X i ⟶ Y, IsOpenImmersion j ∧ j ≫ y = (uliftYonedaEquiv (f i)).1)

    (Dγ : ι → RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγU : ∀ i, (Dγ i).SupportedIn U) :
    (∀ (i : ι) (F : Finset (X i)), ∃ U : (X i).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
    (∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)), (sectionIdeal c ε t).IsInvertible) ∧
    (∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)),
      ((Dγ i).pullbackAlong t (Category.comp_id t)).I.IsInvertible) ∧
    (∀ ⦃T T' : Scheme.{u}⦄ {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
      (ψ : SchemeHomOver t' t),
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (sectionTwist c ε t r) ≅ sectionTwist c ε t' r)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro i F
    obtain ⟨j, hjopen, -⟩ := hj i
    haveI := hjopen

    obtain ⟨W, hW, -, hFW⟩ :=
      AlgebraicGeometry.RelEffCartierDiv.exists_isAffineOpen_of_finset_of_universal_supportedIn c U hcov g y Duniv
        hDunivU huniv ⟨⊤, isAffineOpen_top _⟩ (F.image j.base) (fun p _ => trivial)

    obtain ⟨W', hW', hW'le, hFW'⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_le_inf_forall_mem_of_finset W hW j.opensRange (F.image j.base) hFW
        (fun p hp => by
          obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
          exact ⟨x, rfl⟩)
    refine ⟨j ⁻¹ᵁ W', ?_, fun x hx => hFW' _ (Finset.mem_image_of_mem _ hx)⟩
    have hle : W' ≤ j.opensRange := hW'le.trans inf_le_right
    have himg : j ''ᵁ (j ⁻¹ᵁ W') = W' := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_eq_right.mpr hle
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion j, himg]
    exact hW'
  ·
    intro T t
    exact AlgebraicGeometry.RelPicard.isInvertible_sectionIdeal_of_range_subset c ε U hεU t
  ·
    intro i T t
    exact AlgebraicGeometry.RelEffCartierDiv.isInvertible_I_of_supportedIn (f := c) U _
      ((hDγU i).pullbackAlong t (Category.comp_id t))
  ·
    intro T T' t t' ψ
    exact AlgebraicGeometry.RelPicard.nonempty_pullback_sectionTwist_iso_of_range_subset R c ε U hεU ψ r

end S_AlgebraicGeometry_RelPicard_exists_isAffineOpen_and_isInvertible_sectionIdeal_and_isInvertible_pullbackAlong_and_sectionTwist_of_isOpenImmersion_of_supportedIn
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_isAffineOpen_and_isInvertible_sectionIdeal_and_isInvertible_pullbackAlong_and_sectionTwist_of_isOpenImmersion_of_supportedIn (solution)
