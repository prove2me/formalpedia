-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.isClosedImmersion_one_and_forall_iff_isInStabilizer_of_kernelTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/af290fce-2d26-59a0-a245-49b9bb070684

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Theorems.Thm_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit_of_commRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_isClosedImmersion_one_and_forall_iff_isInStabilizer_of_kernelTrivial
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_AlgebraicGeometry_Polarisation_isClosedImmersion_one_and_forall_iff_isInStabilizer_of_kernelTrivial.GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace GoodReductionJacobian p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle RelativeGroupLaw" namespace RelativeGroupLaw p2m_export "GoodReductionJacobian.RelativeGroupLaw" "one_natural one IsInStabilizer isInStabilizer_one" end GoodReductionJacobian.RelativeGroupLaw
namespace GoodReductionJacobian.RelativeGroupLaw
p2m_open_scoped "GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw" in

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.one_coe_eq_comp {R : Type} [CommRing R] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  rw [← h]
  rfl

end GoodReductionJacobian.RelativeGroupLaw
p2m_export "" "GoodReductionJacobian.RelativeGroupLaw.one_coe_eq_comp"
theorem solution
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (hA : AbelianSchemePropertyBundle K f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : KernelTrivial f L 𝓛) :
    IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of K)))).1 ∧
      IsFinite ((L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f) ∧
      ((L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f).finrank (IsLocalRing.closedPoint K) = 1 ∧
      ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
        (∃ x₀ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K), x₀ ≫ (L.one (𝟙 (Spec (CommRingCat.of K)))).1 = x.1) ↔
          L.IsInStabilizer 𝓛 t x := by
  classical
  haveI : IsProper f := hA.proper
  have h1 : (L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f = 𝟙 _ := (L.one _).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI : IsClosedImmersion ((L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f) := by rw [h1]; infer_instance
    exact IsClosedImmersion.of_comp (L.one (𝟙 (Spec (CommRingCat.of K)))).1 f
  · rw [h1]; infer_instance
  · rw [h1]
    have hid : (𝟙 (Spec (CommRingCat.of K))) = Spec.map (CommRingCat.ofHom (algebraMap K K)) := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rw [hid, Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_self]
    rfl
  · intro R _ t x
    constructor
    · rintro ⟨x₀, hx₀⟩
      have hx0 : x₀ = t := by
        have h2 := x.2
        rw [← hx₀, Category.assoc, h1, Category.comp_id] at h2
        exact h2
      have hx : x = L.one t := by
        apply Subtype.ext
        rw [← hx₀, hx0, L.one_coe_eq_comp t]
      rw [hx]
      exact L.isInStabilizer_one 𝓛 t
    · intro hst
      have hloc := (AlgebraicGeometry.Polarisation.isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit_of_commRing
        K f L 𝓛 h𝓛 R t x).1 hst
      have hx : x = L.one t := hK R t x hloc
      exact ⟨t, by rw [hx, L.one_coe_eq_comp t]⟩

end S_AlgebraicGeometry_Polarisation_isClosedImmersion_one_and_forall_iff_isInStabilizer_of_kernelTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_isClosedImmersion_one_and_forall_iff_isInStabilizer_of_kernelTrivial (solution)
