-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_isClosed_mem_iff_exists_unit_hom_pullback_sliceAt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/10e03aac-aa37-53f1-87f2-f85bbde5414c

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isClosed_setOf_le_finrank_sections_pullback_residueField
import Theorems.Thm_AlgebraicGeometry_Polarisation_le_finrank_sections_residueField_fibre_iff_exists_unit_hom_pullback_sliceAt_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_isClosed_mem_iff_exists_unit_hom_pullback_sliceAt_ne_zero
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation Topology"

namespace FibreH0Locus

variable {k : Type} [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
  (hA : AbelianSchemePropertyBundle k f) (Λ : (pullback f f).Modules) (hΛ : Scheme.Modules.IsInvertible Λ)
  (U : A.Opens) (hU : IsAffineOpen U)

abbrev chartBase : Spec Γ(A, U) ⟶ Spec (CommRingCat.of k) := hU.fromSpec ≫ f

abbrev chartTotal : Scheme.{0} := pullback f (chartBase f U hU)

abbrev chartMap : chartTotal f U hU ⟶ Spec Γ(A, U) := pullback.snd f (chartBase f U hU)

def chartToProd : chartTotal f U hU ⟶ pullback f f :=
  pullback.lift (pullback.fst f (chartBase f U hU)) (pullback.snd f (chartBase f U hU) ≫ hU.fromSpec)
    (by rw [Category.assoc]; exact pullback.condition)

abbrev chartMod : (chartTotal f U hU).Modules := (Scheme.Modules.pullback (chartToProd f U hU)).obj Λ

def chartLocus : Set (PrimeSpectrum Γ(A, U)) :=
  {𝔭 : PrimeSpectrum Γ(A, U) |
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd (chartMap f U hU) (Scheme.TwoAffineOpenCover.specMap Γ(A, U) 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst (chartMap f U hU) (Scheme.TwoAffineOpenCover.specMap Γ(A, U) 𝔭.asIdeal.ResidueField))).obj (chartMod f Λ U hU)) ⊤
      1 ≤ Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback
          (Limits.pullback.fst (chartMap f U hU) (Scheme.TwoAffineOpenCover.specMap Γ(A, U) 𝔭.asIdeal.ResidueField))).obj (chartMod f Λ U hU), ⊤)}

include hA hΛ in
theorem isClosed_chartLocus : IsClosed (chartLocus f Λ U hU) := by
  haveI : IsProper f := hA.proper
  haveI : Smooth f := hA.smooth
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsNoetherianRing Γ(A, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : IsProper (chartMap f U hU) := inferInstance
  haveI : Flat (chartMap f U hU) := inferInstance
  exact AlgebraicGeometry.Scheme.Modules.isClosed_setOf_le_finrank_sections_pullback_residueField (chartMap f U hU)
    (chartMod f Λ U hU) ((hΛ.pullback _).1) 1

include hA hΛ in

theorem fibre_ident (L : RelativeGroupLaw k f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (𝔭 : PrimeSpectrum Γ(A, U))
    (h𝔭 : hU.fromSpec.base 𝔭 = x.1.base (IsLocalRing.closedPoint k)) :
    𝔭 ∈ chartLocus f Λ U hU ↔
      ∃ s : 𝟙_ (pullback f (𝟙 (Spec (CommRingCat.of k)))).Modules ⟶ (Scheme.Modules.pullback (sliceAt f x)).obj Λ, s ≠ 0 :=
  AlgebraicGeometry.Polarisation.le_finrank_sections_residueField_fibre_iff_exists_unit_hom_pullback_sliceAt_ne_zero k f L hA Λ hΛ U hU x 𝔭 h𝔭

theorem mem_image_of_mem_closure {S : Set (PrimeSpectrum Γ(A, U))} (hS : IsClosed S) {a : A}
    (haU : a ∈ (U : Set A)) (ha : a ∈ closure (hU.fromSpec.base '' S)) : a ∈ hU.fromSpec.base '' S := by
  classical
  by_contra hnot
  have hrange : a ∈ Set.range hU.fromSpec.base := by rw [IsAffineOpen.range_fromSpec]; exact haU
  obtain ⟨𝔮, rfl⟩ := hrange
  have hmem : hU.fromSpec.base 𝔮 ∈ hU.fromSpec.base '' Sᶜ := ⟨𝔮, fun h => hnot ⟨𝔮, h, rfl⟩, rfl⟩
  have hopen : IsOpen (hU.fromSpec.base '' Sᶜ) := hU.fromSpec.isOpenEmbedding.isOpenMap _ hS.isOpen_compl
  rw [mem_closure_iff] at ha
  obtain ⟨b, ⟨𝔮₁, h1, rfl⟩, ⟨𝔮₂, h2, h12⟩⟩ := ha _ hopen hmem
  have : 𝔮₂ = 𝔮₁ := hU.fromSpec.isOpenEmbedding.injective h12
  exact h1 (this ▸ h2)

end FibreH0Locus

open FibreH0Locus in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (Λ : (pullback f f).Modules) (hΛ : Scheme.Modules.IsInvertible Λ) :
    ∃ Z : Set A, IsClosed Z ∧ ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      x.1.base (IsLocalRing.closedPoint k) ∈ Z ↔
        ∃ s : 𝟙_ (pullback f (𝟙 (Spec (CommRingCat.of k)))).Modules ⟶ (Scheme.Modules.pullback (sliceAt f x)).obj Λ, s ≠ 0 := by
  classical
  let pt := IsLocalRing.closedPoint k
  let P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f → Prop := fun x =>
    ∃ s : 𝟙_ (pullback f (𝟙 (Spec (CommRingCat.of k)))).Modules ⟶ (Scheme.Modules.pullback (sliceAt f x)).obj Λ, s ≠ 0
  let G : Set A := {a | ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, x.1.base pt = a ∧ P x}
  refine ⟨closure G, isClosed_closure, fun x => ⟨fun hx => ?_, fun hP => subset_closure ⟨x, rfl, hP⟩⟩⟩

  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := A.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (x.1.base pt)) isOpen_univ
  have hxU' : x.1.base pt ∈ Set.range hU.fromSpec.base := by rw [IsAffineOpen.range_fromSpec]; exact hxU
  obtain ⟨𝔭, h𝔭⟩ := hxU'
  rw [← fibre_ident f hA Λ hΛ U hU L x 𝔭 h𝔭]

  have hS := isClosed_chartLocus f hA Λ hΛ U hU
  have hGU : (U : Set A) ∩ G ⊆ hU.fromSpec.base '' chartLocus f Λ U hU := by
    rintro a ⟨haU, ⟨y, rfl, hy⟩⟩
    have hyU : y.1.base pt ∈ Set.range hU.fromSpec.base := by rw [IsAffineOpen.range_fromSpec]; exact haU
    obtain ⟨𝔮, h𝔮⟩ := hyU
    exact ⟨𝔮, (fibre_ident f hA Λ hΛ U hU L y 𝔮 h𝔮).2 hy, h𝔮⟩
  have h1 : x.1.base pt ∈ closure ((U : Set A) ∩ G) := U.2.inter_closure ⟨hxU, hx⟩
  have h2 : x.1.base pt ∈ closure (hU.fromSpec.base '' chartLocus f Λ U hU) := closure_mono hGU h1
  obtain ⟨𝔮, h𝔮S, h𝔮⟩ := mem_image_of_mem_closure U hU hS hxU h2
  have : 𝔮 = 𝔭 := hU.fromSpec.isOpenEmbedding.injective (h𝔮.trans h𝔭.symm)
  exact this ▸ h𝔮S

end
end S_AlgebraicGeometry_Polarisation_exists_isClosed_mem_iff_exists_unit_hom_pullback_sliceAt_ne_zero
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_isClosed_mem_iff_exists_unit_hom_pullback_sliceAt_ne_zero (solution)
