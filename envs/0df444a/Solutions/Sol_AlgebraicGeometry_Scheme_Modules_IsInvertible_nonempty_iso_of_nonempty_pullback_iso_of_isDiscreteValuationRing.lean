-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_nonempty_pullback_iso_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/fe277c70-c162-5000-bd57-c5ccc658d7ad

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_basicOpen_iso_of_nonempty_pullback_iso_of_isFractionRing
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_isDiscreteValuationRing_stalk_maximalIdeal_eq_span_germ_of_isIrreducible_fibre
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_basicOpen_le_mem_nonempty_pullback_iso_of_isDiscreteValuationRing_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_isDiscreteValuationRing
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (KK : Type) [Field KK] [Algebra R KK] [IsFractionRing R KK]
    {X XK : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (hsm : Smooth f) [QuasiCompact f]
    (hirr : ∀ s : ↥(Spec (CommRingCat.of R)), IsIrreducible (f.base ⁻¹' {s}))
    (fK : XK ⟶ Spec (CommRingCat.of KK)) (gK : XK ⟶ X) (hgK : IsPullback gK fK f (Spec.map (CommRingCat.ofHom (algebraMap R KK))))
    (M M' : X.Modules) (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')
    (h : Nonempty ((Scheme.Modules.pullback gK).obj M ≅ (Scheme.Modules.pullback gK).obj M')) :
    Nonempty (M ≅ M') := by
  classical
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq
  haveI : Smooth f := hsm

  obtain ⟨hmem, ⟨e₀⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.nonempty_pullback_basicOpen_iso_of_nonempty_pullback_iso_of_isFractionRing
      R ϖ hϖ KK f fK gK hgK M M' h

  obtain ⟨ξ, hξ, hcomp, hdom, hdvr, hmax⟩ :=
    AlgebraicGeometry.Smooth.exists_isDiscreteValuationRing_stalk_maximalIdeal_eq_span_germ_of_isIrreducible_fibre
      R ϖ hϖ f (hirr _)
  haveI := hdom
  haveI := hdvr

  obtain ⟨V, hUV, hξV, ⟨eV⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_basicOpen_le_mem_nonempty_pullback_iso_of_isDiscreteValuationRing_stalk
      _ ξ hmax M M' hM hM' ⟨e₀⟩

  have hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V := by
    intro x hx
    refine AlgebraicGeometry.mem_of_ringKrullDim_stalk_le_one_of_isDiscreteValuationRing R f V ?_ ?_ x hx
    · intro y hy
      exact hUV ((hmem y).mpr hy)
    · intro Z hZ
      obtain ⟨z, hzZ, hz⟩ := hcomp Z hZ
      refine ⟨z, hzZ, ?_⟩
      rw [hz]
      exact hξV

  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hX := fun x => AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R f x
  obtain ⟨⟨ψ, hψ, -⟩, hiso⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk
      hX V hdim hM hM' eV.hom
  haveI : IsIso ψ := hiso ψ hψ inferInstance
  exact ⟨asIso ψ⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_isDiscreteValuationRing
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_isDiscreteValuationRing (solution)
