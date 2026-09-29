-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.exists_point_forall_mem_iff_of_isClosedImmersion_of_forall_geomFibreH0Finrank_eq_eval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/332dd657-b6ac-5b41-a236-357d1f1e9e5e

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_forall_mem_iff_of_isClosedImmersion_of_forall_geomFibreH0Finrank_eq_eval
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false
p2m_open "MvPolynomial CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.HilbertFunctor"
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ m : ℕ, D₀ ≤ m → ∀ (k : Type) [Field k] [IsAlgClosed k]
      (Z : Scheme.{0}) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)), IsClosedImmersion ι →
      ∀ (𝓛 : Z.Modules) (_h𝓛 : Scheme.Modules.IsInvertible 𝓛)
        (𝔓 : Scheme.Modules.ProjPresentation 𝓛 (ι ≫ ProjSpace.π k n) n) (_h𝔓 : 𝔓.toProj = ι),
      (∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
        ((Scheme.Modules.geomFibreH0Finrank (ι ≫ ProjSpace.π k n)
          (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules) (fun _ M => M ⊗ 𝓛) d) k (RingHom.id k) : ℕ) : ℚ) =
          P.eval (d : ℚ)) →
      ∃ q : Point k n (hilbertFunctionOf n P m),
        ∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
          (F ∈ q.I ↔ ∀ i : Fin (n + 1),
            ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))
              ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0) := by
  classical
  obtain ⟨G, hG⟩ :=
    AlgebraicGeometry.HilbertFunctor.exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq n P
  refine ⟨G, ?_⟩
  intro m hm k _ _ Z ι hι 𝓛 h𝓛 𝔓 h𝔓 hh0
  obtain ⟨d₀, hd₀⟩ := hh0

  obtain ⟨I, hIhom, hIZ, P', D₁, hP'⟩ :=
    AlgebraicGeometry.HilbertFunctor.exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial n k Z ι hι

  obtain ⟨q', hq'⟩ :=
    AlgebraicGeometry.HilbertFunctor.exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq n k P' D₁ I hIhom hP'

  have hZ' : ∀ d : ℕ, D₁ ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
      (F ∈ q'.I ↔ ∀ i : Fin (n + 1),
            ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))
              ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0) :=
    fun d hd F hF => (hq' d hd F hF).trans (hIZ d F hF)

  obtain ⟨d₁, hd₁⟩ :=
    AlgebraicGeometry.HilbertFunctor.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point
      n P' D₁ k q' Z ι hι hZ' 𝓛 h𝓛 𝔓 h𝔓

  have hev : ∃ D : ℕ, ∀ d : ℕ, D ≤ d → (Module.finrank k (piece I d) : ℚ) = P.eval (d : ℚ) := by
    refine ⟨max (max d₀ d₁) D₁, fun d hd => ?_⟩
    have hd0 : d₀ ≤ d := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hd
    have hd1 : d₁ ≤ d := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hd
    have hD1 : D₁ ≤ d := le_trans (le_max_right _ _) hd
    have h1 := hd₀ d hd0
    have h2 := hd₁ d hd1
    have h3 := hP' d hD1
    have h4 : hilbertFunctionOf n P' D₁ d = Module.finrank k (piece I d) := by
      have : ¬ d < D₁ := Nat.not_lt.mpr hD1
      simp only [hilbertFunctionOf, this, if_false]
      rw [← h3, Int.floor_natCast]
      exact Int.toNat_natCast _
    have h5 : ((hilbertFunctionOf n P' D₁ d : ℕ) : ℚ) = P.eval (d : ℚ) := by
      rw [← h2]
      exact h1
    rw [← h5, h4]

  have hall := hG k Z ι hι I hIhom hIZ hev

  obtain ⟨q, hq⟩ :=
    AlgebraicGeometry.HilbertFunctor.exists_point_hilbertFunctionOf_forall_mem_iff_of_forall_finrank_piece_eq n k P m I hIhom
      (fun d hd => hall d (le_trans hm hd))
  exact ⟨q, fun d hd F hF => (hq d hd F hF).trans (hIZ d F hF)⟩

end S_AlgebraicGeometry_HilbertFunctor_exists_point_forall_mem_iff_of_isClosedImmersion_of_forall_geomFibreH0Finrank_eq_eval
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_forall_mem_iff_of_isClosedImmersion_of_forall_geomFibreH0Finrank_eq_eval (solution)
