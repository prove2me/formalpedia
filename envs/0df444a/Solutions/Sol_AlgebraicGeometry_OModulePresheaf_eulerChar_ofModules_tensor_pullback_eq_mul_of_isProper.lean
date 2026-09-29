-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.eulerChar_ofModules_tensor_pullback_eq_mul_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/ecabb5fb-4f07-5d65-89bc-0cc40d0ae52f

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_tensor_pullback_eq_sum_mul_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_tensor_pullback_eq_mul_of_isProper
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule CochainCx.Bounded.abGrp CochainCx.Bounded.modR PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

namespace KunnethChiHelpers

theorem cauchy (N : ℕ) (a b : ℕ → ℤ) (hab : ∀ i j, N ≤ i + j → a i * b j = 0) :
    ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (n + 1), a i * b (n - i) =
      (∑ i ∈ Finset.range N, a i) * (∑ j ∈ Finset.range N, b j) := by
  rw [Finset.sum_range_diag_flip N (fun i j => a i * b j), Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < N := Finset.mem_range.mp hi
  apply Finset.sum_subset (Finset.range_mono (Nat.sub_le N i))
  intro j hj hj'
  apply hab
  simp only [Finset.mem_range, not_lt] at hj hj'
  omega

end KunnethChiHelpers

theorem solution
    {K : Type} [Field K] {X Y : Scheme.{0}}
    (πX : X ⟶ Spec (CommRingCat.of K)) (πY : Y ⟶ Spec (CommRingCat.of K)) [IsProper πX] [IsProper πY]
    (F : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (G : Y.Modules) (hG : Scheme.Modules.IsInvertible G)
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover) (𝔚 : (pullback πX πY).OrderedAffineCover) :
    (OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
        ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗
          (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)).eulerChar 𝔚 =
      (OModulePresheaf.ofModules πX F).eulerChar 𝔘 * (OModulePresheaf.ofModules πY G).eulerChar 𝔙 := by

  have hK := OModulePresheaf.cechFinrank_tensor_pullback_eq_sum_mul_of_isProper πX πY F hF G hG 𝔘 𝔙 𝔚
  obtain ⟨-, -, -, hX⟩ := OModulePresheaf.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
    (OModulePresheaf.ofModules πX F) 𝔘
  obtain ⟨-, -, -, hY⟩ := OModulePresheaf.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
    (OModulePresheaf.ofModules πY G) 𝔙
  obtain ⟨-, -, -, hW⟩ := OModulePresheaf.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
    (OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
      ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗
        (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)) 𝔚
  obtain ⟨hX0, hXχ⟩ := hX inferInstance
  obtain ⟨hY0, hYχ⟩ := hY inferInstance
  obtain ⟨-, hWχ⟩ := hW inferInstance

  rw [hWχ (Fintype.card 𝔘.ι + Fintype.card 𝔙.ι + Fintype.card 𝔚.ι) (by omega),
    hXχ (Fintype.card 𝔘.ι + Fintype.card 𝔙.ι + Fintype.card 𝔚.ι) (by omega),
    hYχ (Fintype.card 𝔘.ι + Fintype.card 𝔙.ι + Fintype.card 𝔚.ι) (by omega)]

  have key : ∀ n : ℕ,
      (-1 : ℤ) ^ n * ((OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
          ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗
            (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)).cechFinrank 𝔚 n : ℤ) =
        ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℤ) ^ i * ((OModulePresheaf.ofModules πX F).cechFinrank 𝔘 i : ℤ)) *
            ((-1 : ℤ) ^ (n - i) * ((OModulePresheaf.ofModules πY G).cechFinrank 𝔙 (n - i) : ℤ)) := by
    intro n
    rw [hK n]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hs : (-1 : ℤ) ^ n = (-1) ^ i * (-1) ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi']
    rw [hs]; ring
  simp_rw [key]
  refine KunnethChiHelpers.cauchy _ (fun i => (-1 : ℤ) ^ i * ((OModulePresheaf.ofModules πX F).cechFinrank 𝔘 i : ℤ))
    (fun j => (-1 : ℤ) ^ j * ((OModulePresheaf.ofModules πY G).cechFinrank 𝔙 j : ℤ)) ?_
  intro i j hij
  by_cases hi : Fintype.card 𝔘.ι ≤ i
  · simp [hX0 i hi]
  · have hj : Fintype.card 𝔙.ι ≤ j := by omega
    simp [hY0 j hj]

end S_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_tensor_pullback_eq_mul_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_tensor_pullback_eq_mul_of_isProper (solution)
