-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicKaehlerRegularity
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicKaehlerRegularity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T12:23:35.706546+00:00
-- url     : https://prove2.me/theorems/7116d7b6-cf4f-4362-8283-181de8d92d1f
-- title:
--   LPSOriginal Holomorphic Kaehler Regularity
-- statement:
--   Definitions and structural lemmas for LPSOriginal Holomorphic Kaehler Regularity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalHolomorphicKaehlerRegularity.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicNativeCovectors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeHolomorphicExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeH0
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicCovectorToClass_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeCovectorToLocal_class
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledCovector_contMDiff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedMeromorphicCovector_class

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] LPSOriginalAffineKaehlerCompatibilityDictionary001
  LPSOriginalAffineKaehlerCompatibilityDictionary002
  LPSOriginalAffineKaehlerCompatibilityDictionary003
  LPSOriginalAffineKaehlerCompatibilityDictionary004
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
def lpsOriginalHolomorphicToKaehlerLinearMap :
    LPSOriginalHolomorphicCovectorSections N hN →ₗ[ℂ] KaehlerDifferential ℂ K :=
  (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN).symm.toLinearMap.comp
    (lpsOriginalHolomorphicCovectorToClassLinearMap N hN)
lemma lpsOriginalHolomorphicToKaehler_native
    (sigma : LPSOriginalHolomorphicCovectorSections N hN) :
    lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
      (lpsOriginalHolomorphicToKaehlerLinearMap N hpos hN sigma) =
        lpsOriginalHolomorphicCovectorToClassLinearMap N hN sigma :=
  (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN).apply_symm_apply _
lemma lpsOriginalHolomorphicToKaehler_mem_regular
    (sigma : LPSOriginalHolomorphicCovectorSections N hN) :
    lpsOriginalHolomorphicToKaehlerLinearMap N hpos hN sigma ∈
      lpsOriginalNativeRegularKaehlerSubmodule N hpos := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  apply (lpsOriginalNativeRegularKaehlerSubmodule_mem_iff N hpos hN _).mpr
  intro x
  rw [lpsOriginalHolomorphicToKaehler_native]
  change 0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
    (lpsOriginalNativeCovectorToLocal N hN x
      (lpsOriginalCompactMeromorphicCovectorClass N hN
        (lpsOriginalHolomorphicCovectorToMeromorphicLinearMap N hN sigma)))
  rw [lpsOriginalNativeCovectorToLocal_class]
  change 0 ≤ meromorphicOrderAt (lpsOriginalHolomorphicCovectorChartCoefficient N hN sigma x)
    (chartAt ℂ x x)
  have ha := lpsOriginalHolomorphicCovectorChartCoefficient_analytic N hN sigma x
  exact ha.meromorphicAt.meromorphicOrderAt_nonneg_iff.mpr ⟨_, ha, Filter.EventuallyEq.rfl⟩
def lpsOriginalHolomorphicToRegularKaehlerLinearMap :
    LPSOriginalHolomorphicCovectorSections N hN →ₗ[ℂ]
      lpsOriginalNativeRegularKaehlerSubmodule N hpos :=
  (lpsOriginalHolomorphicToKaehlerLinearMap N hpos hN).codRestrict
    (lpsOriginalNativeRegularKaehlerSubmodule N hpos)
    (lpsOriginalHolomorphicToKaehler_mem_regular N hpos hN)
lemma lpsOriginalHolomorphicToRegularKaehler_injective :
    Function.Injective (lpsOriginalHolomorphicToRegularKaehlerLinearMap N hpos hN) := by
  intro sigma tau he
  have hk := congrArg Subtype.val he
  have hn := congrArg (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN) hk
  change lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
      (lpsOriginalHolomorphicToKaehlerLinearMap N hpos hN sigma) =
      lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
        (lpsOriginalHolomorphicToKaehlerLinearMap N hpos hN tau) at hn
  rw [lpsOriginalHolomorphicToKaehler_native, lpsOriginalHolomorphicToKaehler_native] at hn
  exact lpsOriginalHolomorphicCovectorToClass_injective N hN hn
lemma lpsOriginalHolomorphicToRegularKaehler_surjective :
    Function.Surjective (lpsOriginalHolomorphicToRegularKaehlerLinearMap N hpos hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let : AddCommGroup (LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :=
    (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  intro omega
  let c := lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega.val
  obtain ⟨sigma, hsigma⟩ :=
    (lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN).mkQ_surjective c
  have hs : lpsOriginalCompactMeromorphicCovectorClass N hN sigma = c := hsigma
  have ho : ∀ x : LPSOriginalFilledCurve N,
      0 ≤ meromorphicOrderAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma.val x)
        (chartAt ℂ x x) := by
    intro x
    have hn := (lpsOriginalNativeRegularKaehlerSubmodule_mem_iff N hpos hN omega.val).mp
      omega.property x
    change 0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x c) at hn
    rw [← hs, lpsOriginalNativeCovectorToLocal_class] at hn
    exact hn
  let h : LPSOriginalHolomorphicCovectorSections N hN :=
    ⟨lpsOriginalNormalizedFilledCovector N hN sigma.val,
      lpsOriginalNormalizedFilledCovector_contMDiff N hN sigma.val sigma.property ho⟩
  have hh : lpsOriginalHolomorphicCovectorToClassLinearMap N hN h = c :=
    (lpsOriginalNormalizedMeromorphicCovector_class N hN sigma).symm.trans hs
  refine ⟨h, Subtype.ext ?_⟩
  apply (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN).injective
  change lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
    (lpsOriginalHolomorphicToKaehlerLinearMap N hpos hN h) =
      lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega.val
  rw [lpsOriginalHolomorphicToKaehler_native]
  exact hh
def lpsOriginalHolomorphicRegularKaehlerLinearEquiv :
    LPSOriginalHolomorphicCovectorSections N hN ≃ₗ[ℂ]
      lpsOriginalNativeRegularKaehlerSubmodule N hpos :=
  LinearEquiv.ofBijective (lpsOriginalHolomorphicToRegularKaehlerLinearMap N hpos hN)
    ⟨lpsOriginalHolomorphicToRegularKaehler_injective N hpos hN,
      lpsOriginalHolomorphicToRegularKaehler_surjective N hpos hN⟩
end
end QEC.Coding.TannerLiftedProduct


