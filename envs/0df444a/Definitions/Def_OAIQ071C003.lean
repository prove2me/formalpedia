-- Prove2me | Definitions.Def_OAIQ071C003
-- name    : OAIQ071C003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T05:04:26.30183+00:00
-- url     : https://prove2.me/theorems/1b097561-12b5-4319-8816-59197b5fe3e0
-- title:
--   Definitions bundle OAIQ071C003 of the split of OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 269 declarations of OpenAI's Lean: 52 definitions and 217 theorems. The definitions and types are `OAI.CoulombAnalysis.coulombTestCharge`, `OAI.CoulombAnalysis.countPlateau`, `OAI.CoulombAnalysis.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField`, `OAI.CoulombAnalysis.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_1`, `OAI.CoulombAnalysis.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp`, `OAI.CoulombAnalysis.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_1`, `OAI.CoulombAnalysis.nearTFReaction`, `OAI.CoulombAnalysis.newtonComparisonTest`, `OAI.CoulombAnalysis.packetSecondMoment`, `OAI.CoulombAnalysis.packetSmooth`, `OAI.CoulombAnalysis.radialCombinationSource`, `OAI.CoulombAnalysis.tfCenteredPrice`, `OAI.CoulombAnalysis.tfChargeAnchor`, `OAI.CoulombAnalysis.tfFiniteSlope`, `OAI.CoulombAnalysis.tfFiniteSource`, `OAI.CoulombAnalysis.tfFluxSource`, `OAI.CoulombAnalysis.tfInfiniteCharge`, `OAI.CoulombAnalysis.tfInfiniteField`, `OAI.CoulombAnalysis.tfInfiniteSlope`, `OAI.CoulombAnalysis.tfPatchCapConstant`, `OAI.CoulombAnalysis.tfPatchDensityCapConstant`, `OAI.CoulombAnalysis.tfPatchGap`, `OAI.CoulombAnalysis.tfPatchGradient`, `OAI.CoulombAnalysis.tfPatchMinimizer`, `OAI.CoulombAnalysis.tfPatchNormBound`, `OAI.CoulombAnalysis.tfPatchOscillationConstant`, `OAI.CoulombAnalysis.tfPriceData`, `OAI.CoulombAnalysis.tfPriceDeficit`, `OAI.CoulombAnalysis.tfPriceValue`, `OAI.CoulombAnalysis.tfRealRadial`, `OAI.CoulombAnalysis.tfUnitDeficit`, `OAI.CoulombAnalysis.translatedPatchDensity`, `OAI.CoulombAtom.CoreAntisymmetric`, `OAI.CoulombAtom.SobolevFermion`, `OAI.CoulombAtom.SobolevVector`, `OAI.CoulombAtom.cartesianGradient`, `OAI.CoulombAtom.cartesianValue`, `OAI.CoulombAtom.configurationCoordinates`, `OAI.CoulombAtom.coreSlice`, `OAI.CoulombAtom.flattenConfiguration` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombIonization_Fermionic_CountableTests`, `CoulombIonization_FieldAnalysis_LinearCoulomb`, `CoulombIonization_FieldAnalysis_LocalGreen`, `CoulombIonization_FieldAnalysis_NeumannPhysical`, `CoulombIonization_FieldAnalysis_PatchWeakPoisson`, `CoulombIonization_FieldAnalysis_PressureWeak`, `CoulombIonization_FieldAnalysis_RotationTrace`, `CoulombIonization_FieldAnalysis_WeakHarmonicMean`, `CoulombIonization_FieldAnalysis_WeakHarmonicOscillation`, `CoulombIonization_FieldAnalysis_WeakPositiveComparisonBarrier`, `CoulombIonization_FormDomain_Form`, `CoulombIonization_FormDomain_PhysicalGrid`, `CoulombIonization_FormDomain_SobolevVector`, `CoulombIonization_FormDomain_WeakComparison`, `CoulombIonization_FormDomain_WeakMaximum`, `CoulombIonization_Ionization_TFPriceData`, `CoulombIonization_Localization_ArraySymmetry`, `CoulombIonization_Localization_LipschitzMollifier`, `CoulombIonization_Localization_PacketDensity`, `CoulombIonization_Localization_PacketScale`, `CoulombIonization_Localization_PacketScaleControl`, `CoulombIonization_Localization_QuantumRawLaw`, `CoulombIonization_Localization_RadialPacket`, `CoulombIonization_Localization_RadialPacketBase`, `CoulombIonization_RadialBounds_LocalCountGapBarrier`, `CoulombIonization_RadialBounds_PatchMass`, `CoulombIonization_RadialBounds_RootMomentCauchyBarrier`, `CoulombIonization_RadialBounds_ShellCoulombDuality`, `CoulombIonization_RadialBounds_WeakSemilinearComparison`, `CoulombIonization_ThomasFermi_ActualPatchCap`, `CoulombIonization_ThomasFermi_CoulombLipschitzDuality`, `CoulombIonization_ThomasFermi_NearTFReaction`, `CoulombIonization_ThomasFermi_PatchCoulombControl`, `CoulombIonization_ThomasFermi_PatchEuler`, `CoulombIonization_ThomasFermi_PatchGap`, `CoulombIonization_ThomasFermi_PatchGapMeasurable`, `CoulombIonization_ThomasFermi_PatchRandomVariables`, `CoulombIonization_ThomasFermi_PatchTF`, `CoulombIonization_ThomasFermi_PatchTruncationLoss`, `CoulombIonization_ThomasFermi_RadialPatchCap`, `CoulombIonization_ThomasFermi_RadialShellPotential`, `CoulombIonization_ThomasFermi_TFNonradialBarrier`, `CoulombIonization_ThomasFermi_TFNonradialCap`, `CoulombIonization_ThomasFermi_TFNonradialOscillation`, `CoulombIonization_ThomasFermi_TfBallFunctionalConvex`, `CoulombIonization_ThomasFermi_TfCenteredPrice`, `CoulombIonization_ThomasFermi_TfIncreasingData`, `CoulombIonization_ThomasFermi_TfInfiniteField`, `CoulombIonization_ThomasFermi_TfInfiniteFieldDominatesDilation`, `CoulombIonization_ThomasFermi_WeakSommerfeldBoundsBarrier`, `CoulombIonization_Variational_BlockSwap`, `CoulombIonization_Variational_ConfigurationCoordinates`, `CoulombIonization_Variational_CoulombTestCharge`, `CoulombIonization_Variational_NewtonComparisonTest`, `CoulombIonization_Variational_PatchBounded`, `CoulombIonization_Variational_PatchTranslatedDensity`, `CoulombIonization_Variational_SliceLp`, `CoulombIonization_Variational_Slices`, `CoulombIonization_Variational_SmoothNewton`, `CoulombIonization_Variational_Spatial`, `CoulombIonization_Variational_SpatialRotation`.
--
--   **Imports.** It imports the published bundle `Def_CoulombIonization`; the bundles `OAIQ071C000` and `OAIQ071C001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ071C006` and `OAIQ071C007`.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C000
import Definitions.Def_OAIQ071C001

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_CountableTests
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
namespace CoulombAtom
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]

lemma countable_weak_derivative_tests (v : E) :
    ∃ S : Set (SmoothRealTest E), S.Countable ∧
      ∀ (f g : E → ℂ), MemLp f 2 → MemLp g 2 →
      (∀ φ ∈ S, (∫ x, f x * Complex.ofReal (lineDeriv ℝ φ.val x v)) =
        -(∫ x, g x * (φ.val x : ℂ))) → IsWeakDerivative v f g := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let V := WeakGraphAmbient E Unit
  let L : SmoothRealTest E → V →L[ℂ] ℂ := fun φ =>
    weakGraphTest (fun _ : Unit => v) () φ.val φ.property.1 φ.property.2
  obtain ⟨S, hS, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun φ : SmoothRealTest E => ((L φ).ker : Set V)ᶜ) (fun φ => (L φ).isClosed_ker.isOpen_compl)
  refine ⟨S, hS, ?_⟩
  intro f g hf hg htest
  let A : V := WithLp.toLp 2 (fun j : Option Unit =>
    match j with | none => hf.toLp f | some _ => hg.toLp g)
  have hAS (φ : SmoothRealTest E) (hφ : φ ∈ S) : A ∈ (L φ).ker := by
    change l2Test _ _ (hf.toLp f) + l2Test _ _ (hg.toLp g) = 0
    rw [l2Test_apply, l2Test_apply]
    have h1 := integral_congr_ae (hf.coeFn_toLp.mono fun x hx =>
      congrArg (· * Complex.ofReal (lineDeriv ℝ φ.val x v)) hx)
    have h2 := integral_congr_ae (hg.coeFn_toLp.mono fun x hx =>
      congrArg (· * (φ.val x : ℂ)) hx)
    rw [h1, h2, htest φ hφ, neg_add_cancel]
  have hAll (φ : SmoothRealTest E) : A ∈ (L φ).ker := by
    by_contra hn
    have hm : A ∈ ⋃ φ : SmoothRealTest E, ((L φ).ker : Set V)ᶜ := Set.mem_iUnion.mpr ⟨φ, hn⟩
    rw [← hcover] at hm
    obtain ⟨ψ, hψ⟩ := Set.mem_iUnion.mp hm
    obtain ⟨hψS, hψA⟩ := Set.mem_iUnion.mp hψ
    exact hψA (hAS ψ hψS)
  intro φ hφ hcφ
  have hh := hAll ⟨φ, hφ, hcφ⟩
  change l2Test _ _ (hf.toLp f) + l2Test _ _ (hg.toLp g) = 0 at hh
  rw [l2Test_apply, l2Test_apply] at hh
  have h1 := integral_congr_ae (hf.coeFn_toLp.mono fun x hx =>
    congrArg (· * Complex.ofReal (lineDeriv ℝ φ x v)) hx)
  have h2 := integral_congr_ae (hg.coeFn_toLp.mono fun x hx =>
    congrArg (· * (φ x : ℂ)) hx)
  rw [h1, h2] at hh
  exact eq_neg_of_add_eq_zero_left hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LinearCoulomb
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

lemma nuclear_integrable {N : ℕ} (i : Fin N)
    {f : Configuration N → ℂ} {g : Fin 3 → Configuration N → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : Configuration N → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (direction i a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    Integrable (fun x => ‖f x‖ ^ 2 / ‖x i‖) := by
  let P : Configuration N →L[ℝ] Space := ContinuousLinearMap.proj i
  have hp : ∀ a, P (direction i a) = EuclideanSpace.single a 1 := by
    intro a
    change direction i a i = _
    simp [direction]
  exact linear_coulomb_integrable (E := Configuration N) P (direction i) hp hf hg hweak

lemma pair_integrable {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    {f : Configuration N → ℂ} {g : Fin 3 → Configuration N → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : Configuration N → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (direction i a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    Integrable (fun x => ‖f x‖ ^ 2 / ‖x i - x j‖) := by
  let P : Configuration N →L[ℝ] Space :=
    (ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space) -
      (ContinuousLinearMap.proj j : Configuration N →L[ℝ] Space)
  have hp : ∀ a, P (direction i a) = EuclideanSpace.single a 1 := by
    intro a
    change direction i a i - direction i a j = _
    simp [direction, hij.symm]
  exact linear_coulomb_integrable (E := Configuration N) P (direction i) hp hf hg hweak

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SliceLp
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
namespace CoulombAtom

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]
  [MeasureSpace F] [SFinite (volume : Measure F)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)] in
lemma integral_pair_norm_sq {f : E → ℂ} (hf : MemLp f 2)
    (φ : E → ℝ) (hφ : MemLp (fun x => (φ x : ℂ)) 2) :
    ‖∫ x, f x * (φ x : ℂ)‖ ^ 2 ≤
      ‖hφ.toLp (fun x => (φ x : ℂ))‖ ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  have he : (∫ x, f x * (φ x : ℂ)) = l2Test φ hφ (hf.toLp f) := by
    rw [l2Test_apply]
    exact integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by rw [hx]) |>.symm
  rw [he]
  have h := norm_inner_le_norm (𝕜 := ℂ) (hφ.toLp (fun x => (φ x : ℂ))) (hf.toLp f)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, lp_norm_sq (hf.toLp f)] at hs
  have hi : (∫ x, ‖hf.toLp f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 :=
    integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by simp only [hx])
  rw [hi] at hs
  exact hs

omit [BorelSpace E] in
lemma partial_pairing_memLp {f : E × F → ℂ} (hf : MemLp f 2)
    (φ : E → ℝ) (hφ : MemLp (fun x => (φ x : ℂ)) 2) :
    MemLp (fun y => ∫ x, f (x, y) * (φ x : ℂ)) 2 := by
  have hm : AEStronglyMeasurable (fun y => ∫ x, f (x, y) * (φ x : ℂ)) := by
    exact (hf.aestronglyMeasurable.mul (hφ.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst)
      )).prod_swap.integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  apply (hi.integral_prod_right.const_mul
    (‖hφ.toLp (fun x => (φ x : ℂ))‖ ^ 2)).mono'
      (hm.norm.pow 2)
  filter_upwards [memLp_slice_left hf] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact integral_pair_norm_sq hy φ hφ

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Slices
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
section
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure]

lemma weak_slice_fixed_test {v : E} {f g : E × F → ℂ}
    (hf : MemLp f 2) (hg : MemLp g 2) (hfg : IsWeakDerivative (v,0) f g)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    ∀ᵐ y, (∫ x, f (x,y) * Complex.ofReal (lineDeriv ℝ φ x v)) =
      -(∫ x, g (x,y) * (φ x : ℂ)) := by
  have h1 := partial_pairing_memLp hf (fun x => lineDeriv ℝ φ x v)
    (test_deriv_memLp hφ hcφ v)
  have h2 := partial_pairing_memLp hg φ (test_memLp hφ hcφ)
  apply ae_eq_of_integral_contDiff_smul_eq
    (h1.locallyIntegrable (by norm_num)) ((h2.neg).locallyIntegrable (by norm_num))
  intro ψ hψ hcψ
  obtain ⟨ht, hct⟩ := smooth_test_product hφ hcφ hψ hcψ
  have hi1 := hf.integrable_mul (test_deriv_memLp ht hct (v,0))
  have hi2 := hg.integrable_mul (test_memLp ht hct)
  have he := hfg _ ht hct
  simp only [lineDeriv_test_product hφ hψ] at hi1 he
  have hp1 := integral_prod_symm _ hi1
  have hp2 := integral_prod_symm _ hi2
  simp only [Pi.mul_apply] at hp1 hp2
  rw [Measure.volume_eq_prod E F, hp1, hp2] at he
  simp only [Complex.ofReal_mul, ← mul_assoc, integral_mul_const] at he
  simp only [Complex.real_smul, Pi.neg_apply, mul_neg, integral_neg]
  simpa only [mul_comm] using he

theorem IsWeakDerivative.slice_left {v : E} {f g : E × F → ℂ}
    (hf : MemLp f 2) (hg : MemLp g 2) (hfg : IsWeakDerivative (v,0) f g) :
    ∀ᵐ y, IsWeakDerivative v (fun x => f (x,y)) (fun x => g (x,y)) := by
  obtain ⟨S, hS, htests⟩ := countable_weak_derivative_tests v
  have hall : ∀ᵐ y, ∀ φ ∈ S,
      (∫ x, f (x,y) * Complex.ofReal (lineDeriv ℝ φ.val x v)) =
        -(∫ x, g (x,y) * (φ.val x : ℂ)) := by
    apply (ae_ball_iff hS).mpr
    intro φ _
    exact weak_slice_fixed_test hf hg hfg φ.property.1 φ.property.2
  filter_upwards [memLp_slice_left hf, memLp_slice_left hg, hall] with y hyf hyg hy
  exact htests _ _ hyf hyg hy

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

section ChangeVariables
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasureSpace F] [BorelSpace F]

lemma IsWeakDerivative.pullback {v : F} {w : E} {f g : F → ℂ}
    (hw : IsWeakDerivative v f g) (e : E ≃L[ℝ] F)
    (he : MeasurePreserving e) (hv : e w = v) :
    IsWeakDerivative w (f ∘ e) (g ∘ e) := by
  intro φ hφ hcφ
  let ψ : F → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp e.symm.contDiff
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph e.symm.toHomeomorph
  have hev : e.symm v = w := by rw [← hv, e.symm_apply_apply]
  have hd (x : E) : lineDeriv ℝ ψ (e x) v = lineDeriv ℝ φ x w := by
    rw [(hψ.differentiable (by simp) (e x)).lineDeriv_eq_fderiv,
      (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
    have hh := (hφ.differentiable (by simp) (e.symm (e x))).hasFDerivAt.comp
      (e x) e.symm.hasFDerivAt
    have hh' := congrArg (fun A : F →L[ℝ] ℝ => A v) hh.fderiv
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e.symm_apply_apply, hev] using hh'
  have hi1 := he.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x => f x * Complex.ofReal (lineDeriv ℝ ψ x v))
  have hi2 := he.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x => g x * (ψ x : ℂ))
  have hh := hw ψ hψ hcψ
  rw [← hi1, ← hi2] at hh
  simpa only [hd, ψ, Function.comp_apply, e.symm_apply_apply] using hh

end ChangeVariables

lemma configurationJoin_apply {N M : ℕ} (x : Configuration N) (y : Configuration M) :
    configurationJoin N M (x,y) = joinLists x y := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  change (Equiv.piCongrLeft (fun _ : Fin (N+M) => Space) finSumFinEquiv)
    ((Equiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin M => Space)).symm (x,y))
      (finSumFinEquiv j) = Sum.elim x y (finSumFinEquiv.symm (finSumFinEquiv j))
  rw [Equiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]
  cases j <;> rfl

lemma configurationJoin_direction {N M : ℕ} (i : Fin N) (a : Fin 3) :
    configurationJoin N M (direction i a,0) = direction (finSumFinEquiv (Sum.inl i)) a := by
  rw [configurationJoin_apply]
  funext j
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j => rw [joinLists_left]; simp [direction, Pi.single_apply]
  | inr j =>
    rw [joinLists_right]
    have hn : finSumFinEquiv (Sum.inr j) ≠ finSumFinEquiv (Sum.inl i) :=
      fun h => Sum.inr_ne_inl (finSumFinEquiv.injective h)
    simp only [direction, Pi.single_apply, ite_eq_right hn, Pi.zero_apply]

lemma joinLists_corePerm {α : Type*} {N M : ℕ}
    (x : Fin N → α) (y : Fin M → α) (π : Equiv.Perm (Fin N)) :
    joinLists x y ∘ corePerm M π = joinLists (x ∘ π) y := by
  funext j
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
  cases j <;> simp [joinLists, corePerm, Equiv.permCongr, Function.comp_def]

def coreSlice {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M) (y : Configuration M) :
    FormVector N where
  value s x := ψ.value (joinLists s t) (joinLists x y)
  gradient s i a x := ψ.gradient (joinLists s t) (finSumFinEquiv (Sum.inl i)) a (joinLists x y)

def SobolevFermion {N : ℕ} (ψ : FormVector N) : Prop :=
  (∀ s, MemLp (ψ.value s) 2) ∧
  (∀ s i a, MemLp (ψ.gradient s i a) 2) ∧
  (∀ s i a, IsWeakDerivative (direction i a) (ψ.value s) (ψ.gradient s i a)) ∧
  (∀ (π : Equiv.Perm (Fin N)) s, ∀ᵐ x,
    ψ.value (s ∘ π) (x ∘ π) = (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value s x))

lemma SobolevFermion.scale {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (c : ℝ) : SobolevFermion (scaleForm c ψ) := by
  refine ⟨fun s => (hψ.1 s).const_mul _, fun s i a => (hψ.2.1 s i a).const_mul _, ?_, ?_⟩
  · intro s i a φ hφ hcφ
    change (∫ x, ((c : ℂ) * ψ.value s x) * Complex.ofReal (lineDeriv ℝ φ x (direction i a))) =
      -(∫ x, ((c : ℂ) * ψ.gradient s i a x) * (φ x : ℂ))
    simp only [mul_assoc, integral_const_mul, hψ.2.2.1 s i a φ hφ hcφ, mul_neg]
  · intro π s
    filter_upwards [hψ.2.2.2 π s] with x hx
    change (c : ℂ) * ψ.value (s ∘ π) (x ∘ π) = _
    rw [hx]
    change _ = (((Equiv.Perm.sign π : ℤ) : ℂ) * ((c : ℂ) * ψ.value s x))
    ring

lemma formMass_scale {N : ℕ} (c : ℝ) (ψ : FormVector N) :
    formMass (scaleForm c ψ) = c ^ 2 * formMass ψ := by
  simp only [formMass, scaleForm, scaled_norm_sq, integral_const_mul, Finset.mul_sum]

lemma SobolevFermion.admissible {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hn : formMass ψ = 1) : FormAdmissible ψ := by
  refine ⟨hψ.1,hψ.2.1,hψ.2.2.1,hψ.2.2.2,hn,?_,?_⟩
  · intro s i
    exact nuclear_integrable i (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)
  · intro s i j hij
    exact pair_integrable i j hij (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)

theorem SobolevFermion.normalize {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : 0 < formMass ψ) :
    FormAdmissible (scaleForm (Real.sqrt (formMass ψ))⁻¹ ψ) := by
  apply (hψ.scale _).admissible
  rw [formMass_scale, inv_pow, Real.sq_sqrt (le_of_lt hm), inv_mul_cancel₀ (ne_of_gt hm)]


open Set Filter Topology InnerProductSpace Laplacian

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_SobolevVector
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

def SobolevVector {N : ℕ} (ψ : FormVector N) : Prop :=
  (∀ s, MemLp (ψ.value s) 2) ∧
  (∀ s i a, MemLp (ψ.gradient s i a) 2) ∧
  (∀ s i a, IsWeakDerivative (direction i a) (ψ.value s) (ψ.gradient s i a))

def multiplyForm {N : ℕ} (p : SmoothMultiplier (sectorDirections N))
    (ψ : FormVector N) : FormVector N where
  value s x := (p.value x : ℂ) * ψ.value s x
  gradient s i a x := (p.value x : ℂ) * ψ.gradient s i a x +
    Complex.ofReal (lineDeriv ℝ p.value x (direction i a)) * ψ.value s x

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Spatial
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

def CoreAntisymmetric {N M : ℕ} (ψ : FormVector (N+M)) : Prop :=
  ∀ (π : Equiv.Perm (Fin N)) (s : Spins (N+M)), ∀ᵐ x,
    ψ.value (s ∘ corePerm M π) (x ∘ corePerm M π) =
      (((Equiv.Perm.sign π : ℤ) : ℂ) * ψ.value s x)

theorem SobolevVector.ae_coreSlice {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) : ∀ᵐ y, SobolevVector (coreSlice ψ t y) := by
  have hv (s : Spins N) : ∀ᵐ y, MemLp ((coreSlice ψ t y).value s) 2 := by
    have hh := (hψ.1 (joinLists s t)).comp_measurePreserving (configurationJoin_preserving N M)
    simpa only [Function.comp_apply, configurationJoin_apply, coreSlice] using memLp_slice_left hh
  have hg (s : Spins N) (i : Fin N) (a : Fin 3) :
      ∀ᵐ y, MemLp ((coreSlice ψ t y).gradient s i a) 2 := by
    have hh := (hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).comp_measurePreserving
      (configurationJoin_preserving N M)
    simpa only [Function.comp_apply, configurationJoin_apply, coreSlice] using memLp_slice_left hh
  have hw (s : Spins N) (i : Fin N) (a : Fin 3) :
      ∀ᵐ y, IsWeakDerivative (direction i a) ((coreSlice ψ t y).value s)
        ((coreSlice ψ t y).gradient s i a) := by
    have hh := (hψ.2.2 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).pullback
      (configurationJoin N M) (configurationJoin_preserving N M) (configurationJoin_direction i a)
    simpa only [Function.comp_apply, configurationJoin_apply, coreSlice] using hh.slice_left
      ((hψ.1 (joinLists s t)).comp_measurePreserving (configurationJoin_preserving N M))
      ((hψ.2.1 (joinLists s t) (finSumFinEquiv (Sum.inl i)) a).comp_measurePreserving
        (configurationJoin_preserving N M))
  filter_upwards [ae_all_iff.mpr hv, ae_all_iff.mpr (fun s => ae_all_iff.mpr
      (fun i => ae_all_iff.mpr (hg s i))), ae_all_iff.mpr (fun s => ae_all_iff.mpr
      (fun i => ae_all_iff.mpr (hw s i)))] with y hyv hyg hyw
  exact ⟨hyv,hyg,hyw⟩

theorem CoreAntisymmetric.ae_coreSlice {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) (t : Spins M) :
    ∀ᵐ y, SobolevFermion (coreSlice ψ t y) := by
  have hs (π : Equiv.Perm (Fin N)) (s : Spins N) : ∀ᵐ y, ∀ᵐ x,
      (coreSlice ψ t y).value (s ∘ π) (x ∘ π) =
        (((Equiv.Perm.sign π : ℤ) : ℂ) * (coreSlice ψ t y).value s x) := by
    have hh := (configurationJoin_preserving N M).quasiMeasurePreserving.ae
      (ha π (joinLists s t))
    have hh' : ∀ᵐ z : Configuration N × Configuration M,
        (coreSlice ψ t z.2).value (s ∘ π) (z.1 ∘ π) =
          (((Equiv.Perm.sign π : ℤ) : ℂ) * (coreSlice ψ t z.2).value s z.1) := by
      filter_upwards [hh] with z hz
      rcases z with ⟨x,y⟩
      simpa only [configurationJoin_apply, joinLists_corePerm, coreSlice] using hz
    rw [Measure.volume_eq_prod] at hh'
    exact Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hh')
  filter_upwards [hψ.ae_coreSlice t, ae_all_iff.mpr (fun π => ae_all_iff.mpr (hs π))]
    with y hy hya
  exact ⟨hy.1,hy.2.1,hy.2.2,hya⟩

lemma CoreAntisymmetric.multiply {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (q : SmoothMultiplier (sectorDirections (N+M)))
    (hq : ∀ (π : Equiv.Perm (Fin N)) x, q.value (x ∘ corePerm M π) = q.value x) :
    CoreAntisymmetric (multiplyForm q ψ) := by
  intro π s
  filter_upwards [ha π s] with x hx
  change (q.value (x ∘ corePerm M π) : ℂ) * ψ.value (s ∘ corePerm M π)
    (x ∘ corePerm M π) = _ * ((q.value x : ℂ) * ψ.value s x)
  rw [hq, hx]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Form
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


open MeasureTheory Filter
open scoped BigOperators


def formKinetic {N : ℕ} (ψ : FormVector N) : ℝ :=
  (1/2:ℝ) * ∑ s, ∑ i, ∑ a, ∫ x, ‖ψ.gradient s i a x‖^2


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_RadialPacket
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_RadialPacket_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma radial_potential_le_point {η : Space → ℝ} (hη : Integrable η)
    (hp : MemLp η (5/3 : ENNReal)) (hn : ∀ x, 0 ≤ η x)
    (hr : CoulombAnalysis.IsRadial η) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, η y ≠ 0 → ‖y‖ ≤ R) {x : Space} (hx : x ≠ 0) :
    CoulombAnalysis.tfPotential η x ≤ (∫ y, η y)/‖x‖ := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let S : Set Space := {y | ‖y‖ ≤ ‖x‖}
  have hm : MeasurableSet S := measurableSet_le measurable_norm measurable_const
  have he : Sᶜ = {y : Space | ‖x‖ < ‖y‖} := by ext y; simp [S]
  have houter : (∫ y in Sᶜ, η y/‖y‖) ≤ (∫ y in Sᶜ, η y)/‖x‖ := by
    rw [← integral_div]
    apply integral_mono_ae
      ((CoulombAnalysis.tfPotential_integrable hη hp 0).congr (by filter_upwards [] with y; simp)).integrableOn
      (hη.div_const _).integrableOn
    filter_upwards [ae_restrict_mem hm.compl] with y hy
    exact div_le_div_of_nonneg_left (hn y) hx0 (le_of_lt (by simpa [S] using hy))
  rw [CoulombAnalysis.tfPotential_newton hη hp hr hR hs hx,← he]
  calc
    _ ≤ (∫ y in S, η y)/‖x‖ + (∫ y in Sᶜ, η y)/‖x‖ := add_le_add le_rfl houter
    _ = _ := by rw [← add_div,integral_add_compl hm hη]

end Work_RadialPacket_scope

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchTF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

lemma tfPatchFunctional_continuous (R T : ℝ) (Φ : TFField R) : Continuous (tfPatchFunctional R T Φ) := by
  apply Continuous.add
  · exact ((continuous_norm.rpow_const (fun _ => Or.inr (by norm_num))).const_mul T).add
      (tfPatchLinear R Φ).continuous
  · exact ((tfCoulombL R).continuous₂.comp (continuous_id.prodMk continuous_id)).const_mul _

lemma tfPatchFunctional_lower (R T : ℝ) (Φ : TFField R) (f : TFLp (ballMeasure R)) :
    T * ‖f‖ ^ (5 / 3 : ℝ) - ‖tfPatchLinear R Φ‖ * ‖f‖ ≤ tfPatchFunctional R T Φ f := by
  have hL := (tfPatchLinear R Φ).le_opNorm f
  have hn := neg_abs_le (tfPatchLinear R Φ f)
  have hD := tfCoulombL_nonneg R f
  change |tfPatchLinear R Φ f| ≤ _ at hL
  unfold tfPatchFunctional
  linarith

lemma tfPatchFunctional_bddBelow (R : ℝ) (Φ : TFField R) {T : ℝ} (hT : 0 < T) :
    BddBelow (Set.range (tfPatchFunctional R T Φ)) := by
  obtain ⟨B, hB0, hB⟩ := tf_power_dominates_linear hT ‖tfPatchLinear R Φ‖
  refine ⟨-‖tfPatchLinear R Φ‖ * B, ?_⟩
  rintro _ ⟨f, rfl⟩
  apply le_trans _ (tfPatchFunctional_lower R T Φ f)
  by_cases hb : B ≤ ‖f‖
  · exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (norm_nonneg _)) hB0).trans
      ((norm_nonneg _).trans (hB _ hb))
  · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hb) (norm_nonneg (tfPatchLinear R Φ))
    have hp := mul_nonneg hT.le (Real.rpow_nonneg (norm_nonneg f) (5 / 3 : ℝ))
    linarith

lemma tfPatchFunctional_coercive (R : ℝ) (Φ : TFField R) (a : ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ B : ℝ, ∀ f : TFLp (ballMeasure R), tfPatchFunctional R T Φ f ≤ a → ‖f‖ ≤ B := by
  obtain ⟨B, _, hB⟩ := tf_power_dominates_linear hT ‖tfPatchLinear R Φ‖
  refine ⟨max B a, fun f hf => ?_⟩
  by_cases hb : B ≤ ‖f‖
  · exact ((hB _ hb).trans ((tfPatchFunctional_lower R T Φ f).trans hf)).trans (le_max_right _ _)
  · exact (le_of_not_ge hb).trans (le_max_left _ _)

lemma tfPatchFunctional_gap (R T : ℝ) (Φ : TFField R) (hT : 0 ≤ T) {f g : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hg : NonnegDensity g) :
    (T * (5 / 36 : ℝ)) * densityWeight f g ≤
      (tfPatchFunctional R T Φ f + tfPatchFunctional R T Φ g) / 2 -
        tfPatchFunctional R T Φ ((1 / 2 : ℝ) • (f + g)) := by
  have hk := mul_le_mul_of_nonneg_left (tfLp_midpoint_gap hf hg) hT
  have hD := tfCoulombL_midpoint_gap R f g
  unfold tfPatchFunctional
  simp only [map_smul, map_add, smul_apply, add_apply, smul_eq_mul] at hD ⊢
  nlinarith

theorem tfPatchFunctional_exists_minimizer (R : ℝ) (Φ : TFField R) {T : ℝ} (hT : 0 < T) :
    ∃ f : TFLp (ballMeasure R), NonnegDensity f ∧
      ∀ g : TFLp (ballMeasure R), NonnegDensity g →
        tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ g := by
  apply exists_minimizer_of_tf_gap (C := {f | NonnegDensity f}) isClosed_nonnegDensity
  · refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ (5 / 3) (ballMeasure R)] with x hx
    rw [hx]
    exact le_rfl
  · exact fun _ hf => hf
  · exact fun _ hf _ hg => nonnegDensity_smul (nonnegDensity_add hf hg) (by norm_num)
  · exact (tfPatchFunctional_continuous R T Φ).continuousOn
  · exact (tfPatchFunctional_bddBelow R Φ hT).mono (Set.image_subset_range _ _)
  · intro a
    obtain ⟨B, hB⟩ := tfPatchFunctional_coercive R Φ a hT
    exact ⟨B, fun f _ hf => hB f hf⟩
  · exact mul_pos hT (by norm_num : (0 : ℝ) < 5 / 36)
  · exact fun _ hf _ hg => tfPatchFunctional_gap R T Φ hT.le hf hg

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

def tfPatchMinimizer (R T : ℝ) (hT : 0 < T) (Φ : TFField R) : TFLp (ballMeasure R) :=
  (tfPatchFunctional_exists_minimizer R Φ hT).choose

lemma tfPatchMinimizer_nonneg (R T : ℝ) (hT : 0 < T) (Φ : TFField R) :
    NonnegDensity (tfPatchMinimizer R T hT Φ) :=
  (tfPatchFunctional_exists_minimizer R Φ hT).choose_spec.1

lemma tfPatchMinimizer_min (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {f : TFLp (ballMeasure R)} (hf : NonnegDensity f) :
    tfPatchFunctional R T Φ (tfPatchMinimizer R T hT Φ) ≤ tfPatchFunctional R T Φ f :=
  (tfPatchFunctional_exists_minimizer R Φ hT).choose_spec.2 f hf

lemma nonnegDensity_zero (R : ℝ) : NonnegDensity (0 : TFLp (ballMeasure R)) := by
  filter_upwards [Lp.coeFn_zero ℝ (5/3) (ballMeasure R)] with x hx
  rw [hx]
  exact le_rfl

def tfPatchNormBound (R T : ℝ) (Φ : TFField R) : ℝ :=
  (‖tfPatchLinear R Φ‖ / T) ^ (3/2:ℝ)

lemma tfPatchMinimizer_norm_le (R T : ℝ) (hT : 0 < T) (Φ : TFField R) :
    ‖tfPatchMinimizer R T hT Φ‖ ≤ tfPatchNormBound R T Φ := by
  let f := tfPatchMinimizer R T hT Φ
  have hmin := tfPatchMinimizer_min R T hT Φ (nonnegDensity_zero R)
  rw [tfPatchFunctional_zero] at hmin
  have hlow := tfPatchFunctional_lower R T Φ f
  by_cases hz : ‖f‖ = 0
  · change ‖f‖ ≤ _
    rw [hz]
    exact Real.rpow_nonneg (div_nonneg (norm_nonneg _) hT.le) _
  have hr : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have he : ‖f‖ ^ (5/3:ℝ) = ‖f‖ * ‖f‖ ^ (2/3:ℝ) := by
    rw [show (5/3:ℝ) = 1+2/3 by norm_num, Real.rpow_add hr, Real.rpow_one]
  have hp : ‖f‖ ^ (2/3:ℝ) ≤ ‖tfPatchLinear R Φ‖ / T := by
    apply (le_div_iff₀ hT).mpr
    rw [he] at hlow
    nlinarith
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg f) (2/3:ℝ)) hp
    (show (0:ℝ) ≤ 3/2 by norm_num)
  rw [← Real.rpow_mul (norm_nonneg f)] at hh
  norm_num at hh
  exact hh

lemma tfPatchLinear_continuous (R : ℝ) : Continuous (tfPatchLinear R) :=
  (tfPatchPair R).continuous.neg

lemma tfPatchNormBound_continuous (R T : ℝ) : Continuous (tfPatchNormBound R T) :=
  (((tfPatchLinear_continuous R).norm).div_const T).rpow_const (fun _ => Or.inr (by norm_num))

lemma tfPatchNormBound_nonneg (R T : ℝ) (hT : 0 < T) (Φ : TFField R) :
    0 ≤ tfPatchNormBound R T Φ := Real.rpow_nonneg (by positivity) _

lemma tfPatchMinimizer_distance_rpow (R T : ℝ) (hT : 0 < T) (Φ Ψ : TFField R) :
    ‖tfPatchMinimizer R T hT Φ - tfPatchMinimizer R T hT Ψ‖ ^ (5/3:ℝ) ≤
      (‖tfPatchLinear R Φ - tfPatchLinear R Ψ‖ *
        (tfPatchNormBound R T Φ + tfPatchNormBound R T Ψ) / (2*(T*(5/36:ℝ)))) ^ (5/6:ℝ) *
      (tfPatchNormBound R T Φ + tfPatchNormBound R T Ψ) ^ (5/18:ℝ) := by
  have hBΦ := tfPatchNormBound_nonneg R T hT Φ
  have hBΨ := tfPatchNormBound_nonneg R T hT Ψ
  let f := tfPatchMinimizer R T hT Φ
  let g := tfPatchMinimizer R T hT Ψ
  have hf := tfPatchMinimizer_nonneg R T hT Φ
  have hg := tfPatchMinimizer_nonneg R T hT Ψ
  have hm := tfPatchMinimizer_min R T hT Φ
    (nonnegDensity_smul (nonnegDensity_add hf hg) (show (0:ℝ) ≤ 1/2 by norm_num))
  have hgap := tfPatchFunctional_gap R T Φ hT.le hf hg
  have hgmin := tfPatchMinimizer_min R T hT Ψ hf
  have hdiff : tfPatchFunctional R T Φ g - tfPatchFunctional R T Φ f ≤
      (tfPatchLinear R Φ - tfPatchLinear R Ψ) (g-f) := by
    simp only [tfPatchFunctional] at hgmin ⊢
    simp only [sub_apply, map_sub]
    dsimp only [f,g]
    nlinarith
  have hD := (tfPatchLinear R Φ - tfPatchLinear R Ψ).le_opNorm (g-f)
  have hs : ‖g-f‖ ≤ tfPatchNormBound R T Φ + tfPatchNormBound R T Ψ := by
    have hb1 : ‖f‖ ≤ tfPatchNormBound R T Φ := tfPatchMinimizer_norm_le R T hT Φ
    have hb2 : ‖g‖ ≤ tfPatchNormBound R T Ψ := tfPatchMinimizer_norm_le R T hT Ψ
    exact (norm_sub_le g f).trans (by linarith)
  have hupper : (tfPatchLinear R Φ - tfPatchLinear R Ψ) (g-f) ≤
      ‖tfPatchLinear R Φ - tfPatchLinear R Ψ‖ *
        (tfPatchNormBound R T Φ + tfPatchNormBound R T Ψ) :=
    (le_abs_self _).trans (hD.trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _)))
  have hc : 0 < 2*(T*(5/36:ℝ)) := by positivity
  have hw : densityWeight f g ≤ ‖tfPatchLinear R Φ - tfPatchLinear R Ψ‖ *
      (tfPatchNormBound R T Φ + tfPatchNormBound R T Ψ) / (2*(T*(5/36:ℝ))) := by
    apply (le_div_iff₀ hc).mpr
    dsimp only [f,g] at *
    linarith
  have hib := tfLp_interpolation hf hg
  have hsum : ‖f+g‖ ≤ tfPatchNormBound R T Φ + tfPatchNormBound R T Ψ :=
    (norm_add_le f g).trans (add_le_add (tfPatchMinimizer_norm_le R T hT Φ)
      (tfPatchMinimizer_norm_le R T hT Ψ))
  apply hib.trans
  exact mul_le_mul (Real.rpow_le_rpow (densityWeight_nonneg hf hg) hw (by norm_num))
    (Real.rpow_le_rpow (norm_nonneg _) hsum (by norm_num))
    (Real.rpow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (by positivity) _)

theorem tfPatchMinimizer_continuous (R T : ℝ) (hT : 0 < T) :
    Continuous (tfPatchMinimizer R T hT) := by
  apply continuous_iff_continuousAt.mpr
  intro Φ
  have hL := (tfPatchLinear_continuous R).continuousAt (x := Φ)
  have hB := (tfPatchNormBound_continuous R T).continuousAt (x := Φ)
  have h0 : Tendsto (fun Ψ => ‖tfPatchLinear R Ψ - tfPatchLinear R Φ‖)
      (𝓝 Φ) (𝓝 0) := by simpa using (hL.sub_const (tfPatchLinear R Φ)).norm
  have hu : Tendsto (fun Ψ =>
      (‖tfPatchLinear R Ψ - tfPatchLinear R Φ‖ *
        (tfPatchNormBound R T Ψ + tfPatchNormBound R T Φ) / (2*(T*(5/36:ℝ)))) ^ (5/6:ℝ) *
      (tfPatchNormBound R T Ψ + tfPatchNormBound R T Φ) ^ (5/18:ℝ))
      (𝓝 Φ) (𝓝 0) := by
    have ha := ((h0.mul (hB.add_const (tfPatchNormBound R T Φ))).div_const
      (2*(T*(5/36:ℝ)))).rpow_const (Or.inr (by norm_num : (0:ℝ) ≤ 5/6))
    have hb := (hB.add_const (tfPatchNormBound R T Φ)).rpow_const
      (Or.inr (by norm_num : (0:ℝ) ≤ 5/18))
    simpa using ha.mul hb
  have hp : Tendsto (fun Ψ =>
      ‖tfPatchMinimizer R T hT Ψ - tfPatchMinimizer R T hT Φ‖ ^ (5/3:ℝ))
      (𝓝 Φ) (𝓝 0) :=
    squeeze_zero (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      (fun Ψ => tfPatchMinimizer_distance_rpow R T hT Ψ Φ) hu
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := hp.rpow_const (Or.inr (by norm_num : (0:ℝ) ≤ 3/5))
  simpa only [← Real.rpow_mul (norm_nonneg _), show (5/3:ℝ)*(3/5) = 1 by norm_num,
    Real.rpow_one, Real.zero_rpow (by norm_num : (3/5:ℝ) ≠ 0)] using hh

local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma tfPatchMinimizer_measurable (R T : ℝ) (hT : 0 < T) :
    Measurable (tfPatchMinimizer R T hT) := (tfPatchMinimizer_continuous R T hT).measurable

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace CoulombAnalysis

lemma tfPatchFunctional_hasDerivAt (R T : ℝ) (Φ : TFField R) (f h : TFLp (ballMeasure R)) :
    HasDerivAt (fun t : ℝ => tfPatchFunctional R T Φ (f + t • h))
      (T * (∫ x, tfPowerDerivative (f x) * h x ∂ballMeasure R) +
        tfPatchLinear R Φ h + tfCoulombL R f h) 0 := by
  have he (t : ℝ) : tfPatchFunctional R T Φ (f + t • h) =
      T * ‖f + t • h‖ ^ (5 / 3 : ℝ) +
        (tfPatchLinear R Φ f + t * tfPatchLinear R Φ h) +
        (1 / 2 : ℝ) * (tfCoulombL R f f + 2 * t * tfCoulombL R f h +
          t * t * tfCoulombL R h h) := by
    simp only [tfPatchFunctional, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    rw [tfCoulombL_symmetric R h f]
    ring
  simp_rw [he]
  have hk := (tfLp_kinetic_hasDerivAt f h).const_mul T
  have hl := (((hasDerivAt_id (0 : ℝ)).mul_const (tfPatchLinear R Φ h)).const_add (tfPatchLinear R Φ f))
  have hq := ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (tfCoulombL R f h)).const_add
    (tfCoulombL R f f)).add (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (tfCoulombL R h h))
  convert! (hk.add hl).add (hq.const_mul (1 / 2 : ℝ)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq]
  ring

lemma tfPatchFunctional_variation_nonneg (R T : ℝ) (Φ : TFField R) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ g)
    {h : TFLp (ballMeasure R)} (hh : NonnegDensity h) :
    0 ≤ T * (∫ x, tfPowerDerivative (f x) * h x ∂ballMeasure R) +
      tfPatchLinear R Φ h + tfCoulombL R f h := by
  apply hasDerivAt_nonneg_of_right_min (tfPatchFunctional_hasDerivAt R T Φ f h)
  intro t ht
  simpa using hmin (f + t • h) (nonnegDensity_add hf (nonnegDensity_smul hh ht))

lemma tfPatchFunctional_variation_self (R T : ℝ) (Φ : TFField R) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ g) :
    T * (∫ x, tfPowerDerivative (f x) * f x ∂ballMeasure R) +
      tfPatchLinear R Φ f + tfCoulombL R f f = 0 := by
  apply IsLocalMin.hasDerivAt_eq_zero (f := fun t : ℝ => tfPatchFunctional R T Φ (f + t • f))
    _ (tfPatchFunctional_hasDerivAt R T Φ f f)
  have hm : Ioi (-1 : ℝ) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by norm_num)
  filter_upwards [hm] with t ht
  have hn : NonnegDensity (f + t • f) := by
    rw [show f + t • f = (1 + t) • f by rw [add_smul, one_smul]]
    exact nonnegDensity_smul hf (by change -1 < t at ht; linarith)
  simpa using hmin _ hn

def tfPatchGradient (R T : ℝ) (Φ : TFField R) (f : TFLp (ballMeasure R))
    (x : TFSpace) : ℝ :=
  T * tfPowerDerivative (f x) - Φ x + tfBallPotential R f x

lemma tfPatchGradient_integrable (R T : ℝ) (Φ : TFField R) (f : TFLp (ballMeasure R)) :
    Integrable (tfPatchGradient R T Φ f) (ballMeasure R) := by
  have hi : Integrable (fun x => tfPowerDerivative (f x)) (ballMeasure R) := by
    simpa only [mul_one] using tfPowerDerivative_mul_integrable (Lp.memLp f) (memLp_const (1 : ℝ))
  exact ((hi.const_mul T).sub ((Lp.memLp Φ).integrable
    (Fact.out : (1 : ENNReal) ≤ 5/2))).add (tfBallPotential_integrable R f)

lemma tfPatchGradient_mul_integrable (R T : ℝ) (Φ : TFField R) (f h : TFLp (ballMeasure R)) :
    Integrable (fun x => tfPatchGradient R T Φ f x * h x) (ballMeasure R) := by
  have hi := (tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp h)).const_mul T
  have hn : Integrable (fun x => Φ x * h x) (ballMeasure R) :=
    (Lp.memLp Φ).integrable_mul (Lp.memLp h)
  apply ((hi.sub hn).add (tfBallPotential_mul_integrable R f h)).congr
  exact Eventually.of_forall fun x => by dsimp [tfPatchGradient]; ring

lemma tfPatchGradient_pair (R T : ℝ) (Φ : TFField R) (f h : TFLp (ballMeasure R)) :
    (∫ x, tfPatchGradient R T Φ f x * h x ∂ballMeasure R) =
      T * (∫ x, tfPowerDerivative (f x) * h x ∂ballMeasure R) +
        tfPatchLinear R Φ h + tfCoulombL R f h := by
  have hi := (tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp h)).const_mul T
  have hn : Integrable (fun x => Φ x * h x) (ballMeasure R) :=
    (Lp.memLp Φ).integrable_mul (Lp.memLp h)
  have he : (fun x => tfPatchGradient R T Φ f x * h x) =
      (fun x => T * (tfPowerDerivative (f x) * h x) - Φ x * h x +
        tfBallPotential R f x * h x) := by
    ext x
    dsimp only [tfPatchGradient]
    ring
  rw [he, integral_add (hi.sub' hn) (tfBallPotential_mul_integrable R f h),
    integral_sub hi hn]
  simp only [integral_const_mul, tfPatchLinear_apply, tfCoulombL_potential]
  ring

lemma tfPatchGradient_nonneg (R T : ℝ) (Φ : TFField R) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ g) :
    ∀ᵐ x ∂ballMeasure R, 0 ≤ tfPatchGradient R T Φ f x := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (tfPatchGradient_integrable R T Φ f)
  intro s hs _
  let hm : MemLp (s.indicator (fun _ : TFSpace => (1 : ℝ))) (5 / 3) (ballMeasure R) :=
    (memLp_const 1).indicator hs
  let h := hm.toLp (s.indicator (fun _ : TFSpace => (1 : ℝ)))
  have hcoe : (fun x => h x) =ᵐ[ballMeasure R] s.indicator (fun _ => (1 : ℝ)) := hm.coeFn_toLp
  have hh : NonnegDensity h := by
    filter_upwards [hcoe] with x hx
    rw [hx]
    exact indicator_nonneg (fun _ _ => zero_le_one) x
  have hp := tfPatchFunctional_variation_nonneg R T Φ hf hmin hh
  rw [← tfPatchGradient_pair] at hp
  have he : (fun x => tfPatchGradient R T Φ f x * h x) =ᵐ[ballMeasure R]
      s.indicator (tfPatchGradient R T Φ f) := by
    filter_upwards [hcoe] with x hx
    rw [hx]
    by_cases hx' : x ∈ s <;> simp [hx']
  rwa [integral_congr_ae he, integral_indicator hs] at hp

lemma tfPatchGradient_complementarity (R T : ℝ) (Φ : TFField R) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ g) :
    ∀ᵐ x ∂ballMeasure R, tfPatchGradient R T Φ f x * f x = 0 := by
  have hn : ∀ᵐ x ∂ballMeasure R, 0 ≤ tfPatchGradient R T Φ f x * f x := by
    filter_upwards [hf, tfPatchGradient_nonneg R T Φ hf hmin] with x hfx hgx
    exact mul_nonneg hgx hfx
  apply (integral_eq_zero_iff_of_nonneg_ae hn (tfPatchGradient_mul_integrable R T Φ f f)).mp
  rw [tfPatchGradient_pair]
  exact tfPatchFunctional_variation_self R T Φ hf hmin

theorem tfPatchFunctional_euler (R : ℝ) (Φ : TFField R) {T : ℝ} (hT : 0 < T)
    {f : TFLp (ballMeasure R)} (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ g) :
    ∀ᵐ x ∂ballMeasure R, f x =
      (max (Φ x - tfBallPotential R f x) 0 / ((5 / 3 : ℝ) * T)) ^ (3 / 2 : ℝ) := by
  have hA : 0 < (5 / 3 : ℝ) * T := mul_pos (by norm_num) hT
  filter_upwards [hf, tfPatchGradient_nonneg R T Φ hf hmin,
    tfPatchGradient_complementarity R T Φ hf hmin] with x hfx hgx hcx
  have he : (5 / 3 : ℝ) * T * (f x) ^ (2 / 3 : ℝ) = max (Φ x - tfBallPotential R f x) 0 := by
    dsimp only [tfPatchGradient] at hgx hcx
    rw [tfPowerDerivative_nonneg hfx] at hgx hcx
    by_cases hf0 : f x = 0
    · simp only [hf0, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), mul_zero] at hgx ⊢
      rw [max_eq_right (by linarith)]
    · have hz := (mul_eq_zero.mp hcx).resolve_right hf0
      have hp := Real.rpow_nonneg hfx (2 / 3 : ℝ)
      have hxmax : 0 ≤ Φ x - tfBallPotential R f x := by nlinarith
      rw [max_eq_left hxmax]
      nlinarith
  have hdiv : (f x) ^ (2 / 3 : ℝ) = max (Φ x - tfBallPotential R f x) 0 / ((5 / 3 : ℝ) * T) :=
    (eq_div_iff hA.ne').mpr (by nlinarith [he])
  rw [← hdiv, ← Real.rpow_mul hfx]
  norm_num

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace CoulombAnalysis

lemma tfPower_tangent {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    tfPowerDerivative a * (b-a) ≤ b^(5/3:ℝ)-a^(5/3:ℝ) := by
  rw [tfPowerDerivative_nonneg ha]
  have hc := (strictConvexOn_rpow (by norm_num : (1:ℝ) < 5/3)).convexOn
  have hd : HasDerivAt (fun x : ℝ => x^(5/3:ℝ)) ((5/3:ℝ)*a^(2/3:ℝ)) a := by
    convert Real.hasDerivAt_rpow_const (x := a) (p := 5/3) (Or.inr (by norm_num)) using 1; norm_num
  rcases lt_trichotomy a b with hab | rfl | hba
  · have hh := hc.le_slope_of_hasDerivAt ha hb hab hd
    rw [slope_def_field] at hh
    exact (le_div_iff₀ (sub_pos.mpr hab)).mp hh
  · simp
  · have hh := hc.slope_le_of_hasDerivAt hb ha hba hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr hba)).mp hh
    nlinarith

lemma tfLp_kinetic_tangent {R : ℝ} {f g : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hg : NonnegDensity g) :
    (∫ x, tfPowerDerivative (f x) * (g x-f x) ∂ballMeasure R) ≤
      ‖g‖^(5/3:ℝ)-‖f‖^(5/3:ℝ) := by
  have hd : Integrable (fun x => tfPowerDerivative (f x) * (g x-f x)) (ballMeasure R) := by
    apply (tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp (g-f))).congr
    filter_upwards [Lp.coeFn_sub g f] with x hx
    rw [hx]
    rfl
  rw [tfLp_norm_rpow_nonneg hg, tfLp_norm_rpow_nonneg hf,
    ← integral_sub (tf_integrable (Lp.memLp g) hg) (tf_integrable (Lp.memLp f) hf)]
  apply integral_mono_ae hd ((tf_integrable (Lp.memLp g) hg).sub (tf_integrable (Lp.memLp f) hf))
  filter_upwards [hf, hg] with x hfx hgx
  exact tfPower_tangent hfx hgx

lemma tfCoulombL_sub_self (R : ℝ) (f g : TFLp (ballMeasure R)) :
    tfCoulombL R (g-f) (g-f) =
      tfCoulombL R g g - 2*tfCoulombL R f g + tfCoulombL R f f := by
  simp only [map_sub, sub_apply]
  rw [tfCoulombL_symmetric R g f]
  ring

lemma tfPatchFunctional_gap_gradient (R T : ℝ) (hT : 0 ≤ T) (Φ : TFField R)
    {f g : TFLp (ballMeasure R)} (hf : NonnegDensity f) (hg : NonnegDensity g)
    (hmin : ∀ u, NonnegDensity u → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ u) :
    (1/2:ℝ)*tfCoulombL R (g-f) (g-f) +
      (∫ x, tfPatchGradient R T Φ f x * g x ∂ballMeasure R) ≤
      tfPatchFunctional R T Φ g - tfPatchFunctional R T Φ f := by
  have hp := mul_le_mul_of_nonneg_left (tfLp_kinetic_tangent hf hg) hT
  have hs := tfPatchFunctional_variation_self R T Φ hf hmin
  have hi1 := tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp g)
  have hi2 := tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp f)
  have he : (∫ x, tfPowerDerivative (f x) * (g x-f x) ∂ballMeasure R) =
      (∫ x, tfPowerDerivative (f x) * g x ∂ballMeasure R) -
        (∫ x, tfPowerDerivative (f x) * f x ∂ballMeasure R) := by
    simp_rw [mul_sub]
    exact integral_sub hi1 hi2
  rw [he] at hp
  rw [tfCoulombL_sub_self, tfPatchGradient_pair]
  unfold tfPatchFunctional
  linarith

lemma tfPatchGradient_eq_negative_field (R : ℝ) (Φ : TFField R) {T : ℝ} (hT : 0 < T)
    {f : TFLp (ballMeasure R)} (hf : NonnegDensity f)
    (hmin : ∀ u, NonnegDensity u → tfPatchFunctional R T Φ f ≤ tfPatchFunctional R T Φ u) :
    ∀ᵐ x ∂ballMeasure R,
      tfPatchGradient R T Φ f x = max (tfBallPotential R f x - Φ x) 0 := by
  filter_upwards [hf, tfPatchGradient_nonneg R T Φ hf hmin,
    tfPatchGradient_complementarity R T Φ hf hmin] with x hfx hgx hcx
  by_cases hz : f x = 0
  · simp only [tfPatchGradient, hz, tfPowerDerivative, abs_zero,
      mul_zero, zero_sub] at hgx ⊢
    rw [max_eq_left (by linarith)]
    ring
  · have hge := (mul_eq_zero.mp hcx).resolve_right hz
    rw [hge]
    symm
    apply max_eq_right
    have hk : 0 ≤ T * tfPowerDerivative (f x) := by
      rw [tfPowerDerivative_nonneg hfx]
      positivity
    dsimp [tfPatchGradient] at hge
    linarith

theorem tfPatchFunctional_clipping_gap (R : ℝ) (Φ : TFField R) {T : ℝ} (hT : 0 < T)
    {g : TFLp (ballMeasure R)} (hg : NonnegDensity g) :
    (1/2:ℝ)*tfCoulombL R (g-tfPatchMinimizer R T hT Φ) (g-tfPatchMinimizer R T hT Φ) +
      (∫ x, max (tfBallPotential R (tfPatchMinimizer R T hT Φ) x - Φ x) 0 * g x
        ∂ballMeasure R) ≤
      tfPatchFunctional R T Φ g - tfPatchFunctional R T Φ (tfPatchMinimizer R T hT Φ) := by
  have hf := tfPatchMinimizer_nonneg R T hT Φ
  have hm := fun u (hu : NonnegDensity u) => tfPatchMinimizer_min R T hT Φ hu
  have he := tfPatchGradient_eq_negative_field R Φ hT hf hm
  have hh := tfPatchFunctional_gap_gradient R T hT.le Φ hf hg hm
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchGapMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped ENNReal

namespace CoulombAnalysis

local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_1 (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_1 (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_1 (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_1 (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

attribute [local instance] OAI.CoulombAnalysis.instFactNeENNRealHDivOfNatTop_solutions
local instance instFactNeENNRealHDivOfNatTop_solutions_1_refce4c_1 : Fact ((5/2:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩
lemma tfPowerDerivative_pair_measurable (R : ℝ) :
    Measurable (fun p : TFLp (ballMeasure R) × TFLp (ballMeasure R) =>
      ∫ z, tfPowerDerivative (p.1 z)*p.2 z ∂ballMeasure R) := by
  let f : (TFLp (ballMeasure R) × TFLp (ballMeasure R)) → ℝ → ℝ :=
    fun p t => ‖p.1+t • p.2‖^(5/3:ℝ)
  have hc : Continuous (Function.uncurry f) := by
    exact (continuous_fst.fst.add (continuous_snd.smul continuous_fst.snd)).norm.rpow_const
      (fun _ => Or.inr (by norm_num))
  have hm := (measurable_deriv_with_param hc).comp (measurable_id.prodMk (measurable_const (a := (0:ℝ))))
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact (tfLp_kinetic_hasDerivAt p.1 p.2).deriv.symm

def tfPatchGap (R T : ℝ) (hT : 0 < T) (Φ : TFField R) (σ : TFLp (ballMeasure R)) : ℝ :=
  let ρ := tfPatchMinimizer R T hT Φ
  (1/2:ℝ)*tfCoulombL R (σ-ρ) (σ-ρ)+
    (∫ z, max (tfBallPotential R ρ z-Φ z) 0*σ z ∂ballMeasure R)

lemma tfPatchGap_eq_gradient (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    (σ : TFLp (ballMeasure R)) :
    tfPatchGap R T hT Φ σ =
      (1/2:ℝ)*tfCoulombL R (σ-tfPatchMinimizer R T hT Φ) (σ-tfPatchMinimizer R T hT Φ)+
      T*(∫ z, tfPowerDerivative (tfPatchMinimizer R T hT Φ z)*σ z ∂ballMeasure R)+
      tfPatchLinear R Φ σ+tfCoulombL R (tfPatchMinimizer R T hT Φ) σ := by
  have he := tfPatchGradient_eq_negative_field R Φ hT (tfPatchMinimizer_nonneg R T hT Φ)
    (fun u hu => tfPatchMinimizer_min R T hT Φ hu)
  have hi : (∫ z, max (tfBallPotential R (tfPatchMinimizer R T hT Φ) z-Φ z) 0*σ z ∂ballMeasure R) =
      ∫ z, tfPatchGradient R T Φ (tfPatchMinimizer R T hT Φ) z*σ z ∂ballMeasure R :=
    integral_congr_ae (he.mono (fun _ h => congrArg (fun a : ℝ => a*σ _) h.symm))
  rw [tfPatchGap,hi,tfPatchGradient_pair]
  ring

lemma tfPatchGap_measurable (R T : ℝ) (hT : 0 < T) :
    Measurable (fun p : TFField R × TFLp (ballMeasure R) => tfPatchGap R T hT p.1 p.2) := by
  have hr : Continuous (fun p : TFField R × TFLp (ballMeasure R) =>
      tfPatchMinimizer R T hT p.1) :=
    (tfPatchMinimizer_continuous R T hT).comp continuous_fst
  have hs := continuous_snd.sub hr
  have hq := ((tfCoulombL R).continuous.comp hs).clm_apply hs
  have hl := ((tfPatchLinear_continuous R).comp continuous_fst).clm_apply continuous_snd
  have hc := ((tfCoulombL R).continuous.comp hr).clm_apply continuous_snd
  have hd := (tfPowerDerivative_pair_measurable R).comp (hr.measurable.prodMk measurable_snd)
  simpa only [tfPatchGap_eq_gradient,Function.comp_apply,Pi.add_def,Pi.sub_def,Pi.add_apply,Pi.sub_apply] using
    (((hq.measurable.const_mul (1/2:ℝ)).add (hd.const_mul T)).add hl.measurable).add hc.measurable

lemma tfPatchGap_comp_aemeasurable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (R T : ℝ) (hT : 0 < T) (Φ : α → TFField R) (σ : α → TFLp (ballMeasure R))
    (hΦ : AEMeasurable Φ μ) (hσ : AEMeasurable σ μ) :
    AEMeasurable (fun a => tfPatchGap R T hT (Φ a) (σ a)) μ := by
  have hm := (tfPatchGap_measurable R T hT).comp_aemeasurable (hΦ.prodMk hσ)
  simpa only [Function.comp_def] using hm

lemma tfPatchGap_nonneg (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) : 0 ≤ tfPatchGap R T hT Φ σ := by
  unfold tfPatchGap
  exact add_nonneg (mul_nonneg (by norm_num) (tfCoulombL_nonneg R _))
    (integral_nonneg_of_ae (hσ.mono fun _ h => mul_nonneg (le_max_right _ _) h))

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchCoulombControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory

lemma tfCoulombL_pair_sq_le (R : ℝ) (f g : TFLp (ballMeasure R)) :
    (tfCoulombL R f g)^2 ≤ tfCoulombL R f f*tfCoulombL R g g := by
  have hn (t : ℝ) : 0 ≤ tfCoulombL R f f*(t*t)+(-2*tfCoulombL R f g)*t+tfCoulombL R g g := by
    have hh := tfCoulombL_nonneg R (t • f-g)
    simp only [map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul] at hh
    rw [tfCoulombL_symmetric R g f] at hh
    nlinarith
  have hd := discrim_le_zero hn
  unfold discrim at hd
  nlinarith

lemma tfPatchGap_coulomb_le (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) :
    tfCoulombL R (σ-tfPatchMinimizer R T hT Φ) (σ-tfPatchMinimizer R T hT Φ) ≤
      2*tfPatchGap R T hT Φ σ := by
  have hn : 0 ≤ ∫ z, max (tfBallPotential R (tfPatchMinimizer R T hT Φ) z-Φ z) 0*σ z ∂ballMeasure R :=
    integral_nonneg_of_ae (hσ.mono fun _ h => mul_nonneg (le_max_right _ _) h)
  unfold tfPatchGap
  linarith

open MeasureTheory Set InnerProductSpace Laplacian
open scoped BigOperators

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_RadialPacketBase
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

lemma radialPacketBase_smooth : ContDiff ℝ ∞ radialPacketBase := by
  apply Complex.ofRealCLM.contDiff.comp
  apply Real.smoothTransition.contDiff.comp
  exact contDiff_const.sub (contDiff_id.norm_sq ℝ)

lemma radialPacketBase_compact : HasCompactSupport radialPacketBase := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1)
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  by_contra hh
  exact hx (radialPacketBase_zero (not_le.mp hh).le)

lemma radialPacketBase_zero_value : radialPacketBase 0 = 1 := by
  simp [radialPacketBase,Real.smoothTransition.one_of_one_le]

lemma radialPacketSeed_smooth : ContDiff ℝ ∞ radialPacketSeed :=
  radialPacketBase_smooth.comp (ContinuousLinearMap.proj (0 : Fin 1) : Configuration 1 →L[ℝ] Space).contDiff

lemma radialPacketSeed_compact : HasCompactSupport radialPacketSeed := by
  exact radialPacketBase_compact.comp_homeomorph (Homeomorph.funUnique (Fin 1) Space)

lemma radialScaledSeed_smooth (R : ℝ) : ContDiff ℝ ∞ (radialScaledSeed R) :=
  radialPacketSeed_smooth.comp (R⁻¹ • ContinuousLinearMap.id ℝ (Configuration 1)).contDiff

lemma radialScaledSeed_compact {R : ℝ} (hR : 0 < R) : HasCompactSupport (radialScaledSeed R) :=
  radialPacketSeed_compact.comp_smul (inv_ne_zero hR.ne')

lemma radialScaledRaw_mass_pos {R : ℝ} (hR : 0 < R) : 0 < formMass (radialScaledRaw R) := by
  have hn : radialScaledSeed R 0 = 1 := by
    simp only [radialScaledSeed,smul_zero,radialPacketSeed,Pi.zero_apply,radialPacketBase_zero_value]
  have hi : 0 < ∫ x, ‖radialScaledSeed R x‖^2 :=
    ((radialScaledSeed_smooth R).continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (compact_norm_sq (radialScaledSeed_compact hR)) (fun x => sq_nonneg _)
      (x := 0) (by rw [hn]; norm_num)
  change 0 < ∑ _s : Spins 1, ∫ x, ‖radialScaledSeed R x‖^2
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hi

lemma radialScaledRaw_mass (R : ℝ) (hR : 0 < R) :
    formMass (radialScaledRaw R) = R ^ Module.finrank ℝ (Configuration 1) *
      formMass (smoothForm radialPacketSeed) := by
  unfold formMass
  simp only [radialScaledRaw,smoothForm,radialScaledSeed]
  have hi := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Configuration 1))
    (fun x => ‖radialPacketSeed x‖^2) hR.le
  simp only [smul_eq_mul] at hi
  simp_rw [hi,Finset.mul_sum]

lemma radialLocalSeed_smooth (y : Space) (R : ℝ) : ContDiff ℝ ∞ (radialLocalSeed y R) :=
  (radialScaledSeed_smooth R).comp (contDiff_id.add contDiff_const)

lemma radialLocalSeed_compact (y : Space) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (radialLocalSeed y R) :=
  (radialScaledSeed_compact hR).comp_homeomorph (Homeomorph.addRight (radialCenterShift y))

lemma radialLocalRaw_sobolev (y : Space) {R : ℝ} (hR : 0 < R) :
    SobolevFermion (radialLocalRaw y R) := by
  refine ⟨fun _ => (radialLocalSeed_smooth y R).continuous.memLp_of_hasCompactSupport
    (radialLocalSeed_compact y hR),fun s i a => ?_,fun s i a φ hφ hcφ => ?_,?_⟩
  · exact (smooth_derivative_continuous (radialLocalSeed_smooth y R) _).memLp_of_hasCompactSupport
      (compact_derivative (radialLocalSeed_compact y hR) _)
  · exact smooth_weak_gradient (radialLocalSeed_smooth y R) (radialLocalSeed_compact y hR) hφ hcφ _
  · intro π s
    have hp : π = 1 := Subsingleton.elim _ _
    subst π
    exact Eventually.of_forall fun x => by simp [radialLocalRaw,smoothForm]

lemma radialLocalRaw_mass (y : Space) (R : ℝ) :
    formMass (radialLocalRaw y R) = formMass (radialScaledRaw R) := by
  unfold formMass
  apply Finset.sum_congr rfl
  intro s _
  exact integral_add_right_eq_self (fun x => ‖(radialScaledRaw R).value s x‖^2) _

lemma radialLocalOrbital_admissible (y : Space) {R : ℝ} (hR : 0 < R) :
    FormAdmissible (radialLocalOrbital y R) := by
  apply (radialLocalRaw_sobolev y hR).normalize
  rw [radialLocalRaw_mass]
  exact radialScaledRaw_mass_pos hR

lemma radialLocalRaw_zero (y : Space) {R : ℝ} (hR : 0 < R) {x : Configuration 1}
    (hx : R < ‖x 0-y‖) : FormZeroAt (radialLocalRaw y R) x := by
  have hz (z : Configuration 1) (hz : R < ‖z 0-y‖) : radialLocalSeed y R z = 0 := by
    by_contra hn
    exact (not_lt_of_ge (le_of_lt hz)) (radialLocalSeed_support y hR hn)
  have he : radialLocalSeed y R =ᶠ[𝓝 x] fun _ => (0:ℂ) :=
    ((((continuous_apply (0 : Fin 1)).sub continuous_const).norm.tendsto x).eventually
      (eventually_gt_nhds hx)).mono fun z hz' => hz z hz'
  intro s
  refine ⟨hz x hx,fun i a => ?_⟩
  change fderiv ℝ (radialLocalSeed y R) x (direction i a) = 0
  rw [he.fderiv_eq]
  simp

lemma radialLocalOrbital_zero (y : Space) {R : ℝ} (hR : 0 < R) {x : Configuration 1}
    (hx : R < ‖x 0-y‖) : FormZeroAt (radialLocalOrbital y R) x := by
  intro s
  have hh := radialLocalRaw_zero y hR hx s
  constructor
  · change _ * (radialLocalRaw y R).value s x = 0
    rw [hh.1,mul_zero]
  · intro i a
    change _ * (radialLocalRaw y R).gradient s i a x = 0
    rw [hh.2,mul_zero]

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketDensity
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

lemma integral_one_configuration (f : Configuration 1 → ℝ) :
    (∫ y : Space, f (fun _ => y)) = ∫ x, f x := by
  exact ((volume_preserving_funUnique (Fin 1) Space).symm
    (MeasurableEquiv.funUnique (Fin 1) Space)).integral_comp
    (MeasurableEquiv.funUnique (Fin 1) Space).symm.measurableEmbedding f

lemma packetDensity_formula (y : Space) (R : ℝ) (x : Space) :
    packetDensity y R x = (Fintype.card (Spins 1) : ℝ) *
      (Real.sqrt (formMass (radialScaledRaw R)))⁻¹ ^ 2 *
      ‖radialPacketBase (R⁻¹ • (x-y))‖^2 := by
  simp only [packetDensity,radialLocalOrbital,scaleForm,norm_real_mul_sq,radialLocalRaw_mass]
  simp only [radialLocalRaw,smoothForm,radialLocalSeed,radialScaledSeed,
    radialPacketSeed,radialCenterShift,Pi.smul_apply,Pi.add_apply,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,sub_eq_add_neg,mul_assoc]

lemma packetDensity_continuous (y : Space) (R : ℝ) : Continuous (packetDensity y R) := by
  change Continuous (fun x => packetDensity y R x)
  simp_rw [packetDensity_formula]
  have hc : Continuous (fun x : Space => R⁻¹ • (x-y)) :=
    (continuous_id.sub continuous_const).const_smul R⁻¹
  have hn : Continuous (fun x : Space => ‖radialPacketBase (R⁻¹ • (x-y))‖^2) :=
    (radialPacketBase_smooth.continuous.comp hc).norm.pow 2
  exact continuous_const.mul hn

lemma packetDensity_support (y : Space) {R : ℝ} (hR : 0 < R) {x : Space}
    (hx : packetDensity y R x ≠ 0) : ‖x-y‖ ≤ R := by
  by_contra hh
  have hz := radialLocalOrbital_zero y hR (x := fun _ => x) (not_le.mp hh)
  apply hx
  unfold packetDensity
  apply Finset.sum_eq_zero
  intro s _
  rw [(hz s).1,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)]

lemma packetDensity_compact (y : Space) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (packetDensity y R) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall y R)
  intro x hx
  exact (Metric.mem_closedBall).mpr (packetDensity_support y hR hx)

lemma packetDensity_integrable (y : Space) {R : ℝ} (hR : 0 < R) :
    Integrable (packetDensity y R) :=
  (packetDensity_continuous y R).integrable_of_hasCompactSupport (packetDensity_compact y hR)

lemma packetDensity_memLp (y : Space) {R : ℝ} (hR : 0 < R) :
    MemLp (packetDensity y R) (5/3) :=
  (packetDensity_continuous y R).memLp_of_hasCompactSupport (packetDensity_compact y hR)

lemma packetDensity_mass (y : Space) {R : ℝ} (hR : 0 < R) :
    (∫ x, packetDensity y R x) = 1 := by
  have hm := (radialLocalOrbital_admissible y hR).2.2.2.2.1
  change formMass (radialLocalOrbital y R) = 1 at hm
  rw [← hm]
  unfold packetDensity formMass
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    exact integral_one_configuration (fun x => ‖(radialLocalOrbital y R).value s x‖^2)
  · intro s _
    have hh := ((radialLocalOrbital_admissible y hR).1 s).integrable_norm_pow (by norm_num)
    exact ((volume_preserving_funUnique (Fin 1) Space).symm
        (MeasurableEquiv.funUnique (Fin 1) Space)).integrable_comp_of_integrable hh

lemma packetDensity_radial (R : ℝ) : CoulombAnalysis.IsRadial (packetDensity 0 R) := by
  intro x y hxy
  simp only [packetDensity_formula,sub_zero,radialPacketBase,norm_smul,hxy]

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpatialRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
namespace CoulombAtom

lemma packetDensity_nonneg (p : Space) (r : ℝ) (x : Space) : 0 ≤ packetDensity p r x := by
  simp only [packetDensity_formula]
  positivity

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SmoothNewton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SmoothNewton_scope

open MeasureTheory Filter Set Metric InnerProductSpace Laplacian
open scoped ContDiff BigOperators Convolution

namespace CoulombAnalysis

lemma tfLaplacian_translate (f : TFSpace → ℝ) (a : TFSpace) :
    Δ (fun x => f (a+x)) = fun x => Δ f (a+x) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,iteratedFDeriv_comp_add_left]

end CoulombAnalysis
namespace CoulombAtom

lemma packetDensity_smooth (y : Space) (R : ℝ) :
    ContDiff ℝ ∞ (packetDensity y R) := by
  have hc : ContDiff ℝ ∞ (fun x : Space => R⁻¹ • (x-y)) :=
    (contDiff_id.sub contDiff_const).const_smul R⁻¹
  have hn := (radialPacketBase_smooth.comp hc).norm_sq ℝ
  change ContDiff ℝ ∞ (fun x : Space => packetDensity y R x)
  simp_rw [packetDensity_formula]
  exact contDiff_const.mul hn

end CoulombAtom

end Work_SmoothNewton_scope

open MeasureTheory Filter Set Metric InnerProductSpace Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis

lemma radial_mollifier_laplacian_identity {η : ℕ → TFSpace → ℝ} {r : ℕ → ℝ}
    (hrpos : ∀ n, 0 < r n) (hr : Tendsto r atTop (𝓝 0))
    (hc : ∀ n, ContDiff ℝ 2 (η n)) (hcompact : ∀ n, HasCompactSupport (η n))
    (hn : ∀ n x, 0 ≤ η n x) (hm : ∀ n, ∫ x, η n x = 1)
    (hs : ∀ n x, η n x ≠ 0 → ‖x‖ ≤ r n) (hrad : ∀ n, IsRadial (η n))
    {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    (∫ x, Δ g x/‖x‖) = -(4*Real.pi*g 0) := by
  have hi (n : ℕ) : Integrable (η n) := (hc n).continuous.integrable_of_hasCompactSupport (hcompact n)
  have hp (n : ℕ) : MemLp (η n) (5/3) :=
    (hc n).continuous.memLp_of_hasCompactSupport (hcompact n)
  have hdl := tfLaplacian_continuous hg
  have hdcomp := tfLaplacian_compact hg hcg
  have hbound : Integrable (fun x : TFSpace => |Δ g x|/‖x‖) := by
    simpa only [zero_sub,norm_neg,Real.norm_eq_abs,abs_div,abs_norm] using
      (tfPotential_integrable (hdl.integrable_of_hasCompactSupport hdcomp)
        (hdl.memLp_of_hasCompactSupport hdcomp) 0).norm
  have hlim : Tendsto (fun n => ∫ x, tfPotential (η n) x*Δ g x) atTop
      (𝓝 (∫ x, Δ g x/‖x‖)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |Δ g x|/‖x‖)
    · intro n
      exact (((tfPotential_contDiff (hc n) (hcompact n)).continuous).mul hdl).aestronglyMeasurable
    · exact hbound
    · intro n
      filter_upwards [CoulombAtom.ae_ne_point (0 : TFSpace)] with x hx
      rw [norm_mul,Real.norm_of_nonneg (tfPotential_nonneg (Eventually.of_forall (hn n)) x),
        Real.norm_eq_abs]
      have hb := CoulombAtom.radial_potential_le_point (hi n) (hp n) (hn n) (hrad n)
        (hrpos n).le (hs n) hx
      rw [hm] at hb
      have hh := mul_le_mul_of_nonneg_right hb (abs_nonneg (Δ g x))
      simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
    · filter_upwards [CoulombAtom.ae_ne_point (0 : TFSpace)] with x hx
      have hsmall := hr.eventually (gt_mem_nhds (norm_pos_iff.mpr hx))
      apply tendsto_const_nhds.congr'
      filter_upwards [hsmall] with n hnx
      rw [tfPotential_newton_exterior_closed (hi n) (hp n) (hrad n) (hrpos n) (hs n) hnx.le,hm]
      ring
  have hright := (shrinking_density_test_limit (fun n => (hc n).continuous) hcompact hn hm hs hr
    hg.continuous).const_mul (-(4*Real.pi))
  have he (n : ℕ) : (∫ x, tfPotential (η n) x*Δ g x) =
      -(4*Real.pi)*(∫ x, η n x*g x) := by
    rw [compact_laplacian_green (tfPotential_contDiff (hc n) (hcompact n)) hg hcg,
      tfPotential_poisson_global (hc n) (hcompact n) (hrad n)]
    calc
      _ = ∫ x, -(4*Real.pi)*(η n x*g x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := integral_const_mul _ _
  have hh := tendsto_nhds_unique hlim (hright.congr (fun n => (he n).symm))
  simpa only [neg_mul] using hh

theorem compact_laplacian_newton_zero {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    (∫ x, Δ g x/‖x‖) = -(4*Real.pi*g 0) := by
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hrpos (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply radial_mollifier_laplacian_identity (η := fun n => CoulombAtom.packetDensity 0 (r n)) hrpos hr
    (fun n => (CoulombAtom.packetDensity_smooth 0 (r n)).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (fun n => CoulombAtom.packetDensity_compact 0 (hrpos n))
    (fun n => CoulombAtom.packetDensity_nonneg 0 (r n))
    (fun n => CoulombAtom.packetDensity_mass 0 (hrpos n))
    (fun n x hx => by simpa only [sub_zero] using CoulombAtom.packetDensity_support 0 (hrpos n) hx)
    (fun n => CoulombAtom.packetDensity_radial (r n)) hg hcg

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CoulombTestCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric InnerProductSpace Laplacian
open scoped BigOperators ContDiff Topology

lemma tfLaplacian_support {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) :
    Function.support (Δ g) ⊆ tsupport g := by
  intro x hx
  by_contra hn
  apply hx
  rw [tfLaplacian_eq hg]
  apply Finset.sum_eq_zero
  intro i _
  apply Function.notMem_support.mp
  intro hi
  apply hn
  exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1))
    ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)) (subset_tsupport _ hi))

theorem tfPotential_laplacian {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) (z : TFSpace) :
    tfPotential (Δ g) z = -(4*Real.pi*g z) := by
  have hgc : HasCompactSupport (fun x => g (z+x)) :=
    hcg.comp_homeomorph (Homeomorph.addLeft z)
  have hh := compact_laplacian_newton_zero (hg.comp (contDiff_const.add contDiff_id)) hgc
  simp only [Function.comp_def,id_eq] at hh
  rw [tfLaplacian_translate] at hh
  simp only [add_zero] at hh
  have hi := integral_add_left_eq_self (μ := volume) (fun x => Δ g x/‖z-x‖) z
  calc
    tfPotential (Δ g) z = ∫ x, Δ g (z+x)/‖z-(z+x)‖ := hi.symm
    _ = ∫ x, Δ g (z+x)/‖x‖ := by simp only [sub_add_cancel_left,norm_neg]
    _ = _ := hh

def coulombTestCharge (g : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  -(Δ g x)/(4*Real.pi)

lemma coulombTestCharge_continuous {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) :
    Continuous (coulombTestCharge g) := (tfLaplacian_continuous hg).neg.div_const _

lemma coulombTestCharge_compact {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    HasCompactSupport (coulombTestCharge g) := by
  change HasCompactSupport (fun x => (-Δ g x)*(4*Real.pi)⁻¹)
  exact ((tfLaplacian_compact hg hcg).neg).mul_right

lemma coulombTestCharge_support {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) :
    Function.support (coulombTestCharge g) ⊆ tsupport g := by
  intro x hx
  apply tfLaplacian_support hg
  intro hz
  exact hx (by simp [coulombTestCharge,hz])

theorem tfPotential_testCharge {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) (z : TFSpace) :
    tfPotential (coulombTestCharge g) z = g z := by
  have he : (fun x => coulombTestCharge g x/‖z-x‖) =
      fun x => (-(4*Real.pi)⁻¹)*(Δ g x/‖z-x‖) := by
    funext x
    unfold coulombTestCharge
    ring
  rw [tfPotential,he,integral_const_mul]
  change -(4*Real.pi)⁻¹*tfPotential (Δ g) z = g z
  rw [tfPotential_laplacian hg hcg z]
  field_simp [Real.pi_ne_zero]

theorem testCharge_dirichlet_energy {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    (∫ x, tfPotential (coulombTestCharge g) x*coulombTestCharge g x) =
      (4*Real.pi)⁻¹*(∑ i : Fin 3, ∫ x, (tfPartial g i x)^2) := by
  simp_rw [tfPotential_testCharge hg hcg,coulombTestCharge]
  have he : (fun x => g x*(-Δ g x/(4*Real.pi))) =
      fun x => -(4*Real.pi)⁻¹*(g x*Δ g x) := by funext x; ring
  rw [he,integral_const_mul,compact_laplacian_energy hg hcg]
  ring

open MeasureTheory Filter Set Metric InnerProductSpace Laplacian
open scoped BigOperators ContDiff Topology

lemma exists_patch_testCharge (R : ℝ) {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 R) :
    ∃ f : TFLp (ballMeasure R),
      (∀ x, tfBallPotential R f x = g x) ∧
      tfCoulombL R f f = (4*Real.pi)⁻¹*(∑ i : Fin 3, ∫ x, (tfPartial g i x)^2) := by
  let ρ := coulombTestCharge g
  have hρs : Function.support ρ ⊆ ball 0 R := (coulombTestCharge_support hg).trans hs
  have hρ : MemLp ρ (5/3) := (coulombTestCharge_continuous hg).memLp_of_hasCompactSupport
    (coulombTestCharge_compact hg hcg)
  have hm : MemLp ρ (5/3) (ballMeasure R) := hρ.mono_measure Measure.restrict_le_self
  let f : TFLp (ballMeasure R) := hm.toLp ρ
  have hf : (fun x => f x) =ᵐ[ballMeasure R] ρ := hm.coeFn_toLp
  have hpot (x : TFSpace) : tfBallPotential R f x = g x := by
    calc
      _ = ∫ y, ρ y/‖x-y‖ ∂ballMeasure R := integral_congr_ae (hf.mono fun y hy => by change f y = ρ y at hy; rw [hy])
      _ = ∫ y, ρ y/‖x-y‖ := by
        rw [ballMeasure,←integral_indicator measurableSet_ball]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          by_cases hy : y ∈ ball (0 : TFSpace) R
          · simp [hy]
          · have hz : ρ y = 0 := Function.notMem_support.mp (fun h => hy (hρs h))
            simp [hy,hz]
      _ = _ := tfPotential_testCharge hg hcg x
  refine ⟨f,hpot,?_⟩
  rw [tfCoulombL_potential]
  simp_rw [hpot]
  calc
    _ = ∫ x, g x*ρ x ∂ballMeasure R := integral_congr_ae (hf.mono fun x hx => by change f x = ρ x at hx; rw [hx])
    _ = ∫ x, g x*ρ x := by
      rw [ballMeasure,←integral_indicator measurableSet_ball]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ ball (0 : TFSpace) R
        · simp [hx]
        · have hz : ρ x = 0 := Function.notMem_support.mp (fun h => hx (hρs h))
          simp [hx,hz]
    _ = _ := by simpa only [tfPotential_testCharge hg hcg] using testCharge_dirichlet_energy hg hcg

theorem tfCoulomb_dirichlet_duality (R : ℝ) (f : TFLp (ballMeasure R))
    {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 R) :
    (∫ x, g x*f x ∂ballMeasure R)^2 ≤
      ((4*Real.pi)⁻¹*(∑ i : Fin 3, ∫ x, (tfPartial g i x)^2))*tfCoulombL R f f := by
  obtain ⟨q,hq,hqe⟩ := exists_patch_testCharge R hg hcg hs
  have he : tfCoulombL R q f = ∫ x, g x*f x ∂ballMeasure R := by
    rw [tfCoulombL_potential]
    simp_rw [hq]
  simpa only [he,hqe] using tfCoulombL_pair_sq_le R q f

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis

lemma local_laplacian_green_ball {f g : TFSpace → ℝ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : ∀ x ∈ ball (0 : TFSpace) R, ContDiffAt ℝ 2 f x)
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) (hs : tsupport g ⊆ ball 0 r) :
    (∫ x, f x*Δ g x) = ∫ x, Δ f x*g x := by
  let b : ContDiffBump (0 : TFSpace) := ⟨r,(r+R)/2,hr,by linarith⟩
  let F : TFSpace → ℝ := fun x => b x*f x
  have hbR : b.rOut < R := by dsimp [b]; linarith
  have hF : ContDiff ℝ 2 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball (0 : TFSpace) R
    · exact b.contDiffAt.mul (hf x hx)
    · have hnx : b.rOut < ‖x‖ := hbR.trans_le (le_of_not_gt (by
        simpa only [mem_ball,dist_zero_right] using hx))
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [continuous_norm.continuousAt.eventually (Ioi_mem_nhds hnx)] with z hz
      simp only [F,b.zero_of_le_dist (by simpa only [dist_zero_right] using hz.le),zero_mul]
  have he {x : TFSpace} (hx : x ∈ ball 0 r) : F =ᶠ[𝓝 x] f := by
    have hn : ‖x‖ < b.rIn := by simpa only [mem_ball,dist_zero_right] using hx
    filter_upwards [continuous_norm.continuousAt.eventually (Iio_mem_nhds hn)] with z hz
    simp only [F,b.one_of_mem_closedBall (by simpa only [mem_closedBall,dist_zero_right] using hz.le),one_mul]
  calc
    _ = ∫ x, F x*Δ g x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : Δ g x = 0
        · simp only [hx,mul_zero]
        · change f x * Δ g x = F x * Δ g x
          rw [(he (hs (tfLaplacian_support hg hx))).eq_of_nhds]
    _ = ∫ x, Δ F x*g x := compact_laplacian_green hF hg hcg
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : g x = 0
        · simp only [hx,mul_zero]
        · change Δ F x * g x = Δ f x * g x
          rw [(laplacian_congr_nhds (he (hs (subset_tsupport g hx)))).eq_of_nhds]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_QuantumRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_QuantumRawLaw_scope

open MeasureTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology

namespace CoulombAtom

attribute [local irreducible] graphComponent fermionGraphValue

def graphRawDensity {N : ℕ} (F : fermionGraph N) (x : Configuration N) : ℝ :=
  ∑ s : Spins N, ‖graphComponent s none F x‖^2

def graphRawLaw {N : ℕ} (F : fermionGraph N) : Measure (Configuration N) :=
  volume.withDensity (fun x => ENNReal.ofReal (graphRawDensity F x))

end CoulombAtom

end Work_QuantumRawLaw_scope

open MeasureTheory Filter Set
open scoped ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ArraySymmetry
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom
open CoulombObservation

def flattenConfiguration (N : ℕ) : Configuration N →L[ℝ] (Fin N × Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun q => (EuclideanSpace.proj q.2).comp
    (ContinuousLinearMap.proj q.1))

@[simp] lemma flattenConfiguration_apply {N : ℕ} (x : Configuration N)
    (q : Fin N × Fin 3) : flattenConfiguration N x q = x q.1 q.2 := rfl

@[simp] lemma flattenConfiguration_direction {N : ℕ} (i : Fin N) (a : Fin 3) :
    flattenConfiguration N (direction i a) = Pi.single (i,a) 1 := by
  ext ⟨j,c⟩
  simp only [flattenConfiguration_apply, direction, Pi.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

lemma lineDeriv_flattenConfiguration {N : ℕ} (f : (Fin N × Fin 3 → ℝ) → ℝ)
    (x : Configuration N) (i : Fin N) (a : Fin 3) :
    lineDeriv ℝ (fun y => f (flattenConfiguration N y)) x (direction i a) =
      lineDeriv ℝ f (flattenConfiguration N x) (Pi.single (i,a) 1) := by
  unfold lineDeriv
  simp only [map_add, map_smul, flattenConfiguration_direction]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ConfigurationCoordinates
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

namespace CoulombAtom
variable {N : ℕ}

def configurationCoordinates (N : ℕ) : Configuration N ≃L[ℝ] ((Fin N × Fin 3) → ℝ) :=
  ({ toFun := flattenConfiguration N
     invFun := fun x i => WithLp.toLp 2 (fun a => x (i,a))
     left_inv := by intro x; rfl
     right_inv := by intro x; rfl
     map_add' := (flattenConfiguration N).map_add
     map_smul' := (flattenConfiguration N).map_smul }: Configuration N ≃ₗ[ℝ] ((Fin N × Fin 3) → ℝ)).toContinuousLinearEquiv

@[simp] lemma configurationCoordinates_apply (x : Configuration N) (q : Fin N × Fin 3) :
    configurationCoordinates N x q = x q.1 q.2 := rfl

@[simp] lemma configurationCoordinates_symm_apply (x : (Fin N × Fin 3) → ℝ) (i : Fin N) (a : Fin 3) :
    (configurationCoordinates N).symm x i a = x (i,a) := rfl

lemma configurationCoordinates_preserving (N : ℕ) : MeasurePreserving (configurationCoordinates N) := by
  refine ⟨(configurationCoordinates N).continuous.measurable, ?_⟩
  apply Eq.symm
  change Measure.pi (fun _ : Fin N × Fin 3 => (volume : Measure ℝ)) = _
  apply Measure.pi_eq
  intro A hA
  rw [Measure.map_apply (configurationCoordinates N).continuous.measurable (MeasurableSet.univ_pi hA)]
  have he : configurationCoordinates N ⁻¹' pi univ A =
      pi univ (fun i : Fin N => (WithLp.ofLp : Space → (Fin 3 → ℝ)) ⁻¹'
        pi univ (fun a => A (i,a))) := by
    ext x
    simp only [mem_preimage,mem_univ_pi,configurationCoordinates_apply,Prod.forall]
  rw [he,volume_pi,Measure.pi_pi]
  calc
    _ = ∏ i : Fin N, ∏ a : Fin 3, volume (A (i,a)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [(PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
        (MeasurableSet.univ_pi (fun a => hA (i,a))).nullMeasurableSet,volume_pi,Measure.pi_pi]
    _ = _ := (Fintype.prod_prod_type (fun q : Fin N × Fin 3 => (volume : Measure ℝ) (A q))).symm

lemma configurationCoordinates_symm_preserving (N : ℕ) :
    MeasurePreserving (configurationCoordinates N).symm :=
  MeasurePreserving.symm (configurationCoordinates N).toHomeomorph.toMeasurableEquiv
    (configurationCoordinates_preserving N)

lemma configurationCoordinates_permute (π : Equiv.Perm (Fin N)) (x : (Fin N × Fin 3) → ℝ) :
    (configurationCoordinates N).symm (CoulombNeumann.flatPermutation π x) =
      (configurationCoordinates N).symm x ∘ π := by
  funext i
  apply WithLp.ofLp_injective
  funext a
  change CoulombNeumann.flatPermutation π x (i,a) = x (π i,a)
  simp [CoulombNeumann.flatPermutation_apply,CoulombNeumann.particlePermute]

lemma integral_configurationCoordinates {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ((Fin N × Fin 3) → ℝ) → E) :
    (∫ x : Configuration N, f (configurationCoordinates N x)) = ∫ x, f x :=
  (configurationCoordinates_preserving N).integral_comp
    (configurationCoordinates N).toHomeomorph.measurableEmbedding f

lemma integral_configurationCoordinates_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Configuration N → E) :
    (∫ x : (Fin N × Fin 3) → ℝ, f ((configurationCoordinates N).symm x)) = ∫ x, f x :=
  (configurationCoordinates_symm_preserving N).integral_comp
    (configurationCoordinates N).symm.toHomeomorph.measurableEmbedding f

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_NeumannPhysical
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

namespace CoulombAtom
open CoulombNeumann
variable {N : ℕ}

def cartesianValue (ψ : FormVector N) (s : Spins N) (x : (Fin N × Fin 3) → ℝ) : ℂ :=
  ψ.value s ((configurationCoordinates N).symm x)

def cartesianGradient (ψ : FormVector N) (s : Spins N) (q : Fin N × Fin 3)
    (x : (Fin N × Fin 3) → ℝ) : ℂ := ψ.gradient s q.1 q.2 ((configurationCoordinates N).symm x)

lemma SobolevFermion.cartesian_anti {ψ : FormVector N} (hψ : SobolevFermion ψ) :
    FlatAEAntisymmetric (cartesianValue ψ) := by
  intro π s
  filter_upwards [(configurationCoordinates_symm_preserving N).quasiMeasurePreserving.ae
    (hψ.2.2.2 π s)] with x hx
  simpa only [cartesianValue,configurationCoordinates_permute] using hx

lemma SobolevFermion.cartesian_weak {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (s : Spins N) (q : Fin N × Fin 3) (φ : ((Fin N × Fin 3) → ℝ) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, cartesianValue ψ s x * Complex.ofReal (lineDeriv ℝ φ x (Pi.single q 1))) =
      -(∫ x, cartesianGradient ψ s q x*(φ x:ℂ)) := by
  have hh := hψ.2.2.1 s q.1 q.2 (fun y => φ (configurationCoordinates N y))
    (hφ.comp (configurationCoordinates N).contDiff)
    (hc.comp_homeomorph (configurationCoordinates N).toHomeomorph)
  have hd (x : Configuration N) :
      lineDeriv ℝ (fun y => φ (configurationCoordinates N y)) x (direction q.1 q.2) =
        lineDeriv ℝ φ (configurationCoordinates N x) (Pi.single q 1) := by
    exact lineDeriv_flattenConfiguration φ x q.1 q.2
  simp only [hd] at hh
  calc
    _ = ∫ x : Configuration N, cartesianValue ψ s (configurationCoordinates N x) *
        Complex.ofReal (lineDeriv ℝ φ (configurationCoordinates N x) (Pi.single q 1)) :=
      (integral_configurationCoordinates (fun x => cartesianValue ψ s x *
        Complex.ofReal (lineDeriv ℝ φ x (Pi.single q 1)))).symm
    _ = -(∫ x : Configuration N, cartesianGradient ψ s q (configurationCoordinates N x) *
        (φ (configurationCoordinates N x):ℂ)) := by
      simpa only [cartesianValue,cartesianGradient,ContinuousLinearEquiv.symm_apply_apply] using hh
    _ = _ := congrArg Neg.neg (integral_configurationCoordinates (fun x => cartesianGradient ψ s q x*(φ x:ℂ)))

end CoulombAtom

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_RadialShellPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombAnalysis

lemma tfPotential_radial_max {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5/3)) (hr : IsRadial ρ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) (x : TFSpace) :
    tfPotential ρ x = ∫ y, ρ y / max ‖x‖ ‖y‖ := by
  by_cases hx : x = 0
  · subst x
    simp only [tfPotential, norm_zero, max_eq_right (norm_nonneg _), zero_sub, norm_neg]
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hi : Integrable (fun y => ρ y/max ‖x‖ ‖y‖) := by
    apply (h1.norm.div_const ‖x‖).mono'
      (h1.aemeasurable.div
        ((continuous_const.max continuous_norm).aemeasurable)).aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      change ‖ρ y/max ‖x‖ ‖y‖‖ ≤ ‖ρ y‖/‖x‖
      rw [norm_div, Real.norm_of_nonneg
        (show 0 ≤ max ‖x‖ ‖y‖ from (norm_nonneg x).trans (le_max_left _ _))]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hx0 (le_max_left _ _)
  rw [tfPotential_newton h1 hp hr hR hs hx]
  let A := {y : TFSpace | ‖y‖ ≤ ‖x‖}
  have hA : MeasurableSet A := measurableSet_le measurable_norm measurable_const
  rw [← integral_add_compl hA hi]
  congr 1
  · rw [← integral_div]
    apply setIntegral_congr_fun hA
    intro y hy
    change ρ y/‖x‖ = ρ y/max ‖x‖ ‖y‖
    rw [max_eq_left (show ‖y‖ ≤ ‖x‖ from hy)]
  · have he : Aᶜ = {y : TFSpace | ‖x‖ < ‖y‖} := by ext y; simp [A, not_le]
    rw [he]
    apply setIntegral_congr_fun (measurableSet_lt measurable_const measurable_norm)
    intro y hy
    change ρ y/‖y‖ = ρ y/max ‖x‖ ‖y‖
    rw [max_eq_right hy.le]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellCoulombDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombAnalysis

lemma exists_patch_density (R : ℝ) {ρ : TFSpace → ℝ} (hp : MemLp ρ (5/3))
    (hs : Function.support ρ ⊆ ball 0 R) :
    ∃ q : TFLp (ballMeasure R),
      (∀ᵐ x ∂ballMeasure R, q x = ρ x) ∧
      (∀ x, tfBallPotential R q x = tfPotential ρ x) := by
  have hm : MemLp ρ (5/3) (ballMeasure R) := hp.mono_measure Measure.restrict_le_self
  let q : TFLp (ballMeasure R) := hm.toLp ρ
  have hq : (fun x => q x) =ᵐ[ballMeasure R] ρ := hm.coeFn_toLp
  refine ⟨q,hq,fun x => ?_⟩
  change (∫ y, q y/‖x-y‖ ∂ballMeasure R) = ∫ y, ρ y/‖x-y‖
  rw [integral_congr_ae (hq.mono fun y hy => congrArg (fun z : ℝ => z/‖x-y‖) hy)]
  rw [ballMeasure,← integral_indicator measurableSet_ball]
  apply integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ ball (0 : TFSpace) R
  · simp [hy]
  · have hz : ρ y = 0 := Function.notMem_support.mp (fun hh => hy (hs hh))
    simp [hy,hz]

end CoulombAnalysis

open MeasureTheory Filter Set Metric
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_PatchWeakPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff

namespace CoulombAnalysis

theorem tfBallPotential_weak_laplacian (R : ℝ) (f : TFLp (ballMeasure R))
    {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 R) :
    (∫ x, tfBallPotential R f x*Δ g x ∂ballMeasure R) =
      -(4*Real.pi)*(∫ x, f x*g x ∂ballMeasure R) := by
  obtain ⟨q,hq,hpot⟩ := exists_patch_density R
    ((tfLaplacian_continuous hg).memLp_of_hasCompactSupport (tfLaplacian_compact hg hcg))
    ((tfLaplacian_support hg).trans hs)
  calc
    _ = tfCoulombL R f q := by
      rw [tfCoulombL_potential]
      exact integral_congr_ae (hq.mono fun x hx => by simp only [hx])
    _ = tfCoulombL R q f := tfCoulombL_symmetric R f q
    _ = ∫ x, tfPotential (Δ g) x*f x ∂ballMeasure R := by
      rw [tfCoulombL_potential]
      simp_rw [hpot]
    _ = -(4*Real.pi)*(∫ x, f x*g x ∂ballMeasure R) := by
      simp_rw [tfPotential_laplacian hg hcg]
      rw [← integral_const_mul]
      congr 1
      funext x
      ring

lemma tfBallPotential_laplacian_integrable (R : ℝ) (f : TFLp (ballMeasure R))
    {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 R) :
    Integrable (fun x => tfBallPotential R f x*Δ g x) (ballMeasure R) := by
  obtain ⟨q,hq,_⟩ := exists_patch_density R
    ((tfLaplacian_continuous hg).memLp_of_hasCompactSupport (tfLaplacian_compact hg hcg))
    ((tfLaplacian_support hg).trans hs)
  exact (tfBallPotential_mul_integrable R f q).congr
    (hq.mono fun x hx => by simp only [hx])

end CoulombAnalysis

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RotationTrace
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

open CoulombAtom
variable {N : ℕ}

def particleRotation (R : Space ≃ₗᵢ[ℝ] Space) : Configuration N ≃L[ℝ] Configuration N :=
  ContinuousLinearEquiv.piCongrRight (fun _ => R.toContinuousLinearEquiv)

def flatRotation (R : Space ≃ₗᵢ[ℝ] Space) :
    ((Fin N × Fin 3) → ℝ) ≃L[ℝ] ((Fin N × Fin 3) → ℝ) :=
  ((configurationCoordinates N).symm.trans (particleRotation R)).trans (configurationCoordinates N)

@[simp] lemma flatRotation_apply (R : Space ≃ₗᵢ[ℝ] Space)
    (x : (Fin N × Fin 3) → ℝ) (q : Fin N × Fin 3) :
    flatRotation R x q = R (WithLp.toLp 2 (fun a => x (q.1,a))) q.2 := rfl

lemma particleRotation_preserving (R : Space ≃ₗᵢ[ℝ] Space) :
    MeasurePreserving (particleRotation (N := N) R) :=
  measurePreserving_pi (fun _ : Fin N => (volume : Measure Space))
    (fun _ => volume) (fun _ => R.measurePreserving)

lemma flatRotation_preserving (R : Space ≃ₗᵢ[ℝ] Space) :
    MeasurePreserving (flatRotation (N := N) R) :=
  (configurationCoordinates_preserving N).comp
    ((particleRotation_preserving R).comp (configurationCoordinates_symm_preserving N))

lemma flatRotation_anti {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (ha : FlatAntisymmetric f) (R : Space ≃ₗᵢ[ℝ] Space) :
    FlatAntisymmetric (fun s x => f s (flatRotation R x)) := by
  intro i j hij s x
  convert ha i j hij s (flatRotation R x) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

def flatInsertion (i : Fin N) : Space →L[ℝ] ((Fin N × Fin 3) → ℝ) :=
  (configurationCoordinates N).toContinuousLinearMap.comp (ContinuousLinearMap.single ℝ (fun _ : Fin N => Space) i)

lemma flatRotation_fderiv {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (R : Space ≃ₗᵢ[ℝ] Space) (x v : (Fin N × Fin 3) → ℝ) :
    fderiv ℝ (fun y => f (flatRotation R y)) x v =
      fderiv ℝ f (flatRotation R x) (flatRotation R v) := by
  have hh := (hf.differentiable (by simp) (flatRotation R x)).hasFDerivAt.comp x
    (flatRotation R).hasFDerivAt
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
    using congrArg (fun L : ((Fin N × Fin 3) → ℝ) →L[ℝ] ℂ => L v) hh.fderiv

lemma flatRotation_gradient_memLp {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hg : ∀ q, MemLp (fun x => fderiv ℝ f x (Pi.single q 1)) 2)
    (R : Space ≃ₗᵢ[ℝ] Space) (q : Fin N × Fin 3) :
    MemLp (fun x => fderiv ℝ (fun y => f (flatRotation R y)) x (Pi.single q 1)) 2 := by
  simp_rw [flatRotation_fderiv hf]
  exact (memLp_fderiv_apply hg _).comp_measurePreserving (flatRotation_preserving R)

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_PressureWeak
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

open CoulombAtom
variable {N : ℕ}

def rotatedGridPressure (b : ℝ) (t : Fin 3 → ℝ) (R : Space ≃ₗᵢ[ℝ] Space)
    (x : (Fin N × Fin 3) → ℝ) : ℝ :=
  gridPressure b t ((flatRotation R).symm x)

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_NewtonComparisonTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfPotential_radial_lower {ρ : Space → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5/3)) (hr : IsRadial ρ) (hn : ∀ y, 0 ≤ ρ y)
    (hm : ∫ y, ρ y = 1) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) (x : Space) :
    1/max ‖x‖ R ≤ tfPotential ρ x := by
  have hmajor : Integrable (fun y => ρ y/‖y‖) := by
    simpa only [zero_sub,norm_neg] using tfPotential_integrable h1 hp 0
  have hi : Integrable (fun y => ρ y/max ‖x‖ ‖y‖) := by
    apply hmajor.mono'
      (h1.aemeasurable.div ((continuous_const.max continuous_norm).aemeasurable)).aestronglyMeasurable
    filter_upwards [ae_ne_point (0 : Space)] with y hy
    change ‖ρ y/max ‖x‖ ‖y‖‖ ≤ ρ y/‖y‖
    rw [Real.norm_of_nonneg (div_nonneg (hn _) ((norm_nonneg x).trans (le_max_left _ _)))]
    exact div_le_div_of_nonneg_left (hn y) (norm_pos_iff.mpr hy) (le_max_right _ _)
  rw [tfPotential_radial_max h1 hp hr hR.le hs,←hm,←integral_div]
  apply integral_mono_ae (h1.div_const _) hi
  filter_upwards [ae_ne_point (0 : Space)] with y hy
  by_cases hz : ρ y = 0
  · simp [hz]
  · exact div_le_div_of_nonneg_left (hn y)
      ((norm_pos_iff.mpr hy).trans_le (le_max_right _ _)) (max_le_max_left _ (hs y hz))

def newtonComparisonTest (r R : ℝ) (x : Space) : ℝ :=
  tfPotential (packetDensity 0 r) x-tfPotential (packetDensity 0 R) x

lemma newtonComparisonTest_smooth {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    ContDiff ℝ 2 (newtonComparisonTest r R) :=
  (tfPotential_contDiff ((packetDensity_smooth 0 r).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (packetDensity_compact 0 hr)).sub
  (tfPotential_contDiff ((packetDensity_smooth 0 R).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (packetDensity_compact 0 hR))

lemma newtonComparisonTest_tsupport {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R) :
    tsupport (newtonComparisonTest r R) ⊆ closedBall 0 R := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hn
  have hxR : R ≤ ‖x‖ := (not_le.mp (by simpa only [mem_closedBall,dist_zero_right] using hn)).le
  apply hx
  simp only [newtonComparisonTest]
  rw [tfPotential_newton_exterior_closed (packetDensity_integrable 0 hr)
    (packetDensity_memLp 0 hr) (packetDensity_radial r) hr
    (fun y hy => by simpa only [sub_zero] using packetDensity_support 0 hr hy) (hrR.trans hxR),
    tfPotential_newton_exterior_closed (packetDensity_integrable 0 hR)
    (packetDensity_memLp 0 hR) (packetDensity_radial R) hR
    (fun y hy => by simpa only [sub_zero] using packetDensity_support 0 hR hy) hxR,
    packetDensity_mass 0 hr,packetDensity_mass 0 hR,sub_self]

lemma newtonComparisonTest_compact {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    HasCompactSupport (newtonComparisonTest r R) := by
  by_cases hh : r ≤ R
  · exact (isCompact_closedBall 0 R).of_isClosed_subset isClosed_closure
      (newtonComparisonTest_tsupport hr hR hh)
  · have ht : HasCompactSupport (newtonComparisonTest R r) := (isCompact_closedBall 0 r).of_isClosed_subset isClosed_closure
      (newtonComparisonTest_tsupport hR hr (le_of_not_ge hh))
    have he : newtonComparisonTest r R = -newtonComparisonTest R r := by
      funext x; simp only [newtonComparisonTest,Pi.neg_apply,neg_sub]
    rw [he]
    exact ht.neg

lemma newtonComparisonTest_laplacian {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    Δ (newtonComparisonTest r R) = fun x => 4*Real.pi*(packetDensity 0 R x-packetDensity 0 r x) := by
  funext x
  rw [show newtonComparisonTest r R = tfPotential (packetDensity 0 r)-tfPotential (packetDensity 0 R) from rfl,
    ((tfPotential_contDiff ((packetDensity_smooth 0 r).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
      (packetDensity_compact 0 hr)).contDiffAt).laplacian_sub
      ((tfPotential_contDiff ((packetDensity_smooth 0 R).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
      (packetDensity_compact 0 hR)).contDiffAt),
    tfPotential_poisson_global ((packetDensity_smooth 0 r).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
      (packetDensity_compact 0 hr) (packetDensity_radial r),
    tfPotential_poisson_global ((packetDensity_smooth 0 R).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
      (packetDensity_compact 0 hR) (packetDensity_radial R)]
  ring

lemma newtonComparisonTest_nonneg {r R M : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hrR : r ≤ R) (hM : ∀ x ∈ closedBall (0 : Space) R, tfPotential (packetDensity 0 R) x ≤ M)
    (hrM : M ≤ 1/r) (x : Space) : 0 ≤ newtonComparisonTest r R x := by
  apply sub_nonneg.mpr
  by_cases hx : ‖x‖ ≤ r
  · have hh := tfPotential_radial_lower (packetDensity_integrable 0 hr)
      (packetDensity_memLp 0 hr) (packetDensity_radial r) (packetDensity_nonneg 0 r)
      (packetDensity_mass 0 hr) hr
      (fun y hy => by simpa only [sub_zero] using packetDensity_support 0 hr hy) x
    rw [max_eq_right hx] at hh
    exact (hM x (by simpa only [mem_closedBall,dist_zero_right] using hx.trans hrR)).trans (hrM.trans hh)
  · have hx0 : x ≠ 0 := norm_pos_iff.mp (hr.trans (lt_of_not_ge hx))
    have hh := radial_potential_le_point (packetDensity_integrable 0 hR)
      (packetDensity_memLp 0 hR) (packetDensity_nonneg 0 R) (packetDensity_radial R)
      hR.le (fun y hy => by simpa only [sub_zero] using packetDensity_support 0 hR hy) hx0
    rw [packetDensity_mass 0 hR] at hh
    rw [tfPotential_newton_exterior_closed (packetDensity_integrable 0 hr)
      (packetDensity_memLp 0 hr) (packetDensity_radial r) hr
      (fun y hy => by simpa only [sub_zero] using packetDensity_support 0 hr hy) (le_of_not_ge hx),
      packetDensity_mass 0 hr]
    exact hh

def packetSecondMoment (r : ℝ) : ℝ := ∫ x : Space, ‖x‖^2*packetDensity 0 r x

lemma packetSecondMoment_nonneg (r : ℝ) : 0 ≤ packetSecondMoment r :=
  integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (packetDensity_nonneg 0 r x))

lemma packetSecondMoment_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : Space => ‖x‖^2*packetDensity 0 r x) :=
  ((continuous_norm.pow 2).mul (packetDensity_continuous 0 r)).integrable_of_hasCompactSupport
    (packetDensity_compact 0 hr).mul_left

lemma packetSecondMoment_le {r : ℝ} (hr : 0 < r) : packetSecondMoment r ≤ r^2 := by
  calc
    _ ≤ ∫ x : Space, r^2*packetDensity 0 r x := by
      apply integral_mono (packetSecondMoment_integrable hr) ((packetDensity_integrable 0 hr).const_mul _)
      intro x
      by_cases hx : packetDensity 0 r x = 0
      · simp [hx]
      · apply mul_le_mul_of_nonneg_right _ (packetDensity_nonneg 0 r x)
        exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [sub_zero] using packetDensity_support 0 hr hx) _
    _ = r^2 := by rw [integral_const_mul,packetDensity_mass 0 hr,mul_one]

lemma packetSecondMoment_pos {r : ℝ} (hr : 0 < r) : 0 < packetSecondMoment r := by
  by_contra hh
  have he := le_antisymm (le_of_not_gt hh) (packetSecondMoment_nonneg r)
  have hz := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun x => mul_nonneg (sq_nonneg ‖x‖) (packetDensity_nonneg 0 r x))
    (packetSecondMoment_integrable hr)).mp he
  have hd : packetDensity 0 r =ᵐ[volume] 0 := by
    filter_upwards [hz,ae_ne_point (0 : Space)] with x hx hn
    exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero _ (norm_ne_zero_iff.mpr hn))
  have hm := integral_congr_ae hd
  rw [packetDensity_mass 0 hr] at hm
  simp only [Pi.zero_apply,integral_zero] at hm
  norm_num at hm

lemma newtonComparisonTest_integral {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    6*(∫ x, newtonComparisonTest r R x) = 4*Real.pi*(packetSecondMoment R-packetSecondMoment r) := by
  have he := compact_laplacian_green (contDiff_norm_sq ℝ)
    (newtonComparisonTest_smooth hr hR) (newtonComparisonTest_compact hr hR)
  have hl : Δ (fun x : Space => ‖x‖^2) = fun _ => (6 : ℝ) := by
    funext x
    have h := CoulombPDE.laplacian_norm_sq x
    norm_num [Space,finrank_euclideanSpace_fin] at h
    exact h
  rw [hl,newtonComparisonTest_laplacian hr hR] at he
  simp only at he
  rw [←integral_const_mul,←he]
  calc
    _ = ∫ x : Space, 4*Real.pi*(‖x‖^2*packetDensity 0 R x-‖x‖^2*packetDensity 0 r x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by rw [integral_const_mul,integral_sub (packetSecondMoment_integrable hR)
      (packetSecondMoment_integrable hr)]; rfl

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

open CoulombAtom

lemma newtonComparisonTest_pairing {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {u : Space → ℝ} (hu : Continuous u) :
    (∫ x, u x*Δ (newtonComparisonTest r R) x) =
      4*Real.pi*((∫ x, packetDensity 0 R x*u x)-(∫ x, packetDensity 0 r x*u x)) := by
  have hi (a : ℝ) (ha : 0 < a) : Integrable (fun x => packetDensity 0 a x*u x) :=
    ((packetDensity_continuous 0 a).mul hu).integrable_of_hasCompactSupport
      (packetDensity_compact 0 ha).mul_right
  rw [newtonComparisonTest_laplacian hr hR]
  calc
    _ = ∫ x, 4*Real.pi*(packetDensity 0 R x*u x-packetDensity 0 r x*u x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => by ring
    _ = _ := by rw [integral_const_mul,integral_sub (hi R hR) (hi r hr)]

theorem weak_laplacian_no_positive_at_max {u : Space → ℝ} (hu : Continuous u)
    {S c : ℝ} (hS : 0 < S) (hc : 0 < c)
    (hmax : ∀ x ∈ ball (0 : Space) S, u x ≤ u 0)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 S → (∀ x, 0 ≤ g x) →
      c*(∫ x, g x) ≤ ∫ x, u x*Δ g x) : False := by
  let R := S/2
  have hR : 0 < R := half_pos hS
  have hRS : R < S := half_lt_self hS
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpot := tfPotential_continuous (packetDensity_integrable 0 hR) (packetDensity_memLp 0 hR)
  obtain ⟨z,hz,hMz⟩ := (isCompact_closedBall (0 : Space) R).exists_isMaxOn
    (show (closedBall (0 : Space) R).Nonempty from ⟨0,by simp [hR.le]⟩) hpot.continuousOn
  let M := tfPotential (packetDensity 0 R) z
  have hM0 : 0 ≤ M := tfPotential_nonneg (Eventually.of_forall (packetDensity_nonneg 0 R)) z
  have hev : ∀ᶠ n in atTop, c*(∫ x, newtonComparisonTest (r n) R x) ≤
      ∫ x, u x*Δ (newtonComparisonTest (r n) R) x := by
    filter_upwards [hr0.eventually (gt_mem_nhds hR),
      hr0.eventually (gt_mem_nhds (by positivity : 0 < 1/(M+1)))] with n hn hnM
    apply hw _ (newtonComparisonTest_smooth (hr n) hR) (newtonComparisonTest_compact (hr n) hR)
    · exact (newtonComparisonTest_tsupport (hr n) hR hn.le).trans
        (closedBall_subset_ball hRS)
    · apply newtonComparisonTest_nonneg (hr n) hR hn.le (fun x hx => hMz hx)
      apply (le_div_iff₀ (hr n)).mpr
      have hh := (lt_div_iff₀ (by positivity : 0 < M+1)).mp hnM
      nlinarith [hr n]
  have hm0 : Tendsto (fun n => packetSecondMoment (r n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => packetSecondMoment_nonneg (r n))
      (fun n => packetSecondMoment_le (hr n))
    convert hr0.pow 2 using 1; norm_num
  have hgint : Tendsto (fun n => ∫ x, newtonComparisonTest (r n) R x) atTop
      (𝓝 ((4*Real.pi/6)*packetSecondMoment R)) := by
    have hh := (((tendsto_const_nhds (x := packetSecondMoment R)).sub hm0).const_mul (4*Real.pi/6))
    simp only [sub_zero] at hh
    apply hh.congr
    intro n
    have he := newtonComparisonTest_integral (hr n) hR
    linarith
  have hravg : Tendsto (fun n => ∫ x, packetDensity 0 (r n) x*u x) atTop (𝓝 (u 0)) :=
    shrinking_density_test_limit (fun n => packetDensity_continuous 0 (r n))
      (fun n => packetDensity_compact 0 (hr n)) (fun n => packetDensity_nonneg 0 (r n))
      (fun n => packetDensity_mass 0 (hr n))
      (fun n x hx => by simpa only [sub_zero] using packetDensity_support 0 (hr n) hx) hr0 hu
  have hgpair : Tendsto (fun n => ∫ x, u x*Δ (newtonComparisonTest (r n) R) x) atTop
      (𝓝 (4*Real.pi*((∫ x, packetDensity 0 R x*u x)-u 0))) := by
    have hh := ((tendsto_const_nhds (x := ∫ x, packetDensity 0 R x*u x)).sub hravg).const_mul (4*Real.pi)
    exact hh.congr (fun n => (newtonComparisonTest_pairing (hr n) hR hu).symm)
  have havg : (∫ x, packetDensity 0 R x*u x) ≤ u 0 := by
    calc
      _ ≤ ∫ x, packetDensity 0 R x*u 0 := by
        apply integral_mono
          (((packetDensity_continuous 0 R).mul hu).integrable_of_hasCompactSupport
            (packetDensity_compact 0 hR).mul_right)
          ((packetDensity_integrable 0 hR).mul_const _)
        intro x
        by_cases hx : packetDensity 0 R x = 0
        · simp [hx]
        · apply mul_le_mul_of_nonneg_left (hmax x _) (packetDensity_nonneg 0 R x)
          have hn := packetDensity_support 0 hR hx
          simpa only [mem_ball,dist_zero_right] using
            (show ‖x‖ < S from (by simpa only [sub_zero] using hn : ‖x‖ ≤ R).trans_lt hRS)
      _ = u 0 := by rw [integral_mul_const,packetDensity_mass 0 hR,one_mul]
  have hle := le_of_tendsto_of_tendsto (hgint.const_mul c) hgpair hev
  have hp : 0 < c*((4*Real.pi/6)*packetSecondMoment R) :=
    mul_pos hc (mul_pos (by positivity) (packetSecondMoment_pos hR))
  have hn : 4*Real.pi*((∫ x, packetDensity 0 R x*u x)-u 0) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr havg)
  exact (not_le_of_gt hp) (hle.trans hn)

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

open CoulombAtom

lemma tsupport_translate_subset {g : Space → ℝ} (y : Space) :
    tsupport (fun z => g (-y+z)) ⊆ (fun z => -y+z) ⁻¹' tsupport g := by
  apply closure_minimal _ (isClosed_closure.preimage (continuous_const.add continuous_id))
  intro z hz
  exact subset_tsupport g hz

lemma weak_laplacian_no_positive_at_max_center {u : Space → ℝ} (hu : Continuous u)
    {y : Space} {S c : ℝ} (hS : 0 < S) (hc : 0 < c)
    (hmax : ∀ x ∈ ball y S, u x ≤ u y)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball y S → (∀ x, 0 ≤ g x) →
      c*(∫ x, g x) ≤ ∫ x, u x*Δ g x) : False := by
  apply weak_laplacian_no_positive_at_max (u := fun x => u (y+x))
    (hu.comp (continuous_const.add continuous_id)) hS hc
  · intro x hx
    simpa only [add_zero] using hmax (y+x) (by
      simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hx)
  · intro g hg hcg hs hn
    let G : Space → ℝ := fun z => g (-y+z)
    have hG : ContDiff ℝ 2 G := hg.comp (contDiff_const.add contDiff_id)
    have hcG : HasCompactSupport G := hcg.comp_homeomorph (Homeomorph.addLeft (-y))
    have hsG : tsupport G ⊆ ball y S := by
      intro z hz
      have hh := hs (tsupport_translate_subset y hz)
      simpa only [mem_ball,dist_eq_norm,sub_zero,neg_add_eq_sub] using hh
    have hh := hw G hG hcG hsG (fun _ => hn _)
    have hi : (∫ x, G x) = ∫ x, g x := integral_add_left_eq_self (μ := volume) g (-y)
    rw [hi,tfLaplacian_translate g (-y)] at hh
    have hj := integral_add_left_eq_self (μ := volume) (fun z => u z*Δ g (-y+z)) y
    simpa only [neg_add_cancel_left] using hh.trans_eq hj.symm

theorem weak_laplacian_no_positive_at_max_local {u : Space → ℝ}
    {y : Space} {S c : ℝ} (hu : ContinuousOn u (closedBall y S))
    (hS : 0 < S) (hc : 0 < c)
    (hmax : ∀ x ∈ ball y S, u x ≤ u y)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball y S → (∀ x, 0 ≤ g x) →
      c*(∫ x, g x) ≤ ∫ x, u x*Δ g x) : False := by
  let f : C(closedBall y S,ℝ) := ⟨_,hu.domRestrict⟩
  obtain ⟨v,hv⟩ := f.exists_restrict_eq isClosed_closedBall
  have he (z : Space) (hz : z ∈ closedBall y S) : v z = u z :=
    congrArg (fun h : C(closedBall y S,ℝ) => h ⟨z,hz⟩) hv
  apply weak_laplacian_no_positive_at_max_center v.continuous hS hc
  · intro z hz
    rw [he z (ball_subset_closedBall hz),he y (mem_closedBall_self hS.le)]
    exact hmax z hz
  · intro g hg hcg hs hn
    convert hw g hg hcg hs hn using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : Δ g z = 0
      · simp only [hz,mul_zero]
      · change v z * Δ g z = u z * Δ g z
        rw [he z (ball_subset_closedBall (hs (tfLaplacian_support hg hz)))]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_WeakHarmonicMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

lemma weak_harmonic_packet_mean_zero {u : Space → ℝ} (hu : Continuous u)
    {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 S → (∫ x, u x*Δ g x) = 0) :
    (∫ x, packetDensity 0 R x*u x) = u 0 := by
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have havg : Tendsto (fun n => ∫ x, packetDensity 0 (r n) x*u x) atTop (𝓝 (u 0)) :=
    shrinking_density_test_limit (fun n => packetDensity_continuous 0 (r n))
      (fun n => packetDensity_compact 0 (hr n)) (fun n => packetDensity_nonneg 0 (r n))
      (fun n => packetDensity_mass 0 (hr n))
      (fun n x hx => by simpa only [sub_zero] using packetDensity_support 0 (hr n) hx) hr0 hu
  have he : ∀ᶠ n in atTop, (∫ x, packetDensity 0 (r n) x*u x) = ∫ x, packetDensity 0 R x*u x := by
    filter_upwards [hr0.eventually (gt_mem_nhds hR)] with n hn
    have hh := hw (newtonComparisonTest (r n) R) (newtonComparisonTest_smooth (hr n) hR)
      (newtonComparisonTest_compact (hr n) hR)
      ((newtonComparisonTest_tsupport (hr n) hR hn.le).trans (closedBall_subset_ball hRS))
    rw [newtonComparisonTest_pairing (hr n) hR hu] at hh
    have hp := Real.pi_pos
    nlinarith
  exact (tendsto_nhds_unique (havg.congr' he) tendsto_const_nhds).symm

lemma weak_harmonic_packet_mean {u : Space → ℝ} (hu : Continuous u)
    (y : Space) {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball y S → (∫ x, u x*Δ g x) = 0) :
    (∫ x, packetDensity y R x*u x) = u y := by
  have hh := weak_harmonic_packet_mean_zero (u := fun x => u (y+x))
    (hu.comp (continuous_const.add continuous_id)) hR hRS (fun g hg hcg hs => ?_)
  · have hm : (∫ x, packetDensity y R x*u x) = ∫ x, packetDensity 0 R x*u (y+x) := by
      have he := integral_add_left_eq_self (μ := volume) (fun x => packetDensity y R x*u x) y
      simpa only [packetDensity_formula,add_sub_cancel_left,sub_zero] using he.symm
    simpa only [add_zero] using hm.trans hh
  · let G : Space → ℝ := fun z => g (-y+z)
    have hG : ContDiff ℝ 2 G := hg.comp (contDiff_const.add contDiff_id)
    have hcG : HasCompactSupport G := hcg.comp_homeomorph (Homeomorph.addLeft (-y))
    have hsG : tsupport G ⊆ ball y S := by
      intro z hz
      have ht := hs (tsupport_translate_subset y hz)
      simpa only [mem_ball,dist_eq_norm,sub_zero,neg_add_eq_sub] using ht
    have ht := hw G hG hcG hsG
    rw [tfLaplacian_translate g (-y)] at ht
    have hj := integral_add_left_eq_self (μ := volume) (fun z => u z*Δ g (-y+z)) y
    simpa only [neg_add_cancel_left] using hj.trans ht

theorem weak_harmonic_packet_mean_local {u : Space → ℝ} {y : Space} {R S : ℝ}
    (hu : ContinuousOn u (closedBall y S)) (hR : 0 < R) (hRS : R < S)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball y S → (∫ x, u x*Δ g x) = 0) :
    (∫ x, packetDensity y R x*u x) = u y := by
  let f : C(closedBall y S,ℝ) := ⟨_,hu.domRestrict⟩
  obtain ⟨v,hv⟩ := f.exists_restrict_eq isClosed_closedBall
  have he (z : Space) (hz : z ∈ closedBall y S) : v z = u z :=
    congrArg (fun h : C(closedBall y S,ℝ) => h ⟨z,hz⟩) hv
  have hm := weak_harmonic_packet_mean v.continuous y hR hRS (fun g hg hcg hs => ?_)
  · rw [he y (mem_closedBall_self (hR.trans hRS).le)] at hm
    refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans hm
    by_cases hx : packetDensity y R x = 0
    · simp only [hx,zero_mul]
    · rw [he x ((closedBall_subset_closedBall hRS.le) ((mem_closedBall).mpr (packetDensity_support y hR hx)))]
  · convert hw g hg hcg hs using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : Δ g z = 0
      · simp only [hz,mul_zero]
      · change v z*Δ g z = u z*Δ g z
        rw [he z (ball_subset_closedBall (hs (tfLaplacian_support hg hz)))]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketScaleControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff Topology

namespace CoulombAtom

lemma configurationOne_finrank : Module.finrank ℝ (Configuration 1) = 3 := by
  change Module.finrank ℝ (Fin 1 → Space) = 3
  rw [Module.finrank_pi_fintype]
  simp only [Space,finrank_euclideanSpace_fin,Fin.sum_univ_one]

lemma packetDensity_scale (y x : Space) {r : ℝ} (hr : 0 < r) :
    packetDensity y r x = r⁻¹^3 * packetDensity 0 1 (r⁻¹ • (x-y)) := by
  rw [packetDensity_formula,packetDensity_formula,inv_pow,inv_pow,inv_pow,
    Real.sq_sqrt (radialScaledRaw_mass_pos hr).le,
    Real.sq_sqrt (radialScaledRaw_mass_pos (by norm_num : (0:ℝ)<1)).le,
    radialScaledRaw_mass r hr,radialScaledRaw_mass 1 (by norm_num),configurationOne_finrank]
  simp only [sub_zero,inv_one,one_smul,one_pow,one_mul,mul_inv_rev]
  ring

lemma packetDensity_unit_pos {x : Space} (hx : ‖x‖ < 1) : 0 < packetDensity 0 1 x := by
  rw [packetDensity_formula]
  have hn : 0 < ‖radialPacketBase x‖ := by
    rw [radialPacketBase,Complex.norm_real,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    apply Real.smoothTransition.pos_of_pos
    nlinarith [norm_nonneg x]
  simp only [inv_one,sub_zero,one_smul]
  exact mul_pos (mul_pos (Nat.cast_pos.mpr Fintype.card_pos)
    (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (radialScaledRaw_mass_pos (by norm_num)))) _))
    (pow_pos hn _)

lemma exists_packet_unit_control : ∃ (L : NNReal) (p : ℝ), 0 < p ∧
    LipschitzWith L (packetDensity 0 1) ∧
    ∀ x : Space, ‖x‖ ≤ 3/4 → p ≤ packetDensity 0 1 x := by
  obtain ⟨L,hL⟩ := (packetDensity_smooth 0 1).lipschitzWith_of_hasCompactSupport
    (packetDensity_compact 0 (by norm_num)) (by simp)
  obtain ⟨z,hz,hmin⟩ := (isCompact_closedBall (0 : Space) (3/4 : ℝ)).exists_isMinOn
    (show (closedBall (0 : Space) (3/4 : ℝ)).Nonempty from ⟨0,by norm_num⟩)
    (packetDensity_continuous 0 1).continuousOn
  refine ⟨L,packetDensity 0 1 z,packetDensity_unit_pos ?_,hL,?_⟩
  · have hh : ‖z‖ ≤ (3/4 : ℝ) := by simpa only [mem_closedBall,dist_zero_right] using hz
    linarith
  · intro x hx
    exact hmin (by simpa only [mem_closedBall,dist_zero_right] using hx)

lemma packetDensity_scaled_difference {L : NNReal} (hL : LipschitzWith L (packetDensity 0 1))
    {r : ℝ} (hr : 0 < r) (x y z : Space) :
    |packetDensity x r z-packetDensity y r z| ≤ (L:ℝ)/r^4*‖x-y‖ := by
  rw [packetDensity_scale x z hr,packetDensity_scale y z hr,←mul_sub,abs_mul,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) _)]
  have hh := hL.dist_le_mul (r⁻¹ • (z-x)) (r⁻¹ • (z-y))
  rw [Real.dist_eq,dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),
    show z-x-(z-y)=y-x by abel,norm_sub_rev] at hh
  calc
    _ ≤ r⁻¹^3*((L:ℝ)*(r⁻¹*‖x-y‖)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

lemma packetDensity_scaled_lower {p r : ℝ} (hr : 0 < r)
    (hp : ∀ z : Space, ‖z‖ ≤ 3/4 → p ≤ packetDensity 0 1 z)
    {z : Space} (hz : ‖z‖ ≤ 3*r/4) : p/r^3 ≤ packetDensity 0 r z := by
  rw [packetDensity_scale 0 z hr,sub_zero]
  have hn : ‖r⁻¹ • z‖ ≤ (3/4:ℝ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),inv_mul_le_iff₀ hr]
    linarith
  have hh := mul_le_mul_of_nonneg_left (hp (r⁻¹ • z) hn) (pow_nonneg (inv_nonneg.mpr hr.le) 3)
  simpa only [div_eq_mul_inv,inv_pow,mul_comm] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_WeakHarmonicOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

lemma weak_harmonic_packet_oscillation {u : Space → ℝ} (hu : Continuous u)
    {R : ℝ} (hR : 0 < R) (hn : ∀ z ∈ closedBall (0 : Space) (3*R), 0 ≤ u z)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 (3*R) → (∫ z, u z*Δ g z) = 0)
    {L : NNReal} {p : ℝ} (hp : 0 < p) (hL : LipschitzWith L (packetDensity 0 1))
    (hlo : ∀ z : Space, ‖z‖ ≤ 3/4 → p ≤ packetDensity 0 1 z)
    (x : Space) (hx : ‖x‖ ≤ R/2) :
    |u x-u 0| ≤ (8*(L:ℝ)/p)/R*‖x‖*u 0 := by
  have hm0 := weak_harmonic_packet_mean hu 0 hR (by linarith : R < 3*R) hw
  have hmb := weak_harmonic_packet_mean hu 0 (by linarith : 0 < 2*R)
    (by linarith : 2*R < 3*R) hw
  have hmx := weak_harmonic_packet_mean hu x hR (by linarith : R < 2*R)
    (fun g hg hcg hs => hw g hg hcg (fun z hz => ?_))
  · let D : ℝ := (8*(L:ℝ)/p)/R*‖x‖
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hi (y : Space) {r : ℝ} (hr : 0 < r) : Integrable (fun z => packetDensity y r z*u z) :=
      ((packetDensity_continuous y r).mul hu).integrable_of_hasCompactSupport
        (packetDensity_compact y hr).mul_right
    have hid : Integrable (fun z => (packetDensity x R z-packetDensity 0 R z)*u z) := by
      convert! (hi x hR).sub (hi 0 hR) using 1
      all_goals try with_reducible_and_instances rfl
      ext z
      change (packetDensity x R z-packetDensity 0 R z)*u z =
        packetDensity x R z*u z-packetDensity 0 R z*u z
      ring
    have hbn (z : Space) : 0 ≤ packetDensity 0 (2*R) z*u z := by
      by_cases hz : packetDensity 0 (2*R) z = 0
      · simp [hz]
      · apply mul_nonneg (packetDensity_nonneg _ _ _) (hn z _)
        have ht := packetDensity_support 0 (by linarith : 0 < 2*R) hz
        rw [sub_zero] at ht
        simpa only [mem_closedBall,dist_zero_right] using ht.trans (by linarith : 2*R ≤ 3*R)
    have hb (z : Space) : |(packetDensity x R z-packetDensity 0 R z)*u z| ≤
        D*(packetDensity 0 (2*R) z*u z) := by
      by_cases hd : packetDensity x R z-packetDensity 0 R z = 0
      · simpa only [hd,zero_mul,abs_zero] using mul_nonneg hD (hbn z)
      · have hz : ‖z‖ ≤ 3*R/2 := by
          by_cases ha : packetDensity x R z = 0
          · have hb : packetDensity 0 R z ≠ 0 := by intro hb; simp [ha,hb] at hd
            have ht := packetDensity_support 0 hR hb
            rw [sub_zero] at ht
            linarith
          · have ht := packetDensity_support x hR ha
            have hh : ‖z‖ ≤ ‖z-x‖+‖x‖ := by
              calc ‖z‖ = ‖(z-x)+x‖ := by rw [sub_add_cancel]
                   _ ≤ ‖z-x‖+‖x‖ := norm_add_le _ _
            linarith
        have huz : 0 ≤ u z := hn z (by
          simpa only [mem_closedBall,dist_zero_right] using hz.trans (by linarith : 3*R/2 ≤ 3*R))
        have hpl := packetDensity_scaled_lower (by linarith : 0 < 2*R) hlo
          (z := z) (by linarith)
        have hdf := packetDensity_scaled_difference hL hR x 0 z
        rw [sub_zero] at hdf
        have he : D*(p/(2*R)^3) = (L:ℝ)/R^4*‖x‖ := by
          dsimp [D]
          field_simp
          ring
        rw [abs_mul,abs_of_nonneg huz,←mul_assoc]
        apply mul_le_mul_of_nonneg_right _ huz
        calc
          _ ≤ (L:ℝ)/R^4*‖x‖ := hdf
          _ = D*(p/(2*R)^3) := he.symm
          _ ≤ D*packetDensity 0 (2*R) z := mul_le_mul_of_nonneg_left hpl hD
    calc
      |u x-u 0| = |∫ z, (packetDensity x R z-packetDensity 0 R z)*u z| := by
        simp only [sub_mul,integral_sub (hi x hR) (hi 0 hR),hmx,hm0]
      _ ≤ ∫ z, |(packetDensity x R z-packetDensity 0 R z)*u z| := abs_integral_le_integral_abs
      _ ≤ ∫ z, D*(packetDensity 0 (2*R) z*u z) :=
        integral_mono hid.abs ((hi 0 (by linarith : 0 < 2*R)).const_mul D) hb
      _ = D*u 0 := by rw [integral_const_mul,hmb]
  · have ht : ‖z-x‖ < 2*R := by simpa only [mem_ball,dist_eq_norm] using hs hz
    have hh : ‖z‖ ≤ ‖z-x‖+‖x‖ := by
      calc ‖z‖ = ‖(z-x)+x‖ := by rw [sub_add_cancel]
           _ ≤ ‖z-x‖+‖x‖ := norm_add_le _ _
    simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < 3*R by linarith)

theorem exists_weak_harmonic_oscillation_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (u : Space → ℝ) (R : ℝ), 0 < R → ContinuousOn u (closedBall 0 (3*R)) →
      (∀ z ∈ closedBall (0 : Space) (3*R), 0 ≤ u z) →
      (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball 0 (3*R) → (∫ z, u z*Δ g z) = 0) →
      ∀ x : Space, ‖x‖ ≤ R/2 → |u x-u 0| ≤ C/R*‖x‖*u 0 := by
  obtain ⟨L,p,hp,hL,hlo⟩ := exists_packet_unit_control
  let C : ℝ := 8*(L:ℝ)/p+1
  have hbase : 0 ≤ 8*(L:ℝ)/p := by positivity
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro u R hR hu hn hw x hx
  let f : C(closedBall (0 : Space) (3*R),ℝ) := ⟨_,hu.domRestrict⟩
  obtain ⟨v,hv⟩ := f.exists_restrict_eq isClosed_closedBall
  have he (z : Space) (hz : z ∈ closedBall (0 : Space) (3*R)) : v z = u z :=
    congrArg (fun h : C(closedBall (0 : Space) (3*R),ℝ) => h ⟨z,hz⟩) hv
  have hh := weak_harmonic_packet_oscillation v.continuous hR
    (fun z hz => by rw [he z hz]; exact hn z hz) (fun g hg hcg hs => ?_) hp hL hlo x hx
  · rw [he x (by simpa only [mem_closedBall,dist_zero_right] using hx.trans (by linarith : R/2 ≤ 3*R)),
      he 0 (mem_closedBall_self (by positivity))] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (hn 0 (mem_closedBall_self (by positivity)))
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply div_le_div_of_nonneg_right _ hR.le
    dsimp [C]; linarith
  · convert hw g hg hcg hs using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : Δ g z = 0
      · simp only [hz,mul_zero]
      · change v z*Δ g z = u z*Δ g z
        rw [he z (ball_subset_closedBall (hs (tfLaplacian_support hg hz)))]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

lemma continuousOn_mul_integrable_support {K : Set Space} (hK : IsCompact K)
    {f g : Space → ℝ} (hf : ContinuousOn f K) (hg : Continuous g)
    (hs : Function.support g ⊆ K) : Integrable (fun x => f x*g x) := by
  apply (integrableOn_iff_integrable_of_support_subset (s := K) ?_).mp
    ((hf.mul hg.continuousOn).integrableOn_compact hK)
  intro x hx
  exact hs ((mul_ne_zero_iff.mp hx).2)

theorem weak_strict_source_comparison {K : Set Space} (hK : IsCompact K)
    {u F : Space → ℝ} (hu : ContinuousOn u K) (hF : ContinuousOn F K)
    (hpos : ∀ x ∈ interior K, 0 < u x → 0 < F x)
    (hb : ∀ x ∈ K, x ∉ interior K → u x ≤ 0)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ interior K → (∀ x, 0 ≤ g x) →
      (∫ x, F x*g x) ≤ ∫ x, u x*Δ g x) : ∀ x ∈ K, u x ≤ 0 := by
  intro x hx
  by_contra! hux
  obtain ⟨y,hy,hmax⟩ := hK.exists_isMaxOn ⟨x,hx⟩ hu
  have huy : 0 < u y := hux.trans_le (hmax hx)
  have hyi : y ∈ interior K := by
    by_contra hn
    exact (not_lt_of_ge (hb y hy hn)) huy
  let c := F y/2
  have hc : 0 < c := half_pos (hpos y hyi huy)
  have hcf : c < F y := half_lt_self (hpos y hyi huy)
  have hnb : {z | c < F z} ∩ interior K ∈ 𝓝 y :=
    inter_mem ((hF.continuousAt (mem_interior_iff_mem_nhds.mp hyi)).preimage_mem_nhds
      (Ioi_mem_nhds hcf)) (isOpen_interior.mem_nhds hyi)
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hnb
  have hbsub : closedBall y (r/2) ⊆ ball y r := closedBall_subset_ball (half_lt_self hr)
  have hsub : closedBall y (r/2) ⊆ K := fun z hz => interior_subset (hrs (hbsub hz)).2
  apply weak_laplacian_no_positive_at_max_local (hu.mono hsub) (half_pos hr) hc
  · intro z hz
    exact hmax (hsub (ball_subset_closedBall hz))
  · intro g hg hcg hs hn
    have hsi : tsupport g ⊆ interior K := fun z hz =>
      (hrs (hbsub (ball_subset_closedBall (hs hz)))).2
    have hiF := continuousOn_mul_integrable_support hK hF hg.continuous
      ((subset_tsupport g).trans (hsi.trans interior_subset))
    calc
      c*(∫ z, g z) = ∫ z, c*g z := (integral_const_mul c g).symm
      _ ≤ ∫ z, F z*g z := by
        apply integral_mono ((hg.continuous.integrable_of_hasCompactSupport hcg).const_mul c) hiF
        intro z
        by_cases hz : g z = 0
        · simp only [hz,mul_zero,le_refl]
        · exact mul_le_mul_of_nonneg_right
            ((hrs (hbsub (ball_subset_closedBall (hs (subset_tsupport g hz))))).1.le) (hn z)
      _ ≤ _ := hw g hg hcg hsi hn

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_WeakPositiveComparisonBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WeakPositiveComparison_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

open CoulombAtom

lemma norm_sq_weak_laplacian {g : Space → ℝ} (hg : ContDiff ℝ 2 g)
    (hcg : HasCompactSupport g) :
    (∫ x, ‖x‖^2*Δ g x) = 6*(∫ x, g x) := by
  have he := compact_laplacian_green (contDiff_norm_sq ℝ) hg hcg
  have hl : Δ (fun x : Space => ‖x‖^2) = fun _ => (6 : ℝ) := by
    funext x
    have h := CoulombPDE.laplacian_norm_sq x
    norm_num [Space,finrank_euclideanSpace_fin] at h
    exact h
  rw [hl,integral_const_mul] at he
  exact he

lemma quadratic_weak_pairing {u : Space → ℝ} {R e : ℝ}
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hui : Integrable (fun x => u x*Δ g x)) :
    (∫ x, (u x+e*(‖x‖^2-R^2))*Δ g x) =
      (∫ x, u x*Δ g x)+6*e*(∫ x, g x) := by
  have hli : Integrable (Δ g) := (tfLaplacian_continuous hg).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg)
  have hqi : Integrable (fun x : Space => ‖x‖^2*Δ g x) := ((continuous_norm.pow 2).mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport
    (tfLaplacian_compact hg hcg).mul_left
  have hei : Integrable (fun x : Space => e*(‖x‖^2*Δ g x-R^2*Δ g x)) :=
    (hqi.sub (hli.const_mul (R^2))).const_mul e
  have hsum := integral_add hui hei
  have hsub := integral_sub hqi (hli.const_mul (R^2))
  calc
    _ = ∫ x, u x*Δ g x+e*(‖x‖^2*Δ g x-R^2*Δ g x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by
      rw [hsum,
        integral_const_mul,hsub,integral_const_mul,
        compact_laplacian_mass hg hcg,norm_sq_weak_laplacian hg hcg]
      ring

end Work_WeakPositiveComparison_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom

theorem weak_subharmonic_positive_compact {K : Set Space} (hK : IsCompact K)
    {u : Space → ℝ} (hu : ContinuousOn u K)
    (hb : ∀ x ∈ K, x ∉ interior K → u x ≤ 0)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ interior K ∩ {x | 0 < u x} → (∀ x, 0 ≤ g x) →
      0 ≤ ∫ x, u x*Δ g x) : ∀ x ∈ K, u x ≤ 0 := by
  intro x hx
  by_contra! hux
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  let R := max M 1
  have hn (z : Space) (hz : z ∈ K) : ‖z‖ ≤ R := by
    have ht := hM z hz
    rw [Real.norm_of_nonneg (norm_nonneg z)] at ht
    exact ht.trans (le_max_left _ _)
  let e := u x/(2*(R^2+1))
  have he : 0 < e := div_pos hux (by positivity)
  have heq : e*(2*(R^2+1)) = u x := div_mul_cancel₀ _ (by positivity)
  let w : Space → ℝ := fun z => u z+e*(‖z‖^2-R^2)
  have hwcont : ContinuousOn w K :=
    hu.add (continuousOn_const.mul ((continuous_norm.pow 2).continuousOn.sub continuousOn_const))
  have hwx : 0 < w x := by
    dsimp only [w]
    nlinarith [sq_nonneg ‖x‖,mul_nonneg he.le (sq_nonneg ‖x‖),sq_nonneg R]
  obtain ⟨y,hy,hmax⟩ := hK.exists_isMaxOn ⟨x,hx⟩ hwcont
  have hwy : 0 < w y := hwx.trans_le (hmax hx)
  have hpert : e*(‖y‖^2-R^2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos he.le
      (sub_nonpos.mpr (pow_le_pow_left₀ (norm_nonneg y) (hn y hy) 2))
  have huy : 0 < u y := by dsimp only [w] at hwy; linarith
  have hyi : y ∈ interior K := by
    by_contra hh
    exact (not_lt_of_ge (hb y hy hh)) huy
  have hnb : interior K ∩ {z | 0 < u z} ∈ 𝓝 y :=
    inter_mem (isOpen_interior.mem_nhds hyi)
      ((hu.continuousAt (mem_interior_iff_mem_nhds.mp hyi)).preimage_mem_nhds (Ioi_mem_nhds huy))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hnb
  have hsub : closedBall y (r/2) ⊆ interior K ∩ {z | 0 < u z} :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrs
  apply weak_laplacian_no_positive_at_max_local
    (hwcont.mono (hsub.trans (inter_subset_left.trans interior_subset)))
    (half_pos hr) (mul_pos (by norm_num : (0:ℝ) < 6) he)
  · intro z hz
    exact hmax (interior_subset (hsub (ball_subset_closedBall hz)).1)
  · intro g hg hcg hs hgn
    have hs' : tsupport g ⊆ interior K ∩ {z | 0 < u z} :=
      hs.trans (ball_subset_closedBall.trans hsub)
    have hui := continuousOn_mul_integrable_support hK hu (tfLaplacian_continuous hg)
      ((tfLaplacian_support hg).trans (hs'.trans (inter_subset_left.trans interior_subset)))
    change 6*e*(∫ z, g z) ≤ ∫ z, (u z+e*(‖z‖^2-R^2))*Δ g z
    rw [quadratic_weak_pairing hg hcg hui]
    linarith only [hw g hg hcg hs' hgn]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_PhysicalGrid
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators unitInterval ContDiff

namespace CoulombAtom
open CoulombNeumann
variable {N : ℕ}

def formDensity (ψ : FormVector N) (x : Configuration N) : ℝ := ∑ s, ‖ψ.value s x‖^2
lemma SobolevFermion.formDensity_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ) :
    Integrable (formDensity ψ) := integrable_finsetSum _ (fun s _ => (hψ.1 s).norm.integrable_sq)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfIncreasingData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
namespace CoulombAnalysis
open CoulombAtom

def tfFluxSource (r : ℝ) : ℝ := r^2 * CoulombPDE.reaction tfReactionCoefficient (tfInfiniteRadial r)
def tfFiniteSource (n : ℕ) (r : ℝ) : ℝ := r^2 * CoulombPDE.reaction tfReactionCoefficient (tfIncreasingField n r)

lemma tfChargeAnchor_nonempty : Nonempty TFChargeAnchor := by
  obtain ⟨q, _, κ, hk, hl⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) (TFUnitData.chargeCap 1))).tendsto_subseq
    (fun n => ⟨(tfIncreasingData n).charge_nonneg (by positivity) 1,
      (tfIncreasingData n).charge_le_cap (by positivity) zero_lt_one le_rfl⟩)
  exact ⟨⟨q, κ, hk, hl⟩⟩

def tfChargeAnchor : TFChargeAnchor := Classical.choice tfChargeAnchor_nonempty
def tfInfiniteCharge (r : ℝ) : ℝ := tfChargeAnchor.charge - ∫ t in (1:ℝ)..r, tfFluxSource t

def tfInfiniteSlope (r : ℝ) : ℝ := -tfInfiniteCharge r / r^2
def tfFiniteSlope (n : ℕ) (r : ℝ) : ℝ := -tfIncreasingCharge n r / r^2

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfInfiniteField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
namespace CoulombAnalysis

def tfInfiniteField (x : TFSpace) : ℝ := tfInfiniteRadial ‖x‖

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfInfiniteFieldDominatesDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian


open MeasureTheory Filter Set Metric Topology
section
open CoulombAtom

def tfRealRadial (Z r : ℝ) : ℝ := if hZ : 0 < Z then (tfUnitData Z hZ).radialField r else 0
def tfUnitDeficit (Z : ℝ) : ℝ := if hZ : 0 < Z then Z-(tfUnitData Z hZ).mass else 0

end

open MeasureTheory Filter Set Metric Topology

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_TFPriceData
attribute [-instance] _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
namespace CoulombAnalysis
open CoulombAtom

def tfPriceData {Z μ : ℝ} (hZ : 0 < Z) (hμ : 0 < μ) : TFPriceData Z μ := by
  let b := tfPriceLength μ
  have hb : 0 < b := tfPriceLength_pos hμ
  have hW : 0 < Z/b^3 := div_pos hZ (pow_pos hb _)
  let D := tfUnitData (Z/b^3) hW
  let S := D.scale hW hb
  refine ⟨b^3*D.mass, tfDilation b D.density, S.admissible, ?_, S.nonneg, S.compact⟩
  intro M σ hσ
  have hh := S.minimal M σ hσ
  change tfFunctional (b^3*(Z/b^3)) (tfDilation b D.density) + b^4*(b^3*D.mass) ≤
    tfFunctional (b^3*(Z/b^3)) σ + b^4*M at hh
  rwa [mul_div_cancel₀ _ (pow_pos hb 3).ne', tfPriceLength_four hμ] at hh

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_LipschitzMollifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LipschitzMollifier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff Topology Convolution NNReal

lemma normalized_convolution_integrable {η g : TFSpace → ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η) (hg : Continuous g) (x : TFSpace) :
    Integrable (fun z => η z*g (x-z)) :=
  (hη.mul (hg.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport hcη.mul_right

lemma normalized_convolution_lipschitz {η g : TFSpace → ℝ} {L : ℝ≥0}
    (hη : Continuous η) (hcη : HasCompactSupport η)
    (hnη : ∀ x, 0 ≤ η x) (hmη : ∫ x, η x = 1) (hg : LipschitzWith L g) :
    LipschitzWith L (η ⋆[newtonMul] g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hi : Integrable η := hη.integrable_of_hasCompactSupport hcη
  have he : (η ⋆[newtonMul] g) x-(η ⋆[newtonMul] g) y =
      ∫ z, η z*(g (x-z)-g (y-z)) := by
    simp only [convolution,newtonMul,ContinuousLinearMap.mul_apply',mul_sub]
    rw [integral_sub (normalized_convolution_integrable hη hcη hg.continuous x)
      (normalized_convolution_integrable hη hcη hg.continuous y)]
  rw [dist_eq_norm,he]
  calc
    _ ≤ ∫ z, ((L:ℝ)*dist x y)*η z := norm_integral_le_of_norm_le
      (hi.const_mul _) (Eventually.of_forall fun z => by
        rw [norm_mul,Real.norm_of_nonneg (hnη z)]
        have hh := hg.dist_le_mul (x-z) (y-z)
        rw [dist_sub_right,dist_eq_norm] at hh
        nlinarith [mul_le_mul_of_nonneg_left hh (hnη z)])
    _ = _ := by rw [integral_const_mul,hmη,mul_one]

lemma normalized_convolution_error {η g : TFSpace → ℝ} {L : ℝ≥0} {r : ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η)
    (hnη : ∀ x, 0 ≤ η x) (hmη : ∫ x, η x = 1)
    (hsη : ∀ x, η x ≠ 0 → ‖x‖ ≤ r) (hg : LipschitzWith L g) (x : TFSpace) :
    ‖(η ⋆[newtonMul] g) x-g x‖ ≤ (L:ℝ)*r := by
  have hi : Integrable η := hη.integrable_of_hasCompactSupport hcη
  have he : (η ⋆[newtonMul] g) x-g x = ∫ z, η z*(g (x-z)-g x) := by
    simp only [convolution,newtonMul,ContinuousLinearMap.mul_apply',mul_sub]
    rw [integral_sub (normalized_convolution_integrable hη hcη hg.continuous x)
      (hi.mul_const _),integral_mul_const,hmη,one_mul]
  rw [he]
  calc
    _ ≤ ∫ z, ((L:ℝ)*r)*η z := norm_integral_le_of_norm_le (hi.const_mul _)
      (Eventually.of_forall fun z => by
        by_cases hz : η z = 0
        · simp [hz]
        · rw [norm_mul,Real.norm_of_nonneg (hnη z)]
          have hh := hg.dist_le_mul (x-z) x
          have hd : dist (x-z) x = ‖z‖ := by rw [dist_eq_norm]; simp
          rw [hd,dist_eq_norm] at hh
          have hl : ‖g (x-z)-g x‖ ≤ (L:ℝ)*r :=
            hh.trans (mul_le_mul_of_nonneg_left (hsη z hz) L.coe_nonneg)
          nlinarith [mul_le_mul_of_nonneg_left hl (hnη z)])
    _ = _ := by rw [integral_const_mul,hmη,mul_one]

lemma convolution_tsupport_bound {η g : TFSpace → ℝ} {r s : ℝ}
    (hsη : ∀ x, η x ≠ 0 → ‖x‖ ≤ r) (hsg : ∀ x, g x ≠ 0 → ‖x‖ ≤ s) :
    tsupport (η ⋆[newtonMul] g) ⊆ closedBall 0 (r+s) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  obtain ⟨u,hu,v,hv,rfl⟩ := support_convolution_subset newtonMul hx
  rw [mem_closedBall_zero_iff]
  exact (norm_add_le u v).trans (add_le_add (hsη u hu) (hsg v hv))

def packetSmooth (r : ℝ) (g : TFSpace → ℝ) : TFSpace → ℝ :=
  CoulombAtom.packetDensity 0 r ⋆[newtonMul] g

lemma packetSmooth_contDiff {r : ℝ} (hr : 0 < r) {g : TFSpace → ℝ} (hg : Continuous g) :
    ContDiff ℝ ∞ (packetSmooth r g) :=
  (CoulombAtom.packetDensity_compact 0 hr).contDiff_convolution_left newtonMul
    (CoulombAtom.packetDensity_smooth 0 r) hg.locallyIntegrable

lemma packetSmooth_compact {r : ℝ} (hr : 0 < r) {g : TFSpace → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (packetSmooth r g) :=
  HasCompactSupport.convolution newtonMul (CoulombAtom.packetDensity_compact 0 hr) hg

lemma packetSmooth_lipschitz {r : ℝ} (hr : 0 < r) {g : TFSpace → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) : LipschitzWith L (packetSmooth r g) :=
  normalized_convolution_lipschitz (CoulombAtom.packetDensity_smooth 0 r).continuous
    (CoulombAtom.packetDensity_compact 0 hr) (CoulombAtom.packetDensity_nonneg 0 r)
    (CoulombAtom.packetDensity_mass 0 hr) hg

lemma packetSmooth_error {r : ℝ} (hr : 0 < r) {g : TFSpace → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (x : TFSpace) : ‖packetSmooth r g x-g x‖ ≤ (L:ℝ)*r :=
  normalized_convolution_error (CoulombAtom.packetDensity_smooth 0 r).continuous
    (CoulombAtom.packetDensity_compact 0 hr) (CoulombAtom.packetDensity_nonneg 0 r)
    (CoulombAtom.packetDensity_mass 0 hr)
    (fun z hz => by simpa only [sub_zero] using CoulombAtom.packetDensity_support 0 hr hz) hg x

lemma packetSmooth_support {r s : ℝ} (hr : 0 < r) {g : TFSpace → ℝ}
    (hsg : Function.support g ⊆ closedBall 0 s) :
    tsupport (packetSmooth r g) ⊆ closedBall 0 (r+s) :=
  convolution_tsupport_bound
    (fun z hz => by simpa only [sub_zero] using CoulombAtom.packetDensity_support 0 hr hz)
    (fun z hz => by simpa only [mem_closedBall_zero_iff] using hsg hz)

end Work_LipschitzMollifier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff NNReal Topology

lemma packetSmooth_tendsto {ε : ℕ → ℝ} (he : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) {g : TFSpace → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (x : TFSpace) :
    Tendsto (fun n => packetSmooth (ε n) g x) atTop (𝓝 (g x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => packetSmooth_error (he n) hg x)
  simpa only [mul_zero] using hlim.const_mul (L:ℝ)

lemma packetSmooth_pair_tendsto (μ : Measure TFSpace) {f : TFSpace → ℝ}
    (hf : Integrable f μ) {ε : ℕ → ℝ} {r : ℝ}
    (he : ∀ n, 0 < ε n) (heb : ∀ n, ε n ≤ r) (hlim : Tendsto ε atTop (𝓝 0))
    {g : TFSpace → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) (hcg : HasCompactSupport g) :
    Tendsto (fun n => ∫ x, packetSmooth (ε n) g x*f x ∂μ) atTop
      (𝓝 (∫ x, g x*f x ∂μ)) := by
  obtain ⟨B,hB⟩ := compact_continuous_bound hg.continuous hcg
  have hn (n : ℕ) (x : TFSpace) : ‖packetSmooth (ε n) g x‖ ≤ (L:ℝ)*r+B := by
    calc
      _ = ‖packetSmooth (ε n) g x-g x+g x‖ := by rw [sub_add_cancel]
      _ ≤ ‖packetSmooth (ε n) g x-g x‖+‖g x‖ := norm_add_le _ _
      _ ≤ (L:ℝ)*r+B := add_le_add ((packetSmooth_error (he n) hg x).trans
        (mul_le_mul_of_nonneg_left (heb n) L.coe_nonneg)) (hB x)
  apply tendsto_integral_of_dominated_convergence (fun x => ((L:ℝ)*r+B)*‖f x‖)
  · intro n
    exact ((packetSmooth_contDiff (he n) hg.continuous).continuous.aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  · exact hf.norm.const_mul _
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hn n x) (norm_nonneg _)
  · exact Eventually.of_forall fun x => (packetSmooth_tendsto he hlim hg x).mul_const (f x)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketScale
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

def scaledRealPacket (b : ℝ) (g : Space → ℝ) (x : Space) : ℝ :=
  b ^ (-(3/2 : ℝ))*g (b⁻¹ • x)

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BlockSwap
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

lemma joinLists_blockSwap {N M : ℕ} {α : Type*} (s : Fin M → α) (t : Fin N → α) :
    joinLists s t ∘ (blockSwap N M).symm = joinLists t s := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simp [Function.comp_def,blockSwap,joinLists]

def swapBlocks {N M : ℕ} (ψ : FormVector (N+M)) : FormVector (M+N) :=
  reindexForm (blockSwap N M) ψ

@[simp] lemma swapBlocks_value {N M : ℕ} (ψ : FormVector (N+M))
    (s : Spins M) (t : Spins N) (x : Configuration M) (y : Configuration N) :
    (swapBlocks ψ).value (joinLists s t) (joinLists x y) =
      ψ.value (joinLists t s) (joinLists y x) := by
  simp only [swapBlocks,reindexForm,joinLists_blockSwap]

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_PatchBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

lemma tfBallPotential_nonneg {R : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (x : TFSpace) : 0 ≤ tfBallPotential R f x := by
  apply integral_nonneg_of_ae
  filter_upwards [hf] with y hy
  exact div_nonneg hy (norm_nonneg _)

lemma tfPatchMinimizer_ae_bound {R T F : ℝ} (hT : 0 < T) (Φ : TFField R)
    (hΦ : ∀ᵐ x ∂ballMeasure R, Φ x ≤ F) :
    ∀ᵐ x ∂ballMeasure R, tfPatchMinimizer R T hT Φ x ≤
      (max F 0 / ((5/3:ℝ)*T))^(3/2:ℝ) := by
  let f := tfPatchMinimizer R T hT Φ
  have hf := tfPatchMinimizer_nonneg R T hT Φ
  have he := tfPatchFunctional_euler R Φ hT hf (fun g hg => tfPatchMinimizer_min R T hT Φ hg)
  filter_upwards [he,hΦ] with x he hpx
  rw [he]
  apply Real.rpow_le_rpow (div_nonneg (le_max_right _ _) (by positivity)) _ (by norm_num)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact max_le_max_right 0 (by linarith [tfBallPotential_nonneg hf x])

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_PatchTranslatedDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace CoulombAnalysis

def translatedPatchDensity (y : TFSpace) (R B : ℝ) (f : TFLp (ballMeasure R))
    (x : TFSpace) : ℝ := boundedPatchRepresentative R B f (-y+x)

lemma translatedPatchDensity_measurable (y : TFSpace) (R B : ℝ) (f : TFLp (ballMeasure R)) :
    Measurable (translatedPatchDensity y R B f) :=
  (boundedPatchRepresentative_measurable R B f).comp (measurable_const.add measurable_id)

lemma translatedPatchDensity_nonneg (y : TFSpace) (R B : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) :
    0 ≤ translatedPatchDensity y R B f x := boundedPatchRepresentative_nonneg R B f _

lemma translatedPatchDensity_le (y : TFSpace) (R B : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) :
    translatedPatchDensity y R B f x ≤ max B 0 := boundedPatchRepresentative_le R B f _

lemma translatedPatchDensity_support (y : TFSpace) (R B : ℝ) (f : TFLp (ballMeasure R)) :
    Function.support (translatedPatchDensity y R B f) ⊆ closedBall y R := by
  intro x hx
  have hh := boundedPatchRepresentative_support R B f hx
  simpa only [mem_closedBall,dist_eq_norm,sub_zero,neg_add_eq_sub] using hh

lemma translatedPatchDensity_mass (y : TFSpace) {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    (∫ x, translatedPatchDensity y R B f x) = ∫ x, f x ∂ballMeasure R := by
  rw [←boundedPatchRepresentative_mass hf hb]
  exact (measurePreserving_add_left (volume : Measure TFSpace) (-y)).integral_comp
    (Homeomorph.addLeft (-y)).measurableEmbedding _

lemma translatedPatchDensity_kinetic (y : TFSpace) {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    (∫ x, (translatedPatchDensity y R B f x)^(5/3:ℝ)) = ‖f‖^(5/3:ℝ) := by
  rw [←boundedPatchRepresentative_kinetic hf hb]
  exact (measurePreserving_add_left (volume : Measure TFSpace) (-y)).integral_comp
    (Homeomorph.addLeft (-y)).measurableEmbedding (fun x => (boundedPatchRepresentative R B f x)^(5/3:ℝ))

lemma translatedPatchDensity_coulomb (y : TFSpace) {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    (∫ p : TFSpace × TFSpace, translatedPatchDensity y R B f p.1 *
      translatedPatchDensity y R B f p.2 / ‖p.1-p.2‖) = tfCoulombL R f f := by
  rw [←boundedPatchRepresentative_coulomb hf hb]
  have he := ((measurePreserving_add_left (volume : Measure TFSpace) (-y)).prod
    (measurePreserving_add_left (volume : Measure TFSpace) (-y))).integral_comp
    ((Homeomorph.addLeft (-y)).measurableEmbedding.prodMap (Homeomorph.addLeft (-y)).measurableEmbedding)
    (fun p : TFSpace × TFSpace => boundedPatchRepresentative R B f p.1 *
      boundedPatchRepresentative R B f p.2 / ‖p.1-p.2‖)
  simpa only [Measure.volume_eq_prod,Prod.map,translatedPatchDensity,
    add_sub_add_left_eq_sub] using he

lemma translatedPatchDensity_field (y : TFSpace) {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) (Φ : TFSpace → ℝ) :
    (∫ x, Φ x*translatedPatchDensity y R B f x) = ∫ x, Φ (y+x)*f x ∂ballMeasure R := by
  have he := (measurePreserving_add_left (volume : Measure TFSpace) y).integral_comp
    (Homeomorph.addLeft y).measurableEmbedding (fun x => Φ x*translatedPatchDensity y R B f x)
  simp only [translatedPatchDensity,neg_add_cancel_left] at he
  change (∫ x, Φ x * boundedPatchRepresentative R B f (-y+x)) = _
  rw [←he]
  exact boundedPatchRepresentative_field hf hb (fun x => Φ (y+x))

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_PatchMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace CoulombAnalysis

lemma tfCoulombL_mass_lower {R : ℝ} (_hR : 0 < R) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) :
    (∫ x, f x ∂ballMeasure R)^2 / (2*R) ≤ tfCoulombL R f f := by
  have hi := (Lp.memLp f).integrable (Fact.out : (1:ENNReal) ≤ 5/3)
  have hx : ∀ᵐ x ∂ballMeasure R, x ∈ ball (0 : TFSpace) R := ae_restrict_mem measurableSet_ball
  have hp : ∀ᵐ p ∂(ballMeasure R).prod (ballMeasure R),
      f p.1 * f p.2 / (2*R) ≤ f p.1 * f p.2 / ‖p.1-p.2‖ := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hf, Measure.quasiMeasurePreserving_snd.ae hf,
      Measure.quasiMeasurePreserving_fst.ae hx, Measure.quasiMeasurePreserving_snd.ae hx,
      ballMeasure_ae_ne R] with p hf1 hf2 hx1 hx2 hne
    have hd : ‖p.1-p.2‖ ≤ 2*R := by
      have h1 := mem_ball_zero_iff.mp hx1
      have h2 := mem_ball_zero_iff.mp hx2
      exact (norm_sub_le p.1 p.2).trans (by linarith)
    have hd0 : 0 < ‖p.1-p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    exact div_le_div_of_nonneg_left (mul_nonneg hf1 hf2) hd0 hd
  have hh := integral_mono_ae ((hi.mul_prod hi).div_const (2*R)) (tfCoulomb_integrable R f f) hp
  rw [integral_div, integral_prod_mul, ← pow_two, ← tfCoulombL_apply] at hh
  exact hh

theorem tfPatchMinimizer_mass_le {R T F : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hF : 0 ≤ F) (Φ : TFField R) (hΦ : ∀ᵐ x ∂ballMeasure R, Φ x ≤ F) :
    (∫ x, tfPatchMinimizer R T hT Φ x ∂ballMeasure R) ≤ 4*R*F := by
  let f := tfPatchMinimizer R T hT Φ
  have hf : NonnegDensity f := tfPatchMinimizer_nonneg R T hT Φ
  have hi := (Lp.memLp f).integrable (Fact.out : (1:ENNReal) ≤ 5/3)
  have he : (∫ x, Φ x * f x ∂ballMeasure R) ≤ F * (∫ x, f x ∂ballMeasure R) := by
    rw [← integral_const_mul]
    exact integral_mono_ae ((Lp.memLp Φ).integrable_mul (Lp.memLp f)) (hi.const_mul F)
      (by filter_upwards [hΦ, hf] with x hpx hfx; exact mul_le_mul_of_nonneg_right hpx hfx)
  have hmin := tfPatchMinimizer_min R T hT Φ (nonnegDensity_zero R)
  rw [tfPatchFunctional_zero] at hmin
  change tfPatchFunctional R T Φ f ≤ 0 at hmin
  rw [tfPatchFunctional, tfPatchLinear_apply] at hmin
  have hk : 0 ≤ T * ‖f‖ ^ (5/3:ℝ) := mul_nonneg hT.le (Real.rpow_nonneg (norm_nonneg _) _)
  have hm : 0 ≤ ∫ x, f x ∂ballMeasure R := integral_nonneg_of_ae hf
  have hc := (div_le_iff₀ (by positivity : (0:ℝ) < 2*R)).mp (tfCoulombL_mass_lower hR hf)
  by_cases hm0 : (∫ x, f x ∂ballMeasure R) = 0
  · change (∫ x, f x ∂ballMeasure R) ≤ _
    rw [hm0]
    positivity
  · have hmp : 0 < ∫ x, f x ∂ballMeasure R := lt_of_le_of_ne hm (Ne.symm hm0)
    change (∫ x, f x ∂ballMeasure R) ≤ _
    nlinarith

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchRandomVariables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAnalysis

lemma tfPatchIntegral_continuous (R : ℝ) :
    Continuous (fun f : TFLp (ballMeasure R) => ∫ z, f z ∂ballMeasure R) := by
  let Φ : TFField R := (memLp_const (1:ℝ)).toLp (fun _ : TFSpace => (1:ℝ))
  have he (f : TFLp (ballMeasure R)) : -(tfPatchLinear R Φ f) = ∫ z, f z ∂ballMeasure R := by
    rw [tfPatchLinear_apply,neg_neg]
    have hΦ : Φ =ᵐ[ballMeasure R] fun _ => (1:ℝ) :=
      (memLp_const (1:ℝ)).coeFn_toLp
    exact integral_congr_ae (hΦ.mono fun z hz => by simp only [hz,one_mul])
  convert (tfPatchLinear R Φ).continuous.neg using 1
  all_goals try with_reducible_and_instances rfl
  funext f
  exact (he f).symm

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_CoulombLipschitzDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff NNReal Topology

namespace CoulombAnalysis

lemma tfSpace_closedBall_real (r : ℝ) (hr : 0 ≤ r) :
    volume.real (closedBall (0 : TFSpace) r) = r^3*(Real.pi*4/3) := by
  rw [Measure.real,EuclideanSpace.volume_closedBall_fin_three,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hr,ENNReal.toReal_ofReal (by positivity)]

theorem tfCoulomb_lipschitz_duality {R r : ℝ} (hr : 0 < r) (hR : 2*r < R)
    (f : TFLp (ballMeasure R)) {g : TFSpace → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hs : Function.support g ⊆ closedBall 0 r) :
    (∫ x, g x*f x ∂ballMeasure R)^2 ≤
      (8*r^3*(L:ℝ)^2)*tfCoulombL R f f := by
  have hcg : HasCompactSupport g :=
    (isCompact_closedBall (0 : TFSpace) r).of_isClosed_subset isClosed_closure
      (closure_minimal hs isClosed_closedBall)
  let ε : ℕ → ℝ := fun n => r/((n:ℝ)+1)
  have he (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have heb (n : ℕ) : ε n ≤ r := by
    dsimp [ε]
    exact div_le_self hr.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have helim : Tendsto ε atTop (𝓝 0) := by
    have hh := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r
    simpa only [mul_one_div,mul_zero] using hh
  have hlim := packetSmooth_pair_tendsto (ballMeasure R)
    ((Lp.memLp f).integrable (Fact.out : (1:ENNReal) ≤ 5/3)) he heb helim hg hcg
  apply le_of_tendsto (hlim.pow 2)
  apply Eventually.of_forall
  intro n
  have hgn : ContDiff ℝ 2 (packetSmooth (ε n) g) :=
    (packetSmooth_contDiff (he n) hg.continuous).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hcgn := packetSmooth_compact (he n) hcg
  have hsn : tsupport (packetSmooth (ε n) g) ⊆ closedBall 0 (2*r) :=
    (packetSmooth_support (he n) hs).trans (closedBall_subset_closedBall (by linarith [heb n]))
  have hder := compact_dirichlet_bound (hgn.of_le (by norm_num)) hcgn
    (packetSmooth_lipschitz (he n) hg) hsn
  have hh := tfCoulomb_dirichlet_duality R f hgn hcgn (hsn.trans (closedBall_subset_ball hR))
  have hn : 0 ≤ (4*Real.pi)⁻¹ := by positivity
  have hl := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hder hn) (tfCoulombL_nonneg R f)
  apply hh.trans
  convert hl using 1
  all_goals try with_reducible_and_instances rfl
  rw [tfSpace_closedBall_real (2*r) (by positivity)]
  field_simp [Real.pi_ne_zero]
  ring

theorem tfPatchGap_lipschitz_control {R r : ℝ} (hr : 0 < r) (hR : 2*r < R)
    (T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ)
    {g : TFSpace → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hs : Function.support g ⊆ closedBall 0 r) :
    (∫ x, g x*(σ-tfPatchMinimizer R T hT Φ) x ∂ballMeasure R)^2 ≤
      (16*r^3*(L:ℝ)^2)*tfPatchGap R T hT Φ σ := by
  have hh := tfCoulomb_lipschitz_duality hr hR (σ-tfPatchMinimizer R T hT Φ) hg hs
  have hb := mul_le_mul_of_nonneg_left (tfPatchGap_coulomb_le R T hT Φ hσ)
    (show 0 ≤ 8*r^3*(L:ℝ)^2 by positivity)
  exact hh.trans (by nlinarith)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_WeakSemilinearComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

theorem weak_semilinear_classical_ball {u v : Space → ℝ} {r R k : ℝ}
    (hr : 0 < r) (hrR : r < R) (hk : 0 < k)
    (hu : ContinuousOn u (closedBall 0 r))
    (hv : ∀ x ∈ ball (0 : Space) R, ContDiffAt ℝ 2 v x)
    (hlv : ContinuousOn (Δ v) (closedBall 0 r))
    (hvp : ∀ x ∈ closedBall (0 : Space) r, 0 < v x)
    (hvs : ∀ x ∈ ball (0 : Space) r, Δ v x ≤ k*(v x)^(3/2:ℝ))
    (hb : ∀ x : Space, ‖x‖ = r → u x ≤ v x)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R →
      (∫ x, u x*Δ g x) = ∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x) :
    ∀ x ∈ closedBall (0 : Space) r, u x ≤ v x := by
  have hvcont : ContinuousOn v (closedBall (0 : Space) r) := fun x hx =>
    (hv x (closedBall_subset_ball hrR hx)).continuousAt.continuousWithinAt
  let F : Space → ℝ := fun x => k*(max (u x) 0)^(3/2:ℝ)-Δ v x
  have hreaction : ContinuousOn (fun x => k*(max (u x) 0)^(3/2:ℝ)) (closedBall 0 r) :=
    continuousOn_const.mul ((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/2)).comp_continuousOn
      (hu.sup continuousOn_const))
  have hF : ContinuousOn F (closedBall 0 r) := hreaction.sub hlv
  have hcmp := weak_strict_source_comparison (isCompact_closedBall (0 : Space) r)
    (hu.sub hvcont) hF (fun x hx hp => ?_) (fun x hx hn => ?_) (fun g hg hcg hs _hn => ?_)
  · intro x hx
    exact sub_nonpos.mp (hcmp x hx)
  · rw [interior_closedBall (0 : Space) hr.ne'] at hx
    have hpv := hvp x (ball_subset_closedBall hx)
    have hpu : 0 < u x := hpv.trans (sub_pos.mp hp)
    have hs := hvs x hx
    have ht := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hpv.le (sub_pos.mp hp) (by norm_num : (0:ℝ) < 3/2)) hk
    dsimp only [F]
    rw [max_eq_left hpu.le]
    linarith
  · rw [interior_closedBall (0 : Space) hr.ne'] at hn
    have hn' : ‖x‖ = r := le_antisymm (by simpa only [mem_closedBall,dist_zero_right] using hx)
      (le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hn))
    exact sub_nonpos.mpr (hb x hn')
  · have hs' : tsupport g ⊆ ball (0 : Space) r := by
      simpa only [interior_closedBall (0 : Space) hr.ne'] using hs
    have hsk := hs'.trans ball_subset_closedBall
    have hui := continuousOn_mul_integrable_support (isCompact_closedBall 0 r) hu
      (tfLaplacian_continuous hg) ((tfLaplacian_support hg).trans hsk)
    have hvi := continuousOn_mul_integrable_support (isCompact_closedBall 0 r) hvcont
      (tfLaplacian_continuous hg) ((tfLaplacian_support hg).trans hsk)
    have hri := continuousOn_mul_integrable_support (isCompact_closedBall 0 r) hreaction
      hg.continuous ((subset_tsupport g).trans hsk)
    have hlvi := continuousOn_mul_integrable_support (isCompact_closedBall 0 r) hlv
      hg.continuous ((subset_tsupport g).trans hsk)
    have he := hw g hg hcg (hs'.trans (ball_subset_ball hrR.le))
    have hvgreen := local_laplacian_green_ball hr hrR hv hg hcg hs'
    have heq : (∫ x, (u x-v x)*Δ g x) = ∫ x, F x*g x := by
      simp_rw [F,sub_mul]
      rw [integral_sub hui hvi,integral_sub hri hlvi,he,hvgreen]
    exact heq.ge

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TFNonradialBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfCapBarrier_pos {A R : ℝ} (hA : 0 < A) {x : Space} (hx : ‖x‖ < R) :
    0 < tfCapBarrier A R x := by
  have hR : 0 < R := (norm_nonneg x).trans_lt hx
  exact div_pos (mul_pos hA (pow_pos hR _)) (pow_pos (capDenominator_pos hx) _)

lemma tfCapBarrier_contDiffAt (A : ℝ) {R : ℝ} {x : Space} (hx : ‖x‖ < R) :
    ContDiffAt ℝ 2 (tfCapBarrier A R) x :=
  contDiffAt_const.div ((contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).pow 4)
    (pow_ne_zero _ (capDenominator_pos hx).ne')

lemma tfCapBarrier_laplacian (A : ℝ) {R : ℝ} {x : Space} (hx : ‖x‖ < R) :
    Δ (tfCapBarrier A R) x = A*R^4*(24*R^2+56*‖x‖^2)/(R^2-‖x‖^2)^6 := by
  have hn := (capDenominator_pos hx).ne'
  have hc : ContDiffAt ℝ 2 (fun s : ℝ => A*R^4/(R^2-s)^4) (‖x‖^2) :=
    contDiffAt_const.div ((contDiffAt_const.sub contDiffAt_id).pow 4) (pow_ne_zero _ hn)
  change Δ (fun x : Space => (fun s : ℝ => A*R^4/(R^2-s)^4) (‖x‖^2)) x = _
  rw [CoulombPDE.laplacian_norm_sq_comp hc,cap_scalar_second _ _ _ hn,
    (cap_scalar_deriv_four _ _ _ hn).deriv]
  norm_num [Space,finrank_euclideanSpace_fin]
  field_simp
  ring

lemma tfCapBarrier_reaction {A R : ℝ} (hA : 0 ≤ A) {x : Space} (hx : ‖x‖ < R) :
    (tfCapBarrier A R x)^(3/2:ℝ) = A^(3/2:ℝ)*R^6/(R^2-‖x‖^2)^6 := by
  have hR : 0 ≤ R := (norm_nonneg x).trans hx.le
  have hd := (capDenominator_pos hx).le
  rw [tfCapBarrier,Real.div_rpow (mul_nonneg hA (pow_nonneg hR _)) (pow_nonneg hd _),
    Real.mul_rpow hA (pow_nonneg hR _)]
  have hp (a : ℝ) (ha : 0 ≤ a) : (a^4)^(3/2:ℝ) = a^6 := by
    rw [←Real.rpow_natCast a 4,←Real.rpow_mul ha]
    norm_num
  rw [hp R hR,hp _ hd]

lemma tfCapBarrier_supersolution {A R k : ℝ} (hA : 0 < A)
    (hkA : 80*A ≤ k*A^(3/2:ℝ)) {x : Space} (hx : ‖x‖ < R) :
    Δ (tfCapBarrier A R) x ≤ k*(tfCapBarrier A R x)^(3/2:ℝ) := by
  rw [tfCapBarrier_laplacian A hx,tfCapBarrier_reaction hA.le hx]
  have hR : 0 < R := (norm_nonneg x).trans_lt hx
  have hd : 0 < (R^2-‖x‖^2)^6 := pow_pos (capDenominator_pos hx) _
  rw [←mul_div_assoc,div_le_div_iff_of_pos_right hd]
  have hn : ‖x‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg x) hx.le 2
  calc
    _ ≤ A*R^4*(80*R^2) := mul_le_mul_of_nonneg_left (by nlinarith)
      (mul_nonneg hA.le (pow_nonneg hR.le _))
    _ = (80*A)*R^6 := by ring
    _ ≤ (k*A^(3/2:ℝ))*R^6 := mul_le_mul_of_nonneg_right hkA (pow_nonneg hR.le _)
    _ = _ := by ring

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TFNonradialCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

theorem weak_tfCapBarrier_bound {u : Space → ℝ} {A R k : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hk : 0 < k) (hkA : 80*A ≤ k*A^(3/2:ℝ))
    (hu : ContinuousOn u (closedBall 0 R))
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R →
      (∫ x, u x*Δ g x) = ∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x)
    (x : Space) (hx : ‖x‖ < R) : u x ≤ tfCapBarrier A R x := by
  obtain ⟨z,hz,hmax⟩ := (isCompact_closedBall (0 : Space) R).exists_isMaxOn
    (show (closedBall (0 : Space) R).Nonempty from ⟨0,mem_closedBall_self hR.le⟩) hu
  obtain ⟨r,hr,hxr,hrR,hrM⟩ := exists_tfCapBarrier_radius hA hR hx (u z)
  have hn (w : Space) (hw : w ∈ closedBall (0 : Space) r) : ‖w‖ < R :=
    (show ‖w‖ ≤ r by simpa only [mem_closedBall,dist_zero_right] using hw).trans_lt hrR
  have hl : ContinuousOn (Δ (tfCapBarrier A R)) (closedBall 0 r) := by
    have hc : ContinuousOn
        (fun w : Space => A*R^4*(24*R^2+56*‖w‖^2)/(R^2-‖w‖^2)^6) (closedBall 0 r) :=
      (continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul (continuous_norm.pow 2).continuousOn))).div
        (continuousOn_const.sub (continuous_norm.pow 2).continuousOn |>.pow 6)
        (fun w hw => pow_ne_zero _ (capDenominator_pos (hn w hw)).ne')
    exact hc.congr (fun w hw => tfCapBarrier_laplacian A (hn w hw))
  apply weak_semilinear_classical_ball hr hrR hk
    (hu.mono (closedBall_subset_closedBall hrR.le))
    (fun w hw => tfCapBarrier_contDiffAt A (by simpa only [mem_ball,dist_zero_right] using hw)) hl
    (fun w hw => tfCapBarrier_pos hA (hn w hw))
    (fun w hw => tfCapBarrier_supersolution hA hkA (hn w (ball_subset_closedBall hw)))
    (fun w hw => ?_) hw x (by simpa only [mem_closedBall,dist_zero_right] using hxr.le)
  change u w ≤ A*R^4/(R^2-‖w‖^2)^4
  rw [hw]
  exact (hmax (by simpa only [mem_closedBall,dist_zero_right,hw] using hrR.le)).trans hrM

lemma tfCapBarrier_inner_quarter {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    {x : Space} (hx : ‖x‖ ≤ 3*R/4) : tfCapBarrier A R x ≤ (256*A)/R^4 := by
  have hxR : ‖x‖ < R := hx.trans_lt (by linarith)
  have hsq := pow_le_pow_left₀ (norm_nonneg x) hx 2
  have hd : R^2/4 ≤ R^2-‖x‖^2 := by nlinarith [sq_nonneg R]
  calc
    _ ≤ A*R^4/(R^2/4)^4 := div_le_div_of_nonneg_left
      (mul_nonneg hA (pow_nonneg hR.le _)) (pow_pos (by positivity) _)
      (pow_le_pow_left₀ (by positivity) hd 4)
    _ = _ := by field_simp; ring

theorem weak_tf_nonradial_cap {u : Space → ℝ} {R k : ℝ} (hR : 0 < R) (hk : 0 < k)
    (hu : ContinuousOn u (closedBall 0 R))
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R →
      (∫ x, u x*Δ g x) = ∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x)
    (x : Space) (hx : ‖x‖ ≤ 3*R/4) : u x ≤ (256*(80/k)^2)/R^4 := by
  have hA := tfCapBarrier_coefficient hk
  exact (weak_tfCapBarrier_bound hA.1 hR hk hA.2 hu hw x (hx.trans_lt (by linarith))).trans
    (tfCapBarrier_inner_quarter hA.1.le hR hx)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_ActualPatchCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

def tfPatchCapConstant : ℝ := 256*(80/tfReactionCoefficient)^2

lemma tfPatchCapConstant_pos : 0 < tfPatchCapConstant := by
  unfold tfPatchCapConstant
  exact mul_pos (by norm_num) (pow_pos (div_pos (by norm_num) tfReactionCoefficient_pos) _)

lemma tfReactionCoefficient_formula (v : ℝ) :
    4*Real.pi*(max v 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ) =
      tfReactionCoefficient*(max v 0)^(3/2:ℝ) := by
  rw [Real.div_rpow (le_max_right _ _) (mul_nonneg (by norm_num) tfKinetic_pos.le)]
  simp only [tfReactionCoefficient,div_eq_mul_inv]
  ring

lemma tf_weak_pde_volume {W : Space → ℝ} {R : ℝ}
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R →
      (∫ x, W x*Δ g x ∂ballMeasure R) = 4*Real.pi*
        (∫ x, (max (W x) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*g x ∂ballMeasure R))
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 R) :
    (∫ x, W x*Δ g x) = ∫ x, tfReactionCoefficient*(max (W x) 0)^(3/2:ℝ)*g x := by
  have h1 : Function.support (fun x => W x*Δ g x) ⊆ ball (0 : Space) R := by
    intro x hx
    exact hs (tfLaplacian_support hg (mul_ne_zero_iff.mp hx).2)
  have h2 : Function.support (fun x => (max (W x) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*g x)
      ⊆ ball (0 : Space) R := by
    intro x hx
    exact hs (subset_tsupport g (mul_ne_zero_iff.mp hx).2)
  have he := hw g hg hcg hs
  rw [ballMeasure_integral_eq_of_support h1,ballMeasure_integral_eq_of_support h2,←integral_const_mul] at he
  refine he.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
  dsimp only
  rw [←mul_assoc,tfReactionCoefficient_formula]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_NearTFReaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology ContDiff

namespace CoulombAnalysis
open CoulombAtom

lemma tfPotential_weak_laplacian_ball {ρ : Space → ℝ} (hp : MemLp ρ (5/3))
    {S : ℝ} (hs : Function.support ρ ⊆ ball 0 S)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hsg : tsupport g ⊆ ball 0 S) :
    (∫ x, tfPotential ρ x*Δ g x) = -(4*Real.pi)*(∫ x, ρ x*g x) := by
  obtain ⟨q,hq,hpot⟩ := exists_patch_density S hp hs
  have hh := tfBallPotential_weak_laplacian S q hg hcg hsg
  simp_rw [hpot] at hh
  have h1 : Function.support (fun x => tfPotential ρ x*Δ g x) ⊆ ball 0 S := by
    intro x hx
    exact hsg (tfLaplacian_support hg (mul_ne_zero_iff.mp hx).2)
  have h2 : Function.support (fun x => ρ x*g x) ⊆ ball 0 S := by
    intro x hx
    exact hsg (subset_tsupport g (mul_ne_zero_iff.mp hx).2)
  rw [ballMeasure_integral_eq_of_support h1] at hh
  have he : (∫ x, q x*g x ∂ballMeasure S) = ∫ x, ρ x*g x ∂ballMeasure S :=
    integral_congr_ae (hq.mono fun x hx => by dsimp only; rw [hx])
  rw [he,ballMeasure_integral_eq_of_support h2] at hh
  exact hh

def nearTFReaction (u : Space → ℝ) (k S : ℝ) : Space → ℝ :=
  (ball 0 S).indicator (fun x => k/(4*Real.pi)*(max (u x) 0)^(3/2:ℝ))

lemma nearTFReaction_measurable {u : Space → ℝ} (hu : Continuous u) (k S : ℝ) :
    Measurable (nearTFReaction u k S) := by
  exact ((measurable_const.mul ((hu.measurable.max measurable_const).pow_const _))).indicator measurableSet_ball

lemma nearTFReaction_nonneg (u : Space → ℝ) {k : ℝ} (hk : 0 ≤ k) (S : ℝ) (x : Space) :
    0 ≤ nearTFReaction u k S x := by
  exact indicator_nonneg (fun _ _ => mul_nonneg (by positivity) (Real.rpow_nonneg (le_max_right _ _) _)) x

lemma nearTFReaction_support (u : Space → ℝ) (k S : ℝ) :
    Function.support (nearTFReaction u k S) ⊆ ball 0 S := support_indicator_subset

lemma nearTFReaction_bound {u : Space → ℝ} {k S B : ℝ} (hk : 0 ≤ k) (hB : 0 ≤ B)
    (hu : ∀ x ∈ ball (0 : Space) S, u x ≤ B) (x : Space) :
    nearTFReaction u k S x ≤ k/(4*Real.pi)*B^(3/2:ℝ) := by
  by_cases hx : x ∈ ball (0 : Space) S
  · rw [nearTFReaction,indicator_of_mem hx]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (le_max_right _ _) (max_le (hu x hx) hB) (by norm_num)) (by positivity)
  · rw [nearTFReaction,indicator_of_notMem hx]
    positivity

lemma nearTFReaction_continuous_potential {u : Space → ℝ} (hu : Continuous u)
    {k S B : ℝ} (hk : 0 ≤ k) (hB : 0 ≤ B)
    (hb : ∀ x ∈ ball (0 : Space) S, u x ≤ B) :
    Continuous (tfPotential (nearTFReaction u k S)) :=
  tfPotential_continuous
    (bounded_support_integrable (nearTFReaction_measurable hu k S)
      (nearTFReaction_nonneg u hk S) (nearTFReaction_bound hk hB hb) (nearTFReaction_support u k S))
    (bounded_support_memLp (nearTFReaction_measurable hu k S)
      (nearTFReaction_nonneg u hk S) (nearTFReaction_bound hk hB hb) (nearTFReaction_support u k S) (5/3))

theorem nearTFReaction_weak_harmonic {u : Space → ℝ} (hu : Continuous u)
    {k S B T : ℝ} (hk : 0 ≤ k) (hB : 0 ≤ B)
    (hb : ∀ x ∈ ball (0 : Space) S, u x ≤ B) (hST : S ≤ T)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 T → (∫ x, u x*Δ g x) = ∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hsg : tsupport g ⊆ ball 0 S) :
    (∫ x, (u x+tfPotential (nearTFReaction u k S) x)*Δ g x) = 0 := by
  have hcp := nearTFReaction_continuous_potential hu hk hB hb
  have hp := bounded_support_memLp (nearTFReaction_measurable hu k S)
    (nearTFReaction_nonneg u hk S) (nearTFReaction_bound hk hB hb) (nearTFReaction_support u k S) (5/3)
  have he := tfPotential_weak_laplacian_ball hp (nearTFReaction_support u k S) hg hcg hsg
  have h1 : Integrable (fun x => u x*Δ g x) :=
    (hu.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg).mul_left
  have h2 : Integrable (fun x => tfPotential (nearTFReaction u k S) x*Δ g x) :=
    (hcp.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg).mul_left
  simp_rw [add_mul]
  rw [integral_add h1 h2,he,hw g hg hcg (hsg.trans (ball_subset_ball hST))]
  have hr : (∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x) =
      4*Real.pi*(∫ x, nearTFReaction u k S x*g x) := by
    rw [←integral_const_mul]
    apply integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : g x = 0
    · simp only [hx,mul_zero]
    · have hsx := hsg (subset_tsupport g hx)
      rw [nearTFReaction,indicator_of_mem hsx]
      field_simp
  rw [hr]
  ring

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TFNonradialOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology ContDiff

namespace CoulombAnalysis
open CoulombAtom

lemma weak_harmonic_upper_distance {H : Space → ℝ} (hH : Continuous H) (K : ℝ)
    {S : ℝ} (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 S → (∫ x, H x*Δ g x) = 0)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hsg : tsupport g ⊆ ball 0 S) : (∫ x, (K-H x)*Δ g x) = 0 := by
  have hi : Integrable (fun x => H x*Δ g x) :=
    (hH.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg).mul_left
  have hic : Integrable (fun x => K*Δ g x) :=
    (continuous_const.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg).mul_left
  have he := compact_laplacian_green (f := fun _ : Space => K) contDiff_const hg hcg
  simp only [laplacian_const,Pi.zero_apply,zero_mul,integral_zero] at he
  simp_rw [sub_mul]
  rw [integral_sub hic hi,he,hw g hg hcg hsg,sub_self]

lemma exists_global_weak_tf_oscillation_constant {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Space → ℝ) (R : ℝ), 0 < R → Continuous u →
      (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball 0 R →
        (∫ x, u x*Δ g x) = ∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x) →
      ∀ x : Space, ‖x‖ ≤ R/12 →
        |u x-u 0| ≤ C/R*‖x‖*(R⁻¹^4+max (-u 0) 0) := by
  obtain ⟨Ch,hCh,harm⟩ := exists_weak_harmonic_oscillation_constant
  let A : ℝ := 256*(80/k)^2
  let E : ℝ := k*A^(3/2:ℝ)
  let K : ℝ := A+E
  let C : ℝ := 6*Ch*(K+1)+E+1
  have hA : 0 < A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hK : 0 ≤ K := add_nonneg hA.le hE
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro u R hR hu hw x hx
  have hcap (z : Space) (hz : ‖z‖ ≤ 3*R/4) : u z ≤ A/R^4 :=
    weak_tf_nonradial_cap hR hk hu.continuousOn hw z hz
  have hB : 0 ≤ A/R^4 := by positivity
  have hbr (z : Space) (hz : z ∈ ball (0 : Space) (R/2)) : u z ≤ A/R^4 :=
    hcap z (by have ht := mem_ball_zero_iff.mp hz; linarith)
  let ρ := nearTFReaction u k (R/2)
  let P := tfPotential ρ
  have hm : Measurable ρ := nearTFReaction_measurable hu k (R/2)
  have hn : ∀ z, 0 ≤ ρ z := nearTFReaction_nonneg u hk.le (R/2)
  have hb : ∀ z, ρ z ≤ k/(4*Real.pi)*(A/R^4)^(3/2:ℝ) := nearTFReaction_bound hk.le hB hbr
  have hs : Function.support ρ ⊆ ball 0 (R/2) := nearTFReaction_support u k (R/2)
  have hP : Continuous P := nearTFReaction_continuous_potential hu hk.le hB hbr
  have hPn (z : Space) : 0 ≤ P z := tfPotential_nonneg (Eventually.of_forall hn) z
  have hM : 0 ≤ k/(4*Real.pi)*(A/R^4)^(3/2:ℝ) := by positivity
  have hpb (z : Space) (hz : ‖z‖ ≤ R/2) : P z ≤ E/R^4 := by
    have hh := bounded_density_potential_le hm hM (by linarith : 0 < R/2) hn hb hs z hz
    apply hh.trans
    calc
      _ = (E/2)/R^4 := by
        rw [cap_reaction_scale hA.le hR]
        dsimp [E]
        field_simp
        ring
      _ ≤ E/R^4 := div_le_div_of_nonneg_right (by linarith) (pow_nonneg hR.le _)
  have hpd : |P x-P 0| ≤ E/R^5*‖x‖ := by
    have hh := bounded_density_potential_difference hm hM (by linarith : 0 < R/2) hn hb hs x 0
      (by linarith) (by simp; positivity)
    apply hh.trans_eq
    rw [sub_zero,cap_reaction_scale hA.le hR]
    dsimp [E]
    field_simp
    ring
  let H : Space → ℝ := fun z => u z+P z
  have hH : Continuous H := hu.add hP
  have hHw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 (R/2) → (∫ z, H z*Δ g z) = 0 := by
    intro g hg hcg hsg
    exact nearTFReaction_weak_harmonic hu hk.le hB hbr (by linarith : R/2 ≤ R) hw hg hcg hsg
  let v : Space → ℝ := fun z => K/R^4-H z
  have hvc : Continuous v := continuous_const.sub hH
  have hvn : ∀ z ∈ closedBall (0 : Space) (3*(R/6)), 0 ≤ v z := by
    intro z hz
    have ht : ‖z‖ ≤ R/2 := by
      have he : 3*(R/6) = R/2 := by ring
      simpa only [he,mem_closedBall,dist_zero_right] using hz
    have hc := hcap z (by linarith)
    have hp := hpb z ht
    dsimp [v,H,K]
    rw [add_div]
    linarith
  have hvw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 (3*(R/6)) → (∫ z, v z*Δ g z) = 0 := by
    intro g hg hcg hsg
    apply weak_harmonic_upper_distance hH (K/R^4) hHw hg hcg
    convert hsg using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hv := harm v (R/6) (by linarith) hvc.continuousOn hvn hvw x (by linarith)
  have hv0 : v 0 ≤ K/R^4+max (-u 0) 0 := by
    have hp := hPn 0
    have hn0 := le_max_left (-u 0) 0
    dsimp [v,H]
    linarith
  have hneg : 0 ≤ max (-u 0) 0 := le_max_right _ _
  let Q : ℝ := R⁻¹^4+max (-u 0) 0
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hb0 : v 0 ≤ (K+1)*Q := by
    apply hv0.trans
    dsimp [Q]
    rw [div_eq_mul_inv,←inv_pow]
    nlinarith [mul_nonneg hK hneg,pow_nonneg (inv_nonneg.mpr hR.le) 4]
  have hv' : |H x-H 0| ≤ (6*Ch*(K+1))/R*‖x‖*Q := by
    have he : v x-v 0 = -(H x-H 0) := by dsimp [v]; ring
    rw [he,abs_neg] at hv
    apply hv.trans
    calc
      _ ≤ Ch/(R/6)*‖x‖*((K+1)*Q) := mul_le_mul_of_nonneg_left hb0 (by positivity)
      _ = _ := by ring
  have hp' : |P x-P 0| ≤ E/R*‖x‖*Q := by
    apply hpd.trans
    calc
      _ = E/R*‖x‖*(R⁻¹^4) := by ring
      _ ≤ E/R*‖x‖*Q := mul_le_mul_of_nonneg_left (by dsimp [Q]; linarith) (by positivity)
  calc
    |u x-u 0| = |(H x-H 0)-(P x-P 0)| := by dsimp [H]; congr 1; ring
    _ ≤ |H x-H 0|+|P x-P 0| := abs_sub _ _
    _ ≤ (6*Ch*(K+1))/R*‖x‖*Q+E/R*‖x‖*Q := add_le_add hv' hp'
    _ ≤ C/R*‖x‖*Q := by
      dsimp [C]
      calc
        _ = (6*Ch*(K+1)+E)/R*‖x‖*Q := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hQ
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply div_le_div_of_nonneg_right _ hR.le
          linarith

theorem exists_weak_tf_oscillation_constant {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Space → ℝ) (R : ℝ), 0 < R →
      ContinuousOn u (closedBall 0 R) →
      (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball 0 R →
        (∫ x, u x*Δ g x) = ∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x) →
      ∀ x : Space, ‖x‖ ≤ R/12 →
        |u x-u 0| ≤ C/R*‖x‖*(R⁻¹^4+max (-u 0) 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_global_weak_tf_oscillation_constant hk
  refine ⟨C,hC,?_⟩
  intro u R hR hu hw x hx
  let f : C(closedBall (0 : Space) R,ℝ) := ⟨_,hu.domRestrict⟩
  obtain ⟨v,hv⟩ := f.exists_restrict_eq isClosed_closedBall
  have he (z : Space) (hz : z ∈ closedBall (0 : Space) R) : v z = u z :=
    congrArg (fun h : C(closedBall (0 : Space) R,ℝ) => h ⟨z,hz⟩) hv
  have hh := hbound v R hR v.continuous (fun g hg hcg hs => ?_) x hx
  · simpa only [he x (by simpa only [mem_closedBall,dist_zero_right] using hx.trans (by linarith : R/12 ≤ R)),
      he 0 (mem_closedBall_self hR.le)] using hh
  · have hleft : (∫ z, v z*Δ g z) = ∫ z, u z*Δ g z := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        by_cases hz : Δ g z = 0
        · simp only [hz,mul_zero]
        · change v z*Δ g z = u z*Δ g z
          rw [he z (ball_subset_closedBall (hs (tfLaplacian_support hg hz)))]
    rw [hleft,hw g hg hcg hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : g z = 0
      · simp only [hz,mul_zero]
      · change k*(max (u z) 0)^(3/2:ℝ)*g z = k*(max (v z) 0)^(3/2:ℝ)*g z
        rw [he z (ball_subset_closedBall (hs (subset_tsupport g hz)))]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_RadialPatchCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

def tfPatchOscillationConstant : ℝ :=
  Classical.choose (exists_weak_tf_oscillation_constant tfReactionCoefficient_pos)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchTruncationLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

def tfPatchDensityCapConstant : ℝ :=
  (tfPatchCapConstant/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalCountGapBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped NNReal Topology BigOperators

namespace CoulombAnalysis

def countPlateau (a : ℝ) (x : TFSpace) : ℝ :=
  max 0 (min 1 ((2*a-‖x‖)/a))

lemma countPlateau_nonneg (a : ℝ) (x : TFSpace) : 0 ≤ countPlateau a x :=
  le_max_left _ _

lemma countPlateau_le_one (a : ℝ) (x : TFSpace) : countPlateau a x ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

lemma countPlateau_one {a : ℝ} (ha : 0 < a) {x : TFSpace} (hx : ‖x‖ ≤ a) :
    countPlateau a x = 1 := by
  have hh : 1 ≤ (2*a-‖x‖)/a := (le_div_iff₀ ha).mpr (by linarith)
  simp only [countPlateau,min_eq_left hh,max_eq_right (by norm_num : (0:ℝ) ≤ 1)]

lemma countPlateau_support {a : ℝ} (ha : 0 < a) :
    Function.support (countPlateau a) ⊆ closedBall 0 (2*a) := by
  intro x hx
  rw [mem_closedBall_zero_iff]
  by_contra hn
  have hh : (2*a-‖x‖)/a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
  exact hx (max_eq_left ((min_le_right _ _).trans hh))

lemma countPlateau_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzWith ⟨a⁻¹, inv_nonneg.mpr ha.le⟩ (countPlateau a) := by
  have hh : LipschitzWith ⟨a⁻¹, inv_nonneg.mpr ha.le⟩
      (fun x : TFSpace => (2*a-‖x‖)/a) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have he : (2*a-‖x‖)/a-(2*a-‖y‖)/a = (‖y‖-‖x‖)/a := by ring
    rw [he,abs_div,abs_of_pos ha]
    have hd : |‖y‖-‖x‖| ≤ dist x y := by
      simpa only [dist_eq_norm,norm_sub_rev] using abs_norm_sub_norm_le y x
    change |‖y‖-‖x‖|/a ≤ a⁻¹*dist x y
    simpa only [inv_mul_eq_div] using div_le_div_of_nonneg_right hd ha.le
  exact (hh.const_min 1).const_max 0

lemma countPlateau_mul_integrable {R a : ℝ} (ha : 0 < a)
    (σ : TFLp (ballMeasure R)) :
    Integrable (fun x => countPlateau a x*σ x) (ballMeasure R) := by
  apply ((Lp.memLp σ).integrable (Fact.out : (1:ENNReal) ≤ 5/3)).bdd_mul
    (countPlateau_lipschitz ha).continuous.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (countPlateau_nonneg a x)]
    exact countPlateau_le_one a x

lemma countPlateau_mass_lower {R a : ℝ} (ha : 0 < a)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) :
    (∫ x in ball 0 a, σ x ∂ballMeasure R) ≤
      ∫ x, countPlateau a x*σ x ∂ballMeasure R := by
  have hi := (Lp.memLp σ).integrable (Fact.out : (1:ENNReal) ≤ 5/3)
  rw [←integral_indicator measurableSet_ball]
  apply integral_mono_ae (hi.indicator measurableSet_ball) (countPlateau_mul_integrable ha σ)
  filter_upwards [hσ] with x hx
  by_cases hb : x ∈ ball (0:TFSpace) a
  · rw [indicator_of_mem hb,countPlateau_one ha (mem_ball_zero_iff.mp hb).le,one_mul]
  · rw [indicator_of_notMem hb]
    exact mul_nonneg (countPlateau_nonneg a x) hx

lemma countPlateau_mass_upper {R a C : ℝ} (ha : 0 < a) (hR : 2*a < R)
    {f : TFLp (ballMeasure R)} (hC : 0 ≤ C)
    (hc : ∀ᵐ x ∂ballMeasure R, ‖x‖ ≤ 2*a → f x ≤ C) :
    (∫ x, countPlateau a x*f x ∂ballMeasure R) ≤
      C*((2*a)^3*(Real.pi*4/3)) := by
  have hi : Integrable (fun x : TFSpace => (closedBall 0 (2*a)).indicator (fun _ => C) x)
      (ballMeasure R) := (integrable_const C).indicator measurableSet_closedBall
  have hb : (∫ x, countPlateau a x*f x ∂ballMeasure R) ≤
      ∫ x, (closedBall (0:TFSpace) (2*a)).indicator (fun _ => C) x ∂ballMeasure R := by
    apply integral_mono_ae (countPlateau_mul_integrable ha f) hi
    filter_upwards [hc] with x hx
    by_cases hs : x ∈ closedBall (0:TFSpace) (2*a)
    · rw [indicator_of_mem hs]
      exact (mul_le_mul_of_nonneg_left (hx (mem_closedBall_zero_iff.mp hs))
        (countPlateau_nonneg a x)).trans (mul_le_of_le_one_left hC (countPlateau_le_one a x))
    · rw [indicator_of_notMem hs]
      have hz : countPlateau a x = 0 := Function.notMem_support.mp
        (fun hh => hs (countPlateau_support ha hh))
      simp only [hz,zero_mul,le_refl]
  rw [integral_indicator measurableSet_closedBall,setIntegral_const,smul_eq_mul] at hb
  have he : (ballMeasure R).real (closedBall (0:TFSpace) (2*a)) =
      volume.real (closedBall (0:TFSpace) (2*a)) := by
    rw [Measure.real,Measure.real,ballMeasure,Measure.restrict_apply measurableSet_closedBall]
    rw [inter_eq_left.mpr (closedBall_subset_ball hR)]
  rw [he,tfSpace_closedBall_real (2*a) (by positivity)] at hb
  simpa only [mul_comm C] using hb

theorem local_mass_sq_le_gap {R a C : ℝ} (ha : 0 < a) (hR : 4*a < R)
    (T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) (hC : 0 ≤ C)
    (hc : ∀ᵐ x ∂ballMeasure R, ‖x‖ ≤ 2*a → tfPatchMinimizer R T hT Φ x ≤ C) :
    (∫ x in ball 0 a, σ x ∂ballMeasure R)^2 ≤
      2*(C*((2*a)^3*(Real.pi*4/3)))^2+256*a*tfPatchGap R T hT Φ σ := by
  let f := tfPatchMinimizer R T hT Φ
  let q := ∫ x, countPlateau a x*σ x ∂ballMeasure R
  let p := ∫ x, countPlateau a x*f x ∂ballMeasure R
  let m := ∫ x in ball 0 a, σ x ∂ballMeasure R
  let D := C*((2*a)^3*(Real.pi*4/3))
  have hm : 0 ≤ m := integral_nonneg_of_ae (ae_restrict_of_ae hσ)
  have hmq : m ≤ q := countPlateau_mass_lower ha hσ
  have hp : p ≤ D := countPlateau_mass_upper ha (by linarith) hC hc
  have hdiff : (∫ x, countPlateau a x*(σ-f) x ∂ballMeasure R) = q-p := by
    rw [integral_congr_ae ((Lp.coeFn_sub σ f).mono fun x hx => by
      change (σ-f) x = σ x-f x at hx
      rw [hx,mul_sub])]
    exact integral_sub (countPlateau_mul_integrable ha σ) (countPlateau_mul_integrable ha f)
  have hh := tfPatchGap_lipschitz_control (r := 2*a) (by positivity) (by linarith)
    T hT Φ hσ (countPlateau_lipschitz ha) (countPlateau_support ha)
  change (∫ x, countPlateau a x*(σ-f) x ∂ballMeasure R)^2 ≤ _ at hh
  rw [hdiff] at hh
  have he : 16*(2*a)^3*(a⁻¹)^2 = 128*a := by
    field_simp [ha.ne']
    ring
  change (q-p)^2 ≤ (16*(2*a)^3*(a⁻¹)^2)*tfPatchGap R T hT Φ σ at hh
  rw [he] at hh
  have hmd : m ≤ D+(q-p) := by linarith
  have hs := mul_self_le_mul_self hm hmd
  have hsq := sq_nonneg (D-(q-p))
  change m^2 ≤ 2*D^2+256*a*tfPatchGap R T hT Φ σ
  nlinarith

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RootMomentCauchyBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators

 def localCellRadius (y : Space) : ℝ := ‖y‖/100000

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfBallFunctionalConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology

open MeasureTheory Filter Set Metric Topology
section
open CoulombAtom

def tfPriceValue (Z μ : ℝ) : ℝ :=
  if hZ : 0 < Z then if hμ : 0 < μ then
    tfFunctional Z (tfPriceData hZ hμ).density + μ*((tfPriceData hZ hμ).mass-Z)
  else tfEnergy Z Z else tfEnergy Z Z

def tfPriceDeficit (Z μ : ℝ) : ℝ := μ^(3/4:ℝ)*tfUnitDeficit (Z/μ^(3/4:ℝ))

end

open Filter
open scoped Topology

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfCenteredPrice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
namespace CoulombAnalysis
open CoulombAtom

def tfCenteredPrice (Z μ : ℝ) : ℝ := if 0 < Z then tfPriceValue Z μ-tfEnergy Z Z else 0

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_WeakSommerfeldBoundsBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombAnalysis
open CoulombPDE

def radialCombinationSource (B e s : ℝ) (x : Space) : ℝ :=
  radialPower (-3) x*(12*B+(12+14*s+4*s^2)*e*radialPower (-s) x)

end CoulombAnalysis

end

end OAI
end


