-- Prove2me | Definitions.Def_OAIQ071C004
-- name    : OAIQ071C004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T05:06:24.667256+00:00
-- url     : https://prove2.me/theorems/6021d884-3154-47d0-949b-562e450642db
-- title:
--   Definitions bundle OAIQ071C004 of the split of OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 381 declarations of OpenAI's Lean: 94 definitions, 1 inductive type or structure, 3 instances and 283 theorems. The definitions and types are `OAI.CoulombAtom.FermionLipschitzMultiplier`, `OAI.CoulombAtom.FermionLipschitzMultiplier.apply`, `OAI.CoulombAtom.FormAvoids`, `OAI.CoulombAtom.FormsDisjoint`, `OAI.CoulombAtom.LipschitzMultiplier.apply`, `OAI.CoulombAtom.OneBodyIntegrable`, `OAI.CoulombAtom.Pauli.density`, `OAI.CoulombAtom.Pauli.oneParticleDensity`, `OAI.CoulombAtom.Pauli.spatialDensity`, `OAI.CoulombAtom.SmoothMultiplier.restrict`, `OAI.CoulombAtom.SmoothMultiplier.sumSquares`, `OAI.CoulombAtom.SubgroupFermion`, `OAI.CoulombAtom.averagedPacket`, `OAI.CoulombAtom.canonicalRealPacket`, `OAI.CoulombAtom.coherentDensity`, `OAI.CoulombAtom.coherentSpinKinetic`, `OAI.CoulombAtom.coreCoulombAt`, `OAI.CoulombAtom.coreCutLabels`, `OAI.CoulombAtom.coreDensityInteraction`, `OAI.CoulombAtom.coreKinetic`, `OAI.CoulombAtom.coreLeftLinear`, `OAI.CoulombAtom.coreLiftValue`, `OAI.CoulombAtom.coreNuclear`, `OAI.CoulombAtom.corePriceExcess`, `OAI.CoulombAtom.coreRepulsion`, `OAI.CoulombAtom.cosetWedgeTerm`, `OAI.CoulombAtom.crossRepulsion`, `OAI.CoulombAtom.cutCorePositions`, `OAI.CoulombAtom.dyadicUniformEventBudget`, `OAI.CoulombAtom.fermiMeasure`, `OAI.CoulombAtom.fermiRegion`, `OAI.CoulombAtom.finiteSmear`, `OAI.CoulombAtom.formMultiplierError`, `OAI.CoulombAtom.formNuclear`, `OAI.CoulombAtom.formOneBody`, `OAI.CoulombAtom.formRawDensity`, `OAI.CoulombAtom.formRawLaw`, `OAI.CoulombAtom.formRepulsion`, `OAI.CoulombAtom.hardyField`, `OAI.CoulombAtom.insertOrbital` and 55 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombIonization_Fermionic_Density`, `CoulombIonization_Fermionic_Multiplier2`, `CoulombIonization_Fermionic_ParticleDensity`, `CoulombIonization_Fermionic_Sum`, `CoulombIonization_FieldAnalysis_CellFieldNormalizationBarrier`, `CoulombIonization_FieldAnalysis_CoreFieldRegularity`, `CoulombIonization_FieldAnalysis_CubeRotations`, `CoulombIonization_FieldAnalysis_HardyField`, `CoulombIonization_FieldAnalysis_InnerExterior`, `CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier`, `CoulombIonization_FieldAnalysis_NeumannCounts`, `CoulombIonization_FieldAnalysis_NeumannFermions`, `CoulombIonization_FieldAnalysis_NeumannPhysical`, `CoulombIonization_FieldAnalysis_PauliMomentum`, `CoulombIonization_FieldAnalysis_PressureWeak`, `CoulombIonization_FieldAnalysis_RetainedFieldIdentity`, `CoulombIonization_FieldAnalysis_RetainedInnerMassBarrier`, `CoulombIonization_FieldAnalysis_RetainedMeasurable`, `CoulombIonization_FieldAnalysis_RetainedPatchDensity`, `CoulombIonization_FieldAnalysis_RetainedSmear`, `CoulombIonization_FieldAnalysis_ThinFieldConstantsBarrier`, `CoulombIonization_FieldAnalysis_ThinFieldFeedbackBarrier`, `CoulombIonization_FieldAnalysis_Vartheta`, `CoulombIonization_FormDomain_BlockEnergetics`, `CoulombIonization_FormDomain_CoherentLimitInsertion`, `CoulombIonization_FormDomain_CoreKinetic`, `CoulombIonization_FormDomain_CosetWedge`, `CoulombIonization_FormDomain_Form`, `CoulombIonization_FormDomain_FormBody`, `CoulombIonization_FormDomain_Forms`, `CoulombIonization_FormDomain_LipschitzResidualBase`, `CoulombIonization_FormDomain_LipschitzWeak`, `CoulombIonization_FormDomain_Restriction`, `CoulombIonization_FormDomain_ShiftedCoulombIntegrable`, `CoulombIonization_FormDomain_SumForm`, `CoulombIonization_FormDomain_TrialSmoothTest`, `CoulombIonization_FormDomain_WeakChangeVariables`, `CoulombIonization_Ionization_CoherentDerivatives`, `CoulombIonization_Ionization_ConditionalPricedUpper`, `CoulombIonization_Ionization_InsertionTermsDisjointSet`, `CoulombIonization_Ionization_IntegratedStability`, `CoulombIonization_Localization_ActualPosteriorCapBarrier`, `CoulombIonization_Localization_CanonicalRealPacketBarrier`, `CoulombIonization_Localization_CoherentKinetic`, `CoulombIonization_Localization_CoherentPackets`, `CoulombIonization_Localization_CoherentRealKinetic`, `CoulombIonization_Localization_CoreHistoryAverageBarrier`, `CoulombIonization_Localization_CoreHistoryCoordinatesBarrier`, `CoulombIonization_Localization_FermiDensity`, `CoulombIonization_Localization_FormRawLaw`, `CoulombIonization_Localization_GridPacketRadius`, `CoulombIonization_Localization_ObservationIntegral`, `CoulombIonization_Localization_PacketCloud`, `CoulombIonization_Localization_PacketComparison`, `CoulombIonization_Localization_PacketDensity`, `CoulombIonization_Localization_PacketDensityRadius`, `CoulombIonization_Localization_PacketInsert`, `CoulombIonization_Localization_RadialPacket`, `CoulombIonization_Localization_RadialPacketBase`, `CoulombIonization_Localization_SqrtMultiplier`, `CoulombIonization_RadialBounds_CoreHistoryFermionBarrier`, `CoulombIonization_RadialBounds_CoreMultiplierLiftBarrier`, `CoulombIonization_RadialBounds_CoulombSelfBound`, `CoulombIonization_RadialBounds_FermiMeasure`, `CoulombIonization_RadialBounds_LocalHistoryWeightsBarrier`, `CoulombIonization_RadialBounds_MomentumBall`, `CoulombIonization_RadialBounds_RadialCountSelection`, `CoulombIonization_RadialBounds_RadialInside`, `CoulombIonization_RadialBounds_SquareCompletion`, `CoulombIonization_RadialBounds_TailParticleCount`, `CoulombIonization_ThomasFermi_FlatFermionMollify`, `CoulombIonization_ThomasFermi_PatchRandomVariables`, `CoulombIonization_ThomasFermi_QuantumSectorNearMinimizer`, `CoulombIonization_Variational_AllSectorEnergy`, `CoulombIonization_Variational_CoherentDensity`, `CoulombIonization_Variational_CompactPotential`, `CoulombIonization_Variational_CorePriceExcess`, `CoulombIonization_Variational_CutCoreNumber`, `CoulombIonization_Variational_Electrostatic`, `CoulombIonization_Variational_HardySquare`, `CoulombIonization_Variational_InnerPotential`, `CoulombIonization_Variational_InsertionSwap`, `CoulombIonization_Variational_MasterWidth`, `CoulombIonization_Variational_PatchContinuity`, `CoulombIonization_Variational_PhaseBathtub`, `CoulombIonization_Variational_RetainedRepulsion`, `CoulombIonization_Variational_RotationCoreKernelIntegrable`, `CoulombIonization_Variational_Slices`, `CoulombIonization_Variational_SmearRepulsion`, `CoulombIonization_Variational_SmearingPotential`, `CoulombIonization_Variational_SmoothCompactIntegral`, `CoulombIonization_Variational_SmoothTransitionBound`, `CoulombIonization_Variational_Spatial`, `CoulombIonization_Variational_SpatialErrorWeight`, `CoulombIonization_Variational_SpatialProductFactor`, `CoulombIonization_Variational_SpatialRotation`, `CoulombIonization_Variational_SpinJoinEquiv`, `CoulombIonization_Variational_SumPairsHalf`, `CoulombIonization_Variational_TensorLp`, `CoulombIonization_Variational_TruncatedCoulomb`, `CoulombIonization_Variational_WeightedVariance`.
--
--   **Imports.** It imports the published bundle `Def_CoulombIonization`; the bundles `OAIQ071C000`, `OAIQ071C001` and `OAIQ071C002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ071C006`, `OAIQ071C007`, `OAIQ071C011` and `OAIQ071C012`; the statement `OAI_CoulombAtom_actual_priced_deficit_limit`.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C000
import Definitions.Def_OAIQ071C001
import Definitions.Def_OAIQ071C002

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakChangeVariables
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
section WeakChangeVariables
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in

lemma IsWeakDerivative.comp_linearEquiv {v w : E} {f g : E → ℂ}
    (hw : IsWeakDerivative v f g) (e : E ≃L[ℝ] E)
    (he : MeasurePreserving e) (hv : e w = v) :
    IsWeakDerivative w (f ∘ e) (g ∘ e) := by
  intro φ hφ hcφ
  let ψ : E → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp e.symm.contDiff
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph e.symm.toHomeomorph
  have hev : e.symm v = w := by rw [← hv, e.symm_apply_apply]
  have hd (x : E) : lineDeriv ℝ ψ (e x) v = lineDeriv ℝ φ x w := by
    rw [(hψ.differentiable (by simp) (e x)).lineDeriv_eq_fderiv,
      (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
    have hh := (hφ.differentiable (by simp) (e.symm (e x))).hasFDerivAt.comp
      (e x) (e.symm.hasFDerivAt)
    have hh' := congrArg (fun A : E →L[ℝ] ℝ => A v) hh.fderiv
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e.symm_apply_apply, hev] using hh'
  have hi1 : (∫ x, f (e x) * Complex.ofReal (lineDeriv ℝ ψ (e x) v)) =
      ∫ x, f x * Complex.ofReal (lineDeriv ℝ ψ x v) :=
    he.integral_comp e.toHomeomorph.measurableEmbedding
      (fun x => f x * Complex.ofReal (lineDeriv ℝ ψ x v))
  have hi2 : (∫ x, g (e x) * (ψ (e x) : ℂ)) = ∫ x, g x * (ψ x : ℂ) :=
    he.integral_comp e.toHomeomorph.measurableEmbedding
      (fun x => g x * (ψ x : ℂ))
  have hh := hw ψ hψ hcψ
  rw [← hi1, ← hi2] at hh
  simpa only [hd, ψ, Function.comp_apply, e.symm_apply_apply] using hh

end WeakChangeVariables

instance fermionSpace_completeSpace (N : ℕ) : CompleteSpace (fermionSpace N) :=
  (fermionSpace_isClosed N).completeSpace_coe

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SquareCompletion
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution

namespace CoulombAtom

lemma coordinate_radialField_fderiv {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (i : Fin N) (a : Fin 3) (x : Configuration N) :
    fderiv ℝ (fun y : Configuration N => radialField ε a (y i)) x (direction i a) =
      fderiv ℝ (radialField ε a) (x i) (EuclideanSpace.single a 1) := by
  have hh := ((radialField_smooth hε a).differentiable (by simp) (x i)).hasFDerivAt.comp x
    ((ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space).hasFDerivAt (x := x))
  change (fderiv ℝ ((radialField ε a) ∘
    (ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space)) x) _ = _
  rw [hh.fderiv]
  simp [direction]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_WeightedVariance
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma regularized_nuclear_bound {N : ℕ} (i : Fin N) {Z ε : ℝ}
    (hZ : 0 ≤ Z) (hε : 0 < ε) {f : Configuration N → ℂ}
    {g : Fin 3 → Configuration N → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : Configuration N → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (direction i a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    (∫ x, 2 * Z * regularizedCoulomb ε (x i) * ‖f x‖ ^ 2) ≤
      (∑ a, ∫ x, ‖g a x‖ ^ 2) + Z ^ 2 * (∫ x, ‖f x‖ ^ 2) := by
  let b : Fin 3 → Configuration N → ℝ := fun a x => Z * radialField ε a (x i)
  have hb (a : Fin 3) : ContDiff ℝ ∞ (b a) :=
    contDiff_const.mul ((radialField_smooth hε a).comp
      (ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space).contDiff)
  have hdb (a : Fin 3) (x : Configuration N) :
      fderiv ℝ (b a) x (direction i a) =
        Z * fderiv ℝ (radialField ε a) (x i) (EuclideanSpace.single a 1) := by
    have hh := ((radialField_smooth hε a).comp
      (ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space).contDiff
      ).differentiable (by simp) x
    change DifferentiableAt ℝ (fun y : Configuration N => radialField ε a (y i)) x at hh
    change (fderiv ℝ (fun y : Configuration N => Z * radialField ε a (y i)) x) _ = _
    rw [(hh.hasFDerivAt.const_mul Z).fderiv]
    simpa only [smul_apply, smul_eq_mul] using
      congrArg (Z * ·) (coordinate_radialField_fderiv hε i a x)
  refine weak_square_completion_bound hf hg (fun a => direction i a) hweak hb
    (B := fun _ => Z) (D := fun _ => Z * ε⁻¹)
    (BV := 2 * Z * ε⁻¹) (C := Z ^ 2)
    (V := fun x => 2 * Z * regularizedCoulomb ε (x i)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a x
    change ‖Z * radialField ε a (x i)‖ ≤ Z
    rw [norm_mul, Real.norm_of_nonneg hZ]
    exact (mul_le_mul_of_nonneg_left (radialField_norm_le hε a (x i)) hZ).trans_eq
      (mul_one Z)
  · intro a x
    rw [hdb, Real.norm_of_nonneg
      (mul_nonneg hZ (radialField_derivative_bounds hε a (x i)).1)]
    exact mul_le_mul_of_nonneg_left (radialField_derivative_bounds hε a (x i)).2 hZ
  · exact continuous_const.mul ((regularizedCoulomb_continuous hε).comp
      (continuous_apply i))
  · intro x
    exact mul_nonneg (by positivity) (regularizedCoulomb_nonneg ε (x i))
  · intro x
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (regularizedCoulomb_nonneg ε (x i)))]
    exact mul_le_mul_of_nonneg_left (regularizedCoulomb_le hε (x i)) (by positivity)
  · positivity
  · intro x
    simp only [b, mul_pow, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (sum_radialField_sq_le hε (x i))
      (sq_nonneg Z)).trans_eq (mul_one _)
  · intro x
    simp only [hdb, ← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left (radialField_divergence hε (x i)) hZ
    simpa only [regularizedCoulomb, mul_div_assoc, mul_left_comm Z 2, mul_assoc] using hh

lemma nuclear_bound {N : ℕ} (i : Fin N) {Z : ℝ} (hZ : 0 ≤ Z)
    {f : Configuration N → ℂ} {g : Fin 3 → Configuration N → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : Configuration N → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (direction i a))) =
        -(∫ y, g a y * (φ y : ℂ)))
    (hnu : Integrable (fun x => ‖f x‖ ^ 2 / ‖x i‖)) :
    2 * Z * (∫ x, ‖f x‖ ^ 2 / ‖x i‖) ≤
      (∑ a, ∫ x, ‖g a x‖ ^ 2) + Z ^ 2 * (∫ x, ‖f x‖ ^ 2) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have htε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let u : ℕ → Configuration N → ℝ :=
    fun n x => 2 * Z * regularizedCoulomb (ε n) (x i) * ‖f x‖ ^ 2
  have hi (n : ℕ) : Integrable (u n) := by
    apply hf.norm.integrable_sq.bdd_mul (c := 2 * Z * (ε n)⁻¹)
      (continuous_const.mul ((regularizedCoulomb_continuous (hε n)).comp
        (continuous_apply i))).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖2 * Z * regularizedCoulomb (ε n) (x i)‖ ≤ _
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity)
        (regularizedCoulomb_nonneg (ε n) (x i)))]
      exact mul_le_mul_of_nonneg_left (regularizedCoulomb_le (hε n) (x i)) (by positivity)
  rw [← integral_const_mul]
  apply integral_le_of_nonneg_ae_limit hi (hnu.const_mul (2 * Z))
  · intro n
    exact Eventually.of_forall fun x => mul_nonneg
      (mul_nonneg (by positivity) (regularizedCoulomb_nonneg (ε n) (x i))) (sq_nonneg _)
  · exact Eventually.of_forall fun x => mul_nonneg (by positivity) (by positivity)
  · exact Eventually.of_forall fun x => by
      have hh := ((regularizedCoulomb_tendsto htε (x i)).const_mul (2 * Z)
        ).mul_const (‖f x‖ ^ 2)
      have heq : 2 * Z * (1 / ‖x i‖) * ‖f x‖ ^ 2 =
          2 * Z * (‖f x‖ ^ 2 / ‖x i‖) := by ring
      simpa only [heq] using hh
  · exact add_nonneg (Finset.sum_nonneg fun a _ => integral_nonneg fun x => sq_nonneg _)
      (mul_nonneg (sq_nonneg Z) (integral_nonneg fun x => sq_nonneg _))
  · intro n
    exact regularized_nuclear_bound i hZ (hε n) hf hg hweak

theorem formEnergy_lower_bound {N : ℕ} {Z : ℝ} (hZ : 0 ≤ Z)
    {ψ : FormVector N} (hψ : FormAdmissible ψ) :
    -(N : ℝ) * Z ^ 2 / 2 ≤ formEnergy Z ψ := by
  rcases hψ with ⟨hf, hg, hw, _, hnorm, hnu, _⟩
  have hb (s : Spins N) (i : Fin N) := nuclear_bound i hZ (hf s) (hg s i)
    (hw s i) (hnu s i)
  have hs := Finset.sum_le_sum (s := Finset.univ) fun s _ =>
    Finset.sum_le_sum (s := Finset.univ) fun i _ => hb s i
  have heq : (∑ s : Spins N, ∑ i : Fin N,
      ((∑ a : Fin 3, ∫ x, ‖ψ.gradient s i a x‖ ^ 2) +
        Z ^ 2 * (∫ x, ‖ψ.value s x‖ ^ 2))) =
      (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖ψ.gradient s i a x‖ ^ 2) +
        (N : ℝ) * Z ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← Finset.mul_sum]
    rw [hnorm, mul_one]
  rw [heq] at hs
  simp only [← Finset.mul_sum] at hs
  have hr : 0 ≤ (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
      if i < j then (∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖) else 0) := by
    apply Finset.sum_nonneg
    intro s _
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact integral_nonneg fun x => div_nonneg (sq_nonneg _) (norm_nonneg _)
    · exact le_refl 0
  unfold formEnergy
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Slices
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma formMass_nonneg {N : ℕ} (ψ : FormVector N) : 0 ≤ formMass ψ :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

lemma formEnergy_scale {N : ℕ} (Z c : ℝ) (ψ : FormVector N) :
    formEnergy Z (scaleForm c ψ) = c ^ 2 * formEnergy Z ψ := by
  simp only [formEnergy, scaleForm, scaled_norm_sq, mul_div_assoc, integral_const_mul]
  have hi (s : Spins N) (i j : Fin N) :
      (if i < j then c ^ 2 * ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖ else 0) =
        c ^ 2 * (if i < j then ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖ else 0) := by
    split_ifs <;> simp
  simp_rw [hi, ← Finset.mul_sum]
  ring

lemma energy_le_form {N : ℕ} {Z : ℝ} (hZ : 0 ≤ Z)
    {ψ : FormVector N} (hψ : FormAdmissible ψ) : energy Z N ≤ formEnergy Z ψ := by
  by_cases hN : N = 0
  · subst N
    simp [energy, formEnergy]
  · rw [energy, ite_eq_right hN]
    exact csInf_le ⟨-(N : ℝ) * Z ^ 2 / 2, by
      rintro e ⟨φ,hφ,rfl⟩
      exact formEnergy_lower_bound hZ hφ⟩ ⟨ψ,hψ,rfl⟩


open Set Filter Topology InnerProductSpace Laplacian

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_SumForm
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
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
namespace CoulombAtom

def sumForm {ι : Type*} [Fintype ι] {N : ℕ} (ψ : ι → FormVector N) : FormVector N where
  value s x := ∑ k, (ψ k).value s x
  gradient s i a x := ∑ k, (ψ k).gradient s i a x

def FormsDisjoint {ι : Type*} {N : ℕ} (ψ : ι → FormVector N) : Prop :=
  (∀ k l, k ≠ l → ∀ s x, (ψ k).value s x = 0 ∨ (ψ l).value s x = 0) ∧
  (∀ k l, k ≠ l → ∀ s i a x,
    (ψ k).gradient s i a x = 0 ∨ (ψ l).gradient s i a x = 0)

end CoulombAtom

open MeasureTheory Filter
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Forms
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
section
variable {N : ℕ} {J : Type*} [Fintype J]
variable (p : J → SmoothMultiplier (sectorDirections N))
variable (hp : ∀ x, ∑ j, (p j).value x ^ 2 = 1)
include hp

def formMultiplierError (q : SmoothMultiplier (sectorDirections N)) (ψ : FormVector N) : ℝ :=
  (1 / 2 : ℝ) * ∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
    ∫ x, lineDeriv ℝ q.value x (direction i a) ^ 2 * ‖ψ.value s x‖ ^ 2

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

def spaceDirections (a : Fin 3) : Space := EuclideanSpace.single a 1

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_HardySquare
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

lemma square_completion_potential_bound {ι : Type*} [Fintype ι]
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (hf2 : MemLp f 2)
    {b : ι → E → ℝ} (hb : ∀ i, ContDiff ℝ ∞ (b i)) (v : ι → E)
    (hdf2 : ∀ i, MemLp (fun x => fderiv ℝ f x (v i)) 2)
    {B D : ι → ℝ} (hbb : ∀ i x, ‖b i x‖ ≤ B i)
    (hdb : ∀ i x, ‖fderiv ℝ (b i) x (v i)‖ ≤ D i)
    {V : E → ℝ} (hVq : Integrable (fun x => V x * ‖f x‖ ^ 2))
    (hdiv : ∀ x, V x ≤ ∑ i, (fderiv ℝ (b i) x (v i) - (b i x) ^ 2)) :
    (∫ x, V x * ‖f x‖ ^ 2) ≤ ∑ i, ∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2 := by
  have iq : Integrable (fun x => ‖f x‖ ^ 2) := hf2.norm.integrable_sq
  have ib (i : ι) : Integrable (fun x => (b i x) ^ 2 * ‖f x‖ ^ 2) :=
    iq.bdd_mul ((hb i).continuous.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbb i x) _)
  have idb (i : ι) : Integrable (fun x => fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2) :=
    iq.bdd_mul (((hb i).continuous_fderiv (by simp)).clm_apply continuous_const
      ).aestronglyMeasurable (Eventually.of_forall (hdb i))
  have isub (i : ι) : Integrable (fun x =>
      (fderiv ℝ (b i) x (v i) - (b i x) ^ 2) * ‖f x‖ ^ 2) := by
    convert (idb i).sub (ib i) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [Pi.sub_apply]
    ring
  calc
    _ ≤ ∫ x, ∑ i, (fderiv ℝ (b i) x (v i) - (b i x) ^ 2) * ‖f x‖ ^ 2 := by
      apply integral_mono hVq (integrable_finsetSum _ fun i _ => isub i)
      intro x
      simpa only [Finset.sum_mul] using
        mul_le_mul_of_nonneg_right (hdiv x) (sq_nonneg ‖f x‖)
    _ = ∑ i, ∫ x, (fderiv ℝ (b i) x (v i) - (b i x) ^ 2) * ‖f x‖ ^ 2 :=
      integral_finsetSum _ fun i _ => isub i
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have hn : 0 ≤ (∫ x : E, ‖fderiv ℝ f x (v i) + b i x • f x‖ ^ 2) :=
        integral_nonneg (fun x => sq_nonneg _)
      rw [square_completion_integral_of_memLp hf hf2 (hb i) (v i) (hdf2 i)
        (hbb i) (hdb i)] at hn
      simp only [sub_mul]
      rw [integral_sub (idb i) (ib i)]
      linarith

lemma weak_square_completion_potential_bound {ι : Type*} [Fintype ι]
    {f : E → ℂ} {g : ι → E → ℂ} (hf : MemLp f 2) (hg : ∀ i, MemLp (g i) 2)
    (v : ι → E)
    (hweak : ∀ i (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v i))) =
        -(∫ y, g i y * (φ y : ℂ)))
    {b : ι → E → ℝ} (hb : ∀ i, ContDiff ℝ ∞ (b i))
    {B D : ι → ℝ} (hbb : ∀ i x, ‖b i x‖ ≤ B i)
    (hdb : ∀ i x, ‖fderiv ℝ (b i) x (v i)‖ ≤ D i)
    {V : E → ℝ} (hV : Continuous V) (hV0 : ∀ x, 0 ≤ V x)
    {BV : ℝ} (hVC : ∀ x, ‖V x‖ ≤ BV)
    (hdiv : ∀ x, V x ≤ ∑ i, (fderiv ℝ (b i) x (v i) - (b i x) ^ 2)) :
    (∫ x, V x * ‖f x‖ ^ 2) ≤
      ∑ i, ∫ x, ‖g i x‖ ^ 2 := by
  let k : ℕ → E → ℝ := fun n => (shrinkingBump n).normed volume
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)
  let u : ℕ → E → ℂ := fun n => k n ⋆[L] f
  have hk (n : ℕ) : ContDiff ℝ ∞ (k n) := (shrinkingBump n).contDiff_normed
  have hkc (n : ℕ) : HasCompactSupport (k n) := (shrinkingBump n).hasCompactSupport_normed
  have hk0 (n : ℕ) : ∀ x, 0 ≤ k n x := (shrinkingBump n).nonneg_normed
  have hk1 (n : ℕ) : (∫ x, k n x) = 1 := (shrinkingBump n).integral_normed
  have hlocal := hf.locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hu (n : ℕ) : ContDiff ℝ ∞ (u n) :=
    (hkc n).contDiff_convolution_left L (hk n) hlocal
  have hu2 (n : ℕ) : MemLp (u n) 2 ∧
      (∫ x, ‖u n x‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 :=
    convolution_l2_contraction (hk n).continuous (hkc n) (hk0 n) (hk1 n) hf
  have hdu (n : ℕ) (i : ι) : (fun x => fderiv ℝ (u n) x (v i)) = k n ⋆[L] g i := by
    funext x
    exact mollified_weak_derivative (hk n) (hkc n) hlocal (v i) (hweak i) x
  have hdu2 (n : ℕ) (i : ι) : MemLp (fun x => fderiv ℝ (u n) x (v i)) 2 ∧
      (∫ x, ‖fderiv ℝ (u n) x (v i)‖ ^ 2) ≤ ∫ x, ‖g i x‖ ^ 2 := by
    have hh := convolution_l2_contraction (hk n).continuous (hkc n) (hk0 n) (hk1 n) (hg i)
    change MemLp (k n ⋆[L] g i) 2 ∧
      (∫ x, ‖(k n ⋆[L] g i) x‖ ^ 2) ≤ ∫ x, ‖g i x‖ ^ 2 at hh
    simpa only [← hdu n i] using hh
  have hVu (n : ℕ) : Integrable (fun x => V x * ‖u n x‖ ^ 2) :=
    (hu2 n).1.norm.integrable_sq.bdd_mul hV.aestronglyMeasurable (Eventually.of_forall hVC)
  have hVf : Integrable (fun x => V x * ‖f x‖ ^ 2) :=
    hf.norm.integrable_sq.bdd_mul hV.aestronglyMeasurable (Eventually.of_forall hVC)
  have ht : ∀ᵐ x, Tendsto (fun n => u n x) atTop (𝓝 (f x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      shrinkingBump_tendsto
      (Eventually.of_forall fun n => le_refl (2 * (shrinkingBump (E := E) n).rIn)) hlocal
  apply integral_le_of_nonneg_ae_limit hVu hVf
    (fun n => Eventually.of_forall fun x => mul_nonneg (hV0 x) (sq_nonneg _))
    (Eventually.of_forall fun x => mul_nonneg (hV0 x) (sq_nonneg _))
  · filter_upwards [ht] with x hx
    exact (hx.norm.pow 2).const_mul (V x)
  · exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  · intro n
    exact (square_completion_potential_bound (hu n) (hu2 n).1 hb v
      (fun i => (hdu2 n i).1) hbb hdb (hVu n) hdiv).trans
      (Finset.sum_le_sum fun i _ => (hdu2 n i).2)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_HardyField
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

def hardyField (ε : ℝ) (a : Fin 3) (x : Space) : ℝ := x a / (2 * hardyDenom ε x)

lemma hardyDenom_smooth (ε : ℝ) : ContDiff ℝ ∞ (hardyDenom ε) :=
  contDiff_id.norm_sq ℝ |>.add contDiff_const

lemma hardyField_smooth {ε : ℝ} (hε : 0 < ε) (a : Fin 3) :
    ContDiff ℝ ∞ (hardyField ε a) :=
  (EuclideanSpace.proj a).contDiff.div (contDiff_const.mul (hardyDenom_smooth ε))
    (fun x => mul_ne_zero (by norm_num) (hardyDenom_pos hε x).ne')

lemma hardyField_fderiv {ε : ℝ} (hε : 0 < ε) (a : Fin 3) (x : Space) :
    fderiv ℝ (hardyField ε a) x (EuclideanSpace.single a 1) =
      1 / (2 * hardyDenom ε x) - (x a) ^ 2 / (hardyDenom ε x) ^ 2 := by
  have ht := ((hasFDerivAt_id (𝕜 := ℝ) x).norm_sq).add_const ε
  have hi := (hasDerivAt_inv (hardyDenom_pos hε x).ne').comp_hasFDerivAt x ht
  have hp := (((EuclideanSpace.proj a).hasFDerivAt (x := x)).mul hi).const_mul (1 / 2 : ℝ)
  have he : hardyField ε a =
      (fun y => (1 / 2 : ℝ) * ((EuclideanSpace.proj a : Space → ℝ) *
        ((fun y : ℝ => y⁻¹) ∘ hardyDenom ε)) y) := by
    funext y
    simp only [hardyField, Pi.mul_apply, Function.comp_apply, EuclideanSpace.proj,
      PiLp.proj_apply, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, hp.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul,
    EuclideanSpace.proj, PiLp.proj_apply]
  dsimp [hardyDenom]
  simp only [Pi.single_eq_same]
  field_simp
  ring

lemma hardyField_norm_bound {ε : ℝ} (hε : 0 < ε) (a : Fin 3) (x : Space) :
    ‖hardyField ε a x‖ ≤ 1 + ε⁻¹ := by
  have hd := hardyDenom_pos hε x
  have hxd : |x a| ≤ hardyDenom ε x + 1 := by
    have hh := coordinate_sq_le x a
    have hsq := sq_nonneg (|x a| - 1 / 2)
    dsimp [hardyDenom]
    nlinarith [sq_abs (x a)]
  have he : ε ≤ hardyDenom ε x := by dsimp [hardyDenom]; nlinarith [sq_nonneg ‖x‖]
  change |x a / (2 * hardyDenom ε x)| ≤ _
  rw [abs_div, abs_of_pos (mul_pos (by norm_num) hd)]
  apply (div_le_iff₀ (mul_pos (by norm_num) hd)).mpr
  have hi : 1 ≤ ε⁻¹ * hardyDenom ε x := by
    calc
      1 = ε⁻¹ * ε := (inv_mul_cancel₀ hε.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hε.le)
  nlinarith [inv_pos.mpr hε]

lemma hardyField_derivative_bound {ε : ℝ} (hε : 0 < ε) (a : Fin 3) (x : Space) :
    ‖fderiv ℝ (hardyField ε a) x (EuclideanSpace.single a 1)‖ ≤ 2 / ε := by
  rw [hardyField_fderiv hε]
  have hd := hardyDenom_pos hε x
  have he : ε ≤ hardyDenom ε x := by dsimp [hardyDenom]; nlinarith [sq_nonneg ‖x‖]
  have hx : (x a) ^ 2 ≤ hardyDenom ε x := by
    have hh := coordinate_sq_le x a
    dsimp [hardyDenom]
    linarith
  have hq : 0 ≤ (x a) ^ 2 / (hardyDenom ε x) ^ 2 := by positivity
  have hq' : (x a) ^ 2 / (hardyDenom ε x) ^ 2 ≤ 1 / hardyDenom ε x := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    field_simp
    exact hx
  have hi : 1 / hardyDenom ε x ≤ 1 / ε := one_div_le_one_div_of_le hε he
  simp only [div_eq_mul_inv] at hi hq hq' ⊢
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hp : 0 ≤ 1 / (2 * hardyDenom ε x) := by positivity
    simp only [div_eq_mul_inv] at hp
    linarith [inv_pos.mpr hε]
  · have hh : 1 / (2 * hardyDenom ε x) ≤ 1 / hardyDenom ε x := by
      apply one_div_le_one_div_of_le hd
      linarith
    simp only [div_eq_mul_inv] at hh
    linarith [inv_pos.mpr hε]

lemma hardyField_potential {ε : ℝ} (hε : 0 < ε) (x : Space) :
    1 / (4 * hardyDenom ε x) ≤ ∑ a : Fin 3,
      (fderiv ℝ (hardyField ε a) x (EuclideanSpace.single a 1) - (hardyField ε a x) ^ 2) := by
  have hd := hardyDenom_pos hε x
  simp only [hardyField_fderiv hε, hardyField, div_pow, mul_pow, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div,
    sum_coordinate_sq]
  have he : 3 * (1 / (2 * hardyDenom ε x)) - ‖x‖ ^ 2 / hardyDenom ε x ^ 2 -
      ‖x‖ ^ 2 / (4 * hardyDenom ε x ^ 2) =
      1 / (4 * hardyDenom ε x) + 5 * ε / (4 * hardyDenom ε x ^ 2) := by
    field_simp
    dsimp [hardyDenom]
    ring
  norm_num only [Nat.cast_ofNat]
  rw [he]
  exact le_add_of_nonneg_right (by positivity)


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
lemma linear_hardyField_fderiv (P : E →L[ℝ] Space) (v : E) {ε : ℝ}
    (hε : 0 < ε) (a : Fin 3) (x : E) :
    fderiv ℝ (fun y => hardyField ε a (P y)) x v =
      fderiv ℝ (hardyField ε a) (P x) (P v) := by
  have hh := ((hardyField_smooth hε a).differentiable (by simp) (P x)).hasFDerivAt.comp x
    (P.hasFDerivAt (x := x))
  change (fderiv ℝ ((hardyField ε a) ∘ P) x) _ = _
  rw [hh.fderiv]
  rfl

lemma linear_regularized_hardy_bound (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1) {ε : ℝ}
    (hε : 0 < ε) {f : E → ℂ} {g : Fin 3 → E → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    (∫ x, (regularizedCoulomb ε (P x)) ^ 2 * ‖f x‖ ^ 2) ≤
      4 * ∑ a, ∫ x, ‖g a x‖ ^ 2 := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hs := weak_square_completion_potential_bound hf hg v hweak
    (b := fun a x => hardyField (ε ^ 2) a (P x))
    (fun a => (hardyField_smooth hε2 a).comp P.contDiff)
    (B := fun _ => 1 + (ε ^ 2)⁻¹) (D := fun _ => 2 / ε ^ 2)
    (fun a x => hardyField_norm_bound hε2 a (P x))
    (fun a x => by
      change ‖fderiv ℝ (fun y => hardyField (ε ^ 2) a (P y)) x (v a)‖ ≤ _
      rw [linear_hardyField_fderiv P _ hε2, hPv]
      exact hardyField_derivative_bound hε2 a (P x))
    (V := fun x => (regularizedCoulomb ε (P x)) ^ 2 / 4)
    (((regularizedCoulomb_continuous hε).comp P.continuous).pow 2 |>.div_const 4)
    (fun x => by positivity) (BV := (ε⁻¹) ^ 2 / 4)
    (fun x => by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ (regularizedCoulomb ε (P x)) ^ 2 / 4)]
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (regularizedCoulomb_nonneg ε (P x))
          (regularizedCoulomb_le hε (P x)) 2) (by norm_num))
    (fun x => by
      simp only [linear_hardyField_fderiv P _ hε2, hPv]
      apply le_trans _ (hardyField_potential hε2 (P x))
      have hd := hardyDenom_pos hε2 (P x)
      rw [regularizedCoulomb, regularizedRadius_sq, div_pow]
      change (‖P x‖ ^ 2 / (hardyDenom (ε ^ 2) (P x)) ^ 2) / 4 ≤
        1 / (4 * hardyDenom (ε ^ 2) (P x))
      apply (div_le_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
      apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
      field_simp
      dsimp [hardyDenom]
      nlinarith)
  have he : (fun x => (regularizedCoulomb ε (P x)) ^ 2 / 4 * ‖f x‖ ^ 2) =
      (fun x => (1 / 4 : ℝ) * ((regularizedCoulomb ε (P x)) ^ 2 * ‖f x‖ ^ 2)) := by
    funext x; ring
  rw [he, integral_const_mul] at hs
  linarith

lemma linear_hardy_integrable_bound (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1)
    {f : E → ℂ} {g : Fin 3 → E → ℂ} (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    Integrable (fun x => ‖f x‖ ^ 2 / ‖P x‖ ^ 2) ∧
    (∫ x, ‖f x‖ ^ 2 / ‖P x‖ ^ 2) ≤ 4 * ∑ a, ∫ x, ‖g a x‖ ^ 2 := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have htε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let u : ℕ → E → ℝ := fun n x => (regularizedCoulomb (ε n) (P x)) ^ 2 * ‖f x‖ ^ 2
  have hi (n : ℕ) : Integrable (u n) := by
    apply hf.norm.integrable_sq.bdd_mul (c := ((ε n)⁻¹) ^ 2)
      (((regularizedCoulomb_continuous (hε n)).comp P.continuous).pow 2).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖(regularizedCoulomb (ε n) (P x)) ^ 2‖ ≤ _
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (regularizedCoulomb_nonneg (ε n) (P x))
        (regularizedCoulomb_le (hε n) (P x)) 2
  have hu0 (n : ℕ) : ∀ᵐ x, 0 ≤ u n x :=
    Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hf0 : ∀ᵐ x, 0 ≤ ‖f x‖ ^ 2 / ‖P x‖ ^ 2 :=
    Eventually.of_forall fun x => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have ht : ∀ᵐ x, Tendsto (fun n => u n x) atTop (𝓝 (‖f x‖ ^ 2 / ‖P x‖ ^ 2)) := by
    exact Eventually.of_forall fun x => by
      have hh := ((regularizedCoulomb_tendsto htε (P x)).pow 2).mul_const (‖f x‖ ^ 2)
      have heq : (1 / ‖P x‖) ^ 2 * ‖f x‖ ^ 2 = ‖f x‖ ^ 2 / ‖P x‖ ^ 2 := by ring
      simpa only [heq] using hh
  have hb (n : ℕ) : (∫ x, u n x) ≤ 4 * ∑ a, ∫ x, ‖g a x‖ ^ 2 :=
    linear_regularized_hardy_bound P v hPv (hε n) hf hg hweak
  have hfin := integrable_of_nonneg_ae_limit hi
    ((hf.aestronglyMeasurable.norm.pow 2).div₀ (P.continuous.norm.pow 2).aestronglyMeasurable)
    hu0 hf0 ht hb
  exact ⟨hfin, integral_le_of_nonneg_ae_limit hi hfin hu0 hf0 ht
    (by positivity) hb⟩

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_TrialSmoothTest
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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
section TrialSmoothTest
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma integrable_norm_sq_div_of_support {f : E → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) {k : E → ℝ}
    (hk : Measurable k) (hkn : ∀ x, 0 ≤ k x) {ε : ℝ} (hε : 0 < ε)
    (hb : ∀ x, f x ≠ 0 → ε ≤ k x) : Integrable (fun x => ‖f x‖ ^ 2 / k x) := by
  have hsq : Integrable (fun x => ‖f x‖ ^ 2) :=
    (hf.norm.pow 2).integrable_of_hasCompactSupport (compact_norm_sq hcf)
  apply (hsq.div_const ε).mono' ((hf.norm.measurable.pow_const 2).div hk).aestronglyMeasurable
  filter_upwards [] with x
  change |‖f x‖ ^ 2 / k x| ≤ ‖f x‖ ^ 2 / ε
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (hkn x))]
  by_cases hx : f x = 0
  · simp [hx]
  · exact div_le_div_of_nonneg_left (sq_nonneg _) hε (hb x hx)
end TrialSmoothTest

theorem smoothForm_admissible {N : ℕ} {f : Configuration N → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (ha : ∀ (π : Equiv.Perm (Fin N)) x,
      f (x ∘ π) = (((Equiv.Perm.sign π : ℤ) : ℂ) * f x))
    (hn : (Fintype.card (Spins N) : ℝ) * (∫ x, ‖f x‖ ^ 2) = 1)
    {ε : ℝ} (hε : 0 < ε)
    (hnuc : ∀ x, f x ≠ 0 → ∀ i, ε ≤ ‖x i‖)
    (hpair : ∀ x, f x ≠ 0 → ∀ i j, i ≠ j → ε ≤ ‖x i - x j‖) :
    FormAdmissible (smoothForm f) := by
  refine ⟨fun _ => hf.continuous.memLp_of_hasCompactSupport hcf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s i a
    exact (smooth_derivative_continuous hf _).memLp_of_hasCompactSupport (compact_derivative hcf _)
  · intro s i a φ hφ hcφ
    exact smooth_weak_gradient hf hcf hφ hcφ _
  · intro π s
    exact Eventually.of_forall (ha π)
  · simpa only [smoothForm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hn
  · intro s i
    exact integrable_norm_sq_div_of_support hf.continuous hcf
      (continuous_apply i).norm.measurable (fun _ => norm_nonneg _) hε (fun x hx => hnuc x hx i)
  · intro s i j hij
    exact integrable_norm_sq_div_of_support hf.continuous hcf
      ((continuous_apply i).sub (continuous_apply j)).norm.measurable
      (fun _ => norm_nonneg _) hε (fun x hx => hpair x hx i j hij)

theorem exists_normalized_smoothForm {N : ℕ} {g : Configuration N → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (ha : ∀ (π : Equiv.Perm (Fin N)) x,
      g (x ∘ π) = (((Equiv.Perm.sign π : ℤ) : ℂ) * g x))
    {x₀ : Configuration N} (hx : g x₀ ≠ 0)
    {ε : ℝ} (hε : 0 < ε)
    (hnuc : ∀ x, g x ≠ 0 → ∀ i, ε ≤ ‖x i‖)
    (hpair : ∀ x, g x ≠ 0 → ∀ i j, i ≠ j → ε ≤ ‖x i - x j‖) :
    ∃ ψ : FormVector N, FormAdmissible ψ := by
  classical
  let n : ℝ := Fintype.card (Spins N)
  let I : ℝ := ∫ x, ‖g x‖ ^ 2
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hI : 0 < I :=
    (hg.continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (compact_norm_sq hcg) (fun x => sq_nonneg _) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have hnI : 0 < n * I := mul_pos hn hI
  let r : ℝ := (Real.sqrt (n * I))⁻¹
  have hr : r ^ 2 * (n * I) = 1 := by
    dsimp only [r]
    rw [inv_pow, Real.sq_sqrt hnI.le, inv_mul_cancel₀ hnI.ne']
  let f : Configuration N → ℂ := fun x => (r : ℂ) * g x
  refine ⟨smoothForm f, smoothForm_admissible (contDiff_const.mul hg) hcg.mul_left ?_ ?_ hε ?_ ?_⟩
  · intro π x
    dsimp only [f]
    rw [ha π x]
    ring
  · change n * (∫ x, ‖(r : ℂ) * g x‖ ^ 2) = 1
    simp_rw [norm_real_mul_sq]
    rw [integral_const_mul]
    change n * (r ^ 2 * I) = 1
    linarith only [hr]
  · intro x hf i
    exact hnuc x (fun h => hf (by simp only [f, h, mul_zero])) i
  · intro x hf i j hij
    exact hpair x (fun h => hf (by simp only [f, h, mul_zero])) i j hij

theorem formDomain_nonempty (N : ℕ) : ∃ ψ : FormVector N, FormAdmissible ψ := by
  apply exists_normalized_smoothForm
    (antisymmetrize_smooth (trialSeed_smooth N))
    (antisymmetrize_compact (trialSeed_compact N))
    (antisymmetrize_perm (trialSeed N))
    (x₀ := trialCenter N)
    (by rw [antisymmetrize_trialSeed_nonzero]; norm_num)
    (ε := 1) (by norm_num)
  · exact fun _ hx i => antisymmetrize_trialSeed_nucleus hx i
  · exact fun _ hx i j hij => antisymmetrize_trialSeed_pair hx i j hij

lemma formValues_nonempty (Z : ℝ) (N : ℕ) :
    Set.Nonempty {e | ∃ ψ : FormVector N, FormAdmissible ψ ∧ formEnergy Z ψ = e} := by
  obtain ⟨ψ, hψ⟩ := formDomain_nonempty N
  exact ⟨formEnergy Z ψ, ψ, hψ, rfl⟩

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Electrostatic
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma pairPotential_perm {N : ℕ} (x : Configuration N) (σ : Equiv.Perm (Fin N)) :
    pairPotential (x ∘ σ) = pairPotential x := by
  classical
  have hs (y : Configuration N) (i j : Fin N) :
      1 / ‖y i - y j‖ = 1 / ‖y j - y i‖ := by rw [norm_sub_rev]
  unfold pairPotential
  rw [triangular_sum_eq_half _ (hs _), triangular_sum_eq_half _ (hs _)]
  congr 1
  have ht (i j : Fin N) : (if i ≠ j then 1 / ‖(x ∘ σ) i - (x ∘ σ) j‖ else 0) =
      if σ i ≠ σ j then 1 / ‖x (σ i) - x (σ j)‖ else 0 := by
    simp only [ne_eq, σ.injective.eq_iff, Function.comp_apply]
  simp only [ht]
  rw [show (∑ i : Fin N, ∑ j : Fin N, if σ i ≠ σ j then 1 / ‖x (σ i) - x (σ j)‖ else 0) =
      (∑ i : Fin N, ∑ j : Fin N, if σ i ≠ j then 1 / ‖x (σ i) - x j‖ else 0) by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp σ (fun j => if σ i ≠ j then 1 / ‖x (σ i) - x j‖ else 0)]
  exact Equiv.sum_comp σ (fun i => ∑ j, if i ≠ j then 1 / ‖x i - x j‖ else 0)

lemma sorted_pairPotential_lower {N : ℕ} (x : Configuration N)
    (hs : Monotone (fun i => ‖x i‖)) (h0 : ∀ i, x i ≠ 0)
    (hi : Function.Injective x) :
    (∑ i : Fin N, (i.val : ℝ) / (2 * ‖x i‖)) ≤ pairPotential x := by
  classical
  unfold pairPotential
  apply Finset.sum_le_sum
  intro i _
  have hr : 0 < ‖x i‖ := norm_pos_iff.mpr (h0 i)
  calc
    _ = ∑ j : Fin N, if j < i then 1 / (2 * ‖x i‖) else 0 := by
      rw [← Finset.sum_filter]
      have he : Finset.univ.filter (fun j : Fin N => j < i) = Finset.Iio i := by
        ext j; simp
      rw [he, Finset.sum_const, Fin.card_Iio, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j < i
      · simp only [hj, ite_true]
        have hn : 0 < ‖x i - x j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hi.ne hj.ne'))
        apply one_div_le_one_div_of_le hn
        have ht := norm_sub_le (x i) (x j)
        linarith [hs hj.le]
      · simp only [hj, ite_false, le_refl]

lemma sorted_potential_stability {N M : ℕ} {Z : ℝ} (_hZ : 0 ≤ Z) (hM : 2 * Z ≤ M)
    (x : Configuration N) (hs : Monotone (fun i => ‖x i‖))
    (h0 : ∀ i, x i ≠ 0) (hi : Function.Injective x) :
    -(1 / 8 : ℝ) * (∑ i, 1 / ‖x i‖ ^ 2) - 2 * Z ^ 2 * M ≤
      -Z * (∑ i, 1 / ‖x i‖) + pairPotential x := by
  classical
  have hp := sorted_pairPotential_lower x hs h0 hi
  have hc := card_small_fin_le N M
  have ht (i : Fin N) : Z * (1 / ‖x i‖) - (i.val : ℝ) / (2 * ‖x i‖) ≤
      (1 / 8 : ℝ) * (1 / ‖x i‖ ^ 2) + (if i.val < M then 2 * Z ^ 2 else 0) := by
    have hr : 0 ≤ 1 / ‖x i‖ := by positivity
    have he : (i.val : ℝ) / (2 * ‖x i‖) = (i.val : ℝ) / 2 * (1 / ‖x i‖) := by ring
    rw [he]
    by_cases hm : i.val < M
    · rw [ite_eq_left hm]
      have hq := sq_nonneg (1 / ‖x i‖ - 4 * Z)
      have hval : 0 ≤ (i.val : ℝ) / 2 * (1 / ‖x i‖) := by positivity
      have heq : (1 / ‖x i‖) ^ 2 = 1 / ‖x i‖ ^ 2 := by ring
      nlinarith [heq]
    · rw [ite_eq_right hm]
      have hge : (M : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast Nat.le_of_not_gt hm
      have hh : 0 ≤ ((i.val : ℝ) / 2 - Z) * (1 / ‖x i‖) :=
        mul_nonneg (by linarith) hr
      have hsq : 0 ≤ 1 / ‖x i‖ ^ 2 := by positivity
      nlinarith
  have ht' := Finset.sum_le_sum (s := Finset.univ) fun i _ => ht i
  have he : (∑ i : Fin N, if i.val < M then 2 * Z ^ 2 else 0) =
      (Finset.univ.filter (fun i : Fin N => i.val < M)).card * (2 * Z ^ 2) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, he] at ht'
  have hc' : ((Finset.univ.filter (fun i : Fin N => i.val < M)).card : ℝ) ≤ M := by
    exact_mod_cast hc
  have hc'' := mul_le_mul_of_nonneg_right hc' (by positivity : 0 ≤ 2 * Z ^ 2)
  linarith

lemma potential_stability {N M : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) (hM : 2 * Z ≤ M)
    (x : Configuration N) (h0 : ∀ i, x i ≠ 0) (hi : Function.Injective x) :
    -(1 / 8 : ℝ) * (∑ i, 1 / ‖x i‖ ^ 2) - 2 * Z ^ 2 * M ≤
      -Z * (∑ i, 1 / ‖x i‖) + pairPotential x := by
  let σ := Tuple.sort (fun i => ‖x i‖)
  have hs : Monotone (fun i => ‖(x ∘ σ) i‖) := Tuple.monotone_sort (fun i => ‖x i‖)
  have hh := sorted_potential_stability hZ hM (x ∘ σ) hs (fun i => h0 (σ i))
    (hi.comp σ.injective)
  rw [pairPotential_perm] at hh
  change -(1 / 8 : ℝ) * (∑ i, 1 / ‖x (σ i)‖ ^ 2) - 2 * Z ^ 2 * M ≤
    -Z * (∑ i, 1 / ‖x (σ i)‖) + pairPotential x at hh
  rw [Equiv.sum_comp σ (fun i => 1 / ‖x i‖ ^ 2),
    Equiv.sum_comp σ (fun i => 1 / ‖x i‖)] at hh
  exact hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_IntegratedStability
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma nuclear_hardy {N : ℕ} (i : Fin N)
    {f : Configuration N → ℂ} {g : Fin 3 → Configuration N → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : Configuration N → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (direction i a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    Integrable (fun x => ‖f x‖ ^ 2 / ‖x i‖ ^ 2) ∧
    (∫ x, ‖f x‖ ^ 2 / ‖x i‖ ^ 2) ≤ 4 * ∑ a, ∫ x, ‖g a x‖ ^ 2 := by
  let P : Configuration N →L[ℝ] Space := ContinuousLinearMap.proj i
  have hp : ∀ a, P (direction i a) = EuclideanSpace.single a 1 := by
    intro a
    change direction i a i = _
    simp [direction]
  exact linear_hardy_integrable_bound P (direction i) hp hf hg hweak

lemma integrated_potential_stability {N M : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) (hM : 2 * Z ≤ M)
    {f : Configuration N → ℂ} (hf : MemLp f 2)
    (hnu : ∀ i, Integrable (fun x => ‖f x‖ ^ 2 / ‖x i‖))
    (hrep : ∀ i j, i ≠ j → Integrable (fun x => ‖f x‖ ^ 2 / ‖x i - x j‖))
    (hH : ∀ i, Integrable (fun x => ‖f x‖ ^ 2 / ‖x i‖ ^ 2)) :
    -(1 / 8 : ℝ) * (∑ i, ∫ x, ‖f x‖ ^ 2 / ‖x i‖ ^ 2) -
      2 * Z ^ 2 * M * (∫ x, ‖f x‖ ^ 2) ≤
      -Z * (∑ i, ∫ x, ‖f x‖ ^ 2 / ‖x i‖) +
        ∑ i, ∑ j, if i < j then (∫ x, ‖f x‖ ^ 2 / ‖x i - x j‖) else 0 := by
  classical
  have hpair (i j : Fin N) : Integrable
      (fun x => if j < i then ‖f x‖ ^ 2 / ‖x i - x j‖ else 0) := by
    by_cases h : j < i
    · simpa only [h, ite_true] using hrep i j h.ne'
    · simp only [h, ite_false]; exact integrable_zero _ ℝ volume
  have hp := integral_mono_ae
    (((integrable_finsetSum _ fun i _ => hH i).const_mul (-(1 / 8 : ℝ))).sub
      (hf.norm.integrable_sq.const_mul (2 * Z ^ 2 * M)))
    (((integrable_finsetSum _ fun i _ => hnu i).const_mul (-Z)).add
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hpair i j))
    (show ∀ᵐ x : Configuration N,
      -(1 / 8 : ℝ) * (∑ i, ‖f x‖ ^ 2 / ‖x i‖ ^ 2) - 2 * Z ^ 2 * M * ‖f x‖ ^ 2 ≤
        -Z * (∑ i, ‖f x‖ ^ 2 / ‖x i‖) +
          ∑ i, ∑ j, if j < i then ‖f x‖ ^ 2 / ‖x i - x j‖ else 0 from by
      filter_upwards [configuration_ae_nonsingular N] with x hx
      have hh := mul_le_mul_of_nonneg_right (potential_stability hZ hM x hx.1 hx.2)
        (sq_nonneg ‖f x‖)
      simp only [sub_mul, add_mul, pairPotential, Finset.sum_mul, ite_mul, zero_mul] at hh
      simp only [mul_assoc, Finset.sum_mul, Finset.mul_sum] at hh
      simpa only [Finset.mul_sum, div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm, mul_comm] using hh)
  simp only [Pi.sub_apply, Pi.add_apply] at hp
  rw [integral_sub
    ((integrable_finsetSum _ fun i _ => hH i).const_mul (-(1 / 8 : ℝ)))
    (hf.norm.integrable_sq.const_mul (2 * Z ^ 2 * M)),
    integral_add ((integrable_finsetSum _ fun i _ => hnu i).const_mul (-Z))
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hpair i j)] at hp
  simp only [integral_const_mul] at hp
  rw [integral_finsetSum _ (fun i _ => hH i), integral_finsetSum _ (fun i _ => hnu i),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hpair i j)] at hp
  simp_rw [integral_finsetSum _ (fun j _ => hpair _ j)] at hp
  have he : (∑ i : Fin N, ∑ j : Fin N,
      ∫ x, if j < i then ‖f x‖ ^ 2 / ‖x i - x j‖ else 0) =
      ∑ i : Fin N, ∑ j : Fin N,
        if i < j then (∫ x, ‖f x‖ ^ 2 / ‖x i - x j‖) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i < j
    · simp only [h, ite_true]
      congr 1; funext x; rw [norm_sub_rev]
    · simp only [h, ite_false, integral_zero]
  rwa [he] at hp

theorem formEnergy_uniform_lower_bound {N M : ℕ} {Z : ℝ}
    (hZ : 0 ≤ Z) (hM : 2 * Z ≤ M) {ψ : FormVector N} (hψ : FormAdmissible ψ) :
    -2 * Z ^ 2 * M ≤ formEnergy Z ψ := by
  rcases hψ with ⟨hf, hg, hw, _, hnorm, hnu, hrep⟩
  have hh (s : Spins N) (i : Fin N) := nuclear_hardy i (hf s) (hg s i) (hw s i)
  have hp (s : Spins N) := integrated_potential_stability hZ hM (hf s) (hnu s) (hrep s)
    (fun i => (hh s i).1)
  have ht (s : Spins N) : (∑ i : Fin N, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖ ^ 2) ≤
      4 * ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖ψ.gradient s i a x‖ ^ 2 := by
    simpa only [← Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hh s i).2)
  have hps := Finset.sum_le_sum (s := Finset.univ) fun s _ => hp s
  have hts := Finset.sum_le_sum (s := Finset.univ) fun s _ => ht s
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hnorm,
    mul_one] at hps hts
  unfold formEnergy
  nlinarith


theorem exists_priceMinimizes {E : ℕ → ℝ} (hE : BddBelow (Set.range E))
    {lam : ℝ} (hlam : 0 < lam) : ∃ n, PriceMinimizes E lam n := by
  obtain ⟨b, hb⟩ := hE
  obtain ⟨K, hK⟩ := exists_nat_gt ((E 0 - b) / lam)
  obtain ⟨n, hn, hmin⟩ := (Finset.range (K + 1)).exists_min_image
    (fun k : ℕ => E k + lam * k) (by simp)
  refine ⟨n, fun k => ?_⟩
  by_cases hk : k < K + 1
  · exact hmin k (Finset.mem_range.mpr hk)
  · have hk' : K ≤ k := by omega
    have hmin0 := hmin 0 (by simp)
    have hEb := hb ⟨k, rfl⟩
    have hK' := (div_lt_iff₀ hlam).mp hK
    have hcast : (K : ℝ) ≤ k := by exact_mod_cast hk'
    have hmul := mul_le_mul_of_nonneg_left hcast hlam.le
    simp only [Nat.cast_zero, mul_zero, add_zero] at hmin0
    linarith

theorem energy_uniform_lower_bound {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ) :
    -2 * Z ^ 2 * (⌈2 * Z⌉₊ : ℝ) ≤ energy Z N := by
  by_cases hN : N = 0
  · simp only [energy, hN, ↓reduceIte]
    have : 0 ≤ 2 * Z ^ 2 * (⌈2 * Z⌉₊ : ℝ) := by positivity
    linarith
  · rw [energy, ite_eq_right hN]
    apply le_csInf (formValues_nonempty Z N)
    rintro e ⟨ψ, hψ, rfl⟩
    exact formEnergy_uniform_lower_bound hZ (Nat.le_ceil (2 * Z)) hψ

theorem energy_range_bddBelow {Z : ℝ} (hZ : 0 ≤ Z) :
    BddBelow (Set.range (energy Z)) := by
  refine ⟨-2 * Z ^ 2 * (⌈2 * Z⌉₊ : ℝ), ?_⟩
  rintro e ⟨N, rfl⟩
  exact energy_uniform_lower_bound hZ N

theorem quantum_exists_priceMinimizes {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    ∃ n, PriceMinimizes (energy Z) lam n :=
  exists_priceMinimizes (energy_range_bddBelow hZ) hlam

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpinJoinEquiv
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace
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
namespace CoulombAtom

lemma sum_spin_join {N M : ℕ} (f : Spins (N+M) → ℝ) :
    ∑ t : Spins M, ∑ s : Spins N, f (joinLists s t) = ∑ u, f u := by
  have hh := Equiv.sum_comp (spinJoinEquiv N M) f
  rw [Fintype.sum_prod_type, Finset.sum_comm] at hh
  simpa only [spinJoinEquiv_apply] using hh

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_QuantumSectorNearMinimizer
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
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
namespace CoulombAtom

lemma quantum_price_le_sector {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) (N : ℕ) :
    priceEnergy (energy Z) lam ≤ energy Z N + lam * N := by
  obtain ⟨n, hn⟩ := quantum_exists_priceMinimizes hZ hlam
  rw [priceEnergy_eq_of_minimizes hn]
  exact hn N

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Spatial
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
section
variable {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)

lemma spatial_coordinate_derivative (b : Fin 2) (i j : Fin N) (a : Fin 3)
    (x : Configuration N) :
    lineDeriv ℝ (fun y : Configuration N => (p b).value (y i)) x (direction j a) =
      if j = i then lineDeriv ℝ (p b).value (x i) (spaceDirections a) else 0 := by
  classical
  have h := ((p b).regular.differentiable (by simp) (x i)).hasFDerivAt.comp
    x (electronProjection i).hasFDerivAt
  change HasFDerivAt (fun y : Configuration N => (p b).value (y i)) _ x at h
  rw [h.differentiableAt.lineDeriv_eq_fderiv, h.fderiv]
  change fderiv ℝ (p b).value (x i) (direction j a i) = _
  by_cases hij : j = i
  · subst j
    simp only [↓reduceIte, direction, Pi.single_eq_same, spaceDirections]
    exact ((p b).regular.differentiable (by simp) (x i)).lineDeriv_eq_fderiv.symm
  · simp [direction, hij, Ne.symm hij]

def spatialProductValue (b : Fin N → Fin 2) (x : Configuration N) : ℝ :=
  ∏ i, (p (b i)).value (x i)

lemma spatialProduct_regular (b : Fin N → Fin 2) :
    ContDiff ℝ ∞ (spatialProductValue p b) :=
  contDiff_prod fun i _ => (p (b i)).regular.comp (electronProjection i).contDiff

lemma spatialProduct_derivative (b : Fin N → Fin 2) (i : Fin N) (a : Fin 3)
    (x : Configuration N) :
    lineDeriv ℝ (spatialProductValue p b) x (direction i a) =
      (∏ k ∈ Finset.univ.erase i, (p (b k)).value (x k)) *
        lineDeriv ℝ (p (b i)).value (x i) (spaceDirections a) := by
  classical
  have hg (k : Fin N) := ((p (b k)).regular.differentiable (by simp) (x k)).hasFDerivAt.comp
    x (electronProjection k).hasFDerivAt
  have hh := HasFDerivAt.finsetProd (u := Finset.univ) (fun k _ => hg k)
  change HasFDerivAt (spatialProductValue p b) _ x at hh
  rw [hh.differentiableAt.lineDeriv_eq_fderiv, hh.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · congr 1
    change fderiv ℝ (p (b i)).value (x i) (direction i a i) = _
    rw [direction, Pi.single_eq_same]
    exact ((p (b i)).regular.differentiable (by simp) (x i)).lineDeriv_eq_fderiv.symm
  · intro k _ hki
    change _ * fderiv ℝ (p (b k)).value (x k) (direction i a k) = 0
    simp [direction, hki]
  · simp

variable (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)
include hp

lemma spatial_factor_bound (h : Fin 2) (x : Space) : |(p h).value x| ≤ 1 := by
  have hh : (p h).value x ^ 2 ≤ 1 := by
    rw [← hp x]
    exact Finset.single_le_sum (f := fun j : Fin 2 => (p j).value x ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ h)
  nlinarith [sq_abs ((p h).value x), abs_nonneg ((p h).value x)]

lemma spatial_product_sub_bound (b : Fin N → Fin 2) (x : Configuration N)
    (s : Finset (Fin N)) : |∏ i ∈ s, (p (b i)).value (x i)| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => spatial_factor_bound p hp _ _)

def spatialProduct (b : Fin N → Fin 2) : SmoothMultiplier (sectorDirections N) where
  value := spatialProductValue p b
  regular := spatialProduct_regular p b
  bound := ⟨1, fun x => spatial_product_sub_bound p hp b x Finset.univ⟩
  gradient_bound := by
    intro j
    obtain ⟨C,hC⟩ := (p (b j.1)).gradient_bound j.2
    refine ⟨C, fun x => ?_⟩
    change |lineDeriv ℝ (spatialProductValue p b) x (direction j.1 j.2)| ≤ C
    rw [spatialProduct_derivative, abs_mul]
    exact (mul_le_mul_of_nonneg_right (spatial_product_sub_bound p hp b x _)
      (abs_nonneg _)).trans (by simpa only [one_mul] using hC (x j.1))

lemma spatial_square_partition (x : Configuration N) :
    ∑ b : Fin N → Fin 2, (spatialProduct p hp b).value x ^ 2 = 1 := by
  change (∑ b : Fin N → Fin 2, (∏ i, (p (b i)).value (x i)) ^ 2) = 1
  simp_rw [← Finset.prod_pow]
  rw [← Fintype.prod_sum (f := fun (i : Fin N) (b : Fin 2) => (p b).value (x i) ^ 2)]
  simp only [hp, Finset.prod_const_one]

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

lemma spatialProduct_invariant {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (b : Fin N → Fin 2) (π : Equiv.Perm (Fin N)) (hb : b ∘ π = b) (x : Configuration N) :
    spatialProductValue p b (x ∘ π) = spatialProductValue p b x := by
  unfold spatialProductValue
  have hh : (∏ i, (p (b i)).value ((x ∘ π) i)) =
      ∏ i, (p (b (π i))).value (x (π i)) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [show b (π i) = b i from congrFun hb i]
    rfl
  exact hh.trans (Equiv.prod_comp π (fun i => (p (b i)).value (x i)))

def coreCutLabels (N M : ℕ) : Fin (N+M) → Fin 2 :=
  joinLists (fun _ : Fin N => 0) (fun _ : Fin M => 1)

lemma binary_product_square_sum {N : ℕ} (q : Fin N → Fin 2 → ℝ)
    (hq : ∀ k, ∑ h, q k h ^ 2 = 1) (i : Fin N) (r : Fin 2 → ℝ) :
    (∑ b : Fin N → Fin 2, ((∏ k ∈ Finset.univ.erase i, q k (b k)) * r (b i)) ^ 2) =
      ∑ h : Fin 2, r h ^ 2 := by
  classical
  have he (b : Fin N → Fin 2) :
      ((∏ k ∈ Finset.univ.erase i, q k (b k)) * r (b i)) ^ 2 =
        ∏ k : Fin N, if k = i then r (b k) ^ 2 else q k (b k) ^ 2 := by
    rw [mul_pow, ← Finset.prod_pow]
    rw [← Finset.prod_erase_mul Finset.univ
      (fun k => if k = i then r (b k) ^ 2 else q k (b k) ^ 2) (Finset.mem_univ i)]
    simp only [↓reduceIte]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    exact (ite_eq_right (Finset.mem_erase.mp hk).1).symm
  simp_rw [he]
  rw [← Fintype.prod_sum (f := fun (k : Fin N) (h : Fin 2) =>
    if k = i then r h ^ 2 else q k h ^ 2)]
  rw [Finset.prod_eq_single i]
  · simp
  · intro k _ hki
    simpa only [ite_eq_right hki] using hq k
  · simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SumPairsHalf
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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


lemma configurationReindex_preserving {M N : ℕ} (e : Fin M ≃ Fin N) :
    MeasurePreserving (configurationReindex e) :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin N => Space) e

lemma configurationReindex_direction {M N : ℕ} (e : Fin M ≃ Fin N)
    (i : Fin M) (a : Fin 3) :
    configurationReindex e (direction i a) = direction (e i) a := by
  rw [configurationReindex_apply]
  ext j k
  by_cases hj : j = e i
  · subst j; simp [direction]
  · have hi : e.symm j ≠ i := fun hh => hj (by rw [← hh, e.apply_symm_apply])
    simp [direction, hj, hi]

lemma integral_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (f : Configuration N → ℝ) :
    (∫ x : Configuration M, f (x ∘ e.symm)) = ∫ x, f x := by
  simpa only [configurationReindex_apply] using (configurationReindex_preserving e).integral_comp
    (configurationReindex e).toHomeomorph.measurableEmbedding f

lemma sum_spin_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (f : Spins N → ℝ) :
    (∑ s : Spins M, f (s ∘ e.symm)) = ∑ s, f s := by
  have he (s : Spins M) : (Equiv.piCongrLeft (fun _ : Fin N => Fin 2) e) s = s ∘ e.symm := by
    ext i
    simp [Equiv.piCongrLeft_apply]
  simpa only [he] using
    Equiv.sum_comp (Equiv.piCongrLeft (fun _ : Fin N => Fin 2) e) f

lemma formMass_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (ψ : FormVector N) :
    formMass (reindexForm e ψ) = formMass ψ := by
  unfold formMass
  have h (s : Spins M) : (∫ x, ‖(reindexForm e ψ).value s x‖ ^ 2) =
      ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 :=
    integral_reindex e (fun x => ‖ψ.value (s ∘ e.symm) x‖ ^ 2)
  simp_rw [h]
  exact sum_spin_reindex e (fun s => ∫ x, ‖ψ.value s x‖ ^ 2)

lemma nuclear_integral_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (ψ : FormVector N)
    (s : Spins M) (i : Fin M) :
    (∫ x, ‖(reindexForm e ψ).value s x‖ ^ 2 / ‖x i‖) =
      ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x (e i)‖ := by
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, reindexForm] using
    integral_reindex e (fun x => ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x (e i)‖)

lemma pair_integral_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (ψ : FormVector N)
    (s : Spins M) (i j : Fin M) :
    (∫ x, ‖(reindexForm e ψ).value s x‖ ^ 2 / ‖x i-x j‖) =
      ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x (e i)-x (e j)‖ := by
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, reindexForm] using
    integral_reindex e (fun x => ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x (e i)-x (e j)‖)

lemma pair_sum_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (ψ : FormVector N) (s : Spins M) :
    (∑ i : Fin M, ∑ j : Fin M, if i < j then
      ∫ x, ‖(reindexForm e ψ).value s x‖ ^ 2 / ‖x i-x j‖ else 0) =
    ∑ i : Fin N, ∑ j : Fin N, if i < j then
      ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x i-x j‖ else 0 := by
  classical
  rw [sum_pairs_half _ (fun i j => integral_congr_ae
    (Filter.Eventually.of_forall fun x => by rw [norm_sub_rev (x i) (x j)]))]
  rw [sum_pairs_half _ (fun i j => integral_congr_ae
    (Filter.Eventually.of_forall fun x => by rw [norm_sub_rev (x i) (x j)]))]
  simp_rw [pair_integral_reindex e]
  congr 1
  rw [← Equiv.sum_comp e (fun i => ∑ j : Fin N, if i ≠ j then
    ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x i-x j‖ else 0)]
  apply Finset.sum_congr rfl; intro i _
  rw [← Equiv.sum_comp e (fun j => if e i ≠ j then
    ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x (e i)-x j‖ else 0)]
  simp only [ne_eq, e.injective.eq_iff]

theorem formEnergy_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (ψ : FormVector N) (Z : ℝ) :
    formEnergy Z (reindexForm e ψ) = formEnergy Z ψ := by
  unfold formEnergy
  have hk (s : Spins M) : (∑ i : Fin M, ∑ a : Fin 3,
      ∫ x, ‖(reindexForm e ψ).gradient s i a x‖ ^ 2) =
      ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖ψ.gradient (s ∘ e.symm) i a x‖ ^ 2 := by
    have h (i : Fin M) (a : Fin 3) :
        (∫ x, ‖(reindexForm e ψ).gradient s i a x‖ ^ 2) =
        ∫ x, ‖ψ.gradient (s ∘ e.symm) (e i) a x‖ ^ 2 :=
      integral_reindex e (fun x => ‖ψ.gradient (s ∘ e.symm) (e i) a x‖ ^ 2)
    simp_rw [h]
    exact Equiv.sum_comp e (fun i => ∑ a : Fin 3, ∫ x, ‖ψ.gradient (s ∘ e.symm) i a x‖ ^ 2)
  have hn (s : Spins M) : (∑ i : Fin M,
      ∫ x, ‖(reindexForm e ψ).value s x‖ ^ 2 / ‖x i‖) =
      ∑ i : Fin N, ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x i‖ := by
    simp_rw [nuclear_integral_reindex e]
    exact Equiv.sum_comp e (fun i => ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x i‖)
  rw [show (∑ s, ∑ i, ∑ a, ∫ x, ‖(reindexForm e ψ).gradient s i a x‖ ^ 2) =
    ∑ s : Spins N, ∑ i, ∑ a, ∫ x, ‖ψ.gradient s i a x‖ ^ 2 by
      simp_rw [hk]; exact sum_spin_reindex e (fun s => ∑ i, ∑ a, ∫ x, ‖ψ.gradient s i a x‖ ^ 2)]
  rw [show (∑ s, ∑ i, ∫ x, ‖(reindexForm e ψ).value s x‖ ^ 2 / ‖x i‖) =
    ∑ s : Spins N, ∑ i, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖ by
      simp_rw [hn]; exact sum_spin_reindex e (fun s => ∑ i, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖)]
  congr 1
  simp_rw [pair_sum_reindex e]
  exact sum_spin_reindex e (fun s => ∑ i, ∑ j, if i < j then
    ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_TensorLp
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F]
  [(volume : Measure F).IsAddHaarMeasure]

lemma IsWeakDerivative.tensor_left {v : E} {f df : E → ℂ} {g : F → ℂ}
    (hwd : IsWeakDerivative v f df) (hf : MemLp f 2) (hdf : MemLp df 2)
    (hg : MemLp g 2) :
    IsWeakDerivative (v,0) (fun p : E × F => f p.1*g p.2)
      (fun p => df p.1*g p.2) := by
  intro φ hφ hcφ
  have hi1 := (memLp_tensor hf hg).integrable_mul
    (test_deriv_memLp hφ hcφ (v,0))
  have hi2 := (memLp_tensor hdf hg).integrable_mul (test_memLp hφ hcφ)
  have hp1 := integral_prod_symm _ hi1
  have hp2 := integral_prod_symm _ hi2
  simp only [Pi.mul_apply] at hp1 hp2
  rw [Measure.volume_eq_prod E F, hp1, hp2, ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    have ht : ContDiff ℝ ∞ (fun x => φ (x,y)) := hφ.comp (contDiff_id.prodMk contDiff_const)
    have hct : HasCompactSupport (fun x => φ (x,y)) := by
      apply HasCompactSupport.of_support_subset_isCompact (hcφ.image continuous_fst)
      intro x hx
      exact ⟨(x,y), subset_tsupport φ hx, rfl⟩
    have hh := hwd (fun x => φ (x,y)) ht hct
    simp_rw [lineDeriv_slice_left hφ] at hh
    simpa only [mul_right_comm (f _) (g y), mul_right_comm (df _) (g y),
      integral_mul_const, neg_mul] using congrArg (fun c => c*g y) hh

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


lemma configurationJoin_symm_preserving (N M : ℕ) :
    MeasurePreserving (configurationJoin N M).symm :=
  MeasurePreserving.symm (configurationJoin N M).toHomeomorph.toMeasurableEquiv
    (configurationJoin_preserving N M)


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_InsertionSwap
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
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

lemma corePerm_last {N : ℕ} (π : Equiv.Perm (Fin N)) :
    corePerm 1 π (Fin.last N) = Fin.last N := by
  have hh : (Fin.last N : Fin (N+1)) = finSumFinEquiv (Sum.inr (0 : Fin 1)) := by
    ext; simp
  rw [hh]
  simp [corePerm, Equiv.permCongr]

lemma corePerm_castSucc {N : ℕ} (π : Equiv.Perm (Fin N)) (i : Fin N) :
    corePerm 1 π i.castSucc = (π i).castSucc := by
  change corePerm 1 π (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inl (π i))
  simp [corePerm,Equiv.permCongr]

lemma perm_fixed_last_is_core {N : ℕ} (κ : Equiv.Perm (Fin (N+1)))
    (hκ : κ (Fin.last N) = Fin.last N) : ∃ ρ : Equiv.Perm (Fin N), κ = corePerm 1 ρ := by
  let e := finSuccAboveEquiv (Fin.last N)
  have hh (i : Fin (N+1)) : κ i ≠ Fin.last N ↔ i ≠ Fin.last N := by
    rw [← hκ, κ.injective.ne_iff, hκ]
  let ρ := e.symm.permCongr (κ.subtypePerm hh)
  refine ⟨ρ, ?_⟩
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · exact hκ.trans (corePerm_last ρ).symm
  · rw [corePerm_castSucc]
    have he (j : Fin N) : (e j).val = j.castSucc := by
      simp [e, finSuccAboveEquiv, Fin.succAbove_last]
    have hp : κ ((e i).val) = (e (ρ i)).val := by
      simp [ρ, Equiv.permCongr, Equiv.Perm.subtypePerm]
    simpa only [he] using hp

lemma insertion_coset {N : ℕ} (π : Equiv.Perm (Fin (N+1))) (i : Fin (N+1)) :
    ∃ ρ : Equiv.Perm (Fin N), π * insertionSwap i = insertionSwap (π i) * corePerm 1 ρ := by
  let κ := (insertionSwap (π i))⁻¹ * (π * insertionSwap i)
  have hk : κ (Fin.last N) = Fin.last N := by
    simp only [κ, Equiv.Perm.coe_mul, Function.comp_apply, insertionSwap_last,
      Equiv.Perm.inv_def, insertionSwap_symm, insertionSwap_self]
  obtain ⟨ρ,hρ⟩ := perm_fixed_last_is_core κ hk
  refine ⟨ρ, ?_⟩
  rw [← hρ]
  simp only [κ, mul_inv_cancel_left]


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


def wedgeForm {N : ℕ} (T : FormVector (N+1)) : FormVector (N+1) :=
  sumForm (insertionTerm T)

lemma formEnergy_insertionTerm {N : ℕ} (T : FormVector (N+1)) (i : Fin (N+1)) (Z : ℝ) :
    formEnergy Z (insertionTerm T i) = formEnergy Z T := by
  rw [insertionTerm,formEnergy_scale,formEnergy_reindex,real_sign_sq,one_mul]


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Form
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma insertionTerm_zero {N : ℕ} {T : FormVector (N+1)} {x : Configuration (N+1)}
    (i : Fin (N+1)) (hx : FormZeroAt T (x ∘ insertionSwap i)) :
    FormZeroAt (insertionTerm T i) x := by
  intro s
  constructor
  · rw [insertionTerm_value,(hx _).1,mul_zero]
  · intro j a
    change _ * T.gradient (s ∘ (insertionSwap i).symm) (insertionSwap i j) a
      (x ∘ (insertionSwap i).symm) = 0
    rw [insertionSwap_symm,(hx _).2,mul_zero]

lemma tensor_zero_left {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    {x : Configuration (N+M)} (hx : FormZeroAt ψ (leftList x)) :
    FormZeroAt (tensorForm ψ φ) x := by
  intro s
  constructor
  · change ψ.value _ _ * _ = 0
    rw [(hx _).1,zero_mul]
  · intro i a
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i =>
      simp only [tensorForm,Equiv.symm_apply_apply,Sum.elim_inl,(hx _).2,zero_mul]
    | inr i =>
      simp only [tensorForm,Equiv.symm_apply_apply,Sum.elim_inr,(hx _).1,zero_mul]

lemma tensor_zero_right {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    {x : Configuration (N+M)} (hx : FormZeroAt φ (rightList x)) :
    FormZeroAt (tensorForm ψ φ) x := by
  intro s
  constructor
  · change _ * φ.value _ _ = 0
    rw [(hx _).1,mul_zero]
  · intro i a
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i =>
      simp only [tensorForm,Equiv.symm_apply_apply,Sum.elim_inl,(hx _).1,mul_zero]
    | inr i =>
      simp only [tensorForm,Equiv.symm_apply_apply,Sum.elim_inr,(hx _).2,mul_zero]


open MeasureTheory Filter
open scoped BigOperators


def formNuclear {N : ℕ} (ψ : FormVector N) : ℝ :=
  ∑ s, ∑ i, ∫ x, ‖ψ.value s x‖^2 / ‖x i‖

def formRepulsion {N : ℕ} (ψ : FormVector N) : ℝ :=
  ∑ s, ∑ i, ∑ j, if i < j then ∫ x, ‖ψ.value s x‖^2 / ‖x i-x j‖ else 0

def tensorCross {N : ℕ} (ψ : FormVector N) (φ : FormVector 1) : ℝ :=
  ∑ s : Spins N, ∑ t : Spins 1, ∑ i : Fin N,
    ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i.castSucc-z (Fin.last N)‖


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_InsertionTermsDisjointSet
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

lemma insertionTerms_disjoint_set {N : ℕ} {T : FormVector (N+1)} (S : Set Space)
    (hc : ∀ x (j : Fin N), x j.castSucc ∈ S → FormZeroAt T x)
    (he : ∀ x, x (Fin.last N) ∉ S → FormZeroAt T x) :
    FormsDisjoint (insertionTerm T) := by
  have hh (k l : Fin (N+1)) (hkl : k ≠ l) (x : Configuration (N+1)) :
      FormZeroAt (insertionTerm T k) x ∨ FormZeroAt (insertionTerm T l) x := by
    by_cases hk : x k ∈ S
    · right
      have hne : insertionSwap l k ≠ Fin.last N := by
        intro h
        have ht := congrArg (insertionSwap l) h
        exact hkl (by simpa only [insertionSwap,Equiv.swap_apply_self,Equiv.swap_apply_right] using ht)
      obtain ⟨j,hj⟩ := Fin.exists_castSucc_eq.mpr hne
      apply insertionTerm_zero l
      apply hc _ j
      simpa only [Function.comp_apply,hj,insertionSwap,Equiv.swap_apply_self] using hk
    · left
      exact insertionTerm_zero k (he _ (by simpa only [Function.comp_apply,insertionSwap_last] using hk))
  constructor
  · intro k l hkl s x
    rcases hh k l hkl x with hk | hl
    · exact Or.inl (hk s).1
    · exact Or.inr (hl s).1
  · intro k l hkl s i a x
    rcases hh k l hkl x with hk | hl
    · exact Or.inl ((hk s).2 i a)
    · exact Or.inr ((hl s).2 i a)

lemma tensor_insertion_disjoint_set {N : ℕ} (ψ : FormVector N) (φ : FormVector 1)
    (S : Set Space)
    (hc : ∀ x i, x i ∈ S → FormZeroAt ψ x)
    (he : ∀ x, x 0 ∉ S → FormZeroAt φ x) :
    FormsDisjoint (insertionTerm (tensorForm ψ φ)) := by
  apply insertionTerms_disjoint_set S
  · intro x i hx
    exact tensor_zero_left ψ φ (hc _ i hx)
  · intro x hx
    exact tensor_zero_right ψ φ (he _ hx)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SmoothTransitionBound
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

def radialParameter (y : Space) (t b : ℝ) (x : Space) : ℝ :=
  (‖x-y‖ ^ 2 - t ^ 2) / ((t+b)^2-t^2)

def radialPhase (y : Space) (t b : ℝ) (x : Space) : ℝ :=
  (Real.pi / 2) * Real.smoothTransition (radialParameter y t b x)

lemma radialParameter_regular (y : Space) (t b : ℝ) : ContDiff ℝ ∞ (radialParameter y t b) :=
  (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const).div_const _

lemma radialPhase_regular (y : Space) (t b : ℝ) : ContDiff ℝ ∞ (radialPhase y t b) :=
  contDiff_const.mul ((Real.smoothTransition.contDiff (n := ⊤)).comp (radialParameter_regular y t b))

lemma radialParameter_derivative (y : Space) (t b : ℝ) (x v : Space) :
    lineDeriv ℝ (radialParameter y t b) x v =
      2 * inner ℝ (x-y) v / ((t+b)^2-t^2) := by
  have hh := (((hasFDerivAt_id x).sub_const y).norm_sq.sub_const (t^2)).mul_const (((t+b)^2-t^2)⁻¹)
  change HasFDerivAt (radialParameter y t b) _ x at hh
  rw [hh.differentiableAt.lineDeriv_eq_fderiv, hh.fderiv]
  simp [smul_eq_mul, div_eq_mul_inv, inner_sub_left]
  ring

lemma radialPhase_derivative (y : Space) (t b : ℝ) (x v : Space) :
    lineDeriv ℝ (radialPhase y t b) x v =
      (Real.pi / 2) * deriv Real.smoothTransition (radialParameter y t b x) *
        (2 * inner ℝ (x-y) v / ((t+b)^2-t^2)) := by
  have hp := (radialParameter_regular y t b).differentiable (by simp) x
  have hs := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
    (radialParameter y t b x)).hasDerivAt
  have hh := (hs.comp_hasFDerivAt x hp.hasFDerivAt).const_mul (Real.pi/2)
  change HasFDerivAt (radialPhase y t b) _ x at hh
  rw [hh.differentiableAt.lineDeriv_eq_fderiv, hh.fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [← hp.lineDeriv_eq_fderiv, radialParameter_derivative]
  ring

lemma radialPhase_derivative_le (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) (a : Fin 3) :
    |lineDeriv ℝ (radialPhase y t b) x (spaceDirections a)| ≤
      Real.pi * smoothTransitionBound / b := by
  rw [radialPhase_derivative]
  have hD := radial_denominator_pos ht hb
  have hC := smoothTransitionBound_pos
  by_cases hlow : radialParameter y t b x < 0
  · rw [smoothTransition_deriv_zero_of_neg hlow]
    simp only [mul_zero, zero_mul, abs_zero]
    positivity
  by_cases hhigh : 1 < radialParameter y t b x
  · rw [smoothTransition_deriv_zero_of_one_lt hhigh]
    simp only [mul_zero, zero_mul, abs_zero]
    positivity
  have hr : ‖x-y‖ ≤ t+b := by
    have hh : (‖x-y‖ ^ 2 - t^2) ≤ (t+b)^2-t^2 :=
      (div_le_one hD).mp (le_of_not_gt hhigh)
    nlinarith [norm_nonneg (x-y)]
  have hi : |inner ℝ (x-y) (spaceDirections a)| ≤ t+b := by
    calc
      _ ≤ ‖x-y‖ * ‖spaceDirections a‖ := by simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) (x-y) (spaceDirections a))
      _ = ‖x-y‖ := by simp [spaceDirections]
      _ ≤ t+b := hr
  have hd : |2 * inner ℝ (x-y) (spaceDirections a) / ((t+b)^2-t^2)| ≤
      2 * (t+b) / ((t+b)^2-t^2) := by
    rw [abs_div, abs_mul, abs_of_pos hD, abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by norm_num)) hD.le
  rw [abs_mul, abs_mul, abs_of_pos (div_pos Real.pi_pos (by norm_num))]
  calc
    _ ≤ ((Real.pi / 2) * smoothTransitionBound) * (2 * (t+b) / ((t+b)^2-t^2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (smoothTransition_deriv_le _) (by positivity))
        hd (abs_nonneg _) (by positivity)
    _ = (Real.pi * smoothTransitionBound) * ((t+b) / ((t+b)^2-t^2)) := by ring
    _ ≤ (Real.pi * smoothTransitionBound) * (1/b) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (div_le_div_iff₀ hD hb).mpr
      nlinarith [mul_nonneg ht hb.le]
    _ = _ := by ring

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpatialErrorWeight
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom
variable {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ h : Fin 2, (p h).value x ^ 2 = 1)

lemma spatial_derivative_square_sum (x : Configuration N) (i : Fin N) (a : Fin 3) :
    (∑ b : Fin N → Fin 2, lineDeriv ℝ (spatialProduct p hp b).value x (direction i a) ^ 2) =
      ∑ h : Fin 2, lineDeriv ℝ (p h).value (x i) (spaceDirections a) ^ 2 := by
  change (∑ b : Fin N → Fin 2, lineDeriv ℝ (spatialProductValue p b) x (direction i a) ^ 2) = _
  simp_rw [spatialProduct_derivative]
  exact binary_product_square_sum (fun k h => (p h).value (x k)) (fun k => hp (x k)) i
    (fun h => lineDeriv ℝ (p h).value (x i) (spaceDirections a))

def spatialErrorWeight (x : Space) : ℝ :=
  ∑ a : Fin 3, ∑ h : Fin 2, lineDeriv ℝ (p h).value x (spaceDirections a) ^ 2

def weightedParticleCount (ψ : FormVector N) (w : Space → ℝ) : ℝ :=
  ∑ s : Spins N, ∑ i : Fin N, ∫ x, w (x i) * ‖ψ.value s x‖ ^ 2

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialInside
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

lemma radial_cos_derivative (y : Space) (t b : ℝ) (x v : Space) :
    lineDeriv ℝ (fun z => Real.cos (radialPhase y t b z)) x v =
      -Real.sin (radialPhase y t b x) * lineDeriv ℝ (radialPhase y t b) x v := by
  have h := (radialPhase_regular y t b).differentiable (by simp) x
  rw [h.hasFDerivAt.cos.differentiableAt.lineDeriv_eq_fderiv, h.hasFDerivAt.cos.fderiv,
    h.lineDeriv_eq_fderiv]
  simp only [smul_apply, smul_eq_mul]

lemma radial_sin_derivative (y : Space) (t b : ℝ) (x v : Space) :
    lineDeriv ℝ (fun z => Real.sin (radialPhase y t b z)) x v =
      Real.cos (radialPhase y t b x) * lineDeriv ℝ (radialPhase y t b) x v := by
  have h := (radialPhase_regular y t b).differentiable (by simp) x
  rw [h.hasFDerivAt.sin.differentiableAt.lineDeriv_eq_fderiv, h.hasFDerivAt.sin.fderiv,
    h.lineDeriv_eq_fderiv]
  simp only [smul_apply, smul_eq_mul]

def radialInside (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    SmoothMultiplier spaceDirections where
  value x := Real.cos (radialPhase y t b x)
  regular := (radialPhase_regular y t b).cos
  bound := ⟨1, fun x => Real.abs_cos_le_one _⟩
  gradient_bound := by
    intro a
    refine ⟨Real.pi * smoothTransitionBound / b, fun x => ?_⟩
    rw [radial_cos_derivative, abs_mul, abs_neg]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
      (by simpa only [one_mul] using radialPhase_derivative_le y ht hb x a)

def radialOutside (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    SmoothMultiplier spaceDirections where
  value x := Real.sin (radialPhase y t b x)
  regular := (radialPhase_regular y t b).sin
  bound := ⟨1, fun x => Real.abs_sin_le_one _⟩
  gradient_bound := by
    intro a
    refine ⟨Real.pi * smoothTransitionBound / b, fun x => ?_⟩
    rw [radial_sin_derivative, abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans
      (by simpa only [one_mul] using radialPhase_derivative_le y ht hb x a)

def radialCut (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    Fin 2 → SmoothMultiplier spaceDirections :=
  ![radialInside y ht hb, radialOutside y ht hb]

lemma radialPhase_zero {y x : Space} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hx : ‖x-y‖ ≤ t) : radialPhase y t b x = 0 := by
  have hp : radialParameter y t b x ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg (x-y)])
      (radial_denominator_pos ht hb).le
  simp only [radialPhase, Real.smoothTransition.zero_of_nonpos hp, mul_zero]

lemma radialPhase_pi_half {y x : Space} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hx : t+b ≤ ‖x-y‖) : radialPhase y t b x = Real.pi/2 := by
  have hp : 1 ≤ radialParameter y t b x := by
    apply (one_le_div (radial_denominator_pos ht hb)).mpr
    nlinarith [norm_nonneg (x-y)]
  simp only [radialPhase, Real.smoothTransition.one_of_one_le hp, mul_one]

lemma radialCut_outer {y x : Space} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hx : t+b ≤ ‖x-y‖) :
    (radialCut y ht hb 0).value x = 0 ∧ (radialCut y ht hb 1).value x = 1 := by
  simp [radialCut, radialInside, radialOutside, radialPhase_pi_half ht hb hx]

lemma radialCut_local_error (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) :
    spatialErrorWeight (radialCut y ht hb) x =
      ∑ a : Fin 3, lineDeriv ℝ (radialPhase y t b) x (spaceDirections a) ^ 2 := by
  unfold spatialErrorWeight
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fin.sum_univ_two, radialCut, Matrix.cons_val_zero, Matrix.cons_val_one,
    radialInside, radialOutside, radial_cos_derivative, radial_sin_derivative]
  nlinarith [Real.sin_sq_add_cos_sq (radialPhase y t b x)]

lemma radialPhase_derivative_zero_off_collar {y x : Space} {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hx : ¬ (t ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ t+b)) (v : Space) :
    lineDeriv ℝ (radialPhase y t b) x v = 0 := by
  rw [radialPhase_derivative]
  have hD := radial_denominator_pos ht hb
  have hs : deriv Real.smoothTransition (radialParameter y t b x) = 0 := by
    by_cases hlow : ‖x-y‖ < t
    · apply smoothTransition_deriv_zero_of_neg
      apply div_neg_of_neg_of_pos _ hD
      nlinarith [norm_nonneg (x-y)]
    · have hhigh : t+b < ‖x-y‖ := lt_of_not_ge (fun h => hx ⟨le_of_not_gt hlow,h⟩)
      apply smoothTransition_deriv_zero_of_one_lt
      apply (one_lt_div hD).mpr
      nlinarith [norm_nonneg (x-y)]
  rw [hs, mul_zero, zero_mul]

theorem radialCut_error_bound (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) :
    spatialErrorWeight (radialCut y ht hb) x ≤
      (3 * (Real.pi * smoothTransitionBound / b)^2) *
        (if t ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ t+b then (1:ℝ) else 0) := by
  classical
  rw [radialCut_local_error]
  by_cases hx : t ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ t+b
  · simp only [ite_eq_left hx, mul_one]
    calc
      _ ≤ ∑ a : Fin 3, (Real.pi * smoothTransitionBound / b)^2 := by
        apply Finset.sum_le_sum
        intro a _
        have hC : 0 < Real.pi * smoothTransitionBound / b :=
          div_pos (mul_pos Real.pi_pos smoothTransitionBound_pos) hb
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hC.le).mpr (radialPhase_derivative_le y ht hb x a)
      _ = _ := by simp
  · simp only [ite_eq_right hx, mul_zero]
    simp only [radialPhase_derivative_zero_off_collar ht hb hx, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, le_refl]

end CoulombAtom

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_RadialPacketBase
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
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

def radialScaledOrbital (R : ℝ) : FormVector 1 :=
  scaleForm (Real.sqrt (formMass (radialScaledRaw R)))⁻¹ (radialScaledRaw R)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketDensity
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma packetDensity_eq_two (y : Space) (R : ℝ) (x : Space) (s : Spins 1) :
    packetDensity y R x = 2 * ‖(radialLocalOrbital y R).value s (fun _ => x)‖^2 := by
  simp only [packetDensity,radialLocalOrbital,scaleForm,radialLocalRaw,smoothForm,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1

def coreCoulombAt {N : ℕ} (ψ : FormVector N) (y : Space) : ℝ :=
  ∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖ψ.value s x‖^2 / ‖x i-y‖

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FormBody
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

def formOneBody {N : ℕ} (ψ : FormVector N) (w : Space → ℝ) : ℝ :=
  ∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖ψ.value s x‖^2 * w (x i)

def OneBodyIntegrable {N : ℕ} (ψ : FormVector N) (w : Space → ℝ) : Prop :=
  ∀ s i, Integrable (fun x => ‖ψ.value s x‖^2 * w (x i))

lemma formOneBody_scale {N : ℕ} (ψ : FormVector N) (w : Space → ℝ) (c : ℝ) :
    formOneBody (scaleForm c ψ) w = c^2 * formOneBody ψ w := by
  unfold formOneBody
  simp only [scaleForm,norm_real_mul_sq,mul_assoc,integral_const_mul,Finset.mul_sum]

lemma OneBodyIntegrable.scale {N : ℕ} {ψ : FormVector N} {w : Space → ℝ}
    (h : OneBodyIntegrable ψ w) (c : ℝ) : OneBodyIntegrable (scaleForm c ψ) w := by
  intro s i
  simpa only [scaleForm,norm_real_mul_sq,mul_assoc] using (h s i).const_mul (c^2)

lemma OneBodyIntegrable.reindex {N M : ℕ} {ψ : FormVector N} {w : Space → ℝ}
    (h : OneBodyIntegrable ψ w) (e : Fin M ≃ Fin N) : OneBodyIntegrable (reindexForm e ψ) w := by
  intro s i
  simpa only [Function.comp_def,configurationReindex_apply,reindexForm,Equiv.symm_apply_apply]
    using (configurationReindex_preserving e).integrable_comp_of_integrable (h (s ∘ e.symm) (e i))

lemma formOneBody_reindex {N M : ℕ} (ψ : FormVector N) (w : Space → ℝ) (e : Fin M ≃ Fin N) :
    formOneBody (reindexForm e ψ) w = formOneBody ψ w := by
  have hh (s : Spins M) (i : Fin M) :
      (∫ x, ‖(reindexForm e ψ).value s x‖^2 * w (x i)) =
        ∫ x, ‖ψ.value (s ∘ e.symm) x‖^2 * w (x (e i)) := by
    simpa only [Function.comp_apply,Equiv.symm_apply_apply,reindexForm] using
      integral_reindex e (fun x => ‖ψ.value (s ∘ e.symm) x‖^2 * w (x (e i)))
  have hi (s : Spins M) :
      (∑ i : Fin M, ∫ x, ‖ψ.value (s ∘ e.symm) x‖^2 * w (x (e i))) =
      ∑ i : Fin N, ∫ x, ‖ψ.value (s ∘ e.symm) x‖^2 * w (x i) :=
    Equiv.sum_comp e (fun i : Fin N => ∫ x, ‖ψ.value (s ∘ e.symm) x‖^2 * w (x i))
  unfold formOneBody
  simp_rw [hh,hi]
  exact sum_spin_reindex e (fun s => ∑ i, ∫ x, ‖ψ.value s x‖^2 * w (x i))

lemma formOneBody_sum_disjoint {ι : Type*} [Fintype ι] {N : ℕ}
    {ψ : ι → FormVector N} {w : Space → ℝ}
    (h : ∀ k, OneBodyIntegrable (ψ k) w) (hd : FormsDisjoint ψ) :
    formOneBody (sumForm ψ) w = ∑ k, formOneBody (ψ k) w := by
  have hh (s : Spins N) (i : Fin N) :
      (∫ x, ‖(sumForm ψ).value s x‖^2 * w (x i)) =
        ∑ k, ∫ x, ‖(ψ k).value s x‖^2 * w (x i) := by
    simp only [sumForm,norm_sum_sq_disjoint _ (fun k l hkl => hd.1 k l hkl s _),Finset.sum_mul]
    exact integral_finsetSum _ (fun k _ => h k s i)
  unfold formOneBody
  simp_rw [hh]
  calc
    _ = ∑ s, ∑ k, ∑ i, ∫ x, ‖(ψ k).value s x‖^2 * w (x i) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

lemma formOneBody_insertionTerm {N : ℕ} (T : FormVector (N+1)) (w : Space → ℝ) (i : Fin (N+1)) :
    formOneBody (insertionTerm T i) w = formOneBody T w := by
  rw [insertionTerm,formOneBody_scale,formOneBody_reindex,real_sign_sq,one_mul]

lemma formOneBody_wedge {N : ℕ} {T : FormVector (N+1)} {w : Space → ℝ}
    (h : OneBodyIntegrable T w) (hd : FormsDisjoint (insertionTerm T)) :
    formOneBody (wedgeForm T) w = (N+1 : ℝ) * formOneBody T w := by
  have hk (i : Fin (N+1)) : OneBodyIntegrable (insertionTerm T i) w :=
    (h.reindex (insertionSwap i)).scale _
  rw [wedgeForm,formOneBody_sum_disjoint hk hd]
  simp only [formOneBody_insertionTerm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_add,Nat.cast_one]

def insertOrbital {N : ℕ} (ψ : FormVector N) (φ : FormVector 1) : FormVector (N+1) :=
  scaleForm (Real.sqrt (N+1 : ℝ))⁻¹ (wedgeForm (tensorForm ψ φ))


open MeasureTheory Filter
open scoped Topology BigOperators


def FormAvoids {N : ℕ} (ψ : FormVector N) (S : Set Space) : Prop :=
  ∀ x i, x i ∈ S → FormZeroAt ψ x

lemma FormAvoids.scale {N : ℕ} {ψ : FormVector N} {S : Set Space}
    (h : FormAvoids ψ S) (c : ℝ) : FormAvoids (scaleForm c ψ) S := by
  intro x i hx s
  constructor
  · change _ * ψ.value s x = 0
    rw [(h x i hx s).1,mul_zero]
  · intro j a
    change _ * ψ.gradient s j a x = 0
    rw [(h x i hx s).2,mul_zero]

lemma FormAvoids.reindex {N M : ℕ} {ψ : FormVector N} {S : Set Space}
    (h : FormAvoids ψ S) (e : Fin M ≃ Fin N) : FormAvoids (reindexForm e ψ) S := by
  intro x i hx s
  have hz := h (x ∘ e.symm) (e i) (by simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hx)
  exact ⟨(hz (s ∘ e.symm)).1, fun j a => (hz (s ∘ e.symm)).2 (e j) a⟩

lemma FormAvoids.sum {ι : Type*} [Fintype ι] {N : ℕ} {ψ : ι → FormVector N} {S : Set Space}
    (h : ∀ k, FormAvoids (ψ k) S) : FormAvoids (sumForm ψ) S := by
  intro x i hx s
  constructor
  · change (∑ k, (ψ k).value s x) = 0
    exact Finset.sum_eq_zero (fun k _ => (h k x i hx s).1)
  · intro j a
    change (∑ k, (ψ k).gradient s j a x) = 0
    exact Finset.sum_eq_zero (fun k _ => (h k x i hx s).2 j a)

lemma FormAvoids.tensor {N M : ℕ} {ψ : FormVector N} {φ : FormVector M} {S : Set Space}
    (hψ : FormAvoids ψ S) (hφ : FormAvoids φ S) : FormAvoids (tensorForm ψ φ) S := by
  intro x i hx
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i => exact tensor_zero_left ψ φ (hψ (leftList x) i hx)
  | inr i => exact tensor_zero_right ψ φ (hφ (rightList x) i hx)

lemma FormAvoids.wedge {N : ℕ} {T : FormVector (N+1)} {S : Set Space}
    (h : FormAvoids T S) : FormAvoids (wedgeForm T) S := by
  apply FormAvoids.sum
  intro i
  exact (h.reindex (insertionSwap i)).scale _

lemma FormAvoids.insertOrbital {N : ℕ} {ψ : FormVector N} {φ : FormVector 1} {S : Set Space}
    (hψ : FormAvoids ψ S) (hφ : FormAvoids φ S) : FormAvoids (insertOrbital ψ φ) S :=
  (hψ.tensor hφ).wedge.scale _

lemma FormAvoids.mono {N : ℕ} {ψ : FormVector N} {S T : Set Space}
    (h : FormAvoids ψ T) (hst : S ⊆ T) : FormAvoids ψ S :=
  fun x i hx => h x i (hst hx)

lemma coreCoulombAt_eq_formOneBody {N : ℕ} (ψ : FormVector N) (y : Space) :
    coreCoulombAt ψ y = formOneBody ψ (fun x => 1/‖x-y‖) := by
  simp only [coreCoulombAt,formOneBody,mul_one_div]


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_ParticleDensity
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom.Pauli
open CoulombPauli CoulombPackets CoulombLT

def oneParticleDensity {N : ℕ} (ψ : FormVector (N+1))
    (hψ : ∀ s, MemLp (ψ.value s) 2) : Space → ℝ≥0∞ :=
  fermionDensity (toMany ψ hψ)

end CoulombAtom.Pauli

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Density
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombAtom.Pauli
open CoulombPauli CoulombPackets CoulombLT

def density {N : ℕ} (ψ : FormVector (N+1)) (hψ : ∀ s, MemLp (ψ.value s) 2) (x : Space) : ℝ :=
  (oneParticleDensity ψ hψ x).toReal

end CoulombAtom.Pauli

open MeasureTheory Set Metric
open scoped ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_LipschitzWeak
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
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
namespace CoulombAtom
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

lemma bounded_lipschitz_smooth_approx {p : E → ℝ} {C : NNReal}
    (hp : LipschitzWith C p) {B : ℝ} (hB : ∀ x, ‖p x‖ ≤ B) (v : E) :
    ∃ u : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ ∞ (u n)) ∧
      (∀ n x, ‖u n x‖ ≤ B) ∧
      (∀ n x, ‖lineDeriv ℝ (u n) x v‖ ≤ C * ‖v‖) ∧
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (p x))) ∧
      ∀ᵐ x, Tendsto (fun n => lineDeriv ℝ (u n) x v) atTop
        (𝓝 (lineDeriv ℝ p x v)) := by
  let k : ℕ → E → ℝ := fun n => (shrinkingBump n).normed volume
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)
  let u : ℕ → E → ℝ := fun n => k n ⋆[L] p
  have hk (n : ℕ) : ContDiff ℝ ∞ (k n) := (shrinkingBump n).contDiff_normed
  have hkc (n : ℕ) : HasCompactSupport (k n) := (shrinkingBump n).hasCompactSupport_normed
  have hk0 (n : ℕ) : ∀ x, 0 ≤ k n x := (shrinkingBump n).nonneg_normed
  have hk1 (n : ℕ) : (∫ x, k n x) = 1 := (shrinkingBump n).integral_normed
  have hki (n : ℕ) : Integrable (k n) := (hk n).continuous.integrable_of_hasCompactSupport (hkc n)
  have hu (n : ℕ) : ContDiff ℝ ∞ (u n) :=
    (hkc n).contDiff_convolution_left L (hk n) hp.continuous.locallyIntegrable
  have hdu (n : ℕ) (x : E) : lineDeriv ℝ (u n) x v =
      (k n ⋆[L] (fun y => lineDeriv ℝ p y v)) x :=
    ((hu n).differentiable (by simp) x).lineDeriv_eq_fderiv.trans
      (mollified_lipschitz_derivative (hk n) (hkc n) hp v x)
  refine ⟨u, hu, fun n x => convolution_bounded (hki n) (hk0 n) (hk1 n) hB x, ?_, ?_, ?_⟩
  · intro n x
    rw [hdu]
    exact convolution_bounded (hki n) (hk0 n) (hk1 n)
      (fun _ => norm_lineDeriv_le_of_lipschitz ℝ hp) x
  · intro x
    exact ContDiffBump.convolution_tendsto_right_of_continuous shrinkingBump_tendsto
      hp.continuous x
  · simp_rw [hdu]
    exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      shrinkingBump_tendsto
      (Eventually.of_forall fun n => le_refl (2 * (shrinkingBump (E := E) n).rIn))
      (hp.locallyIntegrable_lineDeriv v)

lemma IsWeakDerivative.mul_lipschitz {f g : E → ℂ} {v : E}
    (hw : IsWeakDerivative v f g) (hf : MemLp f 2) (hg : MemLp g 2)
    {p : E → ℝ} {C : NNReal} (hp : LipschitzWith C p)
    (hb : ∃ B : ℝ, ∀ x, |p x| ≤ B) :
    IsWeakDerivative v (fun x => (p x : ℂ) * f x)
      (fun x => (p x : ℂ) * g x + Complex.ofReal (lineDeriv ℝ p x v) * f x) := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨u, hu, hub, hdub, hut, hdut⟩ := bounded_lipschitz_smooth_approx hp hB v
  intro φ hφ hcφ
  have hφ2 := test_memLp hφ hcφ
  have hdφ2 := test_deriv_memLp hφ hcφ v
  have i1 : Integrable (fun x => f x * Complex.ofReal (lineDeriv ℝ φ x v)) :=
    hf.integrable_mul hdφ2
  have i2 : Integrable (fun x => g x * (φ x : ℂ)) := hg.integrable_mul hφ2
  have i3 : Integrable (fun x => f x * (φ x : ℂ)) := hf.integrable_mul hφ2
  have t1 := integral_real_mul_tendsto (fun n => (hu n).continuous.aestronglyMeasurable)
    hub (Eventually.of_forall hut) i1
  have t2 := integral_real_mul_tendsto (fun n => (hu n).continuous.aestronglyMeasurable)
    hub (Eventually.of_forall hut) i2
  have t3 := integral_real_mul_tendsto
    (fun n => (smooth_lineDeriv_continuous (hu n) v).aestronglyMeasurable) hdub hdut i3
  have h1 (n : ℕ) : Integrable (fun x => (u n x : ℂ) * (g x * (φ x : ℂ))) :=
    i2.bdd_mul ((Complex.continuous_ofReal.comp (hu n).continuous).aestronglyMeasurable)
      (Eventually.of_forall fun x => by simpa using hub n x)
  have h2 (n : ℕ) : Integrable (fun x => Complex.ofReal (lineDeriv ℝ (u n) x v) *
      (f x * (φ x : ℂ))) :=
    i3.bdd_mul ((Complex.continuous_ofReal.comp
      (smooth_lineDeriv_continuous (hu n) v)).aestronglyMeasurable)
      (Eventually.of_forall fun x => by simpa using hdub n x)
  have he (n : ℕ) : (∫ x, (u n x : ℂ) * (f x * Complex.ofReal (lineDeriv ℝ φ x v))) =
      -((∫ x, (u n x : ℂ) * (g x * (φ x : ℂ))) +
        (∫ x, Complex.ofReal (lineDeriv ℝ (u n) x v) * (f x * (φ x : ℂ)))) := by
    have hh := hw.mul_smooth hf hg (hu n) φ hφ hcφ
    have ha : (fun x => ((u n x : ℂ) * g x +
        Complex.ofReal (lineDeriv ℝ (u n) x v) * f x) * (φ x : ℂ)) =
        fun x => (u n x : ℂ) * (g x * (φ x : ℂ)) +
          Complex.ofReal (lineDeriv ℝ (u n) x v) * (f x * (φ x : ℂ)) := by
      funext x; ring
    rw [ha, integral_add (h1 n) (h2 n)] at hh
    simpa only [mul_assoc] using hh
  have ht := tendsto_nhds_unique t1 (((t2.add t3).neg).congr (fun n => (he n).symm))
  have ih1 : Integrable (fun x => (p x : ℂ) * (g x * (φ x : ℂ))) :=
    i2.bdd_mul (Complex.continuous_ofReal.comp hp.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using hB x)
  have ih2 : Integrable (fun x => Complex.ofReal (lineDeriv ℝ p x v) * (f x * (φ x : ℂ))) :=
    i3.bdd_mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (aestronglyMeasurable_lineDeriv hp.continuous volume))
      (Eventually.of_forall fun x => by
        simpa using (norm_lineDeriv_le_of_lipschitz ℝ hp (x₀ := x) (v := v)))
  have ha : (fun x => ((p x : ℂ) * g x + Complex.ofReal (lineDeriv ℝ p x v) * f x) *
      (φ x : ℂ)) = fun x => (p x : ℂ) * (g x * (φ x : ℂ)) +
        Complex.ofReal (lineDeriv ℝ p x v) * (f x * (φ x : ℂ)) := by
    funext x; ring
  rw [ha, integral_add ih1 ih2]
  simpa only [mul_assoc] using ht

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Multiplier2
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom
section Multiplier
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma LipschitzMultiplier.value_memLp {v : ι → E} (p : LipschitzMultiplier v)
    (F : weakGraph v) : MemLp (fun x => (p.value x : ℂ) * F.val none x) 2 :=
  memLp_bounded_mul p.lipschitz.continuous p.bound (Lp.memLp _)

omit [Fintype ι] in
lemma LipschitzMultiplier.gradient_memLp {v : ι → E} (p : LipschitzMultiplier v)
    (F : weakGraph v) (i : ι) :
    MemLp (fun x => (p.value x : ℂ) * F.val (some i) x +
      Complex.ofReal (lineDeriv ℝ p.value x (v i)) * F.val none x) 2 := by
  have hd : MemLp (fun x => Complex.ofReal (lineDeriv ℝ p.value x (v i))) ⊤ :=
    memLp_top_of_bound (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (aestronglyMeasurable_lineDeriv p.lipschitz.continuous volume))
      (p.constant * ‖v i‖) (Eventually.of_forall fun x => by
        simpa using (norm_lineDeriv_le_of_lipschitz ℝ p.lipschitz (x₀ := x) (v := v i)))
  exact (memLp_bounded_mul p.lipschitz.continuous p.bound (Lp.memLp _)).add
    ((Lp.memLp (F.val none)).mul' hd)

def LipschitzMultiplier.apply {v : ι → E} (p : LipschitzMultiplier v) (F : weakGraph v) :
    weakGraph v := by
  let G : WeakGraphAmbient E ι := WithLp.toLp 2 fun k => match k with
    | none => (p.value_memLp F).toLp _
    | some i => (p.gradient_memLp F i).toLp _
  refine ⟨G, (mem_weakGraph v G).mpr ?_⟩
  intro i
  exact (((mem_weakGraph v F.val).mp F.property i).mul_lipschitz
    (Lp.memLp _) (Lp.memLp _) p.lipschitz p.bound).congr_ae
      (p.value_memLp F).coeFn_toLp.symm (p.gradient_memLp F i).coeFn_toLp.symm

omit [Fintype ι] in
lemma LipschitzMultiplier.apply_value {v : ι → E} (p : LipschitzMultiplier v)
    (F : weakGraph v) :
    ((p.apply F).val none : E → ℂ) =ᵐ[volume] fun x => (p.value x : ℂ) * F.val none x :=
  (p.value_memLp F).coeFn_toLp

end Multiplier

structure FermionLipschitzMultiplier (N : ℕ) extends LipschitzMultiplier (sectorDirections N) where
  symmetric : ∀ (π : Equiv.Perm (Fin N)) (x : Configuration N), value (x ∘ π) = value x

def FermionLipschitzMultiplier.apply {N : ℕ} (p : FermionLipschitzMultiplier N) (F : fermionGraph N) :
    fermionGraph N := by
  let G : SectorGraph N := WithLp.toLp 2 fun s => p.toLipschitzMultiplier.apply (F.val s)
  refine ⟨G, (mem_fermionSpace_ae (sectorGraphValue N G)).mpr ?_⟩
  intro π s
  have hl := (permuteConfiguration_preserving π).quasiMeasurePreserving.ae
    (p.toLipschitzMultiplier.apply_value (F.val (s ∘ π)))
  filter_upwards [hl, p.toLipschitzMultiplier.apply_value (F.val s),
    (mem_fermionSpace_ae (sectorGraphValue N F.val)).mp F.property π s] with x hx hy hz
  change (p.toLipschitzMultiplier.apply (F.val (s ∘ π))).val none (x ∘ π) =
    (((Equiv.Perm.sign π : ℤ) : ℂ)) * (p.toLipschitzMultiplier.apply (F.val s)).val none x
  simp only [sectorGraphValue_apply] at hz
  simp only [permuteConfiguration_apply] at hx
  rw [hx, hy, p.symmetric, hz]
  ring

attribute [local irreducible] graphNuclear graphPair graphComponent FermionLipschitzMultiplier.apply

attribute [local irreducible] formEnergy graphFormVector fermionGraphValue coulombFormOperator

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FormRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombRadialAveraging

def formRawDensity {N : ℕ} (ψ : FormVector N) (x : Configuration N) : ℝ :=
  ∑ s : Spins N, ‖ψ.value s x‖^2

lemma formRawDensity_nonneg {N : ℕ} (ψ : FormVector N) (x : Configuration N) :
    0 ≤ formRawDensity ψ x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

def formRawLaw {N : ℕ} (ψ : FormVector N) : Measure (Configuration N) :=
  volume.withDensity (fun x => ENNReal.ofReal (formRawDensity ψ x))

def rawBallCount {N : ℕ} (y : Space) (R : ℝ) (x : Configuration N) : ℝ :=
  ∑ i, if ‖x i-y‖ < R then 1 else 0

lemma rawBallCount_nonneg {N : ℕ} (y : Space) (R : ℝ) (x : Configuration N) :
    0 ≤ rawBallCount y R x := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> norm_num

lemma rawBallCount_le {N : ℕ} (y : Space) (R : ℝ) (x : Configuration N) :
    rawBallCount y R x ≤ N := by
  calc
    _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
    _ = N := by simp

lemma configuration_distance_measurable {N : ℕ} (y : Space) (i : Fin N) :
    Measurable (fun x : Configuration N => ‖x i-y‖) := by
  exact (((continuous_apply i).sub continuous_const).norm :
    Continuous (fun x : Configuration N => ‖x i-y‖)).measurable

lemma rawBallCount_measurable {N : ℕ} (y : Space) (R : ℝ) :
    Measurable (rawBallCount (N := N) y R) := by
  apply Finset.measurable_sum; intro i _
  exact Measurable.ite (measurableSet_lt (configuration_distance_measurable y i)
    measurable_const) measurable_const measurable_const

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoreKinetic
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

def coreKinetic {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  (1/2:ℝ) * ∑ s, ∑ i : Fin N, ∑ a, ∫ z, ‖ψ.gradient s (finSumFinEquiv (Sum.inl i)) a z‖^2

def coreNuclear {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  ∑ s, ∑ i : Fin N, ∫ z, ‖ψ.value s z‖^2 / ‖z (finSumFinEquiv (Sum.inl i))‖

def outNuclear {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  ∑ s, ∑ i : Fin M, ∫ z, ‖ψ.value s z‖^2 / ‖z (finSumFinEquiv (Sum.inr i))‖

def coreRepulsion {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  ∑ s, ∑ i : Fin N, ∑ j : Fin N, if i < j then
    ∫ z, ‖ψ.value s z‖^2 / ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inl j))‖ else 0

lemma formNuclear_core_out {N M : ℕ} (ψ : FormVector (N+M)) :
    formNuclear ψ = coreNuclear ψ + outNuclear ψ := by
  unfold formNuclear coreNuclear outNuclear
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CutCoreNumber
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

lemma cutNumbers_sum {L : ℕ} (b : Fin L → Fin 2) : cutCoreNumber b + cutOutNumber b = L := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (cutOrder b)

lemma cutOrder_labels {L : ℕ} (b : Fin L → Fin 2) :
    b ∘ cutOrder b = coreCutLabels (cutCoreNumber b) (cutOutNumber b) := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j
  · change b (cutOrder b (finSumFinEquiv (Sum.inl j))) = _
    simp only [cutOrder, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl, coreCutLabels, joinLists_left]
    exact ((Fintype.equivFin {i // b i = 0}).symm j).property
  · change b (cutOrder b (finSumFinEquiv (Sum.inr j))) = _
    simp only [cutOrder, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr, coreCutLabels, joinLists_right]
    have hh := ((Fintype.equivFin {i // b i ≠ 0}).symm j).property
    omega

lemma spatialProductValue_reindex {M N : ℕ} (e : Fin M ≃ Fin N)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (b : Fin N → Fin 2) (x : Configuration M) :
    spatialProductValue p b (x ∘ e.symm) = spatialProductValue p (b ∘ e) x := by
  unfold spatialProductValue
  rw [← Equiv.prod_comp e (fun i => (p (b i)).value ((x ∘ e.symm) i))]
  simp only [Function.comp_apply, Equiv.symm_apply_apply]

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TailParticleCount
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

lemma cutOutNumber_eq_sum {L : ℕ} (b : Fin L → Fin 2) :
    (cutOutNumber b : ℝ) = ∑ i : Fin L, if b i ≠ 0 then 1 else 0 := by
  classical
  rw [Finset.sum_boole, cutOutNumber, Fintype.card_subtype]

lemma weightedParticleCount_mono {L : ℕ} {ψ : FormVector L}
    {v w : Space → ℝ}
    (hv : ∀ s i, Integrable (fun x => v (x i) * ‖ψ.value s x‖^2))
    (hw : ∀ s i, Integrable (fun x => w (x i) * ‖ψ.value s x‖^2))
    (hvw : ∀ x, v x ≤ w x) :
    weightedParticleCount ψ v ≤ weightedParticleCount ψ w := by
  apply Finset.sum_le_sum; intro s _
  apply Finset.sum_le_sum; intro i _
  apply integral_mono (hv s i) (hw s i)
  intro x
  exact mul_le_mul_of_nonneg_right (hvw (x i)) (sq_nonneg _)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_BlockEnergetics
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

def outKinetic {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  (1/2:ℝ)*∑ s, ∑ i : Fin M, ∑ a, ∫ z, ‖ψ.gradient s (finSumFinEquiv (Sum.inr i)) a z‖^2

def outRepulsion {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  ∑ s, ∑ i : Fin M, ∑ j : Fin M, if i < j then
    ∫ z, ‖ψ.value s z‖^2/‖z (finSumFinEquiv (Sum.inr i))-z (finSumFinEquiv (Sum.inr j))‖ else 0

def crossRepulsion {N M : ℕ} (ψ : FormVector (N+M)) : ℝ :=
  ∑ s, ∑ i : Fin N, ∑ j : Fin M,
    ∫ z, ‖ψ.value s z‖^2/‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖

lemma formRepulsion_core_out_cross {N M : ℕ} (ψ : FormVector (N+M)) :
    formRepulsion ψ = coreRepulsion ψ+outRepulsion ψ+crossRepulsion ψ := by
  unfold formRepulsion coreRepulsion outRepulsion crossRepulsion
  simp_rw [finite_pair_core_out_cross]
  simp only [Finset.sum_add_distrib]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketInsert
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

def packetInsert {N : ℕ} (ψ : FormVector N) (y : ℕ → Space) (r : ℝ) :
    (k : ℕ) → FormVector (N+k)
  | 0 => ψ
  | k+1 => insertOrbital (packetInsert ψ y r k) (radialLocalOrbital (y k) r)

def packetPairEnergy (y : ℕ → Space) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range j, 1/‖y i-y j‖

def packetScreenedSum {N : ℕ} (ψ : FormVector N) (Z : ℝ) (y : ℕ → Space) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (Z*formMass ψ/‖y j‖-coreCoulombAt ψ (y j))

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpatialRotation
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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

instance rotationMeasureProbability : IsProbabilityMeasure rotationMeasure := by
  constructor
  exact Measure.haarMeasure_self

instance rotationMeasureLeftInvariant : rotationMeasure.IsMulLeftInvariant :=
  inferInstanceAs (Measure.haarMeasure (⊤ : PositiveCompacts SpatialRotation)).IsMulLeftInvariant

lemma exists_rotate_norm_eq (x y : Space) (hxy : ‖x‖ = ‖y‖) :
    ∃ g : SpatialRotation, rotate g x = y := by
  obtain ⟨e,he⟩ := exists_orthogonal_map_norm_eq x y hxy
  exact ⟨Unitary.linearIsometryEquiv.symm e, by simpa [rotate] using he⟩

lemma rotation_integral_left (f : SpatialRotation → ℝ) (g : SpatialRotation) :
    (∫ h, f (g*h) ∂rotationMeasure) = ∫ h, f h ∂rotationMeasure :=
  integral_mul_left_eq_self f g

def averagedPacket (p : Space) (r : ℝ) (x : Space) : ℝ :=
  ∫ g : SpatialRotation, packetDensity (rotate g p) r x ∂rotationMeasure

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_TruncatedCoulomb
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
namespace CoulombAtom

def unitCoulombIntegral : ℝ := ∫ x : Space, truncatedCoulomb 1 x

lemma unitCoulombIntegral_nonneg : 0 ≤ unitCoulombIntegral :=
  integral_nonneg (truncatedCoulomb_nonneg 1)

lemma truncatedCoulomb_scaling {R : ℝ} (hR : 0 < R) (x : Space) :
    truncatedCoulomb R x = R⁻¹ * truncatedCoulomb 1 (R⁻¹ • x) := by
  have hmem : R⁻¹ • x ∈ ball (0 : Space) 1 ↔ x ∈ ball (0 : Space) R := by
    simp only [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    rw [inv_mul_lt_iff₀ hR]
    simp only [mul_one]
  by_cases hx : x ∈ ball (0 : Space) R
  · simp only [truncatedCoulomb,indicator_of_mem hx,indicator_of_mem (hmem.mpr hx),
      norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),one_div,mul_inv_rev,inv_inv]
    field_simp
  · simp only [truncatedCoulomb,indicator_of_notMem hx,indicator_of_notMem (mt hmem.mp hx),mul_zero]

lemma truncatedCoulomb_integral {R : ℝ} (hR : 0 < R) :
    (∫ x : Space, truncatedCoulomb R x) = R^2*unitCoulombIntegral := by
  simp_rw [truncatedCoulomb_scaling hR]
  rw [integral_const_mul,Measure.integral_comp_inv_smul_of_nonneg _ _ hR.le]
  simp only [Space,finrank_euclideanSpace_fin,smul_eq_mul]
  unfold unitCoulombIntegral
  field_simp

lemma radialPacketBase_bound (x : Space) : ‖radialPacketBase x‖ ≤ 1 := by
  rw [radialPacketBase,Complex.norm_real,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

def packetDensityConstant : ℝ := (Fintype.card (Spins 1) : ℝ) / formMass (smoothForm radialPacketSeed)

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketCloud
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

def packetCloud (p : ℕ → Space) (r : ℝ) (k : ℕ) (x : Space) : ℝ :=
  ∑ i ∈ Finset.range k, packetDensity (p i) r x

lemma packetCloud_exists {p : ℕ → Space} {r : ℝ} {k : ℕ} {x : Space}
    (hx : packetCloud p r k x ≠ 0) : ∃ i < k, packetDensity (p i) r x ≠ 0 := by
  by_contra hh
  push Not at hh
  exact hx (Finset.sum_eq_zero (fun i hi => hh i (Finset.mem_range.mp hi)))


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators


def packetGridPoint {n : ℕ} (r : ℝ) (v : Fin 3 → Fin n) : Space :=
  WithLp.toLp 2 (fun t => (3*r)*(v t : ℝ))

lemma packetGridPoint_apply {n : ℕ} (r : ℝ) (v : Fin 3 → Fin n) (t : Fin 3) :
    packetGridPoint r v t = (3*r)*(v t : ℝ) := rfl

lemma packetGridPoint_norm {n : ℕ} {r : ℝ} (hr : 0 < r) (v : Fin 3 → Fin n) :
    ‖packetGridPoint r v‖ ≤ 9*r*n := by
  have hb (t : Fin 3) : |packetGridPoint r v t| ≤ 3*r*n := by
    rw [packetGridPoint_apply,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (v t).isLt.le) (by positivity)
  have hs := EuclideanSpace.norm_sq_eq (packetGridPoint r v)
  have hsq : ‖packetGridPoint r v‖^2 ≤ 3*(3*r*n)^2 := by
    rw [hs]
    calc
      _ ≤ ∑ _t : Fin 3, (3*r*n)^2 := by
        apply Finset.sum_le_sum
        intro t _
        simpa only [Real.norm_eq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hb t)
      _ = _ := by simp
  have hp : 0 ≤ 9*r*n := by positivity
  nlinarith [sq_nonneg (3*r*n),norm_nonneg (packetGridPoint r v)]

lemma packetGridPoint_separated {n : ℕ} {r : ℝ} (hr : 0 < r)
    (v w : Fin 3 → Fin n) (hvw : v ≠ w) : 3*r ≤ ‖packetGridPoint r v-packetGridPoint r w‖ := by
  obtain ⟨t,ht⟩ : ∃ t, v t ≠ w t := by
    by_contra hh
    push Not at hh
    exact hvw (funext hh)
  have hcast : 1 ≤ |(v t : ℝ)-(w t : ℝ)| := by
    rcases lt_or_gt_of_ne (show (v t).val ≠ (w t).val from fun hh => ht (Fin.ext hh)) with h | h
    · have hh : (v t : ℝ)+1 ≤ (w t : ℝ) := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith : (v t : ℝ)-(w t : ℝ) ≤ 0)]
      have := hh
      linarith
    · have hh : (w t : ℝ)+1 ≤ (v t : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith : 0 ≤ (v t : ℝ)-(w t : ℝ))]
      have := hh
      linarith
  have hb := PiLp.norm_apply_le (packetGridPoint r v-packetGridPoint r w) t
  change |(3*r)*(v t : ℝ)-(3*r)*(w t : ℝ)| ≤ _ at hb
  rw [← mul_sub,abs_mul,abs_of_pos (by positivity : 0 < 3*r)] at hb
  nlinarith

def packetGrid (n : ℕ) (r : ℝ) (i : ℕ) : Space :=
  if h : i < Fintype.card (Fin 3 → Fin n) then
    packetGridPoint r ((Fintype.equivFin (Fin 3 → Fin n)).symm ⟨i,h⟩) else 0

lemma packetGrid_norm (n : ℕ) {r : ℝ} (hr : 0 < r) (i : ℕ) :
    ‖packetGrid n r i‖ ≤ 9*r*n := by
  unfold packetGrid
  split_ifs
  · exact packetGridPoint_norm hr _
  · simp only [norm_zero]; positivity

lemma packetGrid_separated (n : ℕ) {r : ℝ} (hr : 0 < r)
    (i j : ℕ) (hij : i < j) (hj : j < n^3) :
    3*r ≤ ‖packetGrid n r i-packetGrid n r j‖ := by
  have hj' : j < Fintype.card (Fin 3 → Fin n) := by rwa [packetGrid_card]
  have hi' : i < Fintype.card (Fin 3 → Fin n) := lt_trans hij hj'
  simp only [packetGrid,dite_eq_left hi',dite_eq_left hj']
  apply packetGridPoint_separated hr
  intro hh
  have he := (Fintype.equivFin (Fin 3 → Fin n)).symm.injective hh
  have : i = j := congrArg Fin.val he
  omega


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketDensityRadius
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
namespace CoulombAtom

lemma rotation_kernel_integrable (p z : Space) (hz : ‖p‖ < ‖z‖) :
    Integrable (fun g : SpatialRotation => 1 / ‖z-rotate g p‖) rotationMeasure := by
  have hc : Continuous (fun g : SpatialRotation => rotate g p) :=
    continuous_subtype_val.clm_apply continuous_const
  have hd : ∀ g : SpatialRotation, ‖z-rotate g p‖ ≠ 0 := by
    intro g hg
    have he := sub_eq_zero.mp (norm_eq_zero.mp hg)
    have hh : ‖z‖ = ‖p‖ := by rw [he,(rotate g).norm_map]
    linarith
  exact (continuous_const.div (continuous_const.sub hc).norm hd).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_univ (subset_univ _))

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_RotationCoreKernelIntegrable
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

lemma rotation_nuclear_integrable (y p : Space) (hp : ‖p‖ < ‖y‖) :
    Integrable (fun g : SpatialRotation => 1/‖y+rotate g p‖) rotationMeasure := by
  have hh := rotation_kernel_integrable p (-y) (by simpa only [norm_neg] using hp)
  have he (g : SpatialRotation) : ‖-y-rotate g p‖ = ‖y+rotate g p‖ := by
    rw [show -y-rotate g p = -(y+rotate g p) by abel,norm_neg]
  simpa only [he] using hh


open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators


def rotatedCenters (y : Space) (p : ℕ → Space) (g : SpatialRotation) (i : ℕ) : Space :=
  y+rotate g (p i)

lemma rotatedCenters_distance (y : Space) (p : ℕ → Space) (g : SpatialRotation) (i j : ℕ) :
    ‖rotatedCenters y p g i-rotatedCenters y p g j‖ = ‖p i-p j‖ := by
  simp only [rotatedCenters,add_sub_add_left_eq_sub,← (rotate g).map_sub,(rotate g).norm_map]

lemma rotatedCenters_pair (y : Space) (p : ℕ → Space) (g : SpatialRotation) (k : ℕ) :
    packetPairEnergy (rotatedCenters y p g) k = packetPairEnergy p k := by
  simp only [packetPairEnergy,rotatedCenters_distance]

lemma rotatedCenters_avoids {N : ℕ} {ψ : FormVector N} (y : Space) (p : ℕ → Space)
    (g : SpatialRotation) {B r : ℝ} (hc : FormAvoids ψ (ball y B))
    {i : ℕ} (hi : ‖p i‖+2*r ≤ B) :
    FormAvoids ψ (ball (rotatedCenters y p g i) (2*r)) := by
  apply hc.mono
  intro x hx
  apply mem_ball.mpr
  change ‖x-y‖ < B
  have ht := norm_add_le (x-rotatedCenters y p g i) (rotate g (p i))
  rw [show x-rotatedCenters y p g i+rotate g (p i) = x-y by dsimp [rotatedCenters]; abel,
    (rotate g).norm_map] at ht
  have hh := mem_ball.mp hx
  change ‖x-rotatedCenters y p g i‖ < 2*r at hh
  linarith

lemma rotatedCenters_nuclear (y : Space) (p : ℕ → Space) (g : SpatialRotation)
    {r : ℝ} {i : ℕ} (hi : ‖p i‖+r < ‖y‖) : r < ‖rotatedCenters y p g i‖ := by
  have ht := norm_sub_le (y+rotate g (p i)) (rotate g (p i))
  rw [add_sub_cancel_right,(rotate g).norm_map] at ht
  dsimp only [rotatedCenters]
  linarith


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_GridPacketRadius
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
namespace CoulombAtom

def packetRepulsionConstant : ℝ := 128000*packetDensityConstant*unitCoulombIntegral

lemma packetGrid_ball {B : ℝ} (hB : 0 < B) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    ‖packetGrid n (gridPacketRadius B n) i‖ ≤ 9*B/20 := by
  calc
    _ ≤ 9*gridPacketRadius B n*n := packetGrid_norm n (gridPacketRadius_pos hB hn) i
    _ = _ := by rw [mul_assoc,gridPacketRadius_mul hn]; ring

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CorePriceExcess
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

def corePriceExcess {N : ℕ} (Z lam : ℝ) (ψ : FormVector N) : ℝ :=
  formEnergy Z ψ+lam*N*formMass ψ-priceEnergy (energy Z) lam*formMass ψ

def normalizedCoreField {N : ℕ} (Z lam : ℝ) (ψ : FormVector N) (y : Space) : ℝ :=
  (Z*formMass ψ/‖y‖-coreCoulombAt ψ y)/formMass ψ-lam


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoherentPackets
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff FourierTransform

namespace CoulombAtom

lemma coherentPacket_norm (g : Space → ℂ) (z p x : Space) :
    ‖coherentPacket g z p x‖ = ‖g (x-z)‖ := by
  simp [coherentPacket,Complex.norm_exp_ofReal_mul_I]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SmoothCompactIntegral
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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
open scoped BigOperators ComplexConjugate ContDiff Topology

lemma coherentPacket_zero_outside {g : Space → ℂ} {K : Set (Space × Space)}
    {q : Space × Space} (hq : q ∈ K) {x : Space} (hx : x ∉ coherentSpatialSupport g K) :
    coherentPacket g q.1 q.2 x = 0 := by
  have hg : g (x-q.1) = 0 := by
    by_contra h
    apply hx
    exact ⟨(q,x-q.1), ⟨hq,subset_tsupport g h⟩, by simp⟩
  simp [coherentPacket,hg]

lemma coherentPacket_joint_smooth {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun r : Space × (Space × Space) => coherentPacket g r.2.1 r.2.2 r.1) := by
  unfold coherentPacket
  apply (hg.comp (contDiff_fst.sub contDiff_snd.fst)).mul
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
    (contDiff_snd.snd.inner ℝ contDiff_fst)).mul contDiff_const)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_MomentumBall
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

lemma space_ball_second_moment {R : ℝ} (hR : 0 ≤ R) :
    (∫ p : Space in ball 0 R, ‖p‖^2) = (4*Real.pi/5)*R^5 := by
  have he : (∫ p : Space in ball 0 R, ‖p‖^2) =
      ∫ p : Space, (Iio R).indicator (fun t : ℝ => t^2) ‖p‖ := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with p
    simp only [Set.indicator,mem_ball,dist_zero_right,mem_Iio]
  rw [he,integral_fun_norm_addHaar volume,space_finrank]
  have hi : (fun t : ℝ => t^(3-1) • (Iio R).indicator (fun t : ℝ => t^2) t) =
      (Iio R).indicator (fun t : ℝ => t^4) := by
    funext t
    by_cases ht : t < R <;> simp only [Set.indicator,mem_Iio,ht,ite_true,ite_false,smul_eq_mul] <;> ring
  rw [hi,setIntegral_indicator measurableSet_Iio]
  have hs : Ioi (0 : ℝ) ∩ Iio R = Ioo 0 R := by ext t; simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo]
  rw [hs,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hR,integral_pow]
  rw [space_ball_real_volume (by norm_num : (0:ℝ) ≤ 1)]
  norm_num [smul_eq_mul]
  ring

lemma fermiRadius_ball_kinetic {ρ : Space → ℝ} (hρ : ∀ z, 0 ≤ ρ z) (z : Space) :
    coherentFactor*(∫ p : Space in ball 0 (fermiRadius ρ z), ‖p‖^2) =
      tfKinetic*(ρ z)^(5/3 : ℝ) := by
  rw [space_ball_second_moment (fermiRadius_nonneg hρ z),fermiRadius,
    ← Real.rpow_mul_natCast (mul_nonneg (by positivity) (hρ z) : 0 ≤ 3*Real.pi^2*ρ z)]
  norm_num only [Nat.cast_ofNat]
  rw [Real.mul_rpow (by positivity : 0 ≤ 3*Real.pi^2) (hρ z)]
  have he : (3*Real.pi^2)^(5/3 : ℝ) = (3*Real.pi^2)*(3*Real.pi^2)^(2/3 : ℝ) := by
    rw [show (5/3 : ℝ)=1+2/3 by ring,Real.rpow_add (by positivity : 0 < 3*Real.pi^2),Real.rpow_one]
  rw [he]
  unfold coherentFactor tfKinetic
  field_simp [Real.pi_ne_zero]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_PhaseBathtub
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

theorem phase_bathtub {f : Space → ℝ}
    (hf0 : 0 ≤ᵐ[volume] f) (hf2 : f ≤ᵐ[volume] fun _ => 2*coherentFactor)
    (hf : Integrable f) (hk : Integrable (fun p => ‖p‖^2*f p)) :
    tfKinetic*(∫ p, f p)^(5/3:ℝ) ≤ (1/2:ℝ)*∫ p, ‖p‖^2*f p := by
  let M := ∫ p, f p
  have hM : 0 ≤ M := integral_nonneg_of_ae hf0
  let R := fermiRadius (fun _ => M) 0
  have hR : 0 ≤ R := fermiRadius_nonneg (fun _ => hM) _
  let F : Space → ℝ := (ball 0 R).indicator (fun _ => 2*coherentFactor)
  have hF : Integrable F := by
    apply (integrable_indicator_iff measurableSet_ball).2
    exact integrableOn_const measure_ball_lt_top.ne
  have hFK : Integrable (fun p => ‖p‖^2*F p) := by
    have hc : IntegrableOn (fun p : Space => ‖p‖^2*(2*coherentFactor)) (ball 0 R) :=
      (by fun_prop : Continuous (fun p : Space => ‖p‖^2*(2*coherentFactor))).continuousOn.integrableOn_compact
        (isCompact_closedBall (0:Space) R) |>.mono_set ball_subset_closedBall
    have hh : Integrable ((ball 0 R).indicator (fun p : Space => ‖p‖^2*(2*coherentFactor))) :=
      (integrable_indicator_iff measurableSet_ball).2 hc
    exact hh.congr (Filter.Eventually.of_forall (fun p =>
      Set.indicator_mul_right _ (fun p : Space => ‖p‖^2) (fun _ => 2*coherentFactor)))
  have hmass : (∫ p, F p) = M := by
    rw [integral_indicator measurableSet_ball,integral_const]
    simpa only [smul_eq_mul,Measure.real,Measure.restrict_apply_univ,mul_comm,R] using fermiRadius_ball_mass (fun _ => hM) (0:Space)
  have hkin : (1/2:ℝ)*(∫ p, ‖p‖^2*F p) = tfKinetic*M^(5/3:ℝ) := by
    have heq : (fun p => ‖p‖^2*F p) = (ball 0 R).indicator (fun p => ‖p‖^2*(2*coherentFactor)) := by
      ext p
      exact (Set.indicator_mul_right _ (fun p : Space => ‖p‖^2) (fun _ => 2*coherentFactor)).symm
    rw [heq]
    rw [integral_indicator measurableSet_ball,integral_mul_const]
    have he := fermiRadius_ball_kinetic (fun _ => hM) (0:Space)
    change coherentFactor*(∫ p : Space in ball 0 R, ‖p‖^2) = _ at he
    nlinarith
  have hi : (∫ p, (‖p‖^2-R^2)*F p) ≤ ∫ p, (‖p‖^2-R^2)*f p := by
    have hiF : Integrable (fun p => (‖p‖^2-R^2)*F p) := by
      convert hFK.sub (hF.const_mul (R^2)) using 1
      all_goals try with_reducible_and_instances rfl
      ext p
      change (‖p‖^2-R^2)*F p = ‖p‖^2*F p-R^2*F p
      ring
    have hif : Integrable (fun p => (‖p‖^2-R^2)*f p) := by
      convert hk.sub (hf.const_mul (R^2)) using 1
      all_goals try with_reducible_and_instances rfl
      ext p
      change (‖p‖^2-R^2)*f p = ‖p‖^2*f p-R^2*f p
      ring
    apply integral_mono_ae hiF hif
    filter_upwards [hf0,hf2] with p hp0 hp2
    by_cases hp : p ∈ ball (0:Space) R
    · have hn : ‖p‖ < R := by simpa only [mem_ball,dist_zero_right] using hp
      have hsq : ‖p‖^2-R^2 ≤ 0 := sub_nonpos.mpr (pow_le_pow_left₀ (norm_nonneg _) hn.le 2)
      simpa only [F,Set.indicator_of_mem hp] using mul_le_mul_of_nonpos_left hp2 hsq
    · have hn : R ≤ ‖p‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hp
      have hsq : 0 ≤ ‖p‖^2-R^2 := sub_nonneg.mpr (pow_le_pow_left₀ hR hn 2)
      simpa only [F,Set.indicator_of_notMem hp,mul_zero] using mul_nonneg hsq hp0
  simp only [sub_mul] at hi
  rw [integral_sub hFK (hF.const_mul _),integral_sub hk (hf.const_mul _),
    integral_const_mul,integral_const_mul,hmass] at hi
  change (∫ p, ‖p‖^2*F p)-R^2*M ≤ (∫ p, ‖p‖^2*f p)-R^2*M at hi
  linarith

open MeasureTheory Set Metric
open scoped BigOperators ENNReal

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_PauliMomentum
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PauliMomentum_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal

theorem neumann_lattice_bathtub (S : Finset NeumannSpinMode) :
    tfKinetic*(S.card:ℝ)^(5/3:ℝ) ≤
      (Real.pi^2/2)*∑ q ∈ S, ∑ i, ((q.1 i:ℝ)+1)^2 := by
  have hb := phase_bathtub (Filter.Eventually.of_forall (discretePhaseDensity_nonneg S))
    (Filter.Eventually.of_forall (discretePhaseDensity_pauli S))
    (discretePhaseDensity_integrable S) (discretePhaseDensity_kinetic_integrable S)
  rw [discretePhaseDensity_mass] at hb
  refine hb.trans ?_
  rw [discretePhaseDensity_kinetic_integral,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  have ht := mul_le_mul_of_nonneg_left (momentumCell_kinetic_bound q.1) (by norm_num : (0:ℝ) ≤ 1/2)
  linarith

end Work_PauliMomentum_scope

open MeasureTheory Set
open scoped BigOperators ENNReal

theorem neumann_lattice_lower (S : Finset NeumannSpinMode) :
    tfKinetic*(S.card:ℝ)^(5/3:ℝ) -
        neumannRemainderConstant*((S.card:ℝ)^(4/3:ℝ)+(S.card:ℝ)) ≤
      (Real.pi^2/2)*∑ q ∈ S, ∑ i, (q.1 i:ℝ)^2 := by
  classical
  by_cases hS : S.card = 0
  · have : S = ∅ := Finset.card_eq_zero.mp hS
    subst S
    simp [Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0),
      Real.zero_rpow (by norm_num : (4/3:ℝ) ≠ 0)]
  let M : ℝ := S.card
  let r : ℝ := M^(1/3:ℝ)
  let A : ℝ := tfKinetic*M^(5/3:ℝ)
  let E : ℝ := (Real.pi^2/2)*∑ q ∈ S, ∑ i, (q.1 i:ℝ)^2
  have hM : 0 < M := by
    change 0 < (S.card:ℝ)
    exact_mod_cast Nat.pos_of_ne_zero hS
  have hr : 0 < r := Real.rpow_pos_of_pos hM _
  have hMr : M*r = M^(4/3:ℝ) := by
    dsimp [r]
    calc
      M*M^(1/3:ℝ) = M^(1:ℝ)*M^(1/3:ℝ) := by rw [Real.rpow_one]
      _ = M^(4/3:ℝ) := by rw [←Real.rpow_add hM]; norm_num
  have hAr : A/r = tfKinetic*M^(4/3:ℝ) := by
    dsimp [A,r]
    rw [mul_div_assoc,←Real.rpow_sub hM]
    norm_num
  have hb : A ≤ (1+1/r)*E + (3*Real.pi^2/2)*M*(1+r) := by
    have hh := neumann_lattice_bathtub S
    have hs : (∑ q ∈ S, ∑ i, ((q.1 i:ℝ)+1)^2) ≤
        (1+1/r)*(∑ q ∈ S, ∑ i, (q.1 i:ℝ)^2)+3*M*(1+r) := by
      calc
        _ ≤ ∑ q ∈ S, ∑ i : Fin 3, ((1+1/r)*(q.1 i:ℝ)^2+1+r) := by
          exact Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun i _ => square_shift_bound _ _ hr
        _ = _ := by
          simp only [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_const,
            Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
          dsimp [M]
          ring
    have ht := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ Real.pi^2/2)
    apply hh.trans
    dsimp [E]
    nlinarith
  change A-neumannRemainderConstant*(M^(4/3:ℝ)+M) ≤ E
  by_cases hE : A ≤ E
  · exact (sub_le_self _ (mul_nonneg neumannRemainderConstant_pos.le
      (add_nonneg (Real.rpow_nonneg hM.le _) hM.le))).trans hE
  · have hEA : E ≤ A := (lt_of_not_ge hE).le
    have he : E/r ≤ A/r := div_le_div_of_nonneg_right hEA hr.le
    rw [hAr] at he
    have hc : (3*Real.pi^2/2)*M*(1+r) = (3*Real.pi^2/2)*(M+M^(4/3:ℝ)) := by
      rw [mul_assoc, mul_add, mul_one,hMr]
    rw [hc] at hb
    have hid : (1+1/r)*E = E+E/r := by ring
    rw [hid] at hb
    have ht : 0 ≤ tfKinetic*M := mul_nonneg (by unfold tfKinetic; positivity) hM.le
    unfold neumannRemainderConstant
    nlinarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_NeumannFermions
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

open CoulombAtom

lemma neumann_mode_family_lower {α : Type*} [Fintype α]
    (n : α → Fin 3 → ℕ) (s : α → Fin 2)
    (h : Function.Injective (fun i => (n i,s i))) :
    neumannLowerEnergy (Fintype.card α) ≤
      (1/2:ℝ)*∑ i, ∑ a, (Real.pi*(n i a:ℝ))^2 := by
  classical
  let e : α ↪ NeumannSpinMode := ⟨_,h⟩
  have hb := neumann_lattice_lower (Finset.univ.map e)
  simp only [Finset.card_map,Finset.card_univ,Finset.sum_map] at hb
  refine hb.trans_eq ?_
  simp only [mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  change (Real.pi^2/2)*(n i a:ℝ)^2 = (1/2:ℝ)*(Real.pi^2*(n i a:ℝ)^2)
  ring

variable {N : ℕ}

variable {C : Type*} [DecidableEq C]

lemma cell_coeff_energy_lower (c : Fin N → C)
    {Ψ : (Fin N → Fin 2) → C((Fin N × Fin 3) → I,ℂ)} (hΨ : CellAntisymmetric c Ψ)
    (s : Fin N → Fin 2) (n : (Fin N × Fin 3) → ℕ) :
    cellLowerEnergy c*‖neumannCoeff (Ψ s) n‖^2 ≤
      ((1/2:ℝ)*∑ i : Fin N × Fin 3, (Real.pi*(n i:ℝ))^2)*‖neumannCoeff (Ψ s) n‖^2 := by
  classical
  by_cases hz : neumannCoeff (Ψ s) n = 0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    calc
      _ ≤ ∑ a ∈ Finset.univ.image c,
          (1/2:ℝ)*∑ i ∈ Finset.univ.filter (fun i => c i=a), ∑ k : Fin 3, (Real.pi*(n (i,k):ℝ))^2 := by
        apply Finset.sum_le_sum
        intro a _
        rw [cellCount_eq_fintype]
        have hh := neumann_mode_family_lower
          (fun i : {i : Fin N // c i=a} => fun k => n (i.1,k))
          (fun i : {i : Fin N // c i=a} => s i.1) (cell_coeff_injective c hΨ s n hz a)
        rw [Finset.sum_subtype (p := fun i => c i=a) (Finset.univ.filter (fun i => c i=a))
          (by intro i; simp) (fun i => ∑ k : Fin 3, (Real.pi*(n (i,k):ℝ))^2)]
        exact hh
      _ = _ := by
        rw [←Finset.mul_sum,Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem c (Finset.mem_univ i)),Fintype.sum_prod_type]

theorem neumann_cell_component_lower (c : Fin N → C)
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (hanti : CellAntisymmetric c (fun s => finiteCubeFunction (hf s)))
    (s : Fin N → Fin 2) :
    cellLowerEnergy c * (∫ x, ‖finiteCubeFunction (hf s) x‖^2) ≤
      (1/2:ℝ)*∑ i, ∫ x, ‖finiteCubeGradient (hf s) i x‖^2 := by
  have hm : HasSum
      (fun n => cellLowerEnergy c*‖neumannCoeff (finiteCubeFunction (hf s)) n‖^2)
      (cellLowerEnergy c*(∫ x, ‖finiteCubeFunction (hf s) x‖^2)) := by
    rw [←neumann_parseval]
    exact (neumannCoeff_summable (finiteCubeFunction (hf s))).hasSum.mul_left _
  apply hasSum_le_of_sum_le hm
  intro S
  calc
    _ ≤ ∑ n ∈ S, ((1/2:ℝ)*∑ i : Fin N × Fin 3, (Real.pi*(n i:ℝ))^2)*
        ‖neumannCoeff (finiteCubeFunction (hf s)) n‖^2 := by
      exact Finset.sum_le_sum fun n _ => cell_coeff_energy_lower c hanti s n
    _ = (1/2:ℝ)*(∑ n ∈ S, (∑ i : Fin N × Fin 3, (Real.pi*(n i:ℝ))^2)*
        ‖neumannCoeff (finiteCubeFunction (hf s)) n‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_neumann_spectral_lower (hf s) S) (by norm_num)

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_NeumannCounts
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_NeumannCounts_scope

open MeasureTheory Set
open scoped BigOperators unitInterval

open CoulombAtom
variable {N : ℕ} {C : Type*} [DecidableEq C]

theorem neumann_cells_pressure_lower (c : Fin N → C)
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (hanti : CellAntisymmetric c (fun s => finiteCubeFunction (hf s)))
    (s : Fin N → Fin 2) :
    tfKinetic*(∑ a ∈ Finset.univ.image c, (cellCount c a:ℝ)^(5/3:ℝ)) *
        (∫ x, ‖finiteCubeFunction (hf s) x‖^2) ≤
      (1/2:ℝ)*(∑ i, ∫ x, ‖finiteCubeGradient (hf s) i x‖^2) +
        neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ)) *
          (∫ x, ‖finiteCubeFunction (hf s) x‖^2) := by
  have hb := mul_le_mul_of_nonneg_right (cellLowerEnergy_bound c)
    (integral_nonneg (μ := volume) (fun x => sq_nonneg ‖finiteCubeFunction (hf s) x‖))
  have hl := neumann_cell_component_lower c hf hanti s
  nlinarith

end Work_NeumannCounts_scope

open MeasureTheory Set
open scoped BigOperators unitInterval

open CoulombAtom

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CubeRotations
attribute [-instance] _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombNeumann.cubePartition_probability
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
open scoped BigOperators

lemma radialAverage_integrable {k : CubeSpace → ℝ} (hm : Measurable k) (hk : Integrable k) :
    Integrable (radialAverage k) := (radialAverage_joint_integrable hm hk).integral_prod_right

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_Vartheta
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombNeumann.cubePartition_probability
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
open scoped BigOperators

lemma vartheta_integrable : Integrable vartheta := radialAverage_integrable euclideanCubeOverlap_measurable euclideanCubeOverlap_integrable
lemma varthetaScaled_integrable {b : ℝ} (hb : 0 < b) : Integrable (varthetaScaled b) :=
  (vartheta_integrable.comp_smul (inv_ne_zero hb.ne')).const_mul _

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoulombSelfBound
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom

lemma inv_norm_integrable_ball (r : ℝ) :
    IntegrableOn (fun x : Space => ‖x‖⁻¹) (ball 0 r) := by
  apply integrableOn_ball_of_norm_le_rpow (by simp [Space])
    (show (1:ℝ) < Module.finrank ℝ Space by rw [space_finrank]; norm_num) (C := 1)
  · filter_upwards [] with x
    simp only [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),Real.rpow_neg_one,one_mul,le_refl]
  · exact measurable_norm.inv.aestronglyMeasurable

lemma space_ball_coulomb_integral {r : ℝ} (hr : 0 ≤ r) :
    (∫ x : Space in ball 0 r, ‖x‖⁻¹) = 2*Real.pi*r^2 := by
  have he : (∫ x : Space in ball 0 r, ‖x‖⁻¹) =
      ∫ x : Space, (Iio r).indicator (fun t : ℝ => t⁻¹) ‖x‖ := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Set.indicator,mem_ball,dist_zero_right,mem_Iio]
  rw [he,integral_fun_norm_addHaar volume,space_finrank]
  have hi : (fun t : ℝ => t^(3-1) • (Iio r).indicator (fun t : ℝ => t⁻¹) t) =
      (Iio r).indicator (fun t : ℝ => t) := by
    funext t
    by_cases ht : t < r
    · simp only [Set.indicator,mem_Iio,ht,ite_true,smul_eq_mul]
      by_cases hz : t=0
      · simp [hz]
      · norm_num
        field_simp
    · simp only [Set.indicator,mem_Iio,ht,ite_false,smul_eq_mul,mul_zero]
  rw [hi,setIntegral_indicator measurableSet_Iio]
  have hs : Ioi (0 : ℝ) ∩ Iio r = Ioo 0 r := by ext t; simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo]
  rw [hs,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hr,integral_id]
  rw [space_ball_real_volume (by norm_num : (0:ℝ) ≤ 1)]
  norm_num [smul_eq_mul]
  ring

lemma shifted_truncated_coulomb_integrable (a : Space) (r : ℝ) :
    Integrable ((ball a r).indicator (fun y : Space => ‖a-y‖⁻¹)) := by
  have hi := ((inv_norm_integrable_ball r).integrable_indicator measurableSet_ball).comp_sub_right a
  apply hi.congr
  filter_upwards [] with x
  simp only [Set.indicator,mem_ball,dist_eq_norm,sub_zero,norm_sub_rev a x]

lemma shifted_truncated_coulomb_integral (a : Space) {r : ℝ} (hr : 0 ≤ r) :
    (∫ y : Space, (ball a r).indicator (fun y : Space => ‖a-y‖⁻¹) y) = 2*Real.pi*r^2 := by
  calc
    _ = ∫ y : Space, (ball 0 r).indicator (fun y : Space => ‖y‖⁻¹) (y-a) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Set.indicator,mem_ball,dist_eq_norm,sub_zero,norm_sub_rev a x]
    _ = ∫ y : Space in ball 0 r, ‖y‖⁻¹ := by rw [integral_sub_right_eq_self,integral_indicator measurableSet_ball]
    _ = _ := space_ball_coulomb_integral hr

lemma bounded_density_potential_bound {η : Space → ℝ} (hη : Integrable η)
    (hp : MemLp η (5/3 : ENNReal)) (hn : ∀ x, 0 ≤ η x) {B : ℝ} (hb : ∀ x, η x ≤ B)
    {r : ℝ} (hr : 0 < r) (a : Space) :
    CoulombAnalysis.tfPotential η a ≤ B*(2*Real.pi*r^2)+(∫ y : Space, η y)/r := by
  have hi : Integrable (fun x : Space => B*(ball a r).indicator (fun y : Space => ‖a-y‖⁻¹) x + η x/r) :=
    ((shifted_truncated_coulomb_integrable a r).const_mul B).add (hη.div_const r)
  have he := integral_mono (CoulombAnalysis.tfPotential_integrable hη hp a) hi (fun y => ?_)
  · simpa only [CoulombAnalysis.tfPotential,integral_add ((shifted_truncated_coulomb_integrable a r).const_mul B)
      (hη.div_const r),integral_const_mul,shifted_truncated_coulomb_integral a hr.le,integral_div] using he
  · by_cases hy : y ∈ ball a r
    · rw [Set.indicator_of_mem hy]
      calc
        η y/‖a-y‖ ≤ B*‖a-y‖⁻¹ := by simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right (hb y) (inv_nonneg.mpr (norm_nonneg _))
        _ ≤ _ := le_add_of_nonneg_right (div_nonneg (hn y) hr.le)
    · rw [Set.indicator_of_notMem hy,mul_zero,zero_add]
      have hy' : r ≤ ‖a-y‖ := by simpa only [mem_ball,dist_eq_norm,not_lt,norm_sub_rev y a] using hy
      exact div_le_div_of_nonneg_left (hn y) hr hy'

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CosetWedge
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators

namespace CoulombAtom

def SubgroupFermion {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (T : FormVector n) : Prop :=
  ∀ κ ∈ H, ∀ s, ∀ᵐ x, T.value (s ∘ κ) (x ∘ κ) =
    (((Equiv.Perm.sign κ : ℤ) : ℂ) * T.value s x)

def cosetWedgeTerm {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (T : FormVector n)
    (q : Equiv.Perm (Fin n) ⧸ H) : FormVector n :=
  scaleForm (((Equiv.Perm.sign q.out : ℤ) : ℝ)) (reindexForm q.out.symm T)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CompactPotential
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open scoped BigOperators ContDiff

def coreDensityInteraction {N : ℕ} (ψ : FormVector N) (d : Space → ℝ) : ℝ :=
  ∑ s : Spins N, ∑ j : Fin N, ∫ x : Configuration N,
    ‖ψ.value s x‖^2 * CoulombAnalysis.tfPotential d (x j)

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma bounded_compact_memLp {f : Space → ℝ} (hf : Measurable f)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support f ⊆ J)
    {B : ℝ} (hb : ∀ x, |f x| ≤ B) (p : ENNReal) : MemLp f p := by
  have hi := memLp_indicator_const (μ := volume) p hJ.measurableSet B (Or.inr hJ.measure_lt_top.ne)
  apply hi.mono' hf.aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : x ∈ J
  · simpa only [Set.indicator_of_mem hx,Real.norm_eq_abs] using hb x
  · have hz : f x = 0 := by by_contra hn; exact hx (hs hn)
    simp only [Set.indicator_of_notMem hx,hz,norm_zero,le_refl]

lemma bounded_compact_integrable {f : Space → ℝ} (hf : Measurable f)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support f ⊆ J)
    {B : ℝ} (hb : ∀ x, |f x| ≤ B) : Integrable f :=
  memLp_one_iff_integrable.mp (bounded_compact_memLp hf hJ hs hb 1)

lemma compact_support_potential_bounded {f : Space → ℝ} (h1 : Integrable f)
    (hp : MemLp f (5/3 : ENNReal)) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support f ⊆ J) :
    ∃ C : ℝ, ∀ x : Space, |CoulombAnalysis.tfPotential f x| ≤ C := by
  obtain ⟨R,_,hR⟩ := hJ.isBounded.exists_pos_norm_le
  have hr (y : Space) (hy : f y ≠ 0) : ‖y‖ ≤ R := hR y (hs hy)
  obtain ⟨S,_,hS⟩ := CoulombAnalysis.tfPotential_compact_decay h1 hp hr 1 zero_lt_one
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Space) S).exists_bound_of_continuousOn
    (CoulombAnalysis.tfPotential_continuous h1 hp).continuousOn
  refine ⟨max C 1,fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ S
  · exact (hC x (by simpa using hx)).trans (le_max_left _ _)
  · exact (hS x (le_of_not_ge hx)).trans (le_max_right _ _)

lemma compact_support_coulomb_integrable {f g : Space → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hf : Integrable f) (hg : Integrable g)
    (hgp : MemLp g (5/3 : ENNReal)) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support g ⊆ J) :
    Integrable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖) := by
  have hm : Measurable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  refine ⟨Eventually.of_forall (fun x => ?_),?_⟩
  · simpa only [mul_div_assoc] using (CoulombAnalysis.tfPotential_integrable hg hgp x).const_mul (f x)
  · obtain ⟨C,hC⟩ := compact_support_potential_bounded hg.norm hgp.norm hJ
      (fun x hx => hs (by intro hz; exact hx (by simp [hz])))
    have hi : Integrable (fun x => ‖f x‖*CoulombAnalysis.tfPotential (fun y => ‖g y‖) x) := by
      apply (hf.norm.mul_const C).mono'
        ((hfm.norm.mul (CoulombAnalysis.tfPotential_continuous hg.norm hgp.norm).measurable).aestronglyMeasurable)
      filter_upwards [] with x
      change ‖‖f x‖*CoulombAnalysis.tfPotential (fun y => ‖g y‖) x‖ ≤ ‖f x‖*C
      rw [norm_mul,norm_norm,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)
    apply hi.congr
    filter_upwards [] with x
    simp only [norm_div,norm_mul,norm_norm,CoulombAnalysis.tfPotential,← integral_const_mul]
    congr 1
    funext y
    ring

lemma bounded_compact_coulomb_integrable {f g : Space → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    {J K : Set Space} (hJ : IsCompact J) (hK : IsCompact K)
    (hsf : Function.support f ⊆ J) (hsg : Function.support g ⊆ K)
    {B C : ℝ} (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C) :
    Integrable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖) :=
  compact_support_coulomb_integrable hfm hgm (bounded_compact_integrable hfm hJ hsf hb)
    (bounded_compact_integrable hgm hK hsg hc) (bounded_compact_memLp hgm hK hsg hc _) hK hsg

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SmearingPotential
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

lemma integral_translated_pole (η : Space → ℝ) (a z : Space) :
    (∫ x : Space, η (x-z)/‖a-x‖) = CoulombAnalysis.tfPotential η (a-z) := by
  calc
    _ = ∫ x : Space, η (x-z)/‖(a-z)-(x-z)‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show (a-z)-(x-z)=a-x by abel]
    _ = _ := integral_sub_right_eq_self (fun y : Space => η y/‖(a-z)-y‖) z

lemma translated_pole_integrable {η : Space → ℝ} (h1 : Integrable η)
    (hp : MemLp η (5/3 : ENNReal)) (a z : Space) :
    Integrable (fun x : Space => η (x-z)/‖a-x‖) := by
  have hi := (CoulombAnalysis.tfPotential_integrable h1 hp (a-z)).comp_sub_right z
  apply hi.congr
  filter_upwards [] with x
  rw [show (a-z)-(x-z)=a-x by abel]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_RadialPacket
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

lemma coherentPacket_fderiv {g : Space → ℂ} (hg : Differentiable ℝ g) (z p x v : Space) :
    fderiv ℝ (coherentPacket g z p) x v =
      (fderiv ℝ g (x-z) v + g (x-z) * ((inner ℝ p v : ℂ) * Complex.I)) *
        Complex.exp ((inner ℝ p x : ℂ) * Complex.I) := by
  have hd := (hg (x-z)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const z)
  have hp := ((Complex.ofRealCLM.comp (innerSL ℝ p)).hasFDerivAt (x := x)).mul_const Complex.I
  have hh := hd.mul hp.cexp
  rw [show fderiv ℝ (coherentPacket g z p) x = _ from hh.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul,Complex.ofRealCLM_apply,innerSL_apply_apply,
    Function.comp_apply,id_eq]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FermiMeasure
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

def fermiRegion (ρ : Space → ℝ) : Set (Space × Space) :=
  {q | ‖q.2‖ < fermiRadius ρ q.1}

def fermiMeasure (ρ : Space → ℝ) : Measure (Space × Space) := volume.restrict (fermiRegion ρ)

lemma fermiRadius_measurable {ρ : Space → ℝ} (hm : Measurable ρ) : Measurable (fermiRadius ρ) := by
  unfold fermiRadius
  fun_prop

lemma fermiRegion_measurable {ρ : Space → ℝ} (hm : Measurable ρ) : MeasurableSet (fermiRegion ρ) :=
  measurableSet_lt measurable_snd.norm ((fermiRadius_measurable hm).comp measurable_fst)

lemma fermiRegion_subset {ρ : Space → ℝ} (hn : ∀ z, 0 ≤ ρ z) {J : Set Space}
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, ρ z ≤ B) :
    fermiRegion ρ ⊆ J ×ˢ closedBall 0 ((3*Real.pi^2*B)^(1/3 : ℝ)) := by
  intro q hq
  have hq' : ‖q.2‖ < fermiRadius ρ q.1 := hq
  have hz : ρ q.1 ≠ 0 := by
    intro hz
    simp only [fermiRadius,hz,mul_zero,Real.zero_rpow (by norm_num : (1/3 : ℝ) ≠ 0)] at hq'
    exact (not_lt_of_ge (norm_nonneg _)) hq'
  refine ⟨hs hz,?_⟩
  rw [mem_closedBall,dist_zero_right]
  apply hq'.le.trans
  exact Real.rpow_le_rpow (mul_nonneg (by positivity) (hn q.1))
    (mul_le_mul_of_nonneg_left (hb q.1) (by positivity)) (by norm_num)

lemma fermiMeasure_finite {ρ : Space → ℝ} (hn : ∀ z, 0 ≤ ρ z) {J : Set Space}
    (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, ρ z ≤ B) :
    IsFiniteMeasure (fermiMeasure ρ) := by
  constructor
  rw [fermiMeasure,Measure.restrict_apply_univ]
  exact (measure_mono (fermiRegion_subset hn hs hb)).trans_lt
    (hJ.prod (isCompact_closedBall _ _)).measure_lt_top

lemma fermiMeasure_mem {ρ : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z) {J : Set Space}
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, ρ z ≤ B) :
    ∀ᵐ q ∂fermiMeasure ρ, q ∈ J ×ˢ closedBall 0 ((3*Real.pi^2*B)^(1/3 : ℝ)) :=
  (ae_restrict_mem (fermiRegion_measurable hm)).mono (fun _ hq => fermiRegion_subset hn hs hb hq)

lemma fermiMeasure_integral {ρ : Space → ℝ} (hm : Measurable ρ)
    {f : Space × Space → ℝ} (hf : Integrable f (fermiMeasure ρ)) :
    (∫ q, f q ∂fermiMeasure ρ) =
      ∫ z : Space, ∫ p : Space in ball 0 (fermiRadius ρ z), f (z,p) := by
  have hi : Integrable ((fermiRegion ρ).indicator f) :=
    (integrable_indicator_iff (fermiRegion_measurable hm)).2 hf
  rw [Measure.volume_eq_prod] at hi
  rw [fermiMeasure,← integral_indicator (fermiRegion_measurable hm),Measure.volume_eq_prod,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [Set.indicator,fermiRegion,mem_ofPred_eq,mem_ball,dist_zero_right]
  rfl

lemma fermiMeasure_integrable_continuous {ρ : Space → ℝ} (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) {f : Space × Space → ℝ} (hf : Continuous f) :
    Integrable f (fermiMeasure ρ) :=
  (hf.continuousOn.integrableOn_compact (hJ.prod (isCompact_closedBall _ _))).mono_set
    (fermiRegion_subset hn hs hb)

lemma fermiMeasure_mass {ρ : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) :
    2*coherentFactor*(fermiMeasure ρ).real univ = ∫ z, ρ z := by
  have hi := fermiMeasure_integrable_continuous hn hJ hs hb (continuous_const : Continuous (fun _ : Space × Space => (1:ℝ)))
  have he := fermiMeasure_integral hm hi
  simp only [integral_const,smul_eq_mul,mul_one] at he
  rw [he,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  simpa only [Measure.real,Measure.restrict_apply_univ] using fermiRadius_ball_mass hn z

lemma fermiMeasure_kinetic {ρ : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) :
    coherentFactor*(∫ q, ‖q.2‖^2 ∂fermiMeasure ρ) = tfKinetic*∫ z, (ρ z)^(5/3 : ℝ) := by
  rw [fermiMeasure_integral hm (fermiMeasure_integrable_continuous hn hJ hs hb (by fun_prop)),
    ← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  exact fermiRadius_ball_kinetic hn z

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CoherentDensity
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

namespace CoulombAtom

def coherentDensity (g : Space → ℂ) (μ : Measure (Space × Space)) (x : Space) : ℝ :=
  coherentFactor * ∫ q, ‖coherentPacket g q.1 q.2 x‖^2 ∂μ

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FermiDensity
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

def smearedPacketDensity (g ρ : Space → ℝ) (x : Space) : ℝ :=
  ∫ z : Space, ρ z * (g (x-z))^2

lemma coherentDensity_fermi {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : Continuous g) (x : Space) :
    2*coherentDensity (fun x => (g x : ℂ)) (fermiMeasure ρ) x = smearedPacketDensity g ρ x := by
  have hi := fermiMeasure_integrable_continuous hn hJ hs hb
    (show Continuous (fun q : Space × Space => (g (x-q.1))^2) by fun_prop)
  simp only [coherentDensity,coherentPacket_norm,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [← mul_assoc,fermiMeasure_integral hm hi,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [integral_const]
  simp only [smul_eq_mul,Measure.real,Measure.restrict_apply_univ]
  rw [← mul_assoc]
  exact congrArg (fun a : ℝ => a*(g (x-z))^2) (fermiRadius_ball_mass hn z)

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma coulomb_double_eq_potential {f g : Space → ℝ}
    (hi : Integrable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖)) :
    (∫ r : Space × Space, f r.1*g r.2/‖r.1-r.2‖) =
      ∫ x : Space, f x*CoulombAnalysis.tfPotential g x := by
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  simp only [CoulombAnalysis.tfPotential,mul_div_assoc,integral_const_mul]

lemma coulomb_potential_pair_integrable {f g : Space → ℝ}
    (hi : Integrable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖)) :
    Integrable (fun x : Space => f x*CoulombAnalysis.tfPotential g x) := by
  simpa only [CoulombAnalysis.tfPotential,mul_div_assoc,integral_const_mul] using hi.integral_prod_left

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SmearRepulsion
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom

def translatedDensity (η : Space → ℝ) (a : Space) (x : Space) : ℝ := η (x-a)

def smearPair (η : Space → ℝ) (a b : Space) : ℝ :=
  ∫ r : Space × Space, translatedDensity η a r.1*translatedDensity η b r.2/‖r.1-r.2‖

lemma translatedDensity_support {η : Space → ℝ} {R : ℝ}
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (a : Space) :
    Function.support (translatedDensity η a) ⊆ closedBall a R := by
  intro x hx
  simpa only [mem_closedBall,dist_eq_norm] using hs (x-a) hx

lemma translatedDensity_measurable {η : Space → ℝ} (hm : Measurable η) (a : Space) :
    Measurable (translatedDensity η a) := hm.comp (measurable_id.sub_const a)

lemma translatedDensity_mass (η : Space → ℝ) (a : Space) :
    (∫ x : Space, translatedDensity η a x) = ∫ x : Space, η x := integral_sub_right_eq_self η a

lemma smearPair_integrable {η : Space → ℝ} (hm : Measurable η)
    {R B : ℝ} (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B) (a b : Space) :
    Integrable (fun r : Space × Space => translatedDensity η a r.1*translatedDensity η b r.2/‖r.1-r.2‖) :=
  bounded_compact_coulomb_integrable (translatedDensity_measurable hm a) (translatedDensity_measurable hm b)
    (isCompact_closedBall _ _) (isCompact_closedBall _ _)
    (translatedDensity_support hs a) (translatedDensity_support hs b)
    (fun x => hb (x-a)) (fun x => hb (x-b))

lemma potential_translatedDensity (η : Space → ℝ) (a x : Space) :
    CoulombAnalysis.tfPotential (translatedDensity η a) x = CoulombAnalysis.tfPotential η (x-a) :=
  integral_translated_pole η x a

lemma smearPair_self {η : Space → ℝ} (hm : Measurable η)
    {R B : ℝ} (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B) (a : Space) :
    smearPair η a a = smearPair η 0 0 := by
  rw [smearPair,coulomb_double_eq_potential (smearPair_integrable hm hs hb a a)]
  simp only [potential_translatedDensity,translatedDensity]
  rw [integral_sub_right_eq_self (fun x : Space => η x*CoulombAnalysis.tfPotential η x) a]
  rw [smearPair,coulomb_double_eq_potential (smearPair_integrable hm hs hb 0 0)]
  simp only [potential_translatedDensity,translatedDensity,sub_zero]

def finiteSmear {n : ℕ} (η : Space → ℝ) (y : Fin n → Space) (x : Space) : ℝ :=
  ∑ i : Fin n, translatedDensity η (y i) x

lemma finiteSmear_direct {n : ℕ} (η : Space → ℝ) (y : Fin n → Space)
    (hm : Measurable η) {R B : ℝ} (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B) :
    (∫ r : Space × Space, finiteSmear η y r.1*finiteSmear η y r.2/‖r.1-r.2‖) =
      ∑ i : Fin n, ∑ j : Fin n, smearPair η (y i) (y j) := by
  simp only [finiteSmear]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum,Finset.sum_div]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => smearPair_integrable hm hs hb (y i) (y j))
  · intro i _
    exact integrable_finsetSum _ (fun j _ => smearPair_integrable hm hs hb (y i) (y j))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_RetainedRepulsion
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open scoped BigOperators

lemma smearPair_self_bound {η : Space → ℝ} (hm : Measurable η) (hn : ∀ x, 0 ≤ η x)
    {R b : ℝ} (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : 0 < b)
    (hB : ∀ x, η x ≤ b⁻¹^3) (h1 : ∫ x : Space, η x = 1) :
    smearPair η 0 0 ≤ (2*Real.pi+1)/b := by
  have haB : ∀ x, |η x| ≤ b⁻¹^3 := fun x => by rw [abs_of_nonneg (hn x)]; exact hB x
  have hsupport : Function.support η ⊆ closedBall 0 R :=
    fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hs x hx
  have hi := bounded_compact_integrable hm (isCompact_closedBall _ _) hsupport haB
  have hp := bounded_compact_memLp hm (isCompact_closedBall _ _) hsupport haB (5/3 : ENNReal)
  have hc : ∀ x, CoulombAnalysis.tfPotential η x ≤ (2*Real.pi+1)/b := by
    intro x
    have hh := bounded_density_potential_bound hi hp hn hB hb x
    rw [h1] at hh
    convert hh using 1; field_simp
  have hzero : translatedDensity η 0 = η := by funext x; simp only [translatedDensity,sub_zero]
  have hii := smearPair_integrable hm hs haB 0 0
  rw [hzero] at hii
  rw [smearPair,hzero,coulomb_double_eq_potential hii]
  calc
    _ ≤ ∫ x : Space, η x*((2*Real.pi+1)/b) :=
      integral_mono (coulomb_potential_pair_integrable hii) (hi.mul_const _)
        (fun x => mul_le_mul_of_nonneg_left (hc x) (hn x))
    _ = _ := by rw [integral_mul_const,h1,one_mul]

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma retained_pair_sum_le {n k : ℕ} (x : Fin n → Space) (e : Fin k ↪ Fin n) :
    (∑ i : Fin k, ∑ j : Fin k, if i < j then 1/‖x (e i)-x (e j)‖ else 0) ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then 1/‖x i-x j‖ else 0 := by
  have he (i j : Fin k) : (if i ≠ j then 1/‖x (e i)-x (e j)‖ else 0) =
      (if e i ≠ e j then 1/‖x (e i)-x (e j)‖ else 0) := by simp only [ne_eq,e.injective.eq_iff]
  have h := calc
    (∑ i : Fin k, ∑ j : Fin k, if i ≠ j then 1/‖x (e i)-x (e j)‖ else 0) =
        ∑ i : Fin k, ∑ j : Fin k, if e i ≠ e j then 1/‖x (e i)-x (e j)‖ else 0 := by simp_rw [he]
    _ ≤ ∑ i : Fin k, ∑ j : Fin n, if e i ≠ j then 1/‖x (e i)-x j‖ else 0 :=
      Finset.sum_le_sum (fun i _ => sum_embedding_le_univ e (f := fun j => if e i ≠ j then 1/‖x (e i)-x j‖ else 0) (fun j => by split_ifs <;> positivity))
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, if i ≠ j then 1/‖x i-x j‖ else 0 :=
      sum_embedding_le_univ e (f := fun i => ∑ j : Fin n, if i ≠ j then 1/‖x i-x j‖ else 0)
        (fun i => Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity))
  rw [sum_ordered_pairs _ (fun i j => by rw [norm_sub_rev]),
    sum_ordered_pairs _ (fun i j => by rw [norm_sub_rev])] at h
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RetainedSmear
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombNeumann.cubePartition_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

def retainedSmear (b : ℝ) (S : Finset (Fin N)) (x : Configuration N) (y : Space) : ℝ :=
  ∑ i ∈ S, varthetaScaled b (y-x i)

lemma retainedSmear_nonneg {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) : 0 ≤ retainedSmear b S x y :=
  Finset.sum_nonneg (fun _ _ => varthetaScaled_nonneg hb _)

lemma retainedSmear_le_full {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) : retainedSmear b S x y ≤ physicalSmear b x y := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun _ _ _ => varthetaScaled_nonneg hb _)

lemma retainedSmear_ite (b : ℝ) (S : Finset (Fin N)) (x : Configuration N) (y : Space) :
    retainedSmear b S x y = ∑ i, if i ∈ S then varthetaScaled b (y-x i) else 0 := by
  classical
  simp [retainedSmear]

lemma retainedSmear_measurable (b : ℝ) (S : Configuration N → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {x | i ∈ S x}) :
    Measurable (fun p : Configuration N × Space => retainedSmear b (S p.1) p.1 p.2) := by
  simp_rw [retainedSmear_ite]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurable_fst (hS i))
    ((varthetaScaled_measurable b).comp (measurable_snd.sub ((measurable_pi_apply i).comp measurable_fst)))
    measurable_const

lemma retainedSmear_pressure_integrable {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) : Integrable (fun y => retainedSmear b S x y^(5/3:ℝ)) := by
  have hm : Measurable (fun y => retainedSmear b S x y) := by
    unfold retainedSmear
    exact Finset.measurable_sum _ (fun i _ => (varthetaScaled_measurable b).comp (measurable_id.sub_const (x i)))
  apply (physicalSmear_pressure_integrable hb x).mono' (hm.pow_const _).aestronglyMeasurable
  exact Eventually.of_forall fun y => by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (retainedSmear_nonneg hb S x y) _)]
    exact Real.rpow_le_rpow (retainedSmear_nonneg hb S x y) (retainedSmear_le_full hb S x y) (by norm_num)

def retainedPressure (b : ℝ) (S : Finset (Fin N)) (x : Configuration N) : ℝ :=
  ∫ y, retainedSmear b S x y^(5/3:ℝ)

lemma retainedPressure_measurable (b : ℝ) (S : Configuration N → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {x | i ∈ S x}) :
    Measurable (fun x => retainedPressure b (S x) x) :=
  ((retainedSmear_measurable b S hS).pow_const _).stronglyMeasurable.integral_prod_right.measurable

lemma retainedPressure_nonneg {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) : 0 ≤ retainedPressure b S x :=
  integral_nonneg (fun y => Real.rpow_nonneg (retainedSmear_nonneg hb S x y) _)

lemma retainedPressure_le_full {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) : retainedPressure b S x ≤ physicalPressure b x := by
  exact integral_mono (retainedSmear_pressure_integrable hb S x) (physicalSmear_pressure_integrable hb x)
    (fun y => Real.rpow_le_rpow (retainedSmear_nonneg hb S x y) (retainedSmear_le_full hb S x y) (by norm_num))

lemma retainedPressure_le_average {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) : retainedPressure b S x ≤ physicalPressureAverage b x :=
  (retainedPressure_le_full hb S x).trans (physicalPressure_le_average hb x)

lemma retainedSmear_support {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space)
    (hy : ∀ i ∈ S, Real.sqrt 3*b ≤ ‖y-x i‖) : retainedSmear b S x y = 0 := by
  exact Finset.sum_eq_zero (fun i hi => varthetaScaled_support hb _ (hy i hi))

lemma integral_retainedSmear {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) : (∫ y, retainedSmear b S x y) = (S.card:ℝ) := by
  unfold retainedSmear
  rw [integral_finsetSum _ (fun i _ => (varthetaScaled_integrable hb).comp_sub_right (x i))]
  simp only [integral_sub_right_eq_self,integral_varthetaScaled hb,Finset.sum_const, nsmul_eq_mul,mul_one]

end CoulombNeumann

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

lemma varthetaScaled_support_bound {b : ℝ} (hb : 0 < b) (x : Space)
    (hx : varthetaScaled b x ≠ 0) : ‖x‖ ≤ Real.sqrt 3*b := by
  by_contra! h
  exact hx (varthetaScaled_support hb x h.le)

lemma finiteSmear_retention (b : ℝ) (S : Finset (Fin N)) (x : Configuration N) (y : Space) :
    finiteSmear (varthetaScaled b) (x ∘ (S.orderEmbOfFin rfl).toEmbedding) y = retainedSmear b S x y := by
  classical
  change (∑ i : Fin S.card, varthetaScaled b (y-x ((S.orderIsoOfFin rfl i):Fin N))) = _
  exact ((S.orderIsoOfFin rfl).toEquiv.sum_comp (fun i : ↥S => varthetaScaled b (y-x i))).trans
    (Finset.sum_attach S (fun i => varthetaScaled b (y-x i)))

end CoulombNeumann

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

def retainedDirect (b : ℝ) (S : Finset (Fin N)) (x : Configuration N) : ℝ :=
  (1/2:ℝ)*∫ r : Space × Space,
    retainedSmear b S x r.1*retainedSmear b S x r.2/‖r.1-r.2‖

lemma retainedDirect_nonneg {b : ℝ} (hb : 0 < b) (S : Finset (Fin N)) (x : Configuration N) :
    0 ≤ retainedDirect b S x := by
  apply mul_nonneg (by norm_num)
  exact integral_nonneg (fun r => div_nonneg
    (mul_nonneg (retainedSmear_nonneg hb S x r.1) (retainedSmear_nonneg hb S x r.2)) (norm_nonneg _))

lemma retainedDirect_measurable (b : ℝ) (S : Configuration N → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {x | i ∈ S x}) :
    Measurable (fun x => retainedDirect b (S x) x) := by
  have h1 : Measurable (fun p : Configuration N × (Space × Space) => retainedSmear b (S p.1) p.1 p.2.1) := by
    have hf : Measurable (fun p : Configuration N × (Space × Space) => (p.1,p.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hh := (retainedSmear_measurable b S hS).comp hf
    simpa only [Function.comp_def] using hh
  have h2 : Measurable (fun p : Configuration N × (Space × Space) => retainedSmear b (S p.1) p.1 p.2.2) := by
    have hf : Measurable (fun p : Configuration N × (Space × Space) => (p.1,p.2.2)) :=
      measurable_fst.prodMk (measurable_snd.comp measurable_snd)
    have hh := (retainedSmear_measurable b S hS).comp hf
    simpa only [Function.comp_def] using hh
  have hk : Measurable (fun p : Configuration N × (Space × Space) => ‖p.2.1-p.2.2‖) := by fun_prop
  exact ((h1.mul h2).div hk).stronglyMeasurable.integral_prod_right.measurable.const_mul _

def pointRepulsion (x : Configuration N) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, if i < j then 1/‖x i-x j‖ else 0

lemma pointRepulsion_mul (x : Configuration N) (w : ℝ) :
    pointRepulsion x*w = ∑ i : Fin N, ∑ j : Fin N, if i < j then w/‖x i-x j‖ else 0 := by
  unfold pointRepulsion
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RetainedMeasurable
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombNeumann.cubePartition_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_RetainedMeasurable_scope

open MeasureTheory Set Filter
open scoped BigOperators

open CoulombAtom
variable {N : ℕ} {A : Type*} [MeasurableSpace A]

lemma retainedSmear_measurable_eval (b : ℝ) (S : A → Finset (Fin N))
    (u : A → Configuration N) (v : A → Space)
    (hS : ∀ i, MeasurableSet {a | i ∈ S a}) (hu : Measurable u) (hv : Measurable v) :
    Measurable (fun a => retainedSmear b (S a) (u a) (v a)) := by
  simp_rw [retainedSmear_ite]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (hS i)
    ((varthetaScaled_measurable b).comp (hv.sub ((measurable_pi_apply i).comp hu))) measurable_const

lemma retainedPressure_measurable_param (b : ℝ) (S : A → Finset (Fin N))
    (u : A → Configuration N) (hS : ∀ i, MeasurableSet {a | i ∈ S a}) (hu : Measurable u) :
    Measurable (fun a => retainedPressure b (S a) (u a)) := by
  have hh := retainedSmear_measurable_eval b (fun p : A × Space => S p.1)
    (fun p => u p.1) Prod.snd (fun i => measurable_fst (hS i)) (hu.comp measurable_fst) measurable_snd
  exact (hh.pow_const _).stronglyMeasurable.integral_prod_right.measurable

lemma retainedDirect_measurable_param (b : ℝ) (S : A → Finset (Fin N))
    (u : A → Configuration N) (hS : ∀ i, MeasurableSet {a | i ∈ S a}) (hu : Measurable u) :
    Measurable (fun a => retainedDirect b (S a) (u a)) := by
  have h1 := retainedSmear_measurable_eval b (fun p : A × (Space × Space) => S p.1)
    (fun p => u p.1) (fun p => p.2.1) (fun i => measurable_fst (hS i))
    (hu.comp measurable_fst) (measurable_fst.comp measurable_snd)
  have h2 := retainedSmear_measurable_eval b (fun p : A × (Space × Space) => S p.1)
    (fun p => u p.1) (fun p => p.2.2) (fun i => measurable_fst (hS i))
    (hu.comp measurable_fst) (measurable_snd.comp measurable_snd)
  have hk : Measurable (fun p : A × (Space × Space) => ‖p.2.1-p.2.2‖) := by fun_prop
  exact ((h1.mul h2).div hk).stronglyMeasurable.integral_prod_right.measurable.const_mul _

end Work_RetainedMeasurable_scope

open MeasureTheory Set
open scoped BigOperators unitInterval

open CoulombAtom
variable {N : ℕ}

theorem neumann_global_smooth_component
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (hanti : FlatAntisymmetric f)
    (hm : ∀ s, MemLp (f s) 2)
    (hg : ∀ s q, MemLp (fun x => fderiv ℝ (f s) x (Pi.single q 1)) 2)
    (s : Fin N → Fin 2) :
    tfKinetic*(∫ x, cellPressure (pointCell x)*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ q, ∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2) +
        neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(∫ x, ‖f s x‖^2) := by
  classical
  have hc (z : (Fin N × Fin 3) → ℤ) :
      tfKinetic*(∫ x in floorCube z, cellPressure (pointCell x)*‖f s x‖^2) ≤
        (1/2:ℝ)*(∑ q, ∫ x in floorCube z, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2) +
        neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(∫ x in floorCube z, ‖f s x‖^2) := by
    have hh := neumann_cells_pressure_lower (indexCell z)
      (fun s => shiftedFunction_contDiff (hf s) z) (shiftedFunction_anti hf hanti z) s
    rw [←cellPressure_eq] at hh
    have hegrad (q : Fin N × Fin 3) :
        (∫ x, ‖finiteCubeGradient (shiftedFunction_contDiff (hf s) z) q x‖^2) =
          ∫ x in floorCube z, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2 := by
      calc
        _ = ∫ x : (Fin N × Fin 3) → I, ‖fderiv ℝ (f s) (cubeShift z x) (Pi.single q 1)‖^2 := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact congrArg (fun v : ℂ => ‖v‖^2) (shiftedFunction_gradient (hf s) z q x)
        _ = _ := integral_cubeShift z _ (hg s q).norm.integrable_sq.aestronglyMeasurable.restrict
    simp_rw [hegrad] at hh
    have hv : (∫ x, ‖finiteCubeFunction (shiftedFunction_contDiff (hf s) z) x‖^2) =
        ∫ x in floorCube z, ‖f s x‖^2 :=
      integral_cubeShift z (fun x => ‖f s x‖^2) (hm s).norm.integrable_sq.aestronglyMeasurable.restrict
    rw [hv] at hh
    rw [integral_floorCube_pressure]
    nlinarith
  have hasC {g : ((Fin N × Fin 3) → ℝ) → ℝ} (hi : Integrable g) :
      HasSum (fun z : (Fin N × Fin 3) → ℤ => ∫ x in floorCube z, g x) (∫ x, g x) := by
    have h := hasSum_integral_iUnion floorCube_measurable floorCube_disjoint hi.integrableOn
    simpa only [floorCube_cover,Measure.restrict_univ] using h
  have hl := (hasC (flatPressure_integrable (hm s))).mul_left tfKinetic
  have hr := ((hasSum_sum (s := Finset.univ) (fun q _ => hasC (hg s q).norm.integrable_sq)).mul_left (1/2:ℝ)).add
    ((hasC (hm s).norm.integrable_sq).mul_left (neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))))
  exact hasSum_le hc hl hr

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_FlatFermionMollify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators Topology Convolution ContDiff

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

theorem exists_flatFermion_smooth_approx
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    {g : (Fin N → Fin 2) → (Fin N × Fin 3) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hm : ∀ s, MemLp (f s) 2) (hg : ∀ s q, MemLp (g s q) 2)
    (ha : FlatAEAntisymmetric f)
    (hw : ∀ s q (φ : ((Fin N × Fin 3) → ℝ) → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f s x * Complex.ofReal (lineDeriv ℝ φ x (Pi.single q 1))) =
        -(∫ x, g s q x * (φ x:ℂ))) :
    ∃ u : ℕ → (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ,
      (∀ n s, ContDiff ℝ ∞ (u n s)) ∧
      (∀ n, FlatAntisymmetric (u n)) ∧
      (∀ n s, MemLp (u n s) 2) ∧
      (∀ n s q, MemLp (fun x => fderiv ℝ (u n s) x (Pi.single q 1)) 2) ∧
      (∀ n, (∑ s, ∫ x, ‖u n s x‖^2) ≤ ∑ s, ∫ x, ‖f s x‖^2) ∧
      (∀ n, (∑ s, ∑ q, ∫ x, ‖fderiv ℝ (u n s) x (Pi.single q 1)‖^2) ≤
        ∑ s, ∑ q, ∫ x, ‖g s q x‖^2) ∧
      (∀ s, ∀ᵐ x, Tendsto (fun n => u n s x) atTop (𝓝 (f s x))) := by
  let k : ℕ → ((Fin N × Fin 3) → ℝ) → ℝ := fun n => (shrinkingBump n).normed volume
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)
  let v : ℕ → (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ := fun n s => k n ⋆[L] f s
  have hk (n : ℕ) : ContDiff ℝ ∞ (k n) := (shrinkingBump n).contDiff_normed
  have hkc (n : ℕ) : HasCompactSupport (k n) := (shrinkingBump n).hasCompactSupport_normed
  have hk0 (n : ℕ) : ∀ x, 0 ≤ k n x := (shrinkingBump n).nonneg_normed
  have hk1 (n : ℕ) : (∫ x, k n x) = 1 := (shrinkingBump n).integral_normed
  have hlocal (s : Fin N → Fin 2) := (hm s).locallyIntegrable (by norm_num : (1:ENNReal) ≤ 2)
  have hv (n : ℕ) (s : Fin N → Fin 2) : ContDiff ℝ ∞ (v n s) :=
    (hkc n).contDiff_convolution_left L (hk n) (hlocal s)
  have hv1 (n : ℕ) (s : Fin N → Fin 2) : ContDiff ℝ 1 (v n s) := (hv n s).of_le (by simp)
  have hv2 (n : ℕ) (s : Fin N → Fin 2) : MemLp (v n s) 2 ∧
      (∫ x, ‖v n s x‖^2) ≤ ∫ x, ‖f s x‖^2 :=
    convolution_l2_contraction (hk n).continuous (hkc n) (hk0 n) (hk1 n) (hm s)
  have hdv (n : ℕ) (s : Fin N → Fin 2) (q : Fin N × Fin 3) :
      (fun x => fderiv ℝ (v n s) x (Pi.single q 1)) = k n ⋆[L] g s q := by
    funext x
    exact mollified_weak_derivative (hk n) (hkc n) (hlocal s) (Pi.single q 1) (hw s q) x
  have hdv2 (n : ℕ) (s : Fin N → Fin 2) (q : Fin N × Fin 3) :
      MemLp (fun x => fderiv ℝ (v n s) x (Pi.single q 1)) 2 ∧
      (∫ x, ‖fderiv ℝ (v n s) x (Pi.single q 1)‖^2) ≤ ∫ x, ‖g s q x‖^2 := by
    have hh := convolution_l2_contraction (hk n).continuous (hkc n) (hk0 n) (hk1 n) (hg s q)
    change MemLp (k n ⋆[L] g s q) 2 ∧
      (∫ x, ‖(k n ⋆[L] g s q) x‖^2) ≤ ∫ x, ‖g s q x‖^2 at hh
    simpa only [← hdv n s q] using hh
  have ht (s : Fin N → Fin 2) : ∀ᵐ x, Tendsto (fun n => v n s x) atTop (𝓝 (f s x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      shrinkingBump_tendsto
      (Eventually.of_forall fun n => le_refl (2*(shrinkingBump (E := (Fin N × Fin 3) → ℝ) n).rIn))
      (hlocal s)
  refine ⟨fun n => flatFermionAverage (v n), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n s => flatFermionAverage_contDiff (hv n) s
  · exact fun n => flatFermionAverage_anti (v n)
  · exact fun n s => flatFermionAverage_memLp (fun s => (hv2 n s).1) s
  · exact fun n s q => flatFermionAverage_gradient_memLp (hv1 n) (fun s q => (hdv2 n s q).1) s q
  · intro n
    exact (flatFermionAverage_mass_le (fun s => (hv2 n s).1)).trans
      (Finset.sum_le_sum fun s _ => (hv2 n s).2)
  · intro n
    exact (flatFermionAverage_kinetic_le (hv1 n) (fun s q => (hdv2 n s q).1)).trans
      (Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun q _ => (hdv2 n s q).2)
  · exact flatFermionAverage_ae_tendsto ha ht

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_NeumannPhysical
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

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

namespace CoulombNeumann
open CoulombAtom

variable {N : ℕ}

theorem neumann_affine_smooth_component
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (ha : FlatAntisymmetric f)
    (hm : ∀ s, MemLp (f s) 2)
    (hg : ∀ s q, MemLp (fun x => fderiv ℝ (f s) x (Pi.single q 1)) 2)
    {b : ℝ} (hb : 0 < b) (t : Fin 3 → ℝ) (s : Fin N → Fin 2) :
    tfKinetic*(∫ x, gridPressure b t x*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ q, ∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2) +
        b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(∫ x, ‖f s x‖^2) := by
  have hf' (s) : ContDiff ℝ 1 (fun x => f s (affineGrid b t x)) :=
    (hf s).comp ((affineGrid_contDiff b t).of_le (by simp))
  have hm' (s) : MemLp (fun x => f s (affineGrid b t x)) 2 :=
    memLp_comp_affine (hm s) hb.ne' _
  have hg' (s) (q : Fin N × Fin 3) : MemLp
      (fun x => fderiv ℝ (fun y => f s (affineGrid b t y)) x (Pi.single q 1)) 2 := by
    simp_rw [affineGrid_fderiv (hf s)]
    exact (memLp_comp_affine (hg s q) hb.ne' _).const_smul b
  have hh := neumann_global_smooth_component hf' (affineGrid_anti ha b t) hm' hg' s
  let J : ℝ := (b ^ Module.finrank ℝ ((Fin N × Fin 3) → ℝ))⁻¹
  have hJ : 0 < J := inv_pos.mpr (pow_pos hb _)
  have he : (∫ x, cellPressure (pointCell x)*‖f s (affineGrid b t x)‖^2) =
      J*b^2*(∫ x, gridPressure b t x*‖f s x‖^2) := by
    have hh := integral_comp_affine (fun x => gridPressure b t x*‖f s x‖^2) hb (gridTranslation t)
    change (∫ x, gridPressure b t (affineGrid b t x)*‖f s (affineGrid b t x)‖^2) = J * _ at hh
    have he (x : (Fin N × Fin 3) → ℝ) : gridPressure b t (affineGrid b t x) =
        b⁻¹^2*cellPressure (pointCell x) := by
      simp only [gridPressure,affineGridInv_affineGrid hb.ne']
    simp only [he,mul_assoc,integral_const_mul] at hh
    have hh' := congrArg (fun v : ℝ => b^2*v) hh
    convert hh' using 1 <;> field_simp [hb.ne']
  have heK (q : Fin N × Fin 3) :
      (∫ x, ‖fderiv ℝ (fun y => f s (affineGrid b t y)) x (Pi.single q 1)‖^2) =
      b^2*J*(∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2) := by
    simp_rw [affineGrid_fderiv (hf s),norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
    have hh := integral_comp_affine (fun x => ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2) hb (gridTranslation t)
    change (∫ x, ‖fderiv ℝ (f s) (affineGrid b t x) (Pi.single q 1)‖^2) = J * _ at hh
    rw [hh,mul_assoc]
  have heM : (∫ x, ‖f s (affineGrid b t x)‖^2) = J*(∫ x, ‖f s x‖^2) :=
    by
      simpa only [affineGrid,smul_eq_mul] using integral_comp_affine (fun x => ‖f s x‖^2) hb (gridTranslation t)
  simp_rw [he,heK,heM,←Finset.mul_sum] at hh
  apply (mul_le_mul_iff_right₀ (mul_pos hJ (sq_pos_of_pos hb))).mp
  calc
    _ = tfKinetic*(J*b^2*(∫ x, gridPressure b t x*‖f s x‖^2)) := by ring
    _ ≤ (1/2:ℝ)*(b^2*J*(∑ q, ∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2)) +
        neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(J*(∫ x, ‖f s x‖^2)) := hh
    _ = _ := by field_simp [hb.ne']

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_PressureWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PressureWeak_scope

open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

open CoulombAtom
variable {N : ℕ}

theorem pressure_weak_of_smooth
    (W : ((Fin N × Fin 3) → ℝ) → ℝ) (hW : ∀ x, 0 ≤ W x)
    (hWi : ∀ {v : ((Fin N × Fin 3) → ℝ) → ℂ}, MemLp v 2 →
      Integrable (fun x => W x*‖v x‖^2))
    {C : ℝ} (hC : 0 ≤ C)
    (hsm : ∀ {u : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ},
      (∀ s, ContDiff ℝ 1 (u s)) → FlatAntisymmetric u →
      (∀ s, MemLp (u s) 2) →
      (∀ s q, MemLp (fun x => fderiv ℝ (u s) x (Pi.single q 1)) 2) →
      ∀ s, tfKinetic*(∫ x, W x*‖u s x‖^2) ≤
        (1/2:ℝ)*(∑ q, ∫ x, ‖fderiv ℝ (u s) x (Pi.single q 1)‖^2) +
          C*(∫ x, ‖u s x‖^2))
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    {g : (Fin N → Fin 2) → (Fin N × Fin 3) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hm : ∀ s, MemLp (f s) 2) (hg : ∀ s q, MemLp (g s q) 2)
    (ha : FlatAEAntisymmetric f)
    (hw : ∀ s q (φ : ((Fin N × Fin 3) → ℝ) → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f s x*Complex.ofReal (lineDeriv ℝ φ x (Pi.single q 1))) =
        -(∫ x, g s q x*(φ x:ℂ))) :
    tfKinetic*(∑ s, ∫ x, W x*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖g s q x‖^2) + C*(∑ s, ∫ x, ‖f s x‖^2) := by
  obtain ⟨u,hu,ha',hm',hg',hb,hb',ht⟩ := exists_flatFermion_smooth_approx hm hg ha hw
  have hT : 0 ≤ tfKinetic := CoulombAnalysis.tfKinetic_pos.le
  have hi (n : ℕ) : Integrable (fun x => tfKinetic*∑ s, W x*‖u n s x‖^2) :=
    (integrable_finsetSum _ (fun s _ => hWi (hm' n s))).const_mul _
  have hif : Integrable (fun x => tfKinetic*∑ s, W x*‖f s x‖^2) :=
    (integrable_finsetSum _ (fun s _ => hWi (hm s))).const_mul _
  have hbound (n : ℕ) :
      (∫ x, tfKinetic*∑ s, W x*‖u n s x‖^2) ≤
        (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖g s q x‖^2) + C*(∑ s, ∫ x, ‖f s x‖^2) := by
    rw [integral_const_mul,integral_finsetSum _ (fun s _ => hWi (hm' n s)),
      Finset.mul_sum]
    calc
      _ ≤ ∑ s, ((1/2:ℝ)*(∑ q, ∫ x, ‖fderiv ℝ (u n s) x (Pi.single q 1)‖^2) +
          C*(∫ x, ‖u n s x‖^2)) := by
        exact Finset.sum_le_sum (fun s _ => hsm
          (fun s => (hu n s).of_le (by simp)) (ha' n) (hm' n) (hg' n) s)
      _ = (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖fderiv ℝ (u n s) x (Pi.single q 1)‖^2) +
          C*(∑ s, ∫ x, ‖u n s x‖^2) := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hb' n) (by norm_num))
        (mul_le_mul_of_nonneg_left (hb n) hC)
  have hh : (∫ x, tfKinetic*∑ s, W x*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ s, ∑ q, ∫ x, ‖g s q x‖^2) + C*(∑ s, ∫ x, ‖f s x‖^2) := by
    apply integral_le_of_nonneg_ae_limit hi hif
    · exact fun n => Eventually.of_forall (fun x => mul_nonneg hT
        (Finset.sum_nonneg fun s _ => mul_nonneg (hW _) (sq_nonneg _)))
    · exact Eventually.of_forall (fun x => mul_nonneg hT
        (Finset.sum_nonneg fun s _ => mul_nonneg (hW _) (sq_nonneg _)))
    · filter_upwards [ae_all_iff.mpr ht] with x hx
      exact (tendsto_finsetSum Finset.univ (fun s _ =>
        ((hx s).norm.pow 2).const_mul (W x))).const_mul tfKinetic
    · exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ =>
        Finset.sum_nonneg fun q _ => integral_nonneg fun x => sq_nonneg _))
        (mul_nonneg hC (Finset.sum_nonneg fun s _ => integral_nonneg fun x => sq_nonneg _))
    · exact hbound
  rw [integral_const_mul,integral_finsetSum _ (fun s _ => hWi (hm s))] at hh
  exact hh

end Work_PressureWeak_scope

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

open CoulombAtom

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RetainedFieldIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombAnalysis

lemma radial_translatedDensity_potential {η : Space → ℝ} (hm : Measurable η)
    {R B : ℝ} (hR : 0 < R) (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R)
    (hb : ∀ x, |η x| ≤ B) (hr : IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (y z : Space) (hz : R ≤ ‖z-y‖) :
    tfPotential (translatedDensity η y) z = 1/‖z-y‖ := by
  have hsupport : Function.support η ⊆ closedBall 0 R :=
    fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hs x hx
  rw [potential_translatedDensity,
    tfPotential_newton_exterior_closed
      (bounded_compact_integrable hm (isCompact_closedBall _ _) hsupport hb)
      (bounded_compact_memLp hm (isCompact_closedBall _ _) hsupport hb (5/3 : ENNReal))
      hr hR hs hz,h1]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CoreFieldRegularity
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoreFieldRegularity_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma coreCoulombAt_nonneg {N : ℕ} (ψ : FormVector N) (z : Space) :
    0 ≤ coreCoulombAt ψ z := by
  apply Finset.sum_nonneg
  intro s _
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg (fun x => div_nonneg (sq_nonneg _) (norm_nonneg _))

open CoulombAnalysis

end Work_CoreFieldRegularity_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

open CoulombAnalysis

local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_CoherentDerivatives
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

namespace CoulombAtom

lemma coherentPacket_derivative_joint_continuous {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (v : Space) :
    Continuous (fun r : Space × (Space × Space) =>
      fderiv ℝ (coherentPacket g r.2.1 r.2.2) r.1 v) := by
  have hF := coherentPacket_joint_smooth hg
  have he : (fun r : Space × (Space × Space) =>
      fderiv ℝ (coherentPacket g r.2.1 r.2.2) r.1 v) =
      (fun r => firstPartial (fun t : Space × (Space × Space) =>
        coherentPacket g t.2.1 t.2.2 t.1) r v) := by
    funext r
    rw [(firstPartial_hasFDerivAt (hF.differentiable (by simp)) r.1 r.2).fderiv]
  rw [he]
  exact (firstPartial_contDiff (n := 0) (hF.of_le (by norm_num))).continuous.clm_apply continuous_const

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoherentKinetic
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ContDiff Topology

namespace CoulombAtom

lemma coherentPacket_tsupport_subset {g : Space → ℂ} (hcg : HasCompactSupport g)
    {K : Set (Space × Space)} (hK : IsCompact K) {q : Space × Space} (hq : q ∈ K) :
    tsupport (coherentPacket g q.1 q.2) ⊆ coherentSpatialSupport g K := by
  apply closure_minimal _ (coherentSpatialSupport_compact hcg hK).isClosed
  intro x hx
  by_contra hn
  exact hx (coherentPacket_zero_outside hq hn)

lemma coherentPacket_derivative_zero_outside {g : Space → ℂ} (hcg : HasCompactSupport g)
    {K : Set (Space × Space)} (hK : IsCompact K) {q : Space × Space} (hq : q ∈ K)
    {x : Space} (hx : x ∉ coherentSpatialSupport g K) (v : Space) :
    fderiv ℝ (coherentPacket g q.1 q.2) x v = 0 := by
  rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (coherentPacket_tsupport_subset hcg hK hq h))]
  rfl

lemma coherentPacket_derivative_sq_integrable {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) (v : Space) :
    Integrable (fun r : (Space × Space) × Space =>
      ‖fderiv ℝ (coherentPacket g r.1.1 r.1.2) r.2 v‖^2) (μ.prod volume) := by
  have hc : Continuous (fun r : (Space × Space) × Space =>
      ‖fderiv ℝ (coherentPacket g r.1.1 r.1.2) r.2 v‖^2) :=
    ((coherentPacket_derivative_joint_continuous hg v).comp continuous_swap).norm.pow 2
  have hi := hc.continuousOn.integrableOn_compact
    (hK.prod (coherentSpatialSupport_compact hcg hK)) (μ := μ.prod volume)
  apply hi.integrable_of_ae_notMem_eq_zero
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμ] with r hr
  intro hn
  have hx : r.2 ∉ coherentSpatialSupport g K := fun hx => hn ⟨hr,hx⟩
  simp only [coherentPacket_derivative_zero_outside hcg hK hr hx v,
    norm_zero,zero_pow (by decide : 2 ≠ 0)]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoherentLimitInsertion
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ContDiff Topology

namespace CoulombAtom

def coherentSpinKinetic (g : Space → ℂ) (μ : Measure (Space × Space)) : ℝ :=
  coherentFactor * ∑ a : Fin 3, ∫ q, (∫ x : Space,
    ‖fderiv ℝ (coherentPacket g q.1 q.2) x (EuclideanSpace.single a 1)‖^2) ∂μ

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoherentRealKinetic
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

def packetDirichlet (g : Space → ℝ) : ℝ :=
  ∑ a : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single a 1))^2

lemma packetDirichlet_nonneg (g : Space → ℝ) : 0 ≤ packetDirichlet g :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma real_complex_tsupport (g : Space → ℝ) :
    tsupport (fun x : Space => (g x : ℂ)) = tsupport g := by
  unfold tsupport
  congr 1
  ext x
  simp only [Function.mem_support,ne_eq,Complex.ofReal_eq_zero]

def packetRegion (g : Space → ℝ) (J : Set Space) : Set Space :=
  (fun r : Space × Space => r.1+r.2) '' (tsupport g ×ˢ J)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_ConditionalPricedUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

lemma FormZeroAt.scale {N : ℕ} {ψ : FormVector N} {x : Configuration N}
    (hz : FormZeroAt ψ x) (c : ℝ) : FormZeroAt (scaleForm c ψ) x := by
  intro s
  constructor
  · change (c:ℂ)*ψ.value s x = 0
    rw [(hz s).1,mul_zero]
  · intro i a
    change (c:ℂ)*ψ.gradient s i a x = 0
    rw [(hz s).2,mul_zero]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RetainedPatchDensity
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombNeumann.cubePartition_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis
variable {N : ℕ}

lemma retainedSmear_fixed_measurable (b : ℝ) (S : Finset (Fin N)) (x : Configuration N) :
    Measurable (retainedSmear b S x) := by
  unfold retainedSmear
  exact Finset.measurable_sum _ (fun i _ => (varthetaScaled_measurable b).comp
    (measurable_id.sub_const (x i)))

lemma retainedSmear_bound {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (z : Space) : retainedSmear b S x z ≤ S.card*b⁻¹^3 := by
  exact (Finset.sum_le_sum (fun i _ => varthetaScaled_le hb (z-x i))).trans_eq
    (by simp only [Finset.sum_const,nsmul_eq_mul])

lemma retainedSmear_zero_outside {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R)
    {z : Space} (hz : R ≤ ‖z-y‖) : retainedSmear b S x z = 0 := by
  apply retainedSmear_support hb
  intro i hi
  have hh : ‖z-y‖ ≤ ‖z-x i‖+‖x i-y‖ := by
    simpa only [dist_eq_norm] using dist_triangle z (x i) y
  linarith [hmargin i hi]

lemma retainedPatch_memLp {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (R : ℝ) :
    MemLp (fun z => retainedSmear b S x (y+z)) (5/3) (ballMeasure R) := by
  apply MemLp.of_bound
    (((retainedSmear_fixed_measurable b S x).comp (measurable_const.add measurable_id)).aestronglyMeasurable)
    (S.card*b⁻¹^3)
  exact Eventually.of_forall fun z => by
    change ‖retainedSmear b S x (y+z)‖ ≤ S.card*b⁻¹^3
    rw [Real.norm_of_nonneg (retainedSmear_nonneg hb S x _)]
    exact retainedSmear_bound hb S x _

def retainedPatchLp {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (R : ℝ) : TFLp (ballMeasure R) :=
  (retainedPatch_memLp hb S x y R).toLp (fun z => retainedSmear b S x (y+z))

lemma retainedPatchLp_ae {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (R : ℝ) :
    retainedPatchLp hb S x y R =ᵐ[ballMeasure R] fun z => retainedSmear b S x (y+z) :=
  (retainedPatch_memLp hb S x y R).coeFn_toLp

lemma retainedPatchLp_nonneg {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (R : ℝ) : NonnegDensity (retainedPatchLp hb S x y R) := by
  exact (retainedPatchLp_ae hb S x y R).mono fun z hz => hz.symm ▸ retainedSmear_nonneg hb S x _

lemma retainedPatchLp_bound {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (R : ℝ) :
    ∀ᵐ z ∂ballMeasure R, retainedPatchLp hb S x y R z ≤ S.card*b⁻¹^3 := by
  exact (retainedPatchLp_ae hb S x y R).mono fun z hz => hz.symm ▸ retainedSmear_bound hb S x _

lemma retainedPatchLp_extension {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R) :
    tfExtension R (retainedPatchLp hb S x y R) =ᵐ[volume] fun z => retainedSmear b S x (y+z) := by
  have hh := (ae_restrict_iff' measurableSet_ball).mp (retainedPatchLp_ae hb S x y R)
  filter_upwards [hh] with z hz
  by_cases hm : z ∈ ball (0:Space) R
  · simpa only [tfExtension,indicator_of_mem hm] using hz hm
  · rw [tfExtension,indicator_of_notMem hm]
    symm
    apply retainedSmear_zero_outside hb S x y hmargin
    simpa only [add_sub_cancel_left] using (not_lt.mp (by
      simpa only [mem_ball,dist_eq_norm,sub_zero] using hm : ¬‖z‖ < R))

end CoulombNeumann

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

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis
local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _

attribute [local instance] OAI.CoulombNeumann.instFactNeENNRealHDivOfNatTop_solutions
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_rd21c49_1 (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩
lemma retainedPatchLp_measurable {A : Type*} [MeasurableSpace A] {N : ℕ}
    {b : ℝ} (hb : 0 < b) (S : A → Finset (Fin N)) (x : A → Configuration N)
    (hS : ∀ i, MeasurableSet {a | i ∈ S a}) (hx : Measurable x) (y : Space) (R : ℝ) :
    Measurable (fun a => retainedPatchLp hb (S a) (x a) y R) := by
  have hm := retainedSmear_measurable_eval b (fun p : A × Space => S p.1)
    (fun p => x p.1) (fun p => y+p.2) (fun i => measurable_fst (hS i))
    (hx.comp measurable_fst) (measurable_const.add measurable_snd)
  exact measurable_memLp_toLp hm (fun a => retainedPatch_memLp hb (S a) (x a) y R)

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann CoulombAnalysis
local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_1 (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_1 (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_1_rd21c49_1 (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_1 (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpatialProductFactor
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

lemma spatialProduct_zero_of_factor {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (b : Fin L → Fin 2) (x : Configuration L) (j : Fin L)
    (hv : (p (b j)).value (x j) = 0) : spatialProductValue p b x = 0 := by
  classical
  exact Finset.prod_eq_zero (Finset.mem_univ j) hv

lemma spatialProduct_derivative_zero_of_factor {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (b : Fin L → Fin 2) (x : Configuration L) (j : Fin L)
    (hv : (p (b j)).value (x j) = 0)
    (hd : ∀ a, lineDeriv ℝ (p (b j)).value (x j) (spaceDirections a) = 0)
    (i : Fin L) (a : Fin 3) :
    lineDeriv ℝ (spatialProductValue p b) x (direction i a) = 0 := by
  classical
  rw [spatialProduct_derivative]
  by_cases hij : j = i
  · subst i
    rw [hd,mul_zero]
  · rw [show (∏ k ∈ Finset.univ.erase i, (p (b k)).value (x k)) = 0 from
        Finset.prod_eq_zero (by simp [hij]) hv,zero_mul]

lemma FormZeroAt.reindex {N M : ℕ} {ψ : FormVector N} (e : Fin M ≃ Fin N)
    {x : Configuration M} (h : FormZeroAt ψ (x ∘ e.symm)) :
    FormZeroAt (reindexForm e ψ) x := by
  intro s
  exact ⟨(h (s ∘ e.symm)).1,fun i a => (h (s ∘ e.symm)).2 (e i) a⟩

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialCountSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom
open CoulombRadialAveraging

lemma cutOutNumber_le_total {N : ℕ} (c : Fin N → Fin 2) : cutOutNumber c ≤ N := by
  have h := cutNumbers_sum c
  omega

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_SqrtMultiplier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

lemma arrayLikelihood_fderiv_norm {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ) :
    ‖fderiv ℝ (arrayLikelihood b s) x‖ ≤
      (sqrtLikelihoodLipschitzConstant (I := I) b : ℝ) * Real.sqrt (arrayLikelihood b s x) := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound
  · have hC := observationMomentConstant_pos
    positivity
  intro v
  rw [arrayLikelihood_fderiv b hs, norm_neg, Real.norm_eq_abs]
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun i => v i) (fun i => arrayScore b s x i)
  have hv : (∑ i, (v i)^2) ≤ (Fintype.card I : ℝ)*‖v‖^2 := by
    calc
      _ ≤ ∑ _ : I, ‖v‖^2 := sum_le_sum (fun i _ => by
        have hh := norm_le_pi_norm v i
        simpa only [Real.norm_eq_abs, sq_abs] using (sq_le_sq₀ (abs_nonneg (v i)) (norm_nonneg v)).mpr hh)
      _ = _ := by simp
  have hsg := arrayScore_sq_one b hs x
  have hC := observationMomentConstant_pos
  have hp := arrayLikelihood_nonneg b hs x
  have hB : 0 ≤ ∑ j, (b j)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hr : 0 ≤ observationMomentConstant * (∑ j, (b j)^2) * Fintype.card I := by positivity
  have hh : (∑ i, v i * arrayScore b s x i)^2 ≤
      (observationMomentConstant * (∑ j, (b j)^2) * Fintype.card I) *
        arrayLikelihood b s x * ‖v‖^2 := by
    calc
      _ ≤ (∑ i, (v i)^2) * ∑ i, (arrayScore b s x i)^2 := hcs
      _ ≤ ((Fintype.card I : ℝ)*‖v‖^2) *
          (observationMomentConstant * (∑ j, (b j)^2) * arrayLikelihood b s x) :=
        mul_le_mul hv hsg (sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
      _ = _ := by ring
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  change |∑ i, v i * arrayScore b s x i|^2 ≤
    (Real.sqrt (observationMomentConstant * (∑ j, (b j)^2) * Fintype.card I) *
      Real.sqrt (arrayLikelihood b s x) * ‖v‖)^2
  rw [mul_pow, mul_pow, Real.sq_sqrt hr, Real.sq_sqrt hp, sq_abs]
  exact hh

lemma sqrtArrayLikelihood_lipschitz {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) :
    LipschitzWith (sqrtLikelihoodLipschitzConstant (I := I) b)
      (fun x => Real.sqrt (arrayLikelihood b s x)) := by
  apply sqrt_lipschitz_of_fderiv_bound
    ((arrayLikelihood_contDiff b hs (n := 1)).differentiable one_ne_zero)
    (arrayLikelihood_nonneg b hs)
  intro x
  calc
    _ ≤ _ := arrayLikelihood_fderiv_norm b hs x
    _ ≤ _ := by
      have hz : 0 ≤ (sqrtLikelihoodLipschitzConstant (I := I) b : ℝ) *
          Real.sqrt (arrayLikelihood b s x) := by positivity
      nlinarith

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservationIntegral
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

def observationFisherConstant : ℝ := 8 * Real.exp 1 * observationMomentConstant

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterWidth
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Metric
open scoped NNReal

lemma masterExponent_pos : 0 < masterExponent := by norm_num [masterExponent]
lemma masterExponent_nonneg : 0 ≤ masterExponent := masterExponent_pos.le

lemma masterBaseDistance_lipschitz (r₀ : ℝ) : LipschitzWith 1 (masterBaseDistance r₀) :=
  lipschitzWith_one_norm.max_const r₀

lemma masterWidth_pos {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (x : Space) : 0 < masterWidth c₁ r₀ s x := by
  have hD : 0 < masterBaseDistance r₀ x := hr.trans_le (le_max_right _ _)
  exact mul_pos (mul_pos hc hD) (Real.rpow_pos_of_pos (lt_min hD hs) _)

lemma masterWidth_lipschitz {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r₀) (hs : 0 < s) :
    LipschitzWith ⟨c₁*(1+masterExponent)*s^masterExponent, by
      exact mul_nonneg (mul_nonneg hc (by linarith [masterExponent_pos])) (Real.rpow_nonneg hs.le _)⟩
      (masterWidth c₁ r₀ s) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : 0 < masterBaseDistance r₀ x := hr.trans_le (le_max_right _ _)
  have hy : 0 < masterBaseDistance r₀ y := hr.trans_le (le_max_right _ _)
  have H := cappedWidthProfile_norm_bound masterExponent_nonneg hs hx hy
  have hd := (masterBaseDistance_lipschitz r₀).dist_le_mul x y
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,←Real.norm_eq_abs] at hd
  change dist (masterWidth c₁ r₀ s x) (masterWidth c₁ r₀ s y) ≤
    (c₁*(1+masterExponent)*s^masterExponent)*dist x y
  simp only [dist_eq_norm,masterWidth]
  have he : c₁*masterBaseDistance r₀ x*(min (masterBaseDistance r₀ x) s)^masterExponent-
      c₁*masterBaseDistance r₀ y*(min (masterBaseDistance r₀ y) s)^masterExponent =
      c₁*(cappedWidthProfile s masterExponent (masterBaseDistance r₀ x)-
        cappedWidthProfile s masterExponent (masterBaseDistance r₀ y)) := by
    simp only [cappedWidthProfile]; ring
  rw [he,norm_mul,Real.norm_eq_abs,abs_of_nonneg hc]
  have hp : 0 ≤ (1+masterExponent)*s^masterExponent :=
    mul_nonneg (by linarith [masterExponent_pos]) (Real.rpow_nonneg hs.le _)
  calc
    _ ≤ c₁*((1+masterExponent)*s^masterExponent*‖masterBaseDistance r₀ x-masterBaseDistance r₀ y‖) :=
      mul_le_mul_of_nonneg_left H hc
    _ ≤ c₁*((1+masterExponent)*s^masterExponent*dist x y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hp) hc
    _ = _ := by rw [dist_eq_norm]; ring

open Set Metric
open scoped NNReal

def widthKernel (t : Space → ℝ) (h : Space → ℝ) (x y : Space) : ℝ :=
  (t x)⁻¹^3*h ((t x)⁻¹ • (y-x))

lemma normalizedArgument_distance {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) {q : ℝ} (hq : 0 < q) (hl : ∀ x, q ≤ t x)
    (x z y : Space) (ha : ‖(t x)⁻¹ • (y-x)‖ ≤ 1) :
    ‖(t x)⁻¹ • (y-x)-(t z)⁻¹ • (y-z)‖ ≤ q⁻¹*(1+(T:ℝ))*‖x-z‖ := by
  let a := (t x)⁻¹ • (y-x)
  have hx : 0 < t x := hq.trans_le (hl x)
  have hz : 0 < t z := hq.trans_le (hl z)
  have hax : t x • a = y-x := by simp [a,smul_smul,hx.ne']
  have he : a-(t z)⁻¹ • (y-z) = (t z)⁻¹ • ((t z-t x) • a+(z-x)) := by
    apply (smul_right_injective Space hz.ne')
    simp only [smul_sub,smul_smul,mul_inv_cancel₀ hz.ne',one_smul,sub_smul,hax]
    abel
  change ‖a-(t z)⁻¹ • (y-z)‖ ≤ _
  rw [he,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hz.le)]
  have hh := ht.dist_le_mul z x
  simp only [dist_eq_norm,norm_sub_rev z x] at hh
  have hn : ‖(t z-t x) • a+(z-x)‖ ≤ (1+(T:ℝ))*‖x-z‖ := by
    calc
      _ ≤ ‖(t z-t x) • a‖+‖z-x‖ := norm_add_le _ _
      _ = ‖t z-t x‖*‖a‖+‖x-z‖ := by rw [norm_smul,norm_sub_rev z x]
      _ ≤ ‖t z-t x‖*1+‖x-z‖ := add_le_add_left (mul_le_mul_of_nonneg_left ha (norm_nonneg _)) _
      _ ≤ ((T:ℝ)*‖x-z‖)*1+‖x-z‖ := by nlinarith only [hh]
      _ = _ := by ring
  calc
    _ ≤ (t z)⁻¹*((1+(T:ℝ))*‖x-z‖) := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hz.le)
    _ ≤ q⁻¹*((1+(T:ℝ))*‖x-z‖) := mul_le_mul_of_nonneg_right (inv_anti₀ hq (hl z)) (by positivity)
    _ = _ := by ring

lemma widthKernel_active_norm_bound {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) {q : ℝ} (hq : 0 < q) (hl : ∀ x, q ≤ t x)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (_hM : 0 ≤ M)
    (hb : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1)
    (x z y : Space) (hx : h ((t x)⁻¹ • (y-x)) ≠ 0) :
    ‖widthKernel t h x y-widthKernel t h z y‖ ≤
      ((3*M*(T:ℝ)+(H:ℝ)*(1+(T:ℝ)))*q⁻¹^4)*‖x-z‖ := by
  have hq0 := inv_nonneg.mpr hq.le
  have htpos (u : Space) : 0 < t u := hq.trans_le (hl u)
  have ha : ‖(t x)⁻¹ • (y-x)‖ ≤ 1 := by
    simpa only [mem_closedBall,dist_zero_right] using hs hx
  have hc := invCube_norm_sub_le hq (hl x) (hl z)
  have hwd := ht.dist_le_mul x z
  simp only [dist_eq_norm] at hwd
  have hc' : ‖(t x)⁻¹^3-(t z)⁻¹^3‖ ≤ 3*q⁻¹^4*((T:ℝ)*‖x-z‖) :=
    hc.trans (mul_le_mul_of_nonneg_left hwd (by positivity))
  have ha' := normalizedArgument_distance ht hq hl x z y ha
  have hhd := hh.dist_le_mul ((t x)⁻¹ • (y-x)) ((t z)⁻¹ • (y-z))
  simp only [dist_eq_norm] at hhd
  have hh' := hhd.trans (mul_le_mul_of_nonneg_left ha' H.coe_nonneg)
  have hi : ‖(t z)⁻¹^3‖ ≤ q⁻¹^3 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (htpos z).le) _)]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (htpos z).le) (inv_anti₀ hq (hl z)) 3
  have he : widthKernel t h x y-widthKernel t h z y =
      ((t x)⁻¹^3-(t z)⁻¹^3)*h ((t x)⁻¹ • (y-x))+
      (t z)⁻¹^3*(h ((t x)⁻¹ • (y-x))-h ((t z)⁻¹ • (y-z))) := by
    simp only [widthKernel]; ring
  rw [he]
  calc
    _ ≤ ‖((t x)⁻¹^3-(t z)⁻¹^3)*h ((t x)⁻¹ • (y-x))‖+
        ‖(t z)⁻¹^3*(h ((t x)⁻¹ • (y-x))-h ((t z)⁻¹ • (y-z)))‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul,norm_mul]
    _ ≤ (3*q⁻¹^4*((T:ℝ)*‖x-z‖))*M+
        q⁻¹^3*((H:ℝ)*(q⁻¹*(1+(T:ℝ))*‖x-z‖)) :=
      add_le_add (mul_le_mul hc' (hb _) (norm_nonneg _) (by positivity))
        (mul_le_mul hi hh' (norm_nonneg _) (by positivity))
    _ = _ := by ring

lemma widthKernel_lipschitz {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) {q : ℝ} (hq : 0 < q) (hl : ∀ x, q ≤ t x)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    LipschitzWith ⟨(3*M*(T:ℝ)+(H:ℝ)*(1+(T:ℝ)))*q⁻¹^4, by positivity⟩
      (fun x => widthKernel t h x y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  change dist (widthKernel t h x y) (widthKernel t h z y) ≤
    ((3*M*(T:ℝ)+(H:ℝ)*(1+(T:ℝ)))*q⁻¹^4)*dist x z
  simp only [dist_eq_norm]
  by_cases hx : h ((t x)⁻¹ • (y-x)) ≠ 0
  · exact widthKernel_active_norm_bound ht hq hl hh hM hb hs x z y hx
  by_cases hz : h ((t z)⁻¹ • (y-z)) ≠ 0
  · simpa only [norm_sub_rev z x,norm_sub_rev (widthKernel t h z y) _] using
      widthKernel_active_norm_bound ht hq hl hh hM hb hs z x y hz
  simp only [not_ne_iff] at hx hz
  simp only [widthKernel,hx,hz,mul_zero,sub_zero,norm_zero]
  positivity

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_ShiftedCoulombIntegrable
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

namespace CoulombAtom

lemma IsWeakDerivative.translate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)] {v : E} {f g : E → ℂ}
    (hw : IsWeakDerivative v f g) (a : E) :
    IsWeakDerivative v (fun x => f (x+a)) (fun x => g (x+a)) := by
  intro φ hφ hcφ
  let φ' : E → ℝ := fun x => φ (x-a)
  have hφ' : ContDiff ℝ ∞ φ' := hφ.comp (contDiff_id.sub contDiff_const)
  have hcφ' : HasCompactSupport φ' := by
    simpa [φ',Function.comp_def,sub_eq_add_neg] using hcφ.comp_homeomorph (Homeomorph.addRight (-a))
  have hd (x : E) : lineDeriv ℝ φ' (x+a) v = lineDeriv ℝ φ x v := by
    rw [(hφ'.differentiable (by simp) (x+a)).lineDeriv_eq_fderiv,
      (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
    have hh := (hφ.differentiable (by simp) (x+a-a)).hasFDerivAt.comp (x+a)
      ((hasFDerivAt_id (x+a)).sub_const a)
    have hh' := congrArg (fun T : E →L[ℝ] ℝ => T v) hh.fderiv
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,add_sub_cancel_right,φ',Function.comp_def,id_eq] using hh'
  have h1 : (∫ x, f (x+a)*Complex.ofReal (lineDeriv ℝ φ' (x+a) v)) =
      ∫ x, f x*Complex.ofReal (lineDeriv ℝ φ' x v) :=
    (measurePreserving_add_right (volume : Measure E) a).integral_comp
      (Homeomorph.addRight a).measurableEmbedding
      (fun x => f x*Complex.ofReal (lineDeriv ℝ φ' x v))
  have h2 : (∫ x, g (x+a)*(φ' (x+a) : ℂ)) = ∫ x, g x*(φ' x : ℂ) :=
    (measurePreserving_add_right (volume : Measure E) a).integral_comp
      (Homeomorph.addRight a).measurableEmbedding (fun x => g x*(φ' x : ℂ))
  have hh := hw φ' hφ' hcφ'
  rw [←h1,←h2] at hh
  simpa only [hd,φ',add_sub_cancel_right] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_PatchContinuity
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma tfBallPotential_continuous (R : ℝ) (f : TFLp (ballMeasure R)) :
    Continuous (tfBallPotential R f) := by
  have hp : MemLp (tfExtension R f) (5/3) := by
    rw [tfExtension, memLp_indicator_iff_restrict measurableSet_ball]
    exact Lp.memLp f
  have he : tfPotential (tfExtension R f) = tfBallPotential R f := funext (tfPotential_extension R f)
  rw [←he]
  exact tfPotential_continuous (tfExtension_integrable R f) hp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Restriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
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
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
namespace CoulombAtom
section Restriction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def SmoothMultiplier.restrict {v : ι → E} (p : SmoothMultiplier v) (j : κ → ι) :
    SmoothMultiplier (v ∘ j) where
  value := p.value
  regular := p.regular
  bound := p.bound
  gradient_bound := fun k => p.gradient_bound (j k)

end Restriction

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Sum
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
open scoped Topology BigOperators ContDiff
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
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
section Sum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
variable {ι α : Type*} [Fintype ι] [Fintype α] {v : ι → E}

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [Fintype ι] in
lemma lineDeriv_sumSquares (p : α → SmoothMultiplier v) (x d : E) :
    lineDeriv ℝ (fun y => ∑ i, (p i).value y ^ 2) x d =
      ∑ i, 2 * (p i).value x * lineDeriv ℝ (p i).value x d := by
  have hd (i : α) := ((p i).regular.differentiable (by simp) x).hasFDerivAt.pow 2
  have hh := (HasFDerivAt.sum (u := Finset.univ) (fun i _ => hd i)).hasLineDerivAt d
  have he := hh.lineDeriv
  simp only [sum_apply, smul_apply, smul_eq_mul, Nat.reduceSub,
    pow_one, nsmul_eq_mul, Nat.cast_ofNat] at he
  convert he using 1
  · congr 1
    funext y
    simp only [Finset.sum_apply]
  · apply Finset.sum_congr rfl; intro i _
    rw [((p i).regular.differentiable (by simp) x).lineDeriv_eq_fderiv]

def SmoothMultiplier.sumSquares (p : α → SmoothMultiplier v) : SmoothMultiplier v where
  value := fun x => ∑ i, (p i).value x ^ 2
  regular := ContDiff.sum (fun i _ => (p i).regular.pow 2)
  bound := by
    choose C hC using fun i => (p i).bound
    refine ⟨∑ i, C i ^ 2, fun x => ?_⟩
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    apply Finset.sum_le_sum; intro i _
    exact (sq_le_sq₀ (abs_nonneg _) (le_trans (abs_nonneg _) (hC i x))).mpr (hC i x) |>
      fun h => by simpa only [sq_abs] using h
  gradient_bound := by
    intro j
    choose C hC using fun i => (p i).bound
    choose D hD using fun i => (p i).gradient_bound j
    refine ⟨∑ i, 2 * C i * D i, fun x => ?_⟩
    rw [lineDeriv_sumSquares]
    calc
      _ ≤ ∑ i, |2 * (p i).value x * lineDeriv ℝ (p i).value x (v j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hC i x) (by norm_num))
          (hD i x) (abs_nonneg _) (by linarith [abs_nonneg ((p i).value x), hC i x])

end Sum


open MeasureTheory Filter
open scoped Topology BigOperators


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoreMultiplierLiftBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoreMultiplierLift_barrier_scope

open MeasureTheory Filter
open scoped BigOperators ContDiff

def coreLeftLinear (N M : ℕ) : Configuration (N+M) →L[ℝ] Configuration N :=
  (ContinuousLinearMap.fst ℝ (Configuration N) (Configuration M)).comp
    (configurationJoin N M).symm.toContinuousLinearMap

def coreLiftValue {N : ℕ} (M : ℕ) (p : SmoothMultiplier (sectorDirections N)) :
    Configuration (N+M) → ℝ := p.value ∘ coreLeftLinear N M

lemma coreLiftValue_regular {N : ℕ} (M : ℕ) (p : SmoothMultiplier (sectorDirections N)) :
    ContDiff ℝ ∞ (coreLiftValue M p) := p.regular.comp (coreLeftLinear N M).contDiff

lemma coreLiftValue_derivative {N : ℕ} (M : ℕ) (p : SmoothMultiplier (sectorDirections N))
    (x v : Configuration (N+M)) :
    lineDeriv ℝ (coreLiftValue M p) x v =
      lineDeriv ℝ p.value (coreLeftLinear N M x) (coreLeftLinear N M v) := by
  rw [((coreLiftValue_regular M p).differentiable (by simp) x).lineDeriv_eq_fderiv,
    (p.regular.differentiable (by simp) _).lineDeriv_eq_fderiv]
  have hh := (p.regular.differentiable (by simp) (coreLeftLinear N M x)).hasFDerivAt.comp
    x (coreLeftLinear N M).hasFDerivAt
  exact congrArg (fun A : Configuration (N+M) →L[ℝ] ℝ => A v) hh.fderiv

end Work_CoreMultiplierLift_barrier_scope

open MeasureTheory Filter
open scoped BigOperators

lemma joinLists_order {α : Type*} {K N M : ℕ} (e : Fin K ≃ Fin N)
    (s : Fin K → α) (t : Fin M → α) :
    joinLists s t ∘ (liftCoreOrder M e).symm = joinLists (s ∘ e.symm) t := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simp only [Function.comp_apply,liftCoreOrder_symm,
    liftCoreOrder_left,liftCoreOrder_right,joinLists_left,joinLists_right]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoreHistoryCoordinatesBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

namespace CoulombAtom

lemma joinLists_observation_order {α : Type*} {N K M : ℕ}
    (x : Fin N → α) (y : Fin K → α) (z : Fin M → α) :
    joinLists x (joinLists y z) ∘ (coreObservationAssoc N K M).symm =
      joinLists (joinLists x y) z := by
  apply (Equiv.comp_symm_eq (coreObservationAssoc N K M) _ _).mpr
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j => simp only [Function.comp_apply,coreObservationAssoc_core,joinLists_left]
  | inr j =>
    obtain ⟨k,rfl⟩ := finSumFinEquiv.surjective j
    cases k <;> simp only [Function.comp_apply,coreObservationAssoc_middle,
      coreObservationAssoc_out,joinLists_left,joinLists_right]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoreHistoryAverageBarrier
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
open scoped BigOperators

open MeasureTheory Filter
open scoped BigOperators

def rawFormPair {N : ℕ} (ψ : FormVector N) (g : Configuration N → ℝ) : ℝ :=
  ∑ s : Spins N, ∫ x, g x*‖ψ.value s x‖^2

lemma leftList_measurable {N M : ℕ} : Measurable (leftList (N := N) (M := M) (α := Space)) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

def cutCorePositions {L : ℕ} (c : Fin L → Fin 2) (x : Configuration L) :
    Configuration (cutCoreNumber c) :=
  fun i => x (cutOrder c (finSumFinEquiv (Sum.inl i)))

lemma cutCorePositions_reindex {L : ℕ} (c : Fin L → Fin 2)
    (x : Configuration (cutCoreNumber c+cutOutNumber c)) :
    cutCorePositions c (x ∘ (cutOrder c).symm) = leftList x := by
  ext i
  simp only [cutCorePositions,Function.comp_apply,Equiv.symm_apply_apply,leftList]

lemma cutCorePositions_measurable {L : ℕ} (c : Fin L → Fin 2) : Measurable (cutCorePositions c) := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply _

lemma sum_cutCorePositions {L : ℕ} (c : Fin L → Fin 2) (x : Configuration L) (f : Space → ℝ) :
    (∑ i, f (cutCorePositions c x i)) = ∑ i, if c i = 0 then f (x i) else 0 := by
  classical
  have he := Equiv.sum_comp (Fintype.equivFin {i // c i = 0}).symm (fun i => f (x i.val))
  have hs := Finset.sum_subtype (p := fun i => c i = 0) (F := inferInstance) (Finset.univ.filter (fun i => c i = 0))
    (fun _ => by simp) (fun i => f (x i))
  calc
    _ = ∑ i : {i // c i = 0}, f (x i.val) := by
      simpa only [cutCorePositions,cutOrder,Equiv.trans_apply,Equiv.symm_apply_apply,
        Equiv.sumCongr_apply,Sum.map_inl,Equiv.sumCompl_apply_inl] using he
    _ = ∑ i ∈ Finset.univ.filter (fun i => c i = 0), f (x i) := hs.symm
    _ = _ := Finset.sum_filter _ _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoreHistoryFermionBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

namespace CoulombAtom

lemma leftList_corePerm {α : Type*} {N M : ℕ} (x : Fin (N+M) → α)
    (π : Equiv.Perm (Fin N)) : leftList (x ∘ corePerm M π) = leftList x ∘ π := by
  funext i
  simp [leftList,corePerm]

lemma leftList_liftCoreOrder {α : Type*} {K N M : ℕ} (e : Fin K ≃ Fin N)
    (x : Fin (K+M) → α) :
    leftList (x ∘ (liftCoreOrder M e).symm) = leftList x ∘ e.symm := by
  funext i
  simp only [leftList,Function.comp_apply,liftCoreOrder_symm,liftCoreOrder_left]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalHistoryWeightsBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open scoped BigOperators

def localizationIMSConstant : ℝ := (3/2:ℝ)*(Real.pi*smoothTransitionBound)^2
lemma localizationIMSConstant_nonneg : 0 ≤ localizationIMSConstant := by
  unfold localizationIMSConstant
  positivity

lemma localHistoryRadius_recip {a : ℝ} (ha : 0 < a) (n : ℕ) :
    1/localHistoryRadius a n ≤ ((n:ℝ)+2)^2/a := by
  have he : 1/localHistoryRadius a n = (((n:ℝ)+1)*((n:ℝ)+2))/a := by
    unfold localHistoryRadius
    field_simp
  rw [he]
  apply div_le_div_of_nonneg_right _ ha.le
  have : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith

lemma localHistoryRadius_fourth {a : ℝ} (ha : 0 < a) (n : ℕ) :
    1/(localHistoryRadius a n)^4 ≤ ((n:ℝ)+2)^8/a^4 := by
  have := localHistoryRadius_pos ha n
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1/localHistoryRadius a n)
    (localHistoryRadius_recip ha n) 4
  simpa only [div_pow,one_pow,←pow_mul] using hh

lemma localHistoryRadius_second {a : ℝ} (ha : 0 < a) (n : ℕ) :
    1/(localHistoryRadius a n)^2 ≤ ((n:ℝ)+2)^4/a^2 := by
  have := localHistoryRadius_pos ha n
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1/localHistoryRadius a n)
    (localHistoryRadius_recip ha n) 2
  simpa only [div_pow,one_pow,←pow_mul] using hh

lemma localHistoryRadius_packet {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (1/(localHistoryRadius a n)^4+1/localHistoryRadius a n)^2 ≤
      (1/a^4+1/a)^2*((n:ℝ)+2)^16 := by
  have hw : 1 ≤ (n:ℝ)+2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hp : ((n:ℝ)+2)^2 ≤ ((n:ℝ)+2)^8 := pow_le_pow_right₀ hw (by norm_num)
  have hi := (localHistoryRadius_recip ha n).trans (div_le_div_of_nonneg_right hp ha.le)
  have hu := add_le_add (localHistoryRadius_fourth ha n) hi
  have hn : 0 ≤ 1/(localHistoryRadius a n)^4+1/localHistoryRadius a n := by
    have := localHistoryRadius_pos ha n
    positivity
  have hh := pow_le_pow_left₀ hn hu 2
  calc (1/(localHistoryRadius a n)^4+1/localHistoryRadius a n)^2 ≤
      (((n:ℝ)+2)^8/a^4+((n:ℝ)+2)^8/a)^2 := hh
    _ = (1/a^4+1/a)^2*((n:ℝ)+2)^16 := by ring

lemma localHistoryRadius_ims {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (3/2:ℝ)*(Real.pi*smoothTransitionBound/localHistoryRadius a n)^2 ≤
      (localizationIMSConstant/a^2)*((n:ℝ)+3)^8 := by
  have h1 := mul_le_mul_of_nonneg_left (localHistoryRadius_second ha n) localizationIMSConstant_nonneg
  have hw : ((n:ℝ)+2)^4 ≤ ((n:ℝ)+3)^8 :=
    (pow_le_pow_left₀ (by positivity) (by linarith : (n:ℝ)+2 ≤ (n:ℝ)+3) 4).trans
      (pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num))
  have h2 := mul_le_mul_of_nonneg_left hw (div_nonneg localizationIMSConstant_nonneg (sq_nonneg a))
  calc (3/2:ℝ)*(Real.pi*smoothTransitionBound/localHistoryRadius a n)^2 =
      localizationIMSConstant*(1/localHistoryRadius a n^2) := by unfold localizationIMSConstant; ring
    _ ≤ localizationIMSConstant*(((n:ℝ)+2)^4/a^2) := h1
    _ = (localizationIMSConstant/a^2)*((n:ℝ)+2)^4 := by ring
    _ ≤ (localizationIMSConstant/a^2)*((n:ℝ)+3)^8 := h2

lemma localHistoryRadius_energy {a δ C : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hC : 0 ≤ C) (n : ℕ) :
    (δ+C*((n:ℝ)+1)*((n:ℝ)+3)^8)/localHistoryRadius a n ≤
      (δ/a+256*C/a)*((n:ℝ)+2)^16 := by
  let w : ℝ := (n:ℝ)+2
  have hw : 1 ≤ w := by dsimp [w]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hw0 : 0 ≤ w := le_trans (by norm_num) hw
  have hn : 0 ≤ (n:ℝ)+1 := by positivity
  have hnw : (n:ℝ)+1 ≤ w := by dsimp [w]; linarith
  have hn3 : (n:ℝ)+3 ≤ 2*w := by dsimp [w]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hpow : ((n:ℝ)+3)^8 ≤ 256*w^8 := by
    simpa only [mul_pow,show (2:ℝ)^8 = 256 by norm_num] using pow_le_pow_left₀ (by positivity) hn3 8
  have hp : C*((n:ℝ)+1)*((n:ℝ)+3)^8 ≤ 256*C*w^9 := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hnw hC) hpow (by positivity) (mul_nonneg hC hw0)
    calc C*((n:ℝ)+1)*((n:ℝ)+3)^8 ≤ (C*w)*(256*w^8) := h
      _ = 256*C*w^9 := by ring
  have hE := mul_le_mul (add_le_add le_rfl hp) (localHistoryRadius_recip ha n)
    (by have := localHistoryRadius_pos ha n; positivity) (by positivity : 0 ≤ δ+256*C*w^9)
  have hp2 : w^2 ≤ w^16 := pow_le_pow_right₀ hw (by norm_num)
  have hp11 : w^11 ≤ w^16 := pow_le_pow_right₀ hw (by norm_num)
  have h2 := mul_le_mul_of_nonneg_left hp2 (div_nonneg hδ ha.le)
  have h11 := mul_le_mul_of_nonneg_left hp11 (div_nonneg (by positivity : 0 ≤ 256*C) ha.le)
  calc (δ+C*((n:ℝ)+1)*((n:ℝ)+3)^8)/localHistoryRadius a n ≤
      (δ+256*C*w^9)*(w^2/a) := by simpa only [div_eq_mul_inv,one_mul] using hE
    _ = δ/a*w^2+(256*C/a)*w^11 := by ring
    _ ≤ δ/a*w^16+(256*C/a)*w^16 := add_le_add h2 h11
    _ = (δ/a+256*C/a)*((n:ℝ)+2)^16 := by dsimp [w]; ring

open Set Metric

def localHistoryCostScale (a B H : ℝ) : ℝ := (localizationIMSConstant/a^2+8*H)*Real.sqrt B
lemma localHistoryCostScale_nonneg (a B : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    0 ≤ localHistoryCostScale a B H := by
  unfold localHistoryCostScale
  exact mul_nonneg (add_nonneg (div_nonneg localizationIMSConstant_nonneg (sq_nonneg a)) (by positivity))
    (Real.sqrt_nonneg _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ThinFieldFeedbackBarrier
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

 def thinFieldBase (a b D B : ℝ) : ℝ := localFieldScale a D B+
    localizationIMSConstant*Real.sqrt B/(b^2*a)

open MeasureTheory Set Metric

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ThinFieldConstantsBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma thinFieldBase_nonneg {a b D B : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 ≤ D) (hB : 0 ≤ B) :
    0 ≤ thinFieldBase a b D B := by
  unfold thinFieldBase
  exact add_nonneg (localFieldScale_nonneg ha hD hB)
    (by have := localizationIMSConstant_nonneg; positivity)

lemma countSqScale_le_thinFieldBase {a b D B : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hD : 0 ≤ D) (_hB : 0 ≤ B) :
    B/a^2 ≤ thinFieldBase a b D B := by
  have h1 : 0 ≤ (1/a^4+1/a)^2+1/a^4+D/a := by positivity
  have h2 : 0 ≤ localizationIMSConstant*Real.sqrt B/(b^2*a) := by
    have := localizationIMSConstant_nonneg
    positivity
  unfold thinFieldBase localFieldScale
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CellFieldNormalizationBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma thinFieldBase_antitone {a A b D B : ℝ} (ha : 0 < a) (haA : a ≤ A)
    (hb : 0 < b) (hD : 0 ≤ D) (hB : 0 ≤ B) :
    thinFieldBase A b D B ≤ thinFieldBase a b D B := by
  have hA := lt_of_lt_of_le ha haA
  have hI := localizationIMSConstant_nonneg
  unfold thinFieldBase localFieldScale
  gcongr

lemma thinFieldBase_normalized {a m e D B C P : ℝ}
    (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (he : 0 < e)
    (_hD : 0 ≤ D) (hDm : D*a ≤ m^2) (hB : 0 ≤ B) (hC : 1 ≤ C)
    (hP : 1 ≤ P) (hBC : B ≤ C*P*m^2) :
    thinFieldBase a (e*a) D B ≤
      (6+C+localizationIMSConstant*C)*(m/a)^2*(P+1/e^4) := by
  let S := (m/a)^2
  let V := P+1/e^4
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hS : 0 ≤ S := sq_nonneg _
  have hV : 1 ≤ V := by dsimp [V]; have := one_div_nonneg.mpr (by positivity : 0 ≤ e^4); linarith
  have hPV : P ≤ V := by dsimp [V]; have := one_div_nonneg.mpr (by positivity : 0 ≤ e^4); linarith
  have hI := localizationIMSConstant_nonneg
  have hrec := cell_reciprocal_bounds ha hm h3
  have ham := cell_mass_product ha hm h3
  have hma : 0 ≤ m/a := div_nonneg hm0 ha.le
  have h4 : 1/a^4 ≤ m/a := by
    have hh := div_le_div_of_nonneg_right h3 ha.le
    calc _ = (1/a^3)/a := by ring
         _ ≤ m/a := hh
  have h1 : 1/a ≤ m/a := div_le_div_of_nonneg_right hm ha.le
  have hfirst : (1/a^4+1/a)^2 ≤ 4*S := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1/a^4+1/a) (add_le_add h4 h1) 2
    dsimp [S]
    nlinarith
  have hsecond : 1/a^4 ≤ S := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1/a) hrec.1 2
    have hh := div_le_div_of_nonneg_right h (sq_nonneg a)
    calc _ = (1/a)^2/a^2 := by ring
         _ ≤ m^2/a^2 := hh
         _ = S := by dsimp [S]; ring
  have hthird : D/a ≤ S := by
    have h := div_le_div_of_nonneg_right hDm (sq_nonneg a)
    calc _ = (D*a)/a^2 := by field_simp
         _ ≤ m^2/a^2 := h
         _ = S := by dsimp [S]; ring
  have hfourth : B/a^2 ≤ C*P*S := by
    have h := div_le_div_of_nonneg_right hBC (sq_nonneg a)
    calc _ ≤ (C*P*m^2)/a^2 := h
         _ = C*P*S := by dsimp [S]; ring
  have hsqrt := sqrt_count_scale hB hC hP0 hm0 hBC
  have hroot : Real.sqrt P/e^2 ≤ V := by
    have hs := Real.sq_sqrt hP0
    have hx : (1/e^2)^2 = 1/e^4 := by ring
    have hh := sq_nonneg (Real.sqrt P-1/e^2)
    calc _ = Real.sqrt P*(1/e^2) := by ring
         _ ≤ V := by dsimp [V]; nlinarith
  have hnorm : m/a^3 ≤ S := by
    have hh := mul_le_mul_of_nonneg_right ham (show 0 ≤ m/a^3 by positivity)
    calc _ ≤ (a*m)*(m/a^3) := by simpa using hh
         _ = S := by dsimp [S]; field_simp
  have hims : localizationIMSConstant*Real.sqrt B/((e*a)^2*a) ≤
      localizationIMSConstant*C*V*S := by
    calc _ ≤ localizationIMSConstant*(C*Real.sqrt P*m)/((e*a)^2*a) := by gcongr
         _ = localizationIMSConstant*C*(Real.sqrt P/e^2)*(m/a^3) := by ring
         _ ≤ localizationIMSConstant*C*V*S := by gcongr
  have ht1 := mul_le_mul_of_nonneg_right hV hS
  have ht2 := mul_le_mul_of_nonneg_right hPV (mul_nonneg hC0 hS)
  unfold thinFieldBase localFieldScale
  change (1/a^4+1/a)^2+1/a^4+D/a+B/a^2+_ ≤ (6+C+localizationIMSConstant*C)*S*V
  nlinarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_InnerPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Metric Laplacian
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis

 def sourcePotential (mu : Measure Space) (y : Space) : ℝ :=
    ∫ a, (‖y-a‖)⁻¹ ∂mu

 lemma inner_source_separation {h d : ℝ} {a y : Space}
    (ha : ‖a‖ ≤ h) (hy : h+d ≤ ‖y‖) : d ≤ ‖y-a‖ := by
  have := norm_le_norm_sub_add y a
  linarith

 lemma source_kernel_integrable (mu : Measure Space) [IsFiniteMeasure mu]
    {h d : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) (hd : 0 < d) {y : Space}
    (hy : h+d ≤ ‖y‖) : Integrable (fun a => (‖y-a‖)⁻¹) mu := by
  apply (integrable_const (d⁻¹)).mono' (by fun_prop)
  filter_upwards [hs] with a ha
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_anti₀ hd (inner_source_separation ha hy)

 lemma sourcePotential_nonneg (mu : Measure Space) (y : Space) :
    0 ≤ sourcePotential mu y := integral_nonneg (fun _ => inv_nonneg.mpr (norm_nonneg _))

 lemma sourcePotential_difference (mu : Measure Space) [IsFiniteMeasure mu]
    {h d : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) (hd : 0 < d) {y z : Space}
    (hy : h+d ≤ ‖y‖) (hz : h+d ≤ ‖z‖) :
    |sourcePotential mu y-sourcePotential mu z| ≤
      ((mu Set.univ).toReal/d^2)*‖y-z‖ := by
  have hi := source_kernel_integrable mu hs hd hy
  have hj := source_kernel_integrable mu hs hd hz
  have hb : ∀ᵐ a ∂mu, ‖(‖y-a‖)⁻¹-(‖z-a‖)⁻¹‖ ≤ ‖y-z‖/d^2 := by
    filter_upwards [hs] with a ha
    have hya := inner_source_separation ha hy
    have hza := inner_source_separation ha hz
    have hn1 : a ≠ y := by intro he; subst a; simp only [sub_self,norm_zero] at hya; linarith
    have hn2 : a ≠ z := by intro he; subst a; simp only [sub_self,norm_zero] at hza; linarith
    have hiy := pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg (y-a))) (inv_anti₀ hd hya) 2
    have hiz := pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg (z-a))) (inv_anti₀ hd hza) 2
    rw [Real.norm_eq_abs]
    calc _ ≤ ‖y-z‖*((‖y-a‖)⁻¹^2+(‖z-a‖)⁻¹^2)/2 := coulomb_inv_difference hn1 hn2
         _ ≤ ‖y-z‖*(d⁻¹^2+d⁻¹^2)/2 := by gcongr
         _ = _ := by ring
  have hh := norm_integral_le_of_norm_le (integrable_const (‖y-z‖/d^2) :
    Integrable (fun _ : Space => ‖y-z‖/d^2) mu) hb
  rw [integral_sub hi hj,Real.norm_eq_abs] at hh
  calc
    _ ≤ ∫ _a : Space, ‖y-z‖/d^2 ∂mu := hh
    _ = _ := by simp only [integral_const,Measure.real,smul_eq_mul]; ring

 lemma sourcePotential_lipschitzOn (mu : Measure Space) [IsFiniteMeasure mu]
    {h d : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) (hd : 0 < d) :
    LipschitzOnWith ⟨(mu Set.univ).toReal/d^2,by positivity⟩ (sourcePotential mu)
      {y | h+d ≤ ‖y‖} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  change dist (sourcePotential mu y) (sourcePotential mu z) ≤
    ((mu univ).toReal/d^2)*dist y z
  simpa only [dist_eq_norm,Real.norm_eq_abs] using
    sourcePotential_difference mu hs hd hy hz

 lemma sourcePotential_continuousOn_exterior (mu : Measure Space) [IsFiniteMeasure mu]
    {h : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) :
    ContinuousOn (sourcePotential mu) {y | h < ‖y‖} := by
  intro y hy
  change h < ‖y‖ at hy
  have hd : 0 < (‖y‖-h)/2 := by linarith [hy]
  have hnb : {z : Space | h+(‖y‖-h)/2 ≤ ‖z‖} ∈ 𝓝 y :=
    Filter.mem_of_superset
      (continuous_norm.continuousAt.preimage_mem_nhds
        (Ioi_mem_nhds (show h+(‖y‖-h)/2 < ‖y‖ by linarith [hy])))
      (fun z hz => show h+(‖y‖-h)/2 ≤ ‖z‖ from hz.le)
  exact ((sourcePotential_lipschitzOn mu hs hd).continuousOn.continuousAt hnb).continuousWithinAt

 lemma compact_exterior_separated {K : Set Space} (hK : IsCompact K) {h : ℝ}
    (hs : K ⊆ {y | h < ‖y‖}) : ∃ d > 0, K ⊆ {y | h+d ≤ ‖y‖} := by
  rcases K.eq_empty_or_nonempty with he | hn
  · exact ⟨1,by norm_num,by simp [he]⟩
  obtain ⟨y,hy,hmin⟩ := hK.exists_isMinOn hn continuous_norm.continuousOn
  refine ⟨‖y‖-h,sub_pos.mpr (hs hy),?_⟩
  intro z hz
  change h+(‖y‖-h) ≤ ‖z‖
  simp only [add_sub_cancel]
  exact hmin hz

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_InnerExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis

 def sourceField (Z : ℝ) (mu : Measure Space) (y : Space) : ℝ :=
   Z/‖y‖-sourcePotential mu y

 lemma sourceField_le_nuclear (Z : ℝ) (mu : Measure Space) (y : Space) :
     sourceField Z mu y ≤ Z/‖y‖ := sub_le_self _ (sourcePotential_nonneg mu y)

 lemma sourceField_continuousOn (Z : ℝ) (mu : Measure Space) [IsFiniteMeasure mu]
     {h : ℝ} (hh : 0 ≤ h) (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) :
     ContinuousOn (sourceField Z mu) {y | h < ‖y‖} := by
   exact (continuousOn_const.div continuous_norm.continuousOn
     (fun y hy => ne_of_gt (hh.trans_lt hy))).sub
       (sourcePotential_continuousOn_exterior mu hs)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CanonicalRealPacketBarrier
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped ContDiff

namespace CoulombAtom
open CoulombAnalysis

def realPacketSeed (x : Space) : ℝ := Real.smoothTransition (1-4*‖x‖^2)
lemma realPacketSeed_smooth : ContDiff ℝ ∞ realPacketSeed := by
  apply Real.smoothTransition.contDiff.comp
  exact contDiff_const.sub (contDiff_const.mul (contDiff_id.norm_sq ℝ))
lemma realPacketSeed_zero {x : Space} (hx : 1/2 ≤ ‖x‖) : realPacketSeed x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [norm_nonneg x]
lemma realPacketSeed_tsupport : tsupport realPacketSeed ⊆ closedBall (0 : Space) (1/2) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  rw [mem_closedBall,dist_zero_right]
  by_contra hh
  exact hx (realPacketSeed_zero (not_le.mp hh).le)
lemma realPacketSeed_compact : HasCompactSupport realPacketSeed :=
  (isCompact_closedBall (0:Space) (1/2)).of_isClosed_subset isClosed_closure realPacketSeed_tsupport
lemma realPacketSeed_mass_pos : 0 < ∫ x, realPacketSeed x^2 := by
  apply (realPacketSeed_smooth.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (by simpa only [pow_two] using realPacketSeed_compact.mul_left (f := realPacketSeed)) (fun x => sq_nonneg _ ) (x := 0)
  simp [realPacketSeed,Real.smoothTransition.one_of_one_le]

def canonicalRealPacket (x : Space) : ℝ := (Real.sqrt (∫ z, realPacketSeed z^2))⁻¹*realPacketSeed x
lemma canonicalRealPacket_smooth : ContDiff ℝ ∞ canonicalRealPacket :=
  contDiff_const.mul realPacketSeed_smooth
lemma canonicalRealPacket_compact : HasCompactSupport canonicalRealPacket :=
  realPacketSeed_compact.mul_left
lemma canonicalRealPacket_normalized : ∫ x, canonicalRealPacket x^2 = 1 := by
  simp only [canonicalRealPacket,mul_pow,integral_const_mul,inv_pow,
    Real.sq_sqrt realPacketSeed_mass_pos.le]
  exact inv_mul_cancel₀ realPacketSeed_mass_pos.ne'
lemma canonicalRealPacket_radial : IsRadial canonicalRealPacket := by
  intro x y h
  simp only [canonicalRealPacket,realPacketSeed,h]
lemma canonicalRealPacket_support : tsupport canonicalRealPacket ⊆ ball (0:Space) 1 := by
  intro x hx
  have hh : x ∈ tsupport realPacketSeed := tsupport_mul_subset_right hx
  have hn : ‖x‖ ≤ (1/2:ℝ) := by simpa only [mem_closedBall,dist_zero_right] using realPacketSeed_tsupport hh
  simp only [mem_ball,dist_zero_right]
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RetainedInnerMassBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter Metric
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma retainedSmear_mono {N : ℕ} {b : ℝ} (hb : 0 < b)
    {S T : Finset (Fin N)} (hST : S ⊆ T) (x : Configuration N) (z : Space) :
    retainedSmear b S x z ≤ retainedSmear b T x z := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hST
  intro i _ _
  exact varthetaScaled_nonneg hb _

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_LipschitzResidualBase
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LipschitzResidualBase_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

attribute [local irreducible] graphComponent graphFormVector FermionMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy

def sectorExcessOperator (Z : ℝ) (N : ℕ) : fermionGraph N →L[ℂ] fermionGraph N :=
  coulombFormOperator Z N-(energy Z N : ℂ) •
    ((fermionGraphValue N).adjoint.comp (fermionGraphValue N))

attribute [local irreducible] sectorExcessOperator

end Work_LipschitzResidualBase_scope

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

attribute [local irreducible] graphComponent graphFormVector FermionLipschitzMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma thinFieldBase_linear_bound {a m D B C : ℝ}
    (ha : 0 < a) (hm : 1 ≤ m) (h3 : 1/a^3 ≤ m) (hB : 0 ≤ B)
    (hC : 1 ≤ C) (hBC : B ≤ C*m^2) :
    thinFieldBase a a D B ≤ D/a+(5+C+localizationIMSConstant*C)*(m/a)^2 := by
  have hh := localFieldScale_linear_bound ha hm h3 hC hBC (D := D)
  have hr : Real.sqrt B ≤ C*m := by
    simpa using sqrt_count_scale hB hC (by norm_num : (0:ℝ) ≤ 1)
      (le_trans zero_le_one hm) (by simpa using hBC)
  have hI := localizationIMSConstant_nonneg
  have hma : m/a^3 ≤ (m/a)^2 := by
    have ht := mul_le_mul_of_nonneg_right (cell_mass_product ha hm h3)
      (show 0 ≤ m/a^3 by positivity)
    calc _ ≤ (a*m)*(m/a^3) := by simpa using ht
         _ = (m/a)^2 := by field_simp
  have hi : localizationIMSConstant*Real.sqrt B/(a^2*a) ≤
      localizationIMSConstant*C*(m/a)^2 := by
    calc _ ≤ localizationIMSConstant*(C*m)/(a^2*a) := by gcongr
         _ = localizationIMSConstant*C*(m/a^3) := by ring
         _ ≤ _ := by gcongr
  unfold thinFieldBase
  nlinarith only [hh,hi]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_AllSectorEnergy
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
open MeasureTheory Set Metric
open scoped ENNReal
namespace CoulombAtom

namespace Pauli

def spatialDensity : {N : ℕ} → (ψ : FormVector N) →
    (∀ s, MemLp (ψ.value s) 2) → Space → ℝ
  | 0, _, _ => 0
  | _+1, ψ, hψ => density ψ hψ

end Pauli
end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ActualPosteriorCapBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

def dyadicUniformEventBudget (r p₀ δ : ℝ) : ℝ :=
  observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/p₀))^5+δ

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric Laplacian
noncomputable section
namespace CoulombAtom
open CoulombAnalysis

 def packetPotentialConstant : ℝ := 1+9*packetDensityConstant*unitCoulombIntegral

end CoulombAtom

end

end OAI
end


