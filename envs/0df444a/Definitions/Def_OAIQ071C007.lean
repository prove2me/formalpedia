-- Prove2me | Definitions.Def_OAIQ071C007
-- name    : OAIQ071C007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T05:10:14.167888+00:00
-- url     : https://prove2.me/theorems/3fadf679-5aae-4858-ab08-3c70cfecb661
-- title:
--   Definitions bundle OAIQ071C007 of the split of OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 245 declarations of OpenAI's Lean: 32 definitions, 1 inductive type or structure, 1 instance and 211 theorems. The definitions and types are `OAI.CoulombAtom.OuterCutRetention`, `OAI.CoulombAtom.ballAverageKernel`, `OAI.CoulombAtom.cellDensityMassConstant`, `OAI.CoulombAtom.coherentBasis`, `OAI.CoulombAtom.coherentCoefficient`, `OAI.CoulombAtom.coherentOrbital`, `OAI.CoulombAtom.coherentPhaseRaw`, `OAI.CoulombAtom.coherentPhaseVector`, `OAI.CoulombAtom.conditionalFieldSum`, `OAI.CoulombAtom.cosetWedge`, `OAI.CoulombAtom.cutDeletedCount`, `OAI.CoulombAtom.cutOutPositions`, `OAI.CoulombAtom.diffuseKinetic`, `OAI.CoulombAtom.flatRawLaw`, `OAI.CoulombAtom.localCountCoverConstant`, `OAI.CoulombAtom.localCountStencil`, `OAI.CoulombAtom.localGradientTrace`, `OAI.CoulombAtom.localOffsetMass`, `OAI.CoulombAtom.localPatchDensityCap`, `OAI.CoulombAtom.outFirstLabels`, `OAI.CoulombAtom.outerDeletedCount`, `OAI.CoulombAtom.outerDeletedPotential`, `OAI.CoulombAtom.quantumUpperDeficitConstant`, `OAI.CoulombAtom.radialPatchRetention`, `OAI.CoulombAtom.rawLocalPotential`, `OAI.CoulombAtom.restrictWeakGraph`, `OAI.CoulombAtom.sectorGraphPermutation`, `OAI.CoulombAtom.truncateForm`, `OAI.CoulombAtom.truncationMultiplier`, `OAI.CoulombAtom.unorderedOutKinetic`, `OAI.CoulombAtom.weakGraphChange`, `OAI.CoulombBarrier.InitialNumerics`, `OAI.CoulombBarrier.actualInverseCap`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombIonization_Fermionic_CutCountDomination`, `CoulombIonization_Fermionic_OccupationPairDensity`, `CoulombIonization_Fermionic_SlaterMeasure`, `CoulombIonization_Fermionic_SlaterOccupation`, `CoulombIonization_Fermionic_SlaterRepulsion`, `CoulombIonization_Fermionic_SlaterSymmetry`, `CoulombIonization_FieldAnalysis_ConditionalFieldIdentity`, `CoulombIonization_FieldAnalysis_CoreFieldPairing`, `CoulombIonization_FieldAnalysis_CoreFieldRegularity`, `CoulombIonization_FieldAnalysis_DeletedFieldBudget`, `CoulombIonization_FieldAnalysis_InnerExterior`, `CoulombIonization_FieldAnalysis_PatchWeakPoisson`, `CoulombIonization_FieldAnalysis_RetainedFieldIdentity`, `CoulombIonization_FieldAnalysis_RetainedInnerMassBarrier`, `CoulombIonization_FieldAnalysis_RetainedPatchDensity`, `CoulombIonization_FormDomain_BlockEnergetics`, `CoulombIonization_FormDomain_BlockWedge`, `CoulombIonization_FormDomain_CoherentHilbert`, `CoulombIonization_FormDomain_CoherentLimitInsertion`, `CoulombIonization_FormDomain_CoherentSchwartz`, `CoulombIonization_FormDomain_CompactEigenbasis`, `CoulombIonization_FormDomain_CosetWedge`, `CoulombIonization_FormDomain_FermionicDensity`, `CoulombIonization_FormDomain_Forms`, `CoulombIonization_FormDomain_Restriction`, `CoulombIonization_FormDomain_WeakChangeVariables`, `CoulombIonization_Ionization_ActualUpperDeficitBarrier`, `CoulombIonization_Ionization_CoherentDerivatives`, `CoulombIonization_Ionization_ConditionalPricedUpper`, `CoulombIonization_Ionization_PricedUpperComparison`, `CoulombIonization_Localization_ArraySymmetry`, `CoulombIonization_Localization_CoherentKinetic`, `CoulombIonization_Localization_CoherentRealKinetic`, `CoulombIonization_Localization_CutOuterLaw`, `CoulombIonization_Localization_FermiDensity`, `CoulombIonization_Localization_FormRawLaw`, `CoulombIonization_Localization_PacketScale`, `CoulombIonization_Localization_QuantumRawLaw`, `CoulombIonization_Localization_RadialPacket`, `CoulombIonization_RadialBounds_BallAverageKernelBarrier`, `CoulombIonization_RadialBounds_BarrierDataSelectionBarrier`, `CoulombIonization_RadialBounds_CellCountSupremumBarrier`, `CoulombIonization_RadialBounds_CellScaleBarrier`, `CoulombIonization_RadialBounds_FermiMeasure`, `CoulombIonization_RadialBounds_FiniteBarrier`, `CoulombIonization_RadialBounds_FockKineticReindexBarrier`, `CoulombIonization_RadialBounds_FreshInnerCountsBarrier`, `CoulombIonization_RadialBounds_RadialCountSelection`, `CoulombIonization_RadialBounds_RadialInside`, `CoulombIonization_RadialBounds_RadialPatchGeometry`, `CoulombIonization_RadialBounds_RootMomentCauchyBarrier`, `CoulombIonization_RadialBounds_TailParticleCount`, `CoulombIonization_RadialBounds_TruncationRadius`, `CoulombIonization_ThomasFermi_CellDensityBoundBarrier`, `CoulombIonization_ThomasFermi_CoherentFiniteInsertion`, `CoulombIonization_ThomasFermi_CoherentPhaseBasis`, `CoulombIonization_ThomasFermi_OutCutAntisymmetry`, `CoulombIonization_Variational_CoherentBessel`, `CoulombIonization_Variational_CoherentDensity`, `CoulombIonization_Variational_CoherentDensityTrace`, `CoulombIonization_Variational_CoherentOrbitals`, `CoulombIonization_Variational_CoherentResolution`, `CoulombIonization_Variational_CompactPotential`, `CoulombIonization_Variational_DeletedPotential`, `CoulombIonization_Variational_DiffuseSeed`, `CoulombIonization_Variational_InnerPotential`, `CoulombIonization_Variational_IntegrableCutTower`, `CoulombIonization_Variational_LocalWidthKernel`, `CoulombIonization_Variational_OccupationTraces`, `CoulombIonization_Variational_OutRetainedLower`, `CoulombIonization_Variational_PatchContinuity`, `CoulombIonization_Variational_SmearingPotential`, `CoulombIonization_Variational_SmoothCompactIntegral`, `CoulombIonization_Variational_SpatialErrorWeight`, `CoulombIonization_Variational_SpinEnergy`, `CoulombIonization_Variational_SpinSpaceIntegrable`.
--
--   **Imports.** It imports the published bundle `Def_CoulombIonization`; the bundles `OAIQ071C003`, `OAIQ071C004` and `OAIQ071C005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ071C008`, `OAIQ071C009`, `OAIQ071C011` and `OAIQ071C012`; the statement `OAI.CoulombAtom.actual_uniform_upper_deficit`.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C003
import Definitions.Def_OAIQ071C004
import Definitions.Def_OAIQ071C005

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakChangeVariables
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

section WeakGraphChange
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma weakGraphChangeAmbient_mem (v : ι → E) (e : E ≃L[ℝ] E) (he : MeasurePreserving e)
    (κ : ι → ι) (hv : ∀ i, e (v i) = v (κ i)) (F : weakGraph v) :
    weakGraphChangeAmbient v e he κ F ∈ weakGraph v := by
  rw [mem_weakGraph]
  intro i
  have hh := ((mem_weakGraph v F.val).mp F.property (κ i)).comp_linearEquiv e he (hv i)
  exact hh.congr_ae (Lp.coeFn_compMeasurePreserving (F.val none) he).symm
    (Lp.coeFn_compMeasurePreserving (F.val (some (κ i))) he).symm

def weakGraphChange (v : ι → E) (e : E ≃L[ℝ] E) (he : MeasurePreserving e)
    (κ : ι → ι) (hv : ∀ i, e (v i) = v (κ i)) : weakGraph v →L[ℂ] weakGraph v :=
  (weakGraphChangeAmbient v e he κ).codRestrict (weakGraph v)
    (weakGraphChangeAmbient_mem v e he κ hv)

end WeakGraphChange

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FermionicDensity
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

def sectorGraphPermutation {N : ℕ} (π : Equiv.Perm (Fin N)) : SectorGraph N →L[ℂ] SectorGraph N :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Spins N => weakGraph (sectorDirections N))
    ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun s =>
      ((((Equiv.Perm.sign π : ℤ) : ℂ)) • weakGraphChange (sectorDirections N)
        (permuteConfiguration π) (permuteConfiguration_preserving π)
        (fun k => (π.symm k.1, k.2)) (sectorDirections_permute π)).comp
        (PiLp.proj 2 (fun _ : Spins N => weakGraph (sectorDirections N)) (s ∘ π)))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FormRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma formRawDensity_integral {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    ∫ x, formRawDensity ψ x = formMass ψ :=
  integral_finsetSum _ (fun s _ => (hψ.1 s).norm.integrable_sq)

lemma rawBallCount_sq_integrable {N : ℕ} (y : Space) (R : ℝ)
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] :
    Integrable (fun x => rawBallCount y R x^2) μ := by
  apply Integrable.of_bound ((rawBallCount_measurable y R).pow_const 2).aestronglyMeasurable
    ((N:ℝ)^2)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _) 2)

lemma upperCount_le_rawBallCount {N : ℕ} (y : Space) {R S : ℝ} (hRS : R < S)
    (x : Configuration N) : upperCount (fun i => ‖x i-y‖) R ≤ rawBallCount y S x := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h₁ h₂ <;> try norm_num
  exact False.elim (h₂ (lt_of_le_of_lt h₁ hRS))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Forms
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma finite_partition_gradient (ψ : FormVector N) (s : Spins N)
    (i : Fin N) (a : Fin 3) (x : Configuration N) :
    (∑ j, ‖(multiplyForm (p j) ψ).gradient s i a x‖ ^ 2) =
      ‖ψ.gradient s i a x‖ ^ 2 +
        (∑ j, lineDeriv ℝ (p j).value x (direction i a) ^ 2) * ‖ψ.value s x‖ ^ 2 := by
  exact finite_complex_ims _ _ (hp x)
    (square_partition_derivative _ (fun j => (p j).regular.differentiable (by simp))
      hp x (direction i a)) _ _

omit hp [Fintype J] in
lemma smoothMultiplier_gradient_integrable (j : J) {ψ : FormVector N}
    (hψ : SobolevVector ψ) (s : Spins N) (i : Fin N) (a : Fin 3) :
    Integrable (fun x => lineDeriv ℝ (p j).value x (direction i a) ^ 2 *
      ‖ψ.value s x‖ ^ 2) := by
  have hh := (memLp_bounded_mul ((p j).derivative_continuous (i,a))
    ((p j).gradient_bound (i,a)) (hψ.1 s)).norm.integrable_sq
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using hh

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpatialErrorWeight
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma spatial_derivative_density_integrable {ψ : FormVector N} (hψ : SobolevVector ψ)
    (s : Spins N) (i : Fin N) (a : Fin 3) (h : Fin 2) :
    Integrable (fun x : Configuration N =>
      lineDeriv ℝ (p h).value (x i) (spaceDirections a) ^ 2 * ‖ψ.value s x‖ ^ 2) := by
  have hc : Continuous (fun x : Configuration N =>
      lineDeriv ℝ (p h).value (x i) (spaceDirections a)) :=
    ((p h).derivative_continuous a).comp (continuous_apply i)
  have hb : ∃ C, ∀ x : Configuration N,
      |lineDeriv ℝ (p h).value (x i) (spaceDirections a)| ≤ C := by
    obtain ⟨C,hC⟩ := (p h).gradient_bound a
    exact ⟨C,fun x => hC (x i)⟩
  have hh := (memLp_bounded_mul hc hb (hψ.1 s)).norm.integrable_sq
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using hh

lemma spatial_error_weight_integrable {ψ : FormVector N} (hψ : SobolevVector ψ)
    (s : Spins N) (i : Fin N) :
    Integrable (fun x => spatialErrorWeight p (x i) * ‖ψ.value s x‖ ^ 2) := by
  simp only [spatialErrorWeight, Finset.sum_mul]
  exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _
    (fun h _ => spatial_derivative_density_integrable p hψ s i a h))

theorem spatial_cut_error {ψ : FormVector N} (hψ : SobolevVector ψ) :
    (∑ b : Fin N → Fin 2, formMultiplierError (spatialProduct p hp b) ψ) =
      (1 / 2 : ℝ) * ∑ s : Spins N, ∑ i : Fin N,
        ∫ x, spatialErrorWeight p (x i) * ‖ψ.value s x‖ ^ 2 := by
  simp only [formMultiplierError, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  simp only [spatialErrorWeight, Finset.sum_mul]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
    (fun h _ => spatial_derivative_density_integrable p hψ s i a h))]
  apply Finset.sum_congr rfl; intro a _
  rw [← integral_finsetSum _ (fun b _ =>
    smoothMultiplier_gradient_integrable (spatialProduct p hp) b hψ s i a)]
  apply integral_congr_ae (Eventually.of_forall _)
  intro x
  rw [← Finset.sum_mul, spatial_derivative_square_sum p hp, Finset.sum_mul]

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialInside
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma radialCut_partition (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (x : Space) : ∑ h : Fin 2, (radialCut y ht hb h).value x ^ 2 = 1 := by
  simpa only [Fin.sum_univ_two, radialCut, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, radialInside, radialOutside, add_comm] using
    Real.sin_sq_add_cos_sq (radialPhase y t b x)

end CoulombAtom

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TailParticleCount
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma weightedParticleCount_integrable {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) {w : Space → ℝ} (hw : Measurable w)
    {B : ℝ} (hb : ∀ x, ‖w x‖ ≤ B) (s : Spins L) (i : Fin L) :
    Integrable (fun x => w (x i) * ‖ψ.value s x‖^2) :=
  ((hψ.1 s).norm.integrable_sq).bdd_mul
    (hw.comp (measurable_pi_apply i)).aestronglyMeasurable
    (Eventually.of_forall fun x => hb (x i))

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_BlockEnergetics
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma formKinetic_core_out {N M : ℕ} (ψ : FormVector (N+M)) :
    formKinetic ψ = coreKinetic ψ+outKinetic ψ := by
  unfold formKinetic coreKinetic outKinetic
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [←Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TruncationRadius
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
namespace CoulombAtom

def truncationMultiplier (N k : ℕ) : FermionMultiplier N where
  toSmoothMultiplier := spatialProduct
    (radialCut 0 (truncationRadius_pos k).le (truncationRadius_pos k))
    (radialCut_partition 0 (truncationRadius_pos k).le (truncationRadius_pos k)) (fun _ => 0)
  symmetric π x := spatialProduct_invariant _ _ π rfl x

def truncateForm {N : ℕ} (k : ℕ) (ψ : FormVector N) : FormVector N :=
  multiplyForm (truncationMultiplier N k).toSmoothMultiplier ψ

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_DiffuseSeed
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
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

def diffuseKinetic : ℝ :=
  formKinetic (smoothForm (trialSeed 1)) / formMass (smoothForm (trialSeed 1))


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ConditionalFieldIdentity
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma coreSlice_mass_div {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (y : Configuration M) (j : Fin M) :
    formMass (coreSlice ψ t y)/‖y j‖ =
      ∑ s : Spins N, ∫ x : Configuration N, ‖ψ.value (joinLists s t) (joinLists x y)‖^2/‖y j‖ := by
  simp only [formMass,Finset.sum_div,integral_div,coreSlice]

def conditionalFieldSum {N M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+M))
    (t : Spins M) (y : Configuration M) : ℝ :=
  formMass (coreSlice ψ t y)*∑ j : Fin M,
    normalizedCoreField Z lam (coreSlice ψ t y) (y j)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CoherentResolution
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma coherentOverlap_continuous {g u : Space → ℂ}
    (hg : Continuous g) (hcg : HasCompactSupport g)
    (hu : Continuous u) (hcu : HasCompactSupport u) :
    Continuous (fun q : Space × Space => coherentOverlap g u q.1 q.2) := by
  obtain ⟨C,hC⟩ := hg.norm.exists_forall_ge_of_hasCompactSupport hcg.norm
  apply continuous_of_dominated (bound := fun x => ‖g C‖ * ‖u x‖)
  · intro q
    unfold coherentPacket
    fun_prop
  · intro q
    filter_upwards [] with x
    rw [norm_mul,Complex.norm_conj,coherentPacket_norm]
    exact mul_le_mul_of_nonneg_right (hC (x-q.1)) (norm_nonneg _)
  · exact (hu.norm.integrable_of_hasCompactSupport hcu.norm).const_mul ‖g C‖
  · filter_upwards [] with x
    unfold coherentPacket
    fun_prop

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoherentHilbert
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoherentHilbert_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff FourierTransform Topology

lemma coherentVector_norm_sq {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (q : Space × Space) : ‖coherentVector hg hcg q‖^2 = ∫ x : Space, ‖g x‖^2 := by
  rw [lp_norm_sq]
  calc
    _ = ∫ x : Space, ‖coherentPacket g q.1 q.2 x‖^2 :=
      integral_congr_ae ((coherentVector_coe hg hcg q).fun_comp (fun t : ℂ => ‖t‖^2))
    _ = ∫ x : Space, ‖g (x-q.1)‖^2 := by simp only [coherentPacket_norm]
    _ = _ := integral_sub_right_eq_self (fun x : Space => ‖g x‖^2) q.1

lemma coherentVector_continuous {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g) :
    Continuous (coherentVector hg hcg) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have he : (fun q : Space × Space => ‖coherentVector hg hcg q - coherentVector hg hcg r‖) =
      (fun q : Space × Space => Real.sqrt ((∫ x : Space, ‖g x‖^2) - 2 *
      (coherentOverlap g (coherentPacket g r.1 r.2) q.1 q.2).re + (∫ x : Space, ‖g x‖^2))) := by
    funext q
    have hs : (∫ x : Space, ‖g x‖^2) - 2 *
        (coherentOverlap g (coherentPacket g r.1 r.2) q.1 q.2).re + (∫ x : Space, ‖g x‖^2) =
        ‖coherentVector hg hcg q - coherentVector hg hcg r‖^2 := by
      rw [norm_sub_sq (𝕜 := ℂ),coherentVector_norm_sq,coherentVector_norm_sq,coherentVector_inner]
      rfl
    rw [hs,Real.sqrt_sq (norm_nonneg _)]
  rw [he]
  have hu : Continuous (coherentPacket g r.1 r.2) := by unfold coherentPacket; fun_prop
  have hc := coherentOverlap_continuous hg hcg hu (coherentPacket_compact hcg r.1 r.2)
  have hcont : Continuous (fun q : Space × Space => Real.sqrt ((∫ x : Space, ‖g x‖^2) - 2 *
      (coherentOverlap g (coherentPacket g r.1 r.2) q.1 q.2).re + (∫ x : Space, ‖g x‖^2))) :=
    (((continuous_const.sub ((Complex.continuous_re.comp hc).const_mul 2)).add continuous_const).sqrt)
  have hi : (∫ x : Space, ‖g x‖^2) - 2 *
      (coherentOverlap g (coherentPacket g r.1 r.2) r.1 r.2).re + (∫ x : Space, ‖g x‖^2) = 0 := by
    rw [← coherentVector_inner hg hcg r r]
    have hn : (inner ℂ (coherentVector hg hcg r) (coherentVector hg hcg r)).re =
        ∫ x : Space, ‖g x‖^2 := by
      calc
        _ = ‖coherentVector hg hcg r‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
        _ = _ := coherentVector_norm_sq hg hcg r
    rw [hn]
    ring
  simpa only [ContinuousAt,hi,Real.sqrt_zero] using hcont.continuousAt (x := r)

end Work_CoherentHilbert_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

lemma coherentRankOne_continuous {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) : Continuous (fun q => InnerProductSpace.rankOne ℂ
    (coherentVector hg hcg q) (coherentVector hg hcg q)) := by
  simp only [InnerProductSpace.rankOne_def]
  exact ((ContinuousLinearMap.smulRightL ℂ OrbitalHilbert OrbitalHilbert).continuous.comp
    ((innerSL ℂ).continuous.comp (coherentVector_continuous hg hcg))).clm_apply
      (coherentVector_continuous hg hcg)

lemma coherentRankOne_integrable {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    Integrable (fun q => InnerProductSpace.rankOne ℂ
      (coherentVector hg hcg q) (coherentVector hg hcg q)) μ := by
  apply Integrable.of_bound (coherentRankOne_continuous hg hcg).aestronglyMeasurable
    (∫ x : Space, ‖g x‖^2)
  filter_upwards [] with q
  rw [InnerProductSpace.norm_rankOne,← pow_two,coherentVector_norm_sq]

lemma coherentOperator_inner {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (u : OrbitalHilbert) :
    inner ℂ u (coherentOperator hg hcg μ u) =
      (((2*Real.pi)^3)⁻¹ * ∫ q, ‖inner ℂ (coherentVector hg hcg q) u‖^2 ∂μ : ℝ) := by
  change inner ℂ u ((((2*Real.pi)^3)⁻¹ : ℝ) • ((∫ q,
    InnerProductSpace.rankOne ℂ (coherentVector hg hcg q) (coherentVector hg hcg q) ∂μ) u)) = _
  rw [inner_smul_right_eq_smul,inner_integral_rankOne μ _ (coherentRankOne_integrable hg hcg μ),
    Complex.real_smul,Complex.ofReal_mul]

lemma coherentOperator_inner_left {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (u : OrbitalHilbert) :
    inner ℂ (coherentOperator hg hcg μ u) u =
      (((2*Real.pi)^3)⁻¹ * ∫ q, ‖inner ℂ (coherentVector hg hcg q) u‖^2 ∂μ : ℝ) := by
  rw [← inner_conj_symm (coherentOperator hg hcg μ u) u,coherentOperator_inner]
  exact Complex.conj_ofReal _

lemma coherentOperator_positive {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    (coherentOperator hg hcg μ).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro u
  rw [coherentOperator_inner_left]
  simp only [RCLike.re_to_complex,Complex.ofReal_re]
  exact ⟨trivial,mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))⟩

lemma coherentOperator_compact {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    IsCompactOperator (coherentOperator hg hcg μ) := by
  let K := (compactOperator (RingHom.id ℂ) OrbitalHilbert OrbitalHilbert).restrictScalars ℝ
  have hm (q : Space × Space) : InnerProductSpace.rankOne ℂ
      (coherentVector hg hcg q) (coherentVector hg hcg q) ∈ K := by
    change IsCompactOperator (InnerProductSpace.rankOne ℂ _ _)
    rw [InnerProductSpace.rankOne_def']
    exact (isCompactOperator_of_locallyCompactSpace_rng
      (ContinuousLinearMap.toSpanSingleton ℂ _)).comp_clm _
  by_cases hμ : μ = 0
  · subst μ
    simp [coherentOperator,isCompactOperator_zero]
  let : NeZero μ := ⟨hμ⟩
  have hclosed : IsClosed (K : Set (OrbitalHilbert →L[ℂ] OrbitalHilbert)) := by
    change IsClosed { f : OrbitalHilbert →L[ℂ] OrbitalHilbert | IsCompactOperator f }
    exact isClosed_setOfPred_isCompactOperator
  have ha : (⨍ q, InnerProductSpace.rankOne ℂ (coherentVector hg hcg q)
      (coherentVector hg hcg q) ∂μ) ∈ K :=
    K.convex.average_mem hclosed (Eventually.of_forall hm)
      (coherentRankOne_integrable hg hcg μ)
  have hb := K.smul_mem (μ.real Set.univ) ha
  rw [measure_smul_average] at hb
  exact K.smul_mem (((2*Real.pi)^3)⁻¹ : ℝ) hb

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoherentSchwartz
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoherentSchwartz_scope

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff FourierTransform

lemma coherentOverlap_continuous_schwartz {g : Space → ℂ}
    (hg : Continuous g) (hcg : HasCompactSupport g) (u : SchwartzMap Space ℂ) :
    Continuous (fun q : Space × Space => coherentOverlap g u q.1 q.2) := by
  obtain ⟨C,hC⟩ := hg.norm.exists_forall_ge_of_hasCompactSupport hcg.norm
  apply continuous_of_dominated (bound := fun x => ‖g C‖ * ‖u x‖)
  · intro q
    unfold coherentPacket
    have hu := u.continuous
    fun_prop
  · intro q
    filter_upwards [] with x
    rw [norm_mul,Complex.norm_conj,coherentPacket_norm]
    exact mul_le_mul_of_nonneg_right (hC (x-q.1)) (norm_nonneg _)
  · exact u.integrable.norm.const_mul ‖g C‖
  · filter_upwards [] with x
    unfold coherentPacket
    fun_prop

lemma coherentOverlap_integrable_schwartz {g : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (u : SchwartzMap Space ℂ) :
    Integrable (fun q : Space × Space => ‖coherentOverlap g u q.1 q.2‖^2) := by
  apply (integrable_prod_iff ((coherentOverlap_continuous_schwartz hg.continuous hcg u).norm.pow 2).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (coherentOverlap_momentum_integrable_schwartz hg hcg u)
  · have he (z : Space) : (∫ p : Space, ‖‖coherentOverlap g u z p‖^2‖) =
        (2*Real.pi)^3 * (∫ x : Space, ‖g (x-z)‖^2 * ‖u x‖^2) := by
      simp_rw [norm_pow,Real.norm_of_nonneg (norm_nonneg _)]
      have h := coherentOverlap_momentum_schwartz hg hcg u z
      have hn : (2*Real.pi)^3 ≠ 0 := by positivity
      calc
        _ = (2*Real.pi)^3 * (((2*Real.pi)^3)⁻¹ * _) := by field_simp
        _ = _ := by rw [h]
    change Integrable (fun z : Space => ∫ p : Space, ‖‖coherentOverlap g u z p‖^2‖)
    simp_rw [he]
    exact (coherent_position_integrable_schwartz hg.continuous hcg u).integral_prod_left.const_mul _

lemma coherentOverlap_resolution_schwartz {g : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (u : SchwartzMap Space ℂ) :
    ((2*Real.pi)^3)⁻¹ * (∫ q : Space × Space, ‖coherentOverlap g u q.1 q.2‖^2) =
      (∫ z : Space, ‖g z‖^2) * (∫ x : Space, ‖u x‖^2) := by
  change ((2*Real.pi)^3)⁻¹ * (∫ q : Space × Space, ‖coherentOverlap g u q.1 q.2‖^2 ∂volume.prod volume) = _
  rw [integral_prod _ (coherentOverlap_integrable_schwartz hg hcg u),← integral_const_mul]
  simp_rw [coherentOverlap_momentum_schwartz hg hcg u]
  rw [integral_integral_swap (coherent_position_integrable_schwartz hg.continuous hcg u)]
  simp_rw [integral_mul_const,integral_sub_left_eq_self (fun t : Space => ‖g t‖^2) volume]
  rw [integral_const_mul]

end Work_CoherentSchwartz_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

lemma coherentOverlap_measure_le_schwartz {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (hgn : ∫ x : Space, ‖g x‖^2 = 1)
    (μ : Measure (Space × Space)) (hμ : μ ≤ volume) (v : SchwartzMap Space ℂ) :
    ((2*Real.pi)^3)⁻¹ * (∫ q, ‖coherentOverlap g v q.1 q.2‖^2 ∂μ) ≤ ∫ x : Space, ‖v x‖^2 := by
  have hi : Integrable (fun q : Space × Space => ‖coherentOverlap g v q.1 q.2‖^2) :=
    coherentOverlap_integrable_schwartz hg hcg v
  have hl : (∫ q, ‖coherentOverlap g v q.1 q.2‖^2 ∂μ) ≤
      ∫ q : Space × Space, ‖coherentOverlap g v q.1 q.2‖^2 :=
    integral_mono_measure hμ (Eventually.of_forall (fun q => sq_nonneg _)) hi
  calc
    _ ≤ ((2*Real.pi)^3)⁻¹ * (∫ q : Space × Space, ‖coherentOverlap g v q.1 q.2‖^2) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ = _ := by rw [coherentOverlap_resolution_schwartz hg hcg v,hgn,one_mul]

lemma coherentOperator_schwartz_le {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (hgn : ∫ x : Space, ‖g x‖^2 = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume)
    (v : SchwartzMap Space ℂ) :
    (inner ℂ (v.toLp 2) (coherentOperator hg.continuous hcg μ (v.toLp 2))).re ≤ ‖v.toLp 2‖^2 := by
  rw [coherentOperator_inner,Complex.ofReal_re,schwartz_toLp_norm_sq]
  simp_rw [coherentVector_inner_schwartz]
  exact coherentOverlap_measure_le_schwartz hg hcg hgn μ hμ v

lemma coherentOperator_quadratic_le {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (hgn : ∫ x : Space, ‖g x‖^2 = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume)
    (u : OrbitalHilbert) :
    (inner ℂ u (coherentOperator hg.continuous hcg μ u)).re ≤ ‖u‖^2 := by
  refine (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) (μ := (volume : Measure Space))
    ENNReal.ofNat_ne_top).induction_on u ?_ ?_
  · apply isClosed_le
    · exact Complex.continuous_re.comp (continuous_id.inner
        (coherentOperator hg.continuous hcg μ).continuous)
    · exact continuous_id.norm.pow 2
  · intro v
    exact coherentOperator_schwartz_le hg hcg hgn μ hμ v

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CompactEigenbasis
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

def coherentBasis {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    HilbertBasis (CoherentIndex hg hcg μ) ℂ OrbitalHilbert :=
  compactSpectralBasis _ (coherentOperator_compact hg hcg μ)
    (coherentOperator_positive hg hcg μ).isSymmetric

instance coherentIndex_countable {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] : Countable (CoherentIndex hg hcg μ) :=
  orthonormal_countable (coherentBasis hg hcg μ).orthonormal

lemma coherentBasis_eigen {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    coherentOperator hg hcg μ (coherentBasis hg hcg μ i) =
      i.1 • coherentBasis hg hcg μ i := compactSpectralBasis_eigen _ _ _ i

lemma coherentBasis_inner_eigen {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    inner ℂ (coherentBasis hg hcg μ i) (coherentOperator hg hcg μ (coherentBasis hg hcg μ i)) = i.1 := by
  rw [coherentBasis_eigen,inner_smul_right,inner_self_eq_norm_sq_to_K,
    (coherentBasis hg hcg μ).orthonormal.norm_eq_one]
  simp

lemma coherentBasis_eigenvalue_eq {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    i.1 = (((2*Real.pi)^3)⁻¹ * ∫ q,
      ‖inner ℂ (coherentBasis hg hcg μ i) (coherentVector hg hcg q)‖^2 ∂μ : ℝ) := by
  rw [← coherentBasis_inner_eigen hg hcg μ i,coherentOperator_inner]
  congr 2
  apply integral_congr_ae
  exact Eventually.of_forall (fun q => congrArg (fun t : ℝ => t^2) (norm_inner_symm _ _))

lemma coherentWeight_eq {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    coherentWeight hg hcg μ i = ((2*Real.pi)^3)⁻¹ * ∫ q,
      ‖inner ℂ (coherentBasis hg hcg μ i) (coherentVector hg hcg q)‖^2 ∂μ := by
  rw [coherentWeight,coherentBasis_eigenvalue_eq,Complex.ofReal_re]

lemma coherentWeight_nonneg {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    0 ≤ coherentWeight hg hcg μ i := by
  rw [coherentWeight_eq]
  exact mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))

lemma coherentBasis_real_eigen {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    coherentOperator hg hcg μ (coherentBasis hg hcg μ i) =
      coherentWeight hg hcg μ i • coherentBasis hg hcg μ i := by
  rw [coherentBasis_eigen,coherentBasis_eigenvalue_eq,coherentWeight_eq]
  rw [Complex.coe_smul]
  rfl

lemma coherentWeight_le_one {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (hgn : ∫ x : Space, ‖g x‖^2 = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume)
    (i : CoherentIndex hg.continuous hcg μ) : coherentWeight hg.continuous hcg μ i ≤ 1 := by
  have h := coherentOperator_quadratic_le hg hcg hgn μ hμ (coherentBasis hg.continuous hcg μ i)
  rw [coherentBasis_inner_eigen,(coherentBasis hg.continuous hcg μ).orthonormal.norm_eq_one] at h
  change i.1.re ≤ 1
  simpa only [one_pow] using h

lemma coherentWeight_hasSum {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    HasSum (coherentWeight hg hcg μ) (((2*Real.pi)^3)⁻¹ * μ.real Set.univ * ∫ x : Space, ‖g x‖^2) := by
  have hn : Integrable (fun q => ‖coherentVector hg hcg q‖^2) μ := by
    simp_rw [coherentVector_norm_sq]
    exact integrable_const _
  have ht := hilbertBasis_frame_trace μ (coherentBasis hg hcg μ) (coherentVector hg hcg)
    (coherentVector_continuous hg hcg).aestronglyMeasurable hn
  have he : (∫ q, ‖coherentVector hg hcg q‖^2 ∂μ) = μ.real Set.univ * ∫ x : Space, ‖g x‖^2 := by
    simp only [coherentVector_norm_sq,integral_const,smul_eq_mul]
  rw [he] at ht
  have hsum := ht.mul_left (((2*Real.pi)^3)⁻¹)
  have hf : coherentWeight hg hcg μ = (fun i => ((2*Real.pi)^3)⁻¹ *
      ∫ q, ‖inner ℂ (coherentBasis hg hcg μ i) (coherentVector hg hcg q)‖^2 ∂μ) :=
    funext (coherentWeight_eq hg hcg μ)
  rw [hf,mul_assoc]
  exact hsum

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SmoothCompactIntegral
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma packetSynthesis_smooth {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) :
    ContDiff ℝ ∞ (packetSynthesis g μ w) := by
  have h := weightedSetIntegral_contDiff μ K hK (coherentPacket_joint_smooth hg) hw
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at h
  exact h

lemma packetSynthesis_zero_outside {g : Space → ℂ}
    (μ : Measure (Space × Space)) {K : Set (Space × Space)} (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (w : Space × Space → ℂ) {x : Space} (hx : x ∉ coherentSpatialSupport g K) :
    packetSynthesis g μ w x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hμ] with q hq
  simp only [coherentPacket_zero_outside hq hx,mul_zero,Pi.zero_apply]

lemma packetSynthesis_compact {g : Space → ℂ} (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) {K : Set (Space × Space)} (hK : IsCompact K)
    (hμ : ∀ᵐ q ∂μ, q ∈ K) (w : Space × Space → ℂ) :
    HasCompactSupport (packetSynthesis g μ w) := by
  apply HasCompactSupport.of_support_subset_isCompact (coherentSpatialSupport_compact hcg hK)
  intro x hx
  by_contra hn
  exact hx (packetSynthesis_zero_outside μ hμ w hn)

lemma coherent_test_integrable {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) {v : Space → ℂ} (hv : Continuous v) :
    Integrable (fun r : (Space × Space) × Space =>
      conj (v r.2) * (w r.1 * coherentPacket g r.1.1 r.1.2 r.2)) (μ.prod volume) := by
  have hc : Continuous (fun r : (Space × Space) × Space =>
      conj (v r.2) * (w r.1 * coherentPacket g r.1.1 r.1.2 r.2)) := by
    unfold coherentPacket
    fun_prop
  have hi := hc.continuousOn.integrableOn_compact
    (hK.prod (coherentSpatialSupport_compact hcg hK)) (μ := μ.prod volume)
  apply hi.integrable_of_ae_notMem_eq_zero
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμ] with r hr
  intro hn
  have hx : r.2 ∉ coherentSpatialSupport g K := fun hx => hn ⟨hr,hx⟩
  rw [coherentPacket_zero_outside hr hx,mul_zero,mul_zero]

lemma packetSynthesis_test {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) (v : SchwartzMap Space ℂ) :
    (∫ x : Space, conj (v x) * packetSynthesis g μ w x) =
      ∫ q, w q * inner ℂ (v.toLp 2) (coherentVector hg hcg q) ∂μ := by
  simp only [packetSynthesis,← integral_const_mul]
  have hi : Integrable (fun r : Space × (Space × Space) =>
      conj (v r.1) * (w r.2 * coherentPacket g r.2.1 r.2.2 r.1)) (volume.prod μ) :=
    (coherent_test_integrable hg hcg μ hK hμ hw v.continuous).swap
  rw [integral_integral_swap (f := fun x q =>
    conj (v x) * (w q * coherentPacket g q.1 q.2 x)) hi]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [coherentVector_inner_schwartz_left,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma packetSynthesis_memLp {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) : MemLp (packetSynthesis g μ w) 2 :=
  (packetSynthesis_smooth hg μ hK hμ hw).continuous.memLp_of_hasCompactSupport
    (packetSynthesis_compact hcg μ hK hμ w)

lemma coherentVector_weight_integrable {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) :
    Integrable (fun q => w q • coherentVector hg hcg q) μ := by
  rw [← Measure.restrict_eq_self_of_ae_mem hμ]
  exact (hw.smul (coherentVector_continuous hg hcg)).continuousOn.integrableOn_compact hK

lemma packetSynthesis_toLp {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) :
    (packetSynthesis_memLp hg hcg μ hK hμ hw).toLp (packetSynthesis g μ w) =
      ∫ q, w q • coherentVector hg.continuous hcg q ∂μ := by
  apply ext_inner_left ℂ
  intro u
  refine (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) (μ := (volume : Measure Space))
    ENNReal.ofNat_ne_top).induction_on u ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · intro v
    change inner ℂ (v.toLp 2) _ = inner ℂ (v.toLp 2) _
    rw [← integral_inner (𝕜 := ℂ) (coherentVector_weight_integrable hg.continuous hcg μ hK hμ hw)]
    simp only [inner_smul_right]
    rw [← packetSynthesis_test hg.continuous hcg μ hK hμ hw v,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [v.coeFn_toLp 2 volume,
      (packetSynthesis_memLp hg hcg μ hK hμ hw).coeFn_toLp] with x hv hs
    rw [hv,hs]
    simp only [RCLike.inner_apply,mul_comm]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CoherentOrbitals
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma coherentOperator_synthesis {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (u : OrbitalHilbert) : coherentOperator hg hcg μ u =
      (((2*Real.pi)^3)⁻¹ : ℝ) • ∫ q, inner ℂ (coherentVector hg hcg q) u •
        coherentVector hg hcg q ∂μ := by
  change (((2*Real.pi)^3)⁻¹ : ℝ) • ((∫ q, InnerProductSpace.rankOne ℂ
    (coherentVector hg hcg q) (coherentVector hg hcg q) ∂μ) u) = _
  rw [ContinuousLinearMap.integral_apply (coherentRankOne_integrable hg hcg μ)]
  simp only [InnerProductSpace.rankOne_apply]

def coherentOrbital {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) : Space → ℂ :=
  ((coherentWeight hg hcg μ i)⁻¹ * ((2*Real.pi)^3)⁻¹ : ℝ) •
    packetSynthesis g μ (fun q => inner ℂ (coherentVector hg hcg q) (coherentBasis hg hcg μ i))

lemma coherentOrbital_smooth {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg.continuous hcg μ) : ContDiff ℝ ∞ (coherentOrbital hg.continuous hcg μ i) := by
  unfold coherentOrbital
  exact (packetSynthesis_smooth hg μ hK hμ
    ((coherentVector_continuous hg.continuous hcg).inner continuous_const)).const_smul
      ((coherentWeight hg.continuous hcg μ i)⁻¹ * ((2*Real.pi)^3)⁻¹ : ℝ)

lemma coherentOrbital_zero_outside {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg hcg μ) {x : Space} (hx : x ∉ coherentSpatialSupport g K) :
    coherentOrbital hg hcg μ i x = 0 := by
  simp only [coherentOrbital,Pi.smul_apply,packetSynthesis_zero_outside μ hμ _ hx,smul_zero]

lemma coherentOrbital_compact {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg hcg μ) : HasCompactSupport (coherentOrbital hg hcg μ i) :=
  (packetSynthesis_compact hcg μ hK hμ _).smul_left

lemma coherentOrbital_memLp {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg.continuous hcg μ) : MemLp (coherentOrbital hg.continuous hcg μ i) 2 :=
  (packetSynthesis_memLp hg hcg μ hK hμ
    ((coherentVector_continuous hg.continuous hcg).inner continuous_const)).const_smul _

lemma coherentOrbital_toLp {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg.continuous hcg μ) (hi : coherentWeight hg.continuous hcg μ i ≠ 0) :
    (coherentOrbital_memLp hg hcg μ hK hμ i).toLp (coherentOrbital hg.continuous hcg μ i) =
      coherentBasis hg.continuous hcg μ i := by
  have hw : Continuous (fun q => inner ℂ (coherentVector hg.continuous hcg q)
      (coherentBasis hg.continuous hcg μ i)) :=
    (coherentVector_continuous hg.continuous hcg).inner continuous_const
  have hm := packetSynthesis_memLp hg hcg μ hK hμ hw
  change (hm.const_smul ((coherentWeight hg.continuous hcg μ i)⁻¹ *
    ((2*Real.pi)^3)⁻¹ : ℝ)).toLp _ = _
  rw [MemLp.toLp_const_smul _ hm,packetSynthesis_toLp hg hcg μ hK hμ hw,
    mul_smul,← coherentOperator_synthesis,coherentBasis_real_eigen,smul_smul,
    inv_mul_cancel₀ hi,one_smul]

lemma coherentOrbital_ae {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg.continuous hcg μ) (hi : coherentWeight hg.continuous hcg μ i ≠ 0) :
    coherentBasis hg.continuous hcg μ i =ᵐ[volume] coherentOrbital hg.continuous hcg μ i := by
  rw [← coherentOrbital_toLp hg hcg μ hK hμ i hi]
  exact MemLp.coeFn_toLp _

lemma coherentOrbital_inner {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i j : CoherentIndex hg.continuous hcg μ)
    (hi : coherentWeight hg.continuous hcg μ i ≠ 0)
    (hj : coherentWeight hg.continuous hcg μ j ≠ 0) :
    (∫ x : Space, conj (coherentOrbital hg.continuous hcg μ i x) *
      coherentOrbital hg.continuous hcg μ j x) =
      inner ℂ (coherentBasis hg.continuous hcg μ i) (coherentBasis hg.continuous hcg μ j) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coherentOrbital_ae hg hcg μ hK hμ i hi,
    coherentOrbital_ae hg hcg μ hK hμ j hj] with x hi hj
  rw [hi,hj]
  simp only [RCLike.inner_apply,mul_comm]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_CoherentPhaseBasis
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma coherentVector_norm_eq {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (q r : Space × Space) :
    ‖coherentVector hg hcg q‖ = ‖coherentVector hg hcg r‖ := by
  have hq := coherentVector_norm_sq hg hcg q
  have hr := coherentVector_norm_sq hg hcg r
  nlinarith [norm_nonneg (coherentVector hg hcg q),norm_nonneg (coherentVector hg hcg r)]

lemma coherentOperator_mixed {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (u v : OrbitalHilbert) : inner ℂ u (coherentOperator hg hcg μ v) =
      coherentFactor • ∫ q, conj (inner ℂ (coherentVector hg hcg q) u) *
        inner ℂ (coherentVector hg hcg q) v ∂μ := by
  have hi : Integrable (fun q => inner ℂ (coherentVector hg hcg q) v •
      coherentVector hg hcg q) μ := by
    have h := (ContinuousLinearMap.apply ℂ OrbitalHilbert v).integrable_comp
      (coherentRankOne_integrable hg hcg μ)
    change Integrable (fun q => InnerProductSpace.rankOne ℂ (coherentVector hg hcg q)
      (coherentVector hg hcg q) v) μ at h
    simpa only [InnerProductSpace.rankOne_apply] using h
  rw [coherentOperator_synthesis,inner_smul_right_eq_smul,← integral_inner (𝕜 := ℂ) hi u]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with q
  rw [inner_smul_right,inner_conj_symm]
  ring

def coherentCoefficient {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (i : CoherentIndex hg hcg μ) (q : Space × Space) : ℂ :=
  inner ℂ (coherentVector hg hcg q) (coherentBasis hg hcg μ i)

lemma coherentCoefficient_memLp {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) :
    MemLp (coherentCoefficient hg hcg μ i) 2 μ := by
  apply MemLp.of_bound (((coherentVector_continuous hg hcg).inner
    continuous_const).aestronglyMeasurable) ‖coherentVector hg hcg (0,0)‖
  filter_upwards [] with q
  calc
    _ ≤ ‖coherentVector hg hcg q‖ * ‖coherentBasis hg hcg μ i‖ := norm_inner_le_norm _ _
    _ = _ := by rw [(coherentBasis hg hcg μ).orthonormal.norm_eq_one,mul_one,coherentVector_norm_eq hg hcg q (0,0)]

def coherentPhaseRaw {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentIndex hg hcg μ) : Lp ℂ 2 μ :=
  (coherentCoefficient_memLp hg hcg μ i).toLp _

lemma coherentPhaseRaw_inner {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (i j : CoherentIndex hg hcg μ) :
    coherentFactor • inner ℂ (coherentPhaseRaw hg hcg μ i) (coherentPhaseRaw hg hcg μ j) =
      coherentWeight hg hcg μ j • inner ℂ (coherentBasis hg hcg μ i) (coherentBasis hg hcg μ j) := by
  have he : inner ℂ (coherentPhaseRaw hg hcg μ i) (coherentPhaseRaw hg hcg μ j) =
      ∫ q, conj (coherentCoefficient hg hcg μ i q) * coherentCoefficient hg hcg μ j q ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(coherentCoefficient_memLp hg hcg μ i).coeFn_toLp,
      (coherentCoefficient_memLp hg hcg μ j).coeFn_toLp] with q hi hj
    simp only [coherentPhaseRaw] at ⊢
    rw [hi,hj]
    simp only [RCLike.inner_apply,mul_comm]
  rw [he]
  change coherentFactor • (∫ q, conj (inner ℂ (coherentVector hg hcg q) _) *
    inner ℂ (coherentVector hg hcg q) _ ∂μ) = _
  rw [← coherentOperator_mixed,coherentBasis_real_eigen,inner_smul_right_eq_smul]

def coherentPhaseVector {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (i : CoherentPositiveIndex hg hcg μ) : Lp ℂ 2 μ :=
  Real.sqrt (coherentFactor / coherentWeight hg hcg μ i.1) • coherentPhaseRaw hg hcg μ i.1

lemma coherentPhaseVector_orthonormal {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    Orthonormal ℂ (coherentPhaseVector hg hcg μ) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  have hraw : inner ℂ (coherentPhaseRaw hg hcg μ i.1) (coherentPhaseRaw hg hcg μ j.1) =
      (coherentWeight hg hcg μ j.1 / coherentFactor) •
        inner ℂ (coherentBasis hg hcg μ i.1) (coherentBasis hg hcg μ j.1) := by
    have h := congrArg (fun z : ℂ => coherentFactor⁻¹ • z) (coherentPhaseRaw_inner hg hcg μ i.1 j.1)
    simpa only [smul_smul,inv_mul_cancel₀ coherentFactor_pos.ne',one_smul,div_eq_mul_inv,mul_comm] using h
  rw [coherentPhaseVector,coherentPhaseVector,inner_smul_left_eq_smul,inner_smul_right_eq_smul,hraw]
  by_cases hij : i=j
  · subst j
    rw [(orthonormal_iff_ite.mp (coherentBasis hg hcg μ).orthonormal),ite_eq_left rfl,ite_eq_left rfl]
    rw [smul_smul,smul_smul]
    have he : Real.sqrt (coherentFactor / coherentWeight hg hcg μ i.1) *
        Real.sqrt (coherentFactor / coherentWeight hg hcg μ i.1) *
          (coherentWeight hg hcg μ i.1 / coherentFactor) = 1 := by
      rw [← pow_two,Real.sq_sqrt (div_nonneg coherentFactor_pos.le i.2.le)]
      field_simp [coherentFactor_pos.ne',i.2.ne']
    rw [he,one_smul]
  · have hval : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    rw [(orthonormal_iff_ite.mp (coherentBasis hg hcg μ).orthonormal),ite_eq_right hval,ite_eq_right hij]
    simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CosetWedge
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

def cosetWedge {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (T : FormVector n) : FormVector n :=
  sumForm (cosetWedgeTerm H T)

lemma cosetWedgeTerm_value {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (T : FormVector n)
    (q : Equiv.Perm (Fin n) ⧸ H) (s : Spins n) (x : Configuration n) :
    (cosetWedgeTerm H T q).value s x = (((Equiv.Perm.sign q.out : ℤ) : ℂ)) *
      T.value (s ∘ q.out) (x ∘ q.out) := by
  simp only [cosetWedgeTerm, scaleForm, reindexForm, Equiv.symm_symm, Complex.ofReal_intCast]

lemma formMass_cosetWedgeTerm {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (T : FormVector n) (q : Equiv.Perm (Fin n) ⧸ H) :
    formMass (cosetWedgeTerm H T q) = formMass T := by
  rw [cosetWedgeTerm, formMass_scale, formMass_reindex, real_sign_sq, one_mul]

lemma formEnergy_cosetWedgeTerm {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (T : FormVector n) (q : Equiv.Perm (Fin n) ⧸ H) (Z : ℝ) :
    formEnergy Z (cosetWedgeTerm H T q) = formEnergy Z T := by
  rw [cosetWedgeTerm, formEnergy_scale, formEnergy_reindex, real_sign_sq, one_mul]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_BlockWedge
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma cosetWedgeTerm_zero {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    {T : FormVector n} (q : Equiv.Perm (Fin n) ⧸ H) {x : Configuration n}
    (hx : FormZeroAt T (x ∘ q.out)) : FormZeroAt (cosetWedgeTerm H T q) x := by
  intro s
  constructor
  · rw [cosetWedgeTerm_value,(hx _).1,mul_zero]
  · intro j a
    change _ * T.gradient (s ∘ q.out.symm.symm) (q.out.symm j) a
      (x ∘ q.out.symm.symm) = 0
    rw [Equiv.symm_symm,(hx _).2,mul_zero]

lemma block_coset_terms_disjoint {N M : ℕ} {T : FormVector (N+M)} (A : Set Space)
    (hc : ∀ x i, x (finSumFinEquiv (Sum.inl i)) ∉ A → FormZeroAt T x)
    (he : ∀ x i, x (finSumFinEquiv (Sum.inr i)) ∈ A → FormZeroAt T x) :
    FormsDisjoint (cosetWedgeTerm (blockSubgroup N M) T) := by
  classical
  have hh (q r : Equiv.Perm (Fin (N+M)) ⧸ blockSubgroup N M) (hqr : q ≠ r)
      (x : Configuration (N+M)) :
      FormZeroAt (cosetWedgeTerm (blockSubgroup N M) T q) x ∨
      FormZeroAt (cosetWedgeTerm (blockSubgroup N M) T r) x := by
    by_cases hq : FormZeroAt T (x ∘ q.out)
    · exact Or.inl (cosetWedgeTerm_zero _ q hq)
    by_cases hr : FormZeroAt T (x ∘ r.out)
    · exact Or.inr (cosetWedgeTerm_zero _ r hr)
    exfalso
    apply hqr
    have hk : q.out⁻¹ * r.out ∈ blockSubgroup N M := by
      apply blockSubgroup_mem_of_maps_left
      intro i
      obtain ⟨j,hj⟩ := finSumFinEquiv.surjective ((q.out⁻¹ * r.out) (finSumFinEquiv (Sum.inl i)))
      cases j with
      | inl j => exact ⟨j,hj.symm⟩
      | inr j =>
        have hrA : x (r.out (finSumFinEquiv (Sum.inl i))) ∈ A := by
          by_contra ha
          exact hr (hc _ i ha)
        have hqA : x (q.out (finSumFinEquiv (Sum.inr j))) ∉ A := by
          intro ha
          exact hq (he _ j ha)
        have hij : q.out (finSumFinEquiv (Sum.inr j)) = r.out (finSumFinEquiv (Sum.inl i)) := by
          rw [hj]
          simp only [Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply]
        exact False.elim (hqA (hij ▸ hrA))
    have heq : (q.out : Equiv.Perm (Fin (N+M)) ⧸ blockSubgroup N M) = r.out :=
      QuotientGroup.eq.mpr hk
    simpa only [QuotientGroup.out_eq'] using heq
  constructor
  · intro q r hqr s x
    rcases hh q r hqr x with h | h
    · exact Or.inl (h s).1
    · exact Or.inr (h s).1
  · intro q r hqr s i a x
    rcases hh q r hqr x with h | h
    · exact Or.inl ((h s).2 i a)
    · exact Or.inr ((h s).2 i a)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterSymmetry
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma slaterForm_sobolevFermion {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x))) :
    SobolevFermion (slaterForm φ) := by
  have hd (s : Spins n) (j : Fin n) (a : Fin 3) :
      (slaterForm φ).gradient s j a = fun x =>
        fderiv ℝ (fun y : Configuration n => slater φ (slaterParticles s y)) x (direction j a) :=
    funext (fun x => (slater_spatial_derivative hφ s x j a).symm)
  refine ⟨fun s => (slater_spatial_smooth hφ s).continuous.memLp_of_hasCompactSupport
    (slater_spatial_compact hc s), ?_, ?_, ?_⟩
  · intro s j a
    rw [hd]
    exact (smooth_derivative_continuous (slater_spatial_smooth hφ s) _).memLp_of_hasCompactSupport
      (compact_derivative (slater_spatial_compact hc s) _)
  · intro s j a f hf hcf
    rw [hd]
    exact smooth_weak_gradient (slater_spatial_smooth hφ s) (slater_spatial_compact hc s) hf hcf _
  · intro π s
    exact Eventually.of_forall fun x => slater_perm φ π (slaterParticles s x)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterMeasure
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open scoped BigOperators ComplexConjugate

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

theorem slaterForm_admissible {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z) * φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    FormAdmissible (slaterForm φ) :=
  (slaterForm_sobolevFermion hφ hc).admissible
    (slaterForm_mass (fun i => memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)) ho)

theorem slaterForm_kinetic {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z) * φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    formKinetic (slaterForm φ) = (1/2:ℝ) * ∑ a : Fin 3, ∑ i : Fin n,
      ∫ z, ‖spatialOrbitalDerivative φ a i z‖^2 ∂slaterParticleMeasure := by
  have hl (i : Fin n) : MemLp (φ i) 2 slaterParticleMeasure :=
    memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)
  have hd := memLp_spatialOrbitalDerivative hφ hc
  have he (a : Fin 3) (j : Fin n) := spinSpace_integral
    (fun z => ‖slaterCoordinate φ (spatialOrbitalDerivative φ a) j z‖^2)
    (memLp_slaterCoordinate hl (hd a) j).norm.integrable_sq
  unfold formKinetic
  congr 1
  simp only [slaterForm]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Spins n))) (t := (Finset.univ : Finset (Fin 3)))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ j : Fin n, ∫ z, ‖slaterCoordinate φ (spatialOrbitalDerivative φ a) j z‖^2
        ∂Measure.pi (fun _ : Fin n => slaterParticleMeasure) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (he a j).symm
    _ = _ := slaterCoordinate_sum_norm_sq_integral hl (hd a) ho

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpinSpaceIntegrable
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open scoped BigOperators

lemma formRepulsion_ordered {n : ℕ} (ψ : FormVector n) :
    formRepulsion ψ = (1/2:ℝ) * ∑ s : Spins n, ∑ i : Fin n, ∑ j : Fin n,
      if i ≠ j then ∫ x, ‖ψ.value s x‖^2 / ‖x i-x j‖ else 0 := by
  have he (s : Spins n) := sum_ordered_pairs
    (fun i j : Fin n => ∫ x : Configuration n, ‖ψ.value s x‖^2 / ‖x i-x j‖)
    (fun i j => by simp only [norm_sub_rev])
  simp_rw [he]
  rw [← Finset.mul_sum]
  unfold formRepulsion
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterRepulsion
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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
open scoped BigOperators ComplexConjugate ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

lemma smooth_pair_integrable {n : ℕ} {f : Configuration n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (i j : Fin n) (hij : i ≠ j) :
    Integrable (fun x => ‖f x‖^2 / ‖x i-x j‖) :=
  pair_integrable i j hij (hf.continuous.memLp_of_hasCompactSupport hc)
    (fun _a => (smooth_derivative_continuous hf _).memLp_of_hasCompactSupport (compact_derivative hc _))
    (fun a _g hg hgc => smooth_weak_gradient hf hc hg hgc (direction i a))

lemma orbital_coulomb_product_integrable {f g : SlaterParticle → ℂ}
    (hf : ∀ s, ContDiff ℝ ∞ (fun x : Space => f (s,x)))
    (hg : ∀ s, ContDiff ℝ ∞ (fun x : Space => g (s,x)))
    (hfc : ∀ s, HasCompactSupport (fun x : Space => f (s,x)))
    (hgc : ∀ s, HasCompactSupport (fun x : Space => g (s,x))) :
    Integrable (fun z : SlaterParticle × SlaterParticle =>
      (‖f z.1‖^2 * ‖g z.2‖^2) / ‖z.1.2-z.2.2‖)
      (slaterParticleMeasure.prod slaterParticleMeasure) := by
  apply ((measurePreserving_finTwoArrow slaterParticleMeasure).integrable_comp_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding).mp
  change Integrable (fun z : Fin 2 → SlaterParticle =>
    (‖f (z 0)‖^2 * ‖g (z 1)‖^2) / ‖(z 0).2-(z 1).2‖)
      (Measure.pi fun _ : Fin 2 => slaterParticleMeasure)
  apply spinSpace_integrable
  · have hfm := (continuous_prod_of_discrete_left.mpr (fun s => (hf s).continuous)).measurable
    have hgm := (continuous_prod_of_discrete_left.mpr (fun s => (hg s).continuous)).measurable
    exact (((hfm.comp (measurable_pi_apply 0)).norm.pow_const 2).mul
      ((hgm.comp (measurable_pi_apply 1)).norm.pow_const 2)).div
      (((measurable_pi_apply 0).snd.sub (measurable_pi_apply 1).snd).norm)
  · intro s
    let φ : Fin 2 → SlaterParticle → ℂ := ![f,g]
    have hφ (i : Fin 2) (t : Fin 2) : ContDiff ℝ ∞ (fun x : Space => φ i (t,x)) := by
      fin_cases i
      · exact hf t
      · exact hg t
    have hc (i : Fin 2) (t : Fin 2) : HasCompactSupport (fun x : Space => φ i (t,x)) := by
      fin_cases i
      · exact hfc t
      · exact hgc t
    have hi := smooth_pair_integrable (slater_spatial_tensor_smooth hφ s 1)
      (slater_spatial_tensor_compact hc s 1) (0 : Fin 2) 1 (by decide)
    simpa only [slaterTensor,Fin.prod_univ_two,Equiv.Perm.one_apply,φ,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,norm_mul,mul_pow,
      slaterParticles] using hi

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterOccupation
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

theorem occupationSlater_admissible {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (m : Fin n → Bool) : FormAdmissible (slaterForm (occupationOrbitals φ m)) :=
  slaterForm_admissible (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
    (occupationOrbitals_orthonormal ho m)

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_OccupationPairDensity
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

section Work_WeightedDirectIntegrable_scope

open MeasureTheory
open scoped BigOperators ContDiff

lemma weightedSlater_direct_coulomb_integrable {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x))) (p : Fin n → ℝ) :
    Integrable (fun z : SlaterParticle × SlaterParticle =>
      (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2) / ‖z.1.2-z.2.2‖)
      (slaterParticleMeasure.prod slaterParticleMeasure) := by
  have he (z : SlaterParticle × SlaterParticle) :
      (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2) / ‖z.1.2-z.2.2‖ =
      ∑ j : Fin n, ∑ i : Fin n, (p i*p j)*((‖φ i z.1‖^2 * ‖φ j z.2‖^2) / ‖z.1.2-z.2.2‖) := by
    simp only [weightedSlaterDensity,Finset.sum_mul,Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ =>
    (orbital_coulomb_product_integrable (hφ i) (hφ j) (hc i) (hc j)).const_mul (p i*p j)))

end Work_WeightedDirectIntegrable_scope

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_OccupationTraces
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma occupationSlater_kinetic {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (p : Fin n → ℝ) :
    (∑ m : Fin n → Bool, occupationWeight p m * formKinetic (slaterForm (occupationOrbitals φ m))) =
      (1/2:ℝ) * ∑ a : Fin 3, ∑ i : Fin n,
        p i * ∫ z, ‖spatialOrbitalDerivative φ a i z‖^2 ∂slaterParticleMeasure := by
  have he (m : Fin n → Bool) : formKinetic (slaterForm (occupationOrbitals φ m)) =
      (1/2:ℝ)*∑ a : Fin 3, ∑ i : Fin n, if m i then
        (∫ z, ‖spatialOrbitalDerivative φ a i z‖^2 ∂slaterParticleMeasure) else 0 := by
    rw [slaterForm_kinetic (occupationOrbitals_smooth hφ m) (occupationOrbitals_compact hc m)
      (occupationOrbitals_orthonormal ho m)]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    exact occupationIndex_sum m (fun i => ∫ z, ‖spatialOrbitalDerivative φ a i z‖^2 ∂slaterParticleMeasure)
  calc
    _ = (1/2:ℝ)*∑ m : Fin n → Bool, occupationWeight p m *
        ∑ a : Fin 3, ∑ i : Fin n, if m i then
          (∫ z, ‖spatialOrbitalDerivative φ a i z‖^2 ∂slaterParticleMeasure) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [he]
      ring
    _ = _ := by rw [occupation_expect_sum]; simp_rw [occupation_sum]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CompactPotential
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma core_bounded_potential_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {V : Space → ℝ} (hV : Continuous V) {C : ℝ} (hC : ∀ x, |V x| ≤ C)
    (s : Spins N) (j : Fin N) :
    Integrable (fun x : Configuration N => ‖ψ.value s x‖^2 * V (x j)) := by
  apply ((hψ.1 s).norm.integrable_sq.mul_const C).mono'
    (((hψ.1 s).aestronglyMeasurable.norm.pow 2).mul
      (hV.comp (continuous_apply j)).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖‖ψ.value s x‖^2 * V (x j)‖ ≤ _
  rw [norm_mul,Real.norm_of_nonneg (sq_nonneg _),Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC (x j)) (sq_nonneg _)

lemma core_compact_potential_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {d : Space → ℝ} (hd : Continuous d) (hcd : HasCompactSupport d) (s : Spins N) (j : Fin N) :
    Integrable (fun x : Configuration N => ‖ψ.value s x‖^2 * CoulombAnalysis.tfPotential d (x j)) := by
  obtain ⟨C,hC⟩ := compact_potential_bounded hd hcd
  exact core_bounded_potential_integrable hψ
    (CoulombAnalysis.tfPotential_continuous (hd.integrable_of_hasCompactSupport hcd)
      (hd.memLp_of_hasCompactSupport hcd)) hC s j

lemma spinLift_core_interaction {N : ℕ} (ψ : FormVector N) (u : Space → ℂ) (σ : Fin 2) :
    orbitalCoreInteraction ψ (spinLift u σ) = coreDensityInteraction ψ (fun y => ‖u y‖^2) := by
  simp only [orbitalCoreInteraction,coreDensityInteraction,spinLift_pole]

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SmearingPotential
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma smearing_pole_integrable {η ρ : Space → ℝ} (hη : Continuous η)
    (hcη : HasCompactSupport η) (hmρ : Measurable ρ) (hρ : Integrable ρ) (a : Space) :
    Integrable (fun r : Space × Space => ρ r.1*η (r.2-r.1)/‖a-r.2‖) := by
  have h1 : Integrable η := hη.integrable_of_hasCompactSupport hcη
  have hp : MemLp η (5/3 : ENNReal) := hη.memLp_of_hasCompactSupport hcη
  have hm : Measurable (fun r : Space × Space => ρ r.1*η (r.2-r.1)/‖a-r.2‖) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  refine ⟨Eventually.of_forall (fun z => ?_),?_⟩
  · simpa only [mul_div_assoc] using (translated_pole_integrable h1 hp a z).const_mul (ρ z)
  · obtain ⟨C,hC⟩ := compact_potential_bounded hη.norm hcη.norm
    have hi : Integrable (fun z => ‖ρ z‖*CoulombAnalysis.tfPotential (fun x => ‖η x‖) (a-z)) := by
      apply (hρ.norm.mul_const C).mono'
        ((hmρ.norm.mul ((CoulombAnalysis.tfPotential_continuous h1.norm hp.norm).measurable.comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable)
      filter_upwards [] with z
      change ‖‖ρ z‖*CoulombAnalysis.tfPotential (fun x => ‖η x‖) (a-z)‖ ≤ ‖ρ z‖*C
      rw [norm_mul,norm_norm,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC (a-z)) (abs_nonneg _)
    apply hi.congr
    filter_upwards [] with z
    simp only [norm_div,norm_mul,norm_norm,mul_div_assoc,integral_const_mul]
    rw [integral_translated_pole (fun x => ‖η x‖) a z]

lemma spatialSmearing_potential {η ρ : Space → ℝ} (hη : Continuous η)
    (hcη : HasCompactSupport η) (hmρ : Measurable ρ) (hρ : Integrable ρ) (a : Space) :
    CoulombAnalysis.tfPotential (spatialSmearing η ρ) a =
      ∫ z : Space, ρ z*CoulombAnalysis.tfPotential η (a-z) := by
  have hi := smearing_pole_integrable hη hcη hmρ hρ a
  change (∫ x : Space, (∫ z : Space, ρ z*η (x-z))/‖a-x‖) = _
  calc
    _ = ∫ x : Space, ∫ z : Space, ρ z*η (x-z)/‖a-x‖ := by simp only [integral_div]
    _ = ∫ z : Space, ∫ x : Space, ρ z*η (x-z)/‖a-x‖ := integral_integral_swap hi.swap
    _ = _ := by simp only [mul_div_assoc,integral_const_mul,integral_translated_pole]

lemma smearing_potential_integrable {η ρ : Space → ℝ} (hη : Continuous η)
    (hcη : HasCompactSupport η) (hmρ : Measurable ρ) (hρ : Integrable ρ) (a : Space) :
    Integrable (fun z : Space => ρ z*CoulombAnalysis.tfPotential η (a-z)) := by
  have hi := (smearing_pole_integrable hη hcη hmρ hρ a).integral_prod_left
  simpa only [mul_div_assoc,integral_const_mul,integral_translated_pole] using hi

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_RadialPacket
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma spatialSmearing_potential_le {η ρ : Space → ℝ} (hη : Continuous η)
    (hcη : HasCompactSupport η) (hnη : ∀ x, 0 ≤ η x)
    (hr : CoulombAnalysis.IsRadial η) (hηn : ∫ x : Space, η x = 1)
    (hmρ : Measurable ρ) (hρ : Integrable ρ) (hpρ : MemLp ρ (5/3 : ENNReal))
    (hnρ : ∀ x, 0 ≤ ρ x) (a : Space) :
    CoulombAnalysis.tfPotential (spatialSmearing η ρ) a ≤ CoulombAnalysis.tfPotential ρ a := by
  obtain ⟨R,hR,hS⟩ := hcη.isCompact.isBounded.exists_pos_norm_le
  have hs (y : Space) (hy : η y ≠ 0) : ‖y‖ ≤ R := hS y (subset_tsupport η hy)
  rw [spatialSmearing_potential hη hcη hmρ hρ]
  apply integral_mono_ae (smearing_potential_integrable hη hcη hmρ hρ a)
    (CoulombAnalysis.tfPotential_integrable hρ hpρ a)
  filter_upwards [ae_ne_point a] with z hz
  have hh := radial_potential_le_point (hη.integrable_of_hasCompactSupport hcη)
    (hη.memLp_of_hasCompactSupport hcη) hnη hr hR.le hs
    (x := a-z) (sub_ne_zero.mpr (Ne.symm hz))
  rw [hηn] at hh
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hh (hnρ z)

lemma spatialSmearing_potential_eq {η ρ : Space → ℝ} (hη : Continuous η)
    (hcη : HasCompactSupport η) (hr : CoulombAnalysis.IsRadial η)
    (hηn : ∫ x : Space, η x = 1) (hmρ : Measurable ρ) (hρ : Integrable ρ)
    {R : ℝ} (hR : 0 < R) (hs : ∀ y, η y ≠ 0 → ‖y‖ ≤ R)
    (a : Space) (hsep : ∀ z, ρ z ≠ 0 → R ≤ ‖a-z‖) :
    CoulombAnalysis.tfPotential (spatialSmearing η ρ) a = CoulombAnalysis.tfPotential ρ a := by
  rw [spatialSmearing_potential hη hcη hmρ hρ]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : ρ z = 0
  · simp [hz]
  · rw [CoulombAnalysis.tfPotential_newton_exterior_closed
      (hη.integrable_of_hasCompactSupport hcη) (hη.memLp_of_hasCompactSupport hcη)
      hr hR hs (hsep z hz),hηn,mul_one_div]

end Work_RadialPacket_scope

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

lemma real_coherentPacket_derivative_sq {g : Space → ℝ} (hg : Differentiable ℝ g)
    (z p x v : Space) :
    ‖fderiv ℝ (coherentPacket (fun x => (g x : ℂ)) z p) x v‖^2 =
      (fderiv ℝ g (x-z) v)^2 + (g (x-z))^2 * (inner ℝ p v)^2 := by
  have hd : Differentiable ℝ (fun x => (g x : ℂ)) := Complex.ofRealCLM.differentiable.comp hg
  rw [coherentPacket_fderiv hd,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
  have he : fderiv ℝ (fun x => (g x : ℂ)) (x-z) v = (fderiv ℝ g (x-z) v : ℂ) := by
    exact congrArg (fun A : Space →L[ℝ] ℂ => A v)
      (Complex.ofRealCLM.hasFDerivAt.comp (x-z) (hg (x-z)).hasFDerivAt).fderiv
  rw [he,Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FermiMeasure
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma fermiMeasure_le (ρ : Space → ℝ) : fermiMeasure ρ ≤ volume := Measure.restrict_le_self

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CoherentDensity
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma coherentDensity_continuous {g : Space → ℂ} (hg : Continuous g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    Continuous (coherentDensity g μ) := by
  have hc : Continuous (fun r : Space × (Space × Space) =>
      ‖coherentPacket g r.2.1 r.2.2 r.1‖^2) := by
    unfold coherentPacket
    fun_prop
  have h := continuous_parametric_integral_of_continuous (μ := μ)
    (f := fun (x : Space) (q : Space × Space) => ‖coherentPacket g q.1 q.2 x‖^2) hc hK
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at h
  exact continuous_const.mul h

lemma coherentDensity_zero_outside {g : Space → ℂ}
    (μ : Measure (Space × Space)) {K : Set (Space × Space)} (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {x : Space} (hx : x ∉ coherentSpatialSupport g K) : coherentDensity g μ x = 0 := by
  have he : (∫ q, ‖coherentPacket g q.1 q.2 x‖^2 ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hμ] with q hq
    simp only [coherentPacket_zero_outside hq hx,norm_zero,zero_pow (by decide : 2 ≠ 0),Pi.zero_apply]
  simp only [coherentDensity,he,mul_zero]

lemma coherentDensity_compact {g : Space → ℂ} (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) {K : Set (Space × Space)} (hK : IsCompact K)
    (hμ : ∀ᵐ q ∂μ, q ∈ K) : HasCompactSupport (coherentDensity g μ) := by
  apply HasCompactSupport.of_support_subset_isCompact (coherentSpatialSupport_compact hcg hK)
  intro x hx
  by_contra hn
  exact hx (coherentDensity_zero_outside μ hμ hn)

lemma coherentDensity_integrable {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    Integrable (coherentDensity g μ) :=
  (coherentDensity_continuous hg μ hK hμ).integrable_of_hasCompactSupport
    (coherentDensity_compact hcg μ hK hμ)

lemma coherentPacket_sq_integrable {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    Integrable (fun r : (Space × Space) × Space =>
      ‖coherentPacket g r.1.1 r.1.2 r.2‖^2) (μ.prod volume) := by
  have hc : Continuous (fun r : (Space × Space) × Space =>
      ‖coherentPacket g r.1.1 r.1.2 r.2‖^2) := by
    unfold coherentPacket
    fun_prop
  have hi := hc.continuousOn.integrableOn_compact
    (hK.prod (coherentSpatialSupport_compact hcg hK)) (μ := μ.prod volume)
  apply hi.integrable_of_ae_notMem_eq_zero
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμ] with r hr
  intro hn
  have hx : r.2 ∉ coherentSpatialSupport g K := fun hx => hn ⟨hr,hx⟩
  simp only [coherentPacket_zero_outside hr hx,norm_zero,zero_pow (by decide : 2 ≠ 0)]

lemma coherentPacket_mass {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (q : Space × Space) : (∫ x : Space, ‖coherentPacket g q.1 q.2 x‖^2) = ∫ x : Space, ‖g x‖^2 := by
  rw [← coherentVector_norm_sq hg hcg q,lp_norm_sq]
  apply integral_congr_ae
  filter_upwards [coherentVector_coe hg hcg q] with x hx
  rw [hx]

lemma coherentDensity_mass {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    (∫ x : Space, coherentDensity g μ x) =
      coherentFactor * μ.real Set.univ * ∫ x : Space, ‖g x‖^2 := by
  have hi : Integrable (fun r : Space × (Space × Space) =>
      ‖coherentPacket g r.2.1 r.2.2 r.1‖^2) (volume.prod μ) :=
    (coherentPacket_sq_integrable hg hcg μ hK hμ).swap
  simp only [coherentDensity,integral_const_mul]
  rw [integral_integral_swap (f := fun (x : Space) (q : Space × Space) =>
    ‖coherentPacket g q.1 q.2 x‖^2) hi]
  simp only [coherentPacket_mass hg hcg,integral_const,smul_eq_mul,mul_assoc]

lemma coherentPositiveWeight_hasSum {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    HasSum (fun i : CoherentPositiveIndex hg hcg μ => coherentWeight hg hcg μ i.1)
      (coherentFactor * μ.real Set.univ * ∫ x : Space, ‖g x‖^2) := by
  apply (hasSum_subtype_iff_of_support_subset (f := coherentWeight hg hcg μ) ?_).2
    (coherentWeight_hasSum hg hcg μ)
  intro i hi
  exact lt_of_le_of_ne (coherentWeight_nonneg hg hcg μ i) (Ne.symm hi)

lemma coherentOrbital_mass {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentPositiveIndex hg.continuous hcg μ) :
    (∫ x : Space, ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2) = 1 := by
  have he : (∫ x : Space, ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2) =
      ‖coherentBasis hg.continuous hcg μ i.1‖^2 := by
    rw [lp_norm_sq]
    exact integral_congr_ae ((coherentOrbital_ae hg hcg μ hK hμ i.1 i.2.ne').symm.fun_comp
      (fun z : ℂ => ‖z‖^2))
  rw [he,(coherentBasis hg.continuous hcg μ).orthonormal.norm_eq_one,one_pow]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FermiDensity
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma smearedPacketDensity_nonneg {ρ : Space → ℝ} (hn : ∀ z, 0 ≤ ρ z) (g : Space → ℝ) (x : Space) :
    0 ≤ smearedPacketDensity g ρ x := integral_nonneg (fun z => mul_nonneg (hn z) (sq_nonneg _))

lemma smearedPacketDensity_continuous {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : Continuous g) : Continuous (smearedPacketDensity g ρ) := by
  let := fermiMeasure_finite hn hJ hs hb
  have he : smearedPacketDensity g ρ = fun x => 2*coherentDensity (fun x => (g x : ℂ)) (fermiMeasure ρ) x :=
    funext (fun x => (coherentDensity_fermi hm hn hJ hs hb hg x).symm)
  rw [he]
  exact continuous_const.mul (coherentDensity_continuous (Complex.continuous_ofReal.comp hg)
    (fermiMeasure ρ) (hJ.prod (isCompact_closedBall _ _)) (fermiMeasure_mem hm hn hs hb))

lemma smearedPacketDensity_compact {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : Continuous g) (hcg : HasCompactSupport g) :
    HasCompactSupport (smearedPacketDensity g ρ) := by
  let := fermiMeasure_finite hn hJ hs hb
  have he : smearedPacketDensity g ρ = fun x => 2*coherentDensity (fun x => (g x : ℂ)) (fermiMeasure ρ) x :=
    funext (fun x => (coherentDensity_fermi hm hn hJ hs hb hg x).symm)
  rw [he]
  have hcc : HasCompactSupport (fun x => (g x : ℂ)) := hcg.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hd : HasCompactSupport (coherentDensity (fun x => (g x : ℂ)) (fermiMeasure ρ)) :=
    coherentDensity_compact hcc (fermiMeasure ρ) (hJ.prod (isCompact_closedBall _ _))
      (fermiMeasure_mem hm hn hs hb)
  exact hd.comp_left (g := fun t : ℝ => 2*t) (mul_zero 2)

lemma smearedPacketDensity_mass {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : Continuous g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) : (∫ x : Space, smearedPacketDensity g ρ x) = ∫ z, ρ z := by
  let := fermiMeasure_finite hn hJ hs hb
  have he : smearedPacketDensity g ρ = fun x => 2*coherentDensity (fun x => (g x : ℂ)) (fermiMeasure ρ) x :=
    funext (fun x => (coherentDensity_fermi hm hn hJ hs hb hg x).symm)
  have hgc : Continuous (fun x => (g x : ℂ)) := Complex.continuous_ofReal.comp hg
  have hcc : HasCompactSupport (fun x => (g x : ℂ)) := hcg.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  rw [he,integral_const_mul,coherentDensity_mass hgc hcc (fermiMeasure ρ)
    (hJ.prod (isCompact_closedBall _ _)) (fermiMeasure_mem hm hn hs hb)]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,hgn,mul_one,← mul_assoc]
  exact fermiMeasure_mass hm hn hJ hs hb

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma coulomb_direct_le_of_potential_le {f g : Space → ℝ}
    (hff : Integrable (fun r : Space × Space => f r.1*f r.2/‖r.1-r.2‖))
    (hfg : Integrable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖))
    (hgg : Integrable (fun r : Space × Space => g r.1*g r.2/‖r.1-r.2‖))
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x)
    (hp : ∀ x, CoulombAnalysis.tfPotential f x ≤ CoulombAnalysis.tfPotential g x) :
    (∫ r : Space × Space, f r.1*f r.2/‖r.1-r.2‖) ≤
      ∫ r : Space × Space, g r.1*g r.2/‖r.1-r.2‖ := by
  have hgf : Integrable (fun r : Space × Space => g r.1*f r.2/‖r.1-r.2‖) := by
    rw [Measure.volume_eq_prod] at hfg ⊢
    apply hfg.swap.congr
    filter_upwards [] with r
    change f r.2*g r.1/‖r.2-r.1‖ = g r.1*f r.2/‖r.1-r.2‖
    rw [norm_sub_rev r.1 r.2]
    ring
  rw [coulomb_double_eq_potential hff,coulomb_double_eq_potential hgg]
  calc
    _ ≤ ∫ x : Space, f x*CoulombAnalysis.tfPotential g x :=
      integral_mono (coulomb_potential_pair_integrable hff) (coulomb_potential_pair_integrable hfg)
        (fun x => mul_le_mul_of_nonneg_left (hp x) (hfn x))
    _ = ∫ x : Space, g x*CoulombAnalysis.tfPotential f x := coulomb_potential_pair_comm hfg
    _ ≤ _ := integral_mono (coulomb_potential_pair_integrable hgf) (coulomb_potential_pair_integrable hgg)
      (fun x => mul_le_mul_of_nonneg_left (hp x) (hgn x))

lemma smearedPacketDensity_direct_le {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : Continuous g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) (hr : CoulombAnalysis.IsRadial (fun x => (g x)^2)) :
    (∫ r : Space × Space, smearedPacketDensity g ρ r.1*smearedPacketDensity g ρ r.2/‖r.1-r.2‖) ≤
      ∫ r : Space × Space, ρ r.1*ρ r.2/‖r.1-r.2‖ := by
  have hab (z : Space) : |ρ z| ≤ B := by rw [abs_of_nonneg (hn z)]; exact hb z
  have h1 : Integrable ρ := bounded_compact_integrable hm hJ hs hab
  have hp : MemLp ρ (5/3 : ENNReal) := bounded_compact_memLp hm hJ hs hab _
  have hd := smearedPacketDensity_continuous hm hn hJ hs hb hg
  have hc := smearedPacketDensity_compact hm hn hJ hs hb hg hcg
  apply coulomb_direct_le_of_potential_le
    (continuous_compact_coulomb_integrable hd hd hc hc)
    (compact_support_coulomb_integrable hd.measurable hm (hd.integrable_of_hasCompactSupport hc) h1 hp hJ hs)
    (compact_support_coulomb_integrable hm hm h1 h1 hp hJ hs)
    (smearedPacketDensity_nonneg hn g) hn
  intro x
  exact spatialSmearing_potential_le (hg.pow 2) (square_compact hcg) (fun y => sq_nonneg (g y))
    hr hgn hm h1 hp hn x

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_QuantumRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma graphRawDensity_nonneg {N : ℕ} (F : fermionGraph N) (x : Configuration N) :
    0 ≤ graphRawDensity F x := sum_nonneg (fun _ _ => sq_nonneg _)

lemma graphRawDensity_integrable {N : ℕ} (F : fermionGraph N) :
    Integrable (graphRawDensity F) := by
  apply integrable_finsetSum
  intro s _
  exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)

lemma graphRawDensity_integral {N : ℕ} (F : fermionGraph N) :
    ∫ x, graphRawDensity F x = ‖fermionGraphValue N F‖^2 := by
  change (∫ x, ∑ s : Spins N, ‖graphComponent s none F x‖^2) = _
  rw [integral_finsetSum _ (fun s _ =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))]
  simp_rw [← lp_norm_sq]
  have hv : ‖fermionGraphValue N F‖^2 = ∑ s : Spins N, ‖(F.val s).val none‖^2 := by
    change ‖(fermionGraphValue N F).val‖^2 = _
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [fermionGraphValue_apply]
  rw [hv]
  simp only [graphComponent_apply]

lemma graphRawLaw_univ {N : ℕ} (F : fermionGraph N) :
    graphRawLaw F univ = ENNReal.ofReal (‖fermionGraphValue N F‖^2) := by
  change (volume.withDensity (fun x => ENNReal.ofReal (graphRawDensity F x))) univ = _
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (graphRawDensity_integrable F)
    (ae_of_all _ (graphRawDensity_nonneg F))).symm.trans
      (congrArg ENNReal.ofReal (graphRawDensity_integral F))

end CoulombAtom

end Work_QuantumRawLaw_scope

open MeasureTheory Filter Set
open scoped ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ArraySymmetry
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

def flatRawLaw {N : ℕ} (F : fermionGraph N) : Measure (Fin N × Fin 3 → ℝ) :=
  Measure.map (flattenConfiguration N) (graphRawLaw F)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CoreFieldPairing
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma core_density_product_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B)
    (s : Spins N) (i : Fin N) :
    Integrable (fun r : Configuration N × Space => ‖ψ.value s r.1‖^2 * ρ r.2 / ‖r.1 i-r.2‖) := by
  have h1 := bounded_compact_integrable hm hJ hs hb
  have hp := bounded_compact_memLp hm hJ hs hb (5/3 : ENNReal)
  have ha : AEStronglyMeasurable
      (fun r : Configuration N × Space => ‖ψ.value s r.1‖^2 * ρ r.2 / ‖r.1 i-r.2‖) volume := by
    have hnorm : Measurable (fun r : Configuration N × Space => ‖r.1 i-r.2‖⁻¹) := by fun_prop
    simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.pow_apply,Measure.volume_eq_prod] using
      (((hψ.1 s).aestronglyMeasurable.norm.pow 2).comp_fst.fun_mul hm.aestronglyMeasurable.comp_snd).fun_mul
        hnorm.aestronglyMeasurable
  apply (integrable_prod_iff ha).2
  refine ⟨Eventually.of_forall (fun x => ?_),?_⟩
  · simpa only [mul_div_assoc] using (CoulombAnalysis.tfPotential_integrable h1 hp (x i)).const_mul (‖ψ.value s x‖^2)
  · obtain ⟨C,hC⟩ := compact_support_potential_bounded h1.norm hp.norm hJ
      (fun x hx => hs (by intro hz; exact hx (by simp [hz])))
    have hi := core_bounded_potential_integrable hψ
      (CoulombAnalysis.tfPotential_continuous h1.norm hp.norm) hC s i
    apply hi.congr
    filter_upwards [] with x
    simp only [norm_div,norm_mul,Real.norm_of_nonneg (sq_nonneg _),norm_norm,
      CoulombAnalysis.tfPotential,← integral_const_mul]
    congr 1
    funext y
    ring

lemma core_density_coordinate_pairing {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B)
    (s : Spins N) (i : Fin N) :
    (∫ x : Configuration N, ‖ψ.value s x‖^2 * CoulombAnalysis.tfPotential ρ (x i)) =
      ∫ y : Space, ρ y*(∫ x : Configuration N, ‖ψ.value s x‖^2/‖x i-y‖) := by
  have hi := core_density_product_integrable hψ hm hJ hs hb s i
  have hh := integral_integral_swap (f := fun x y => ‖ψ.value s x‖^2 * ρ y / ‖x i-y‖) hi
  simp only [CoulombAnalysis.tfPotential,← integral_const_mul] at ⊢
  convert hh using 1 <;> (congr 1; funext x; congr 1; funext y; ring)

lemma core_density_coordinate_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B)
    (s : Spins N) (i : Fin N) :
    Integrable (fun y : Space => ρ y*(∫ x : Configuration N, ‖ψ.value s x‖^2/‖x i-y‖)) := by
  have hi := (core_density_product_integrable hψ hm hJ hs hb s i).integral_prod_right
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext y
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem coreDensityInteraction_eq_field {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B) :
    coreDensityInteraction ψ ρ = ∫ y : Space, ρ y*coreCoulombAt ψ y := by
  unfold coreDensityInteraction coreCoulombAt
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ =>
    core_density_coordinate_integrable hψ hm hJ hs hb s i))]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_finsetSum _ (fun i _ => core_density_coordinate_integrable hψ hm hJ hs hb s i)]
  exact Finset.sum_congr rfl (fun i _ => core_density_coordinate_pairing hψ hm hJ hs hb s i)

lemma coreDensityField_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B) :
    Integrable (fun y : Space => ρ y*coreCoulombAt ψ y) := by
  simp only [coreCoulombAt,Finset.mul_sum]
  exact integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun i _ =>
    core_density_coordinate_integrable hψ hm hJ hs hb s i))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RetainedFieldIdentity
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma normalizedCoreField_pair_integrable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B) (Z lam : ℝ) :
    Integrable (fun y => normalizedCoreField Z lam ψ y*ρ y) := by
  have h1 := bounded_compact_integrable hm hJ hs hb
  have hp := bounded_compact_memLp hm hJ hs hb (5/3 : ENNReal)
  have hn : Integrable (fun y : Space => ρ y/‖y‖) := by
    simpa only [zero_sub,norm_neg] using tfPotential_integrable h1 hp 0
  have hc := coreDensityField_integrable hψ hm hJ hs hb
  have hh := (((hn.const_mul (Z*formMass ψ)).sub hc).div_const (formMass ψ)).sub (h1.const_mul lam)
  apply hh.congr
  filter_upwards [] with y
  simp only [normalizedCoreField,Pi.sub_apply]
  ring

lemma normalizedCoreField_pairing {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B) (Z lam : ℝ) :
    (∫ y, normalizedCoreField Z lam ψ y*ρ y) =
      (Z*formMass ψ*tfPotential ρ 0-coreDensityInteraction ψ ρ)/formMass ψ-
        lam*(∫ y, ρ y) := by
  have h1 := bounded_compact_integrable hm hJ hs hb
  have hp := bounded_compact_memLp hm hJ hs hb (5/3 : ENNReal)
  have hn : Integrable (fun y : Space => ρ y/‖y‖) := by
    simpa only [zero_sub,norm_neg] using tfPotential_integrable h1 hp 0
  have hc := coreDensityField_integrable hψ hm hJ hs hb
  have he (y : Space) : normalizedCoreField Z lam ψ y*ρ y =
      (Z*formMass ψ*(ρ y/‖y‖)-ρ y*coreCoulombAt ψ y)/formMass ψ-lam*ρ y := by
    unfold normalizedCoreField
    ring
  simp_rw [he]
  rw [integral_sub (f := fun y => (Z*formMass ψ*(ρ y/‖y‖)-ρ y*coreCoulombAt ψ y)/formMass ψ)
    (g := fun y => lam*ρ y) (((hn.const_mul (Z*formMass ψ)).sub hc).div_const _) (h1.const_mul lam),
    integral_div,integral_sub (f := fun y => Z*formMass ψ*(ρ y/‖y‖))
      (g := fun y => ρ y*coreCoulombAt ψ y) (hn.const_mul (Z*formMass ψ)) hc,
    integral_const_mul,integral_const_mul,←coreDensityInteraction_eq_field hψ hm hJ hs hb]
  simp only [tfPotential,zero_sub,norm_neg]

lemma radial_translatedDensity_core {N : ℕ} (ψ : FormVector N)
    {η : Space → ℝ} (hm : Measurable η) {R B : ℝ} (hR : 0 < R)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B)
    (hr : IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (y : Space) (hc : ∀ a ∈ A, R ≤ ‖a-y‖) :
    coreDensityInteraction ψ (translatedDensity η y) = coreCoulombAt ψ y := by
  unfold coreDensityInteraction coreCoulombAt
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hi : x i ∈ A
  · rw [radial_translatedDensity_potential hm hR hs hb hr h1 y (x i) (hc _ hi),mul_one_div]
  · rw [(hcore x i hi s).1]
    simp only [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,zero_div]

lemma normalizedCoreField_radial_average {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {η : Space → ℝ} (hm : Measurable η) {R B : ℝ} (hR : 0 < R)
    (hs : ∀ x, η x ≠ 0 → ‖x‖ ≤ R) (hb : ∀ x, |η x| ≤ B)
    (hr : IsRadial η) (h1 : ∫ x : Space, η x = 1)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (y : Space) (hn : R ≤ ‖y‖) (hc : ∀ a ∈ A, R ≤ ‖a-y‖) (Z lam : ℝ) :
    (∫ z, normalizedCoreField Z lam ψ z*η (z-y)) = normalizedCoreField Z lam ψ y := by
  change (∫ z, normalizedCoreField Z lam ψ z*translatedDensity η y z) = _
  rw [normalizedCoreField_pairing hψ (translatedDensity_measurable hm y)
    (isCompact_closedBall y R) (translatedDensity_support hs y) (fun z => hb (z-y)),
    radial_translatedDensity_core ψ hm hR hs hb hr h1 A hcore y hc,
    radial_translatedDensity_potential hm hR hs hb hr h1 y 0 (by simpa only [zero_sub,norm_neg] using hn),
    translatedDensity_mass,h1,zero_sub,norm_neg,mul_one,mul_one_div]
  rfl

end CoulombAtom
namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

theorem retainedSmear_core_field {N M : ℕ} {ψ : FormVector M} (hψ : SobolevVector ψ)
    {b : ℝ} (hb : 0 < b) (S : Finset (Fin N)) (x : Configuration N)
    (A : Set Space) (hcore : ∀ u i, u i ∉ A → FormZeroAt ψ u)
    (hn : ∀ i ∈ S, Real.sqrt 3*b ≤ ‖x i‖)
    (hc : ∀ i ∈ S, ∀ a ∈ A, Real.sqrt 3*b ≤ ‖a-x i‖) (Z lam : ℝ) :
    (∫ z, normalizedCoreField Z lam ψ z*retainedSmear b S x z) =
      ∑ i ∈ S, normalizedCoreField Z lam ψ (x i) := by
  have haB (z : Space) : |varthetaScaled b z| ≤ b⁻¹^3 := by
    rw [abs_of_nonneg (varthetaScaled_nonneg hb z)]
    exact varthetaScaled_le hb z
  simp only [retainedSmear,Finset.mul_sum]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i hi => normalizedCoreField_radial_average hψ
      (varthetaScaled_measurable b) (by positivity) (varthetaScaled_support_bound hb) haB
      (fun _ _ h => varthetaScaled_radial b h) (integral_varthetaScaled hb)
      A hcore (x i) (hn i hi) (hc i hi) Z lam)
  · intro i _
    exact normalizedCoreField_pair_integrable hψ
      (translatedDensity_measurable (varthetaScaled_measurable b) (x i))
      (isCompact_closedBall _ _) (translatedDensity_support (varthetaScaled_support_bound hb) (x i))
      (fun z => haB (z-x i)) Z lam

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CoreFieldRegularity
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma coreCoulombTerm_measurable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (s : Spins N) (i : Fin N) :
    Measurable (fun z : Space => ∫ x, ‖ψ.value s x‖^2/‖x i-z‖) := by
  let h := (hψ.1 s).aestronglyMeasurable
  let v := h.mk (ψ.value s)
  have hv : Measurable v := h.stronglyMeasurable_mk.measurable
  have hm : StronglyMeasurable (fun q : Space × Configuration N => ‖v q.2‖^2/‖q.2 i-q.1‖) :=
    (((hv.comp measurable_snd).norm.pow_const 2).div (by fun_prop)).stronglyMeasurable
  have hh : Measurable (fun z : Space => ∫ x, ‖v x‖^2/‖x i-z‖) := hm.integral_prod_right.measurable
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  apply integral_congr_ae
  filter_upwards [h.ae_eq_mk] with x hx
  rw [hx]

lemma coreCoulombAt_measurable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    Measurable (coreCoulombAt ψ) :=
  Finset.measurable_sum _ (fun s _ => Finset.measurable_sum _ (fun i _ => coreCoulombTerm_measurable hψ s i))

lemma normalizedCoreField_measurable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (Z lam : ℝ) : Measurable (normalizedCoreField Z lam ψ) :=
  (((measurable_const.div continuous_norm.measurable).sub
    (coreCoulombAt_measurable hψ)).div_const _).sub_const _

lemma coreCoulombTerm_le_separated {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (A : Set Space) (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    {d : ℝ} (hd : 0 < d) (z : Space) (hsep : ∀ a ∈ A, d ≤ ‖a-z‖)
    (s : Spins N) (i : Fin N) :
    (∫ x, ‖ψ.value s x‖^2/‖x i-z‖) ≤ (∫ x, ‖ψ.value s x‖^2)/d := by
  rw [←integral_div]
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall fun x => div_nonneg (sq_nonneg _) (norm_nonneg _)
  · exact ((hψ.1 s).integrable_norm_pow (by decide)).div_const d
  · apply Eventually.of_forall
    intro x
    dsimp only
    by_cases hi : x i ∈ A
    · exact div_le_div_of_nonneg_left (sq_nonneg _) hd (hsep _ hi)
    · rw [(hc x i hi s).1]
      simp only [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,le_refl]

lemma coreCoulombAt_le_separated {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (A : Set Space) (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    {d : ℝ} (hd : 0 < d) (z : Space) (hsep : ∀ a ∈ A, d ≤ ‖a-z‖) :
    coreCoulombAt ψ z ≤ N*formMass ψ/d := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => coreCoulombTerm_le_separated hψ A hc hd z hsep s i))
  simpa only [coreCoulombAt,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    ←mul_div_assoc,←Finset.sum_div,←Finset.mul_sum,formMass] using hh

lemma normalizedCoreField_abs_le {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (A : Set Space) (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    {d : ℝ} (hd : 0 < d) (z : Space) (hsep : ∀ a ∈ A, d ≤ ‖a-z‖)
    {r : ℝ} (hr : 0 < r) (hz : r ≤ ‖z‖) (Z lam : ℝ) :
    |normalizedCoreField Z lam ψ z| ≤ |Z|/r+|lam|+N/d := by
  by_cases hm : formMass ψ = 0
  · simp only [normalizedCoreField,hm,mul_zero,zero_div,zero_sub,div_zero,abs_neg]
    have : 0 ≤ (N:ℝ)/d := div_nonneg (Nat.cast_nonneg _) hd.le
    have : 0 ≤ |Z|/r := div_nonneg (abs_nonneg _) hr.le
    linarith
  · have hmass : 0 < formMass ψ := lt_of_le_of_ne (formMass_nonneg ψ) (Ne.symm hm)
    have hn := coreCoulombAt_nonneg ψ z
    have hu := coreCoulombAt_le_separated hψ A hc hd z hsep
    have he : normalizedCoreField Z lam ψ z = Z/‖z‖-coreCoulombAt ψ z/formMass ψ-lam := by
      unfold normalizedCoreField
      field_simp
    rw [he]
    have hab := abs_sub (Z/‖z‖-coreCoulombAt ψ z/formMass ψ) lam
    have hab' := abs_sub (Z/‖z‖) (coreCoulombAt ψ z/formMass ψ)
    have hZ : |Z/‖z‖| ≤ |Z|/r := by
      rw [abs_div,abs_of_nonneg (norm_nonneg _)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hr hz
    have hc' : |coreCoulombAt ψ z/formMass ψ| ≤ N/d := by
      rw [abs_of_nonneg (div_nonneg hn hmass.le)]
      apply (div_le_iff₀ hmass).mpr
      simpa only [mul_div_assoc, mul_comm (formMass ψ), div_mul_eq_mul_div] using hu
    linarith

open CoulombAnalysis

lemma normalizedCoreField_memLp_patch {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (A : Set Space) (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (y : Space) (R : ℝ) {d r : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ) :
    MemLp (fun x => normalizedCoreField Z lam ψ (y+x)) (5/2) (ballMeasure R) := by
  apply MemLp.of_bound
    (((normalizedCoreField_measurable hψ Z lam).comp (measurable_const.add measurable_id)).aestronglyMeasurable)
    (|Z|/r+|lam|+N/d)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hz : y+x ∈ closedBall y R := by
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left] using
      (show ‖x‖ ≤ R from (by simpa only [mem_ball,dist_eq_norm,sub_zero] using hx : ‖x‖ < R).le)
  rw [Real.norm_eq_abs]
  exact normalizedCoreField_abs_le hψ A hc hd (y+x) (fun a ha => hsep a ha _ hz)
    hr (hnuc _ hz) Z lam

end Work_CoreFieldRegularity_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

open CoulombAnalysis

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CoherentBessel
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma coherentPhaseRaw_conjTest {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (i : CoherentIndex hg hcg μ) {F : Space × Space → ℂ} (hF : MemLp F 2 μ) :
    inner ℂ (coherentPhaseRaw hg hcg μ i) (hF.star.toLp (star F)) =
      conj (∫ q, coherentCoefficient hg hcg μ i q * F q ∂μ) := by
  rw [L2.inner_def,← integral_conj]
  apply integral_congr_ae
  filter_upwards [(coherentCoefficient_memLp hg hcg μ i).coeFn_toLp,
    hF.star.coeFn_toLp] with q hi hq
  change inner ℂ ((coherentCoefficient_memLp hg hcg μ i).toLp _ q) _ = _
  rw [hi,hq]
  simp only [RCLike.inner_apply,Pi.star_apply,map_mul,starRingEnd_apply,mul_comm]

lemma coherentPhaseVector_normTest {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (i : CoherentPositiveIndex hg hcg μ) {F : Space × Space → ℂ} (hF : MemLp F 2 μ) :
    ‖inner ℂ (coherentPhaseVector hg hcg μ i) (hF.star.toLp (star F))‖^2 =
      (coherentFactor / coherentWeight hg hcg μ i.1) *
        ‖∫ q, coherentCoefficient hg hcg μ i.1 q * F q ∂μ‖^2 := by
  rw [coherentPhaseVector,inner_smul_left_eq_smul,coherentPhaseRaw_conjTest hg hcg μ i.1 hF,
    norm_smul,Complex.norm_conj,mul_pow,Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (div_nonneg coherentFactor_pos.le i.2.le)]

lemma coherent_synthesis_bessel {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (s : Finset (CoherentPositiveIndex hg hcg μ)) {F : Space × Space → ℂ} (hF : MemLp F 2 μ) :
    (∑ i ∈ s, coherentWeight hg hcg μ i.1 *
      ‖((coherentWeight hg hcg μ i.1)⁻¹ * coherentFactor : ℝ) •
        (∫ q, coherentCoefficient hg hcg μ i.1 q * F q ∂μ)‖^2) ≤
      coherentFactor * ∫ q, ‖F q‖^2 ∂μ := by
  have hb := (coherentPhaseVector_orthonormal hg hcg μ).sum_inner_products_le
    (s := s) (hF.star.toLp (star F))
  have hn : ‖hF.star.toLp (star F)‖^2 = ∫ q, ‖F q‖^2 ∂μ := by
    rw [lp_complex_norm_sq]
    apply integral_congr_ae
    filter_upwards [hF.star.coeFn_toLp] with q hq
    rw [hq]
    simp only [Pi.star_apply,norm_star]
  rw [hn] at hb
  have he (i : CoherentPositiveIndex hg hcg μ) :
      coherentWeight hg hcg μ i.1 *
        ‖((coherentWeight hg hcg μ i.1)⁻¹ * coherentFactor : ℝ) •
          (∫ q, coherentCoefficient hg hcg μ i.1 q * F q ∂μ)‖^2 =
      coherentFactor * ‖inner ℂ (coherentPhaseVector hg hcg μ i) (hF.star.toLp (star F))‖^2 := by
    rw [coherentPhaseVector_normTest hg hcg μ i hF,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    field_simp [i.2.ne']
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hb coherentFactor_pos.le

lemma coherentOrbital_density_le {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (s : Finset (CoherentPositiveIndex hg hcg μ)) (x : Space) :
    (∑ i ∈ s, coherentWeight hg hcg μ i.1 * ‖coherentOrbital hg hcg μ i.1 x‖^2) ≤
      coherentFactor * ∫ q, ‖coherentPacket g q.1 q.2 x‖^2 ∂μ := by
  have hc : Continuous (fun q : Space × Space => coherentPacket g q.1 q.2 x) := by
    unfold coherentPacket
    fun_prop
  exact coherent_synthesis_bessel hg hcg μ s (coherentParam_memLp hc μ hK hμ)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_CoherentDerivatives
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma packetSynthesis_fderiv_apply {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {w : Space × Space → ℂ} (hw : Continuous w) (x v : Space) :
    fderiv ℝ (packetSynthesis g μ w) x v =
      ∫ q, w q * fderiv ℝ (coherentPacket g q.1 q.2) x v ∂μ := by
  let F : Space × (Space × Space) → ℂ := fun t => coherentPacket g t.2.1 t.2.2 t.1
  have hF : ContDiff ℝ ∞ F := coherentPacket_joint_smooth hg
  have hd := weightedSetIntegral_hasFDerivAt μ K hK (hF.of_le (by norm_num)) hw x
  rw [Measure.restrict_eq_self_of_ae_mem hμ] at hd
  have hi : Integrable (fun q => w q • firstPartial F (x,q)) μ := by
    rw [← Measure.restrict_eq_self_of_ae_mem hμ]
    exact (hw.smul ((firstPartial_contDiff (n := 0) (hF.of_le (by norm_num))).continuous.comp
      (continuous_const.prodMk continuous_id))).continuousOn.integrableOn_compact hK
  change fderiv ℝ (fun y => ∫ q, w q • F (y,q) ∂μ) x v = _
  rw [hd.fderiv,ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [smul_apply]
  have he := (firstPartial_hasFDerivAt (hF.differentiable (by simp)) x q).fderiv
  exact congrArg (fun A : Space →L[ℝ] ℂ => w q • A v) he.symm

lemma coherentOrbital_fderiv_apply {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg.continuous hcg μ) (x v : Space) :
    fderiv ℝ (coherentOrbital hg.continuous hcg μ i) x v =
      ((coherentWeight hg.continuous hcg μ i)⁻¹ * coherentFactor : ℝ) •
        (∫ q, coherentCoefficient hg.continuous hcg μ i q *
          fderiv ℝ (coherentPacket g q.1 q.2) x v ∂μ) := by
  have hw : Continuous (coherentCoefficient hg.continuous hcg μ i) :=
    (coherentVector_continuous hg.continuous hcg).inner continuous_const
  have hd := (packetSynthesis_smooth hg μ hK hμ hw).differentiable (by simp)
  change fderiv ℝ (((coherentWeight hg.continuous hcg μ i)⁻¹ * coherentFactor : ℝ) •
    packetSynthesis g μ (coherentCoefficient hg.continuous hcg μ i)) x v = _
  rw [fderiv_const_smul (hd x),smul_apply,
    packetSynthesis_fderiv_apply hg μ hK hμ hw]

lemma coherentOrbital_gradient_le {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (s : Finset (CoherentPositiveIndex hg.continuous hcg μ)) (x v : Space) :
    (∑ i ∈ s, coherentWeight hg.continuous hcg μ i.1 *
      ‖fderiv ℝ (coherentOrbital hg.continuous hcg μ i.1) x v‖^2) ≤
      coherentFactor * ∫ q, ‖fderiv ℝ (coherentPacket g q.1 q.2) x v‖^2 ∂μ := by
  simp_rw [coherentOrbital_fderiv_apply hg hcg μ hK hμ]
  apply coherent_synthesis_bessel hg.continuous hcg μ s
  apply coherentParam_memLp _ μ hK hμ
  exact (coherentPacket_derivative_joint_continuous hg v).comp
    (continuous_const.prodMk continuous_id)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoherentKinetic
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

lemma coherentOrbital_derivative_sq_integrable {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg.continuous hcg μ) (v : Space) :
    Integrable (fun x : Space => ‖fderiv ℝ (coherentOrbital hg.continuous hcg μ i) x v‖^2) := by
  have hc := (coherentOrbital_compact hg.continuous hcg μ hK hμ i).fderiv_apply ℝ v
  have hd : Continuous (fun x : Space => fderiv ℝ (coherentOrbital hg.continuous hcg μ i) x v) :=
    ((coherentOrbital_smooth hg hcg μ hK hμ i).continuous_fderiv (by simp)).clm_apply continuous_const
  exact (hd.memLp_of_hasCompactSupport hc (p := 2)).norm.integrable_sq

lemma coherentOrbital_kinetic_le {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (s : Finset (CoherentPositiveIndex hg.continuous hcg μ)) (v : Space) :
    (∑ i ∈ s, coherentWeight hg.continuous hcg μ i.1 * ∫ x : Space,
      ‖fderiv ℝ (coherentOrbital hg.continuous hcg μ i.1) x v‖^2) ≤
      coherentFactor * ∫ q, (∫ x : Space, ‖fderiv ℝ (coherentPacket g q.1 q.2) x v‖^2) ∂μ := by
  have hi : Integrable (fun r : Space × (Space × Space) =>
      ‖fderiv ℝ (coherentPacket g r.2.1 r.2.2) r.1 v‖^2) (volume.prod μ) :=
    (coherentPacket_derivative_sq_integrable hg hcg μ hK hμ v).swap
  calc
    _ = ∫ x : Space, ∑ i ∈ s, coherentWeight hg.continuous hcg μ i.1 *
        ‖fderiv ℝ (coherentOrbital hg.continuous hcg μ i.1) x v‖^2 := by
      rw [integral_finsetSum _ (fun i _ =>
        (coherentOrbital_derivative_sq_integrable hg hcg μ hK hμ i.1 v).const_mul _)]
      simp only [integral_const_mul]
    _ ≤ ∫ x : Space, coherentFactor * ∫ q,
        ‖fderiv ℝ (coherentPacket g q.1 q.2) x v‖^2 ∂μ := by
      apply integral_mono
      · exact integrable_finsetSum _ (fun i _ =>
          (coherentOrbital_derivative_sq_integrable hg hcg μ hK hμ i.1 v).const_mul _)
      · exact hi.integral_prod_left.const_mul _
      · exact fun x => coherentOrbital_gradient_le hg hcg μ hK hμ s x v
    _ = _ := by
      rw [integral_const_mul,integral_integral_swap hi]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_CoherentFiniteInsertion
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma coherentOrbital_tsupport_subset {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (i : CoherentIndex hg hcg μ) :
    tsupport (coherentOrbital hg hcg μ i) ⊆ coherentSpatialSupport g K := by
  apply closure_minimal _ (coherentSpatialSupport_compact hcg hK).isClosed
  intro x hx
  by_contra hn
  exact hx (coherentOrbital_zero_outside hg hcg μ hμ i hn)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CoherentDensityTrace
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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
open scoped BigOperators ContDiff Topology

lemma coherentOrbital_density_tsum {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    (fun x : Space => ∑' i : CoherentPositiveIndex hg.continuous hcg μ,
      coherentWeight hg.continuous hcg μ i.1 * ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2)
      =ᵐ[volume] coherentDensity g μ := by
  apply nonneg_series_eq_of_integral volume
  · intro i
    exact ((coherentOrbital_memLp hg hcg μ hK hμ i.1).norm.integrable_sq).const_mul _
  · intro i x
    exact mul_nonneg i.2.le (sq_nonneg _)
  · exact coherentDensity_integrable hg.continuous hcg μ hK hμ
  · exact fun s x => coherentOrbital_density_le hg.continuous hcg μ hK hμ s x
  · simp only [integral_const_mul,coherentOrbital_mass hg hcg μ hK hμ,mul_one,
      coherentDensity_mass hg.continuous hcg μ hK hμ]
    exact coherentPositiveWeight_hasSum hg.continuous hcg μ

open MeasureTheory Filter
open scoped BigOperators ContDiff Topology

lemma coherentOrbital_density_hasSum {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    ∀ᵐ x : Space ∂volume, HasSum (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
      coherentWeight hg.continuous hcg μ i.1 * ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2)
        (coherentDensity g μ x) := by
  filter_upwards [coherentOrbital_density_tsum hg hcg μ hK hμ] with x hx
  rw [← hx]
  exact (summable_of_sum_le (fun i => mul_nonneg i.2.le (sq_nonneg _))
    (fun s => coherentOrbital_density_le hg.continuous hcg μ hK hμ s x)).hasSum

lemma coherentOrbital_weight_hasSum {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    {W : Space → ℝ} (hW : AEStronglyMeasurable W volume)
    (hWi : Integrable (fun x => |W x| *coherentDensity g μ x)) :
    HasSum (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
      coherentWeight hg.continuous hcg μ i.1 * ∫ x : Space,
        W x * ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2)
      (∫ x : Space, W x * coherentDensity g μ x) := by
  have h := nonneg_series_weight_hasSum volume
    (f := fun (i : CoherentPositiveIndex hg.continuous hcg μ) (x : Space) =>
      coherentWeight hg.continuous hcg μ i.1 * ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2)
    (fun i => continuous_const.mul ((coherentOrbital_smooth hg hcg μ hK hμ i.1).continuous.norm.pow 2)
      |>.aestronglyMeasurable)
    (fun i _ => mul_nonneg i.2.le (sq_nonneg _)) hW hWi
    (coherentOrbital_density_hasSum hg hcg μ hK hμ)
  simpa only [mul_left_comm (W _) (coherentWeight _ _ _ _),integral_const_mul] using h

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpinEnergy
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SpinEnergy_scope

open MeasureTheory
open scoped BigOperators ContDiff

lemma spinFinite_core {N : ℕ} {ι : Type*} [Fintype ι] (ψ : FormVector N) (p : ι → ℝ)
    (u : ι → Space → ℂ) :
    (∑ i : Fin 2 × ι, p i.2 * orbitalCoreInteraction ψ (spinLift (u i.2) i.1)) =
      2 * ∑ i, p i *coreDensityInteraction ψ (fun y => ‖u i y‖^2) := by
  simp only [spinLift_core_interaction,Fintype.sum_prod_type,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]

end Work_SpinEnergy_scope

open MeasureTheory Filter
open scoped BigOperators ContDiff

lemma coherentOrbital_pole_hasSum {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) (a : Space) :
    HasSum (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
      coherentWeight hg.continuous hcg μ i.1 *
        CoulombAnalysis.tfPotential (fun y => ‖coherentOrbital hg.continuous hcg μ i.1 y‖^2) a)
      (CoulombAnalysis.tfPotential (coherentDensity g μ) a) := by
  have hd := coherentDensity_continuous hg.continuous μ hK hμ
  have hs := coherentDensity_compact hcg μ hK hμ
  have hi := CoulombAnalysis.tfPotential_integrable (hd.integrable_of_hasCompactSupport hs)
    (hd.memLp_of_hasCompactSupport hs) a
  have hw : Integrable (fun x : Space => |‖a-x‖⁻¹| * coherentDensity g μ x) := by
    simpa only [abs_inv,abs_norm,div_eq_mul_inv,mul_comm] using hi
  have hW : AEStronglyMeasurable (fun x : Space => ‖a-x‖⁻¹) volume :=
    (continuous_const.sub continuous_id).norm.measurable.inv.aestronglyMeasurable
  simpa only [CoulombAnalysis.tfPotential,div_eq_mul_inv,mul_comm] using
    coherentOrbital_weight_hasSum hg hcg μ hK hμ hW hw

lemma coherentOrbital_core_coordinate_hasSum {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (s : Spins N) (j : Fin N) :
    HasSum (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
      coherentWeight hg.continuous hcg μ i.1 * ∫ x : Configuration N,
        ‖ψ.value s x‖^2 * CoulombAnalysis.tfPotential
          (fun y => ‖coherentOrbital hg.continuous hcg μ i.1 y‖^2) (x j))
      (∫ x : Configuration N, ‖ψ.value s x‖^2 *
        CoulombAnalysis.tfPotential (coherentDensity g μ) (x j)) := by
  have hi := core_compact_potential_integrable hψ
    (coherentDensity_continuous hg.continuous μ hK hμ) (coherentDensity_compact hcg μ hK hμ) s j
  have hh := nonneg_series_weight_hasSum volume
    (f := fun (i : CoherentPositiveIndex hg.continuous hcg μ) (x : Configuration N) =>
      coherentWeight hg.continuous hcg μ i.1 * CoulombAnalysis.tfPotential
        (fun y => ‖coherentOrbital hg.continuous hcg μ i.1 y‖^2) (x j))
    (W := fun x : Configuration N => ‖ψ.value s x‖^2)
    (d := fun x : Configuration N => CoulombAnalysis.tfPotential (coherentDensity g μ) (x j))
    (fun i => by
      have hd := (coherentOrbital_smooth hg hcg μ hK hμ i.1).continuous.norm.pow 2
      have hs := compact_norm_sq (coherentOrbital_compact hg.continuous hcg μ hK hμ i.1)
      exact continuous_const.mul ((CoulombAnalysis.tfPotential_continuous
        (hd.integrable_of_hasCompactSupport hs) (hd.memLp_of_hasCompactSupport hs)).comp
          (continuous_apply j)) |>.aestronglyMeasurable)
    (fun i x => mul_nonneg i.2.le (integral_nonneg (fun y => div_nonneg (sq_nonneg _) (norm_nonneg _))))
    ((hψ.1 s).aestronglyMeasurable.norm.pow 2)
    (by simpa only [abs_pow,abs_norm] using hi)
    (Eventually.of_forall (fun x => coherentOrbital_pole_hasSum hg hcg μ hK hμ (x j)))
  simpa only [mul_left_comm (‖ψ.value s _‖^2) (coherentWeight _ _ _ _),integral_const_mul] using hh

lemma coherentOrbital_core_hasSum {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K) :
    HasSum (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
      coherentWeight hg.continuous hcg μ i.1 * coreDensityInteraction ψ
        (fun y => ‖coherentOrbital hg.continuous hcg μ i.1 y‖^2))
      (coreDensityInteraction ψ (coherentDensity g μ)) := by
  have hh := hasSum_sum (s := (Finset.univ : Finset (Spins N))) (fun s _ =>
    hasSum_sum (s := (Finset.univ : Finset (Fin N))) (fun j _ =>
      coherentOrbital_core_coordinate_hasSum hψ hg hcg μ hK hμ s j))
  simpa only [coreDensityInteraction,Finset.mul_sum] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoherentLimitInsertion
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma coherentFinite_kinetic_le {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (s : Finset (CoherentPositiveIndex hg.continuous hcg μ)) :
    (∑ a : Fin 3, ∑ i : s, coherentWeight hg.continuous hcg μ i.1.1 * ∫ x : Space,
      ‖fderiv ℝ (coherentOrbital hg.continuous hcg μ i.1.1) x (EuclideanSpace.single a 1)‖^2) ≤
      coherentSpinKinetic g μ := by
  unfold coherentSpinKinetic
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.sum_coe_sort s (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
    coherentWeight hg.continuous hcg μ i.1 * ∫ x : Space,
      ‖fderiv ℝ (coherentOrbital hg.continuous hcg μ i.1) x (EuclideanSpace.single a 1)‖^2)]
  exact coherentOrbital_kinetic_le hg hcg μ hK hμ s (EuclideanSpace.single a 1)

lemma coherentFinite_direct_le {g : Space → ℂ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    {K : Set (Space × Space)} (hK : IsCompact K) (hμ : ∀ᵐ q ∂μ, q ∈ K)
    (s : Finset (CoherentPositiveIndex hg.continuous hcg μ)) :
    (∫ r : Space × Space,
      spatialFiniteDensity (fun i : s => coherentWeight hg.continuous hcg μ i.1.1)
        (fun i => coherentOrbital hg.continuous hcg μ i.1.1) r.1 *
      spatialFiniteDensity (fun i : s => coherentWeight hg.continuous hcg μ i.1.1)
        (fun i => coherentOrbital hg.continuous hcg μ i.1.1) r.2 / ‖r.1-r.2‖) ≤
      ∫ r : Space × Space, coherentDensity g μ r.1 * coherentDensity g μ r.2 / ‖r.1-r.2‖ := by
  let p : s → ℝ := fun i => coherentWeight hg.continuous hcg μ i.1.1
  let u : s → Space → ℂ := fun i => coherentOrbital hg.continuous hcg μ i.1.1
  have hc : ∀ i : s, Continuous (u i) := fun i => (coherentOrbital_smooth hg hcg μ hK hμ i.1.1).continuous
  have ht : ∀ i : s, HasCompactSupport (u i) := fun i => coherentOrbital_compact hg.continuous hcg μ hK hμ i.1.1
  have hn : ∀ i : s, 0 ≤ p i := fun i => i.1.2.le
  apply compact_direct_mono (f := spatialFiniteDensity p u) (g := coherentDensity g μ)
    (spatialFiniteDensity_continuous p hc) (coherentDensity_continuous hg.continuous μ hK hμ)
    (spatialFiniteDensity_compact p ht) (coherentDensity_compact hcg μ hK hμ)
    (spatialFiniteDensity_nonneg hn)
  intro x
  change (∑ i : s, coherentWeight hg.continuous hcg μ i.1.1 *
    ‖coherentOrbital hg.continuous hcg μ i.1.1 x‖^2) ≤ _
  rw [Finset.sum_coe_sort s (fun i : CoherentPositiveIndex hg.continuous hcg μ =>
    coherentWeight hg.continuous hcg μ i.1 * ‖coherentOrbital hg.continuous hcg μ i.1 x‖^2)]
  exact coherentOrbital_density_le hg.continuous hcg μ hK hμ s x

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoherentRealKinetic
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma real_coherentPacket_kinetic {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (hgn : ∫ x : Space, (g x)^2 = 1) (z p : Space) :
    (∑ a : Fin 3, ∫ x : Space, ‖fderiv ℝ (coherentPacket (fun y => (g y : ℂ)) z p) x
      (EuclideanSpace.single a 1)‖^2) = packetDirichlet g + ‖p‖^2 := by
  have hg2 : Integrable (fun x : Space => (g x)^2) :=
    (hg.continuous.memLp_of_hasCompactSupport hcg (p := 2)).integrable_sq
  have hs (a : Fin 3) : (∫ x : Space, ‖fderiv ℝ (coherentPacket (fun y => (g y : ℂ)) z p) x
      (EuclideanSpace.single a 1)‖^2) =
      (∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single a 1))^2) + (inner ℝ p (EuclideanSpace.single a 1))^2 := by
    simp_rw [real_coherentPacket_derivative_sq (hg.differentiable (by simp))]
    rw [integral_add ((real_derivative_sq_integrable hg hcg _).comp_sub_right z)
      ((hg2.comp_sub_right z).mul_const _),integral_mul_const,
      integral_sub_right_eq_self (fun x : Space => (fderiv ℝ g x (EuclideanSpace.single a 1))^2) z,
      integral_sub_right_eq_self (fun x : Space => (g x)^2) z,hgn,one_mul]
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← sum_coordinate_sq]
  apply Finset.sum_congr rfl
  intro a _
  simp [EuclideanSpace.inner_single_right]

lemma coherentSpinKinetic_fermi {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) :
    coherentSpinKinetic (fun x => (g x : ℂ)) (fermiMeasure ρ) =
      tfKinetic*(∫ z, (ρ z)^(5/3 : ℝ)) + (packetDirichlet g / 2)*(∫ z, ρ z) := by
  let := fermiMeasure_finite hn hJ hs hb
  have hgc : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hcgc : HasCompactSupport (fun x => (g x : ℂ)) := hcg.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  let K : Set (Space × Space) := J ×ˢ closedBall 0 ((3*Real.pi^2*B)^(1/3 : ℝ))
  have hK : IsCompact K := hJ.prod (isCompact_closedBall _ _)
  have hμ : ∀ᵐ q ∂fermiMeasure ρ, q ∈ K := fermiMeasure_mem hm hn hs hb
  have hi (a : Fin 3) : Integrable (fun q : Space × Space => ∫ x : Space,
      ‖fderiv ℝ (coherentPacket (fun x => (g x : ℂ)) q.1 q.2) x (EuclideanSpace.single a 1)‖^2)
      (fermiMeasure ρ) := (coherentPacket_derivative_sq_integrable hgc hcgc (fermiMeasure ρ)
        hK hμ (EuclideanSpace.single a 1)).integral_prod_left
  unfold coherentSpinKinetic
  rw [← integral_finsetSum _ (fun a _ => hi a)]
  simp_rw [real_coherentPacket_kinetic hg hcg hgn]
  rw [integral_add (integrable_const _) (fermiMeasure_integrable_continuous hn hJ hs hb (by fun_prop)),
    integral_const,smul_eq_mul,mul_add,fermiMeasure_kinetic hm hn hJ hs hb]
  have hmass := fermiMeasure_mass hm hn hJ hs hb
  rw [← hmass]
  ring

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma coreDensityInteraction_const_mul {N : ℕ} (ψ : FormVector N) (c : ℝ) (f : Space → ℝ) :
    coreDensityInteraction ψ (fun x => c*f x) = c*coreDensityInteraction ψ f := by
  simp only [coreDensityInteraction,potential_const_mul,Finset.mul_sum]
  congr 1
  funext s
  congr 1
  funext i
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma coherentSupport_fermi_subset (g : Space → ℝ) (J : Set Space) (r : ℝ) :
    coherentSpatialSupport (fun x => (g x : ℂ)) (J ×ˢ closedBall 0 r) ⊆ packetRegion g J := by
  rintro x ⟨⟨q,u⟩,⟨hq,hu⟩,rfl⟩
  exact ⟨(u,q.1),⟨by simpa only [real_complex_tsupport] using hu,hq.1⟩,rfl⟩

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketScale
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma scaledRealPacket_smooth (b : ℝ) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (scaledRealPacket b g) :=
  contDiff_const.mul (hg.comp (b⁻¹ • ContinuousLinearMap.id ℝ Space).contDiff)

lemma scaledRealPacket_compact {b : ℝ} (hb : 0 < b) {g : Space → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (scaledRealPacket b g) :=
  (hg.comp_smul (inv_ne_zero hb.ne')).mul_left

lemma scaledRealPacket_mass {b : ℝ} (hb : 0 < b) (g : Space → ℝ) :
    (∫ x : Space, (scaledRealPacket b g x)^2) = ∫ x : Space, (g x)^2 := by
  simp only [scaledRealPacket,mul_pow,integral_const_mul]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun x : Space => (g x)^2) hb.le,
    space_finrank,smul_eq_mul,← mul_assoc,packetScale_factor hb,one_mul]

lemma scaledRealPacket_derivative (b : ℝ) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (x v : Space) :
    fderiv ℝ (scaledRealPacket b g) x v =
      b ^ (-(3/2 : ℝ))*b⁻¹*fderiv ℝ g (b⁻¹ • x) v := by
  have hcomp : HasFDerivAt (fun y : Space => g (b⁻¹ • y))
      ((fderiv ℝ g (b⁻¹ • x)).comp (b⁻¹ • ContinuousLinearMap.id ℝ Space)) x :=
    ((hg.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x
      (b⁻¹ • ContinuousLinearMap.id ℝ Space).hasFDerivAt
  have hh := hcomp.const_mul (b ^ (-(3/2 : ℝ)))
  rw [show scaledRealPacket b g = fun x => b ^ (-(3/2 : ℝ))*g (b⁻¹ • x) from rfl,hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  ring

lemma scaledRealPacket_dirichlet {b : ℝ} (hb : 0 < b) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) :
    packetDirichlet (scaledRealPacket b g) = packetDirichlet g / b^2 := by
  unfold packetDirichlet
  simp_rw [scaledRealPacket_derivative b hg,mul_pow,integral_const_mul]
  have hi (a : Fin 3) := Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x : Space => (fderiv ℝ g x (EuclideanSpace.single a 1))^2) hb.le
  simp only [space_finrank,smul_eq_mul] at hi
  simp_rw [hi]
  have hc : (b ^ (-(3/2 : ℝ)))^2*b⁻¹^2*b^3 = (b^2)⁻¹ := by
    calc
      _ = ((b ^ (-(3/2 : ℝ)))^2*b^3)*b⁻¹^2 := by ring
      _ = _ := by rw [packetScale_factor hb,one_mul,inv_pow]
  simp only [← mul_assoc,hc,inv_mul_eq_div,Finset.sum_div]

lemma scaledRealPacket_radial (b : ℝ) {g : Space → ℝ} (hg : CoulombAnalysis.IsRadial g) :
    CoulombAnalysis.IsRadial (scaledRealPacket b g) := by
  intro x y hxy
  unfold scaledRealPacket
  rw [hg (b⁻¹ • x) (b⁻¹ • y) (by simp only [norm_smul,hxy])]

lemma scaledRealPacket_support {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hs : tsupport g ⊆ ball 0 1) {x : Space} (hx : scaledRealPacket b g x ≠ 0) : ‖x‖ < b := by
  have hg : g (b⁻¹ • x) ≠ 0 := by intro hz; exact hx (by simp [scaledRealPacket,hz])
  have hb' := hs (subset_tsupport g hg)
  simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hb.le)] at hb'
  rwa [inv_mul_eq_div,div_lt_one hb] at hb'

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_PricedUpperComparison
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma priced_core_field_pairing {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    {ρ : Space → ℝ} (hm : Measurable ρ) {J : Set Space} (hJ : IsCompact J)
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, |ρ z| ≤ B) (Z lam : ℝ) :
    (∫ y : Space, (Z/‖y‖-lam-coreCoulombAt ψ y)*ρ y) =
      Z*CoulombAnalysis.tfPotential ρ 0-lam*(∫ y, ρ y)-coreDensityInteraction ψ ρ := by
  have h1 := bounded_compact_integrable hm hJ hs hb
  have hp := bounded_compact_memLp hm hJ hs hb (5/3 : ENNReal)
  have hn : Integrable (fun y : Space => ρ y/‖y‖) := by
    simpa only [zero_sub,norm_neg] using CoulombAnalysis.tfPotential_integrable h1 hp 0
  have hc := coreDensityField_integrable hψ hm hJ hs hb
  have he (y : Space) : (Z/‖y‖-lam-coreCoulombAt ψ y)*ρ y =
      Z*(ρ y/‖y‖)-lam*ρ y-ρ y*coreCoulombAt ψ y := by ring
  simp_rw [he]
  have hi := integral_sub ((hn.const_mul Z).sub (h1.const_mul lam)) hc
  simp only [Pi.sub_apply] at hi
  rw [hi]
  have hi' := integral_sub (hn.const_mul Z) (h1.const_mul lam)
  rw [hi',integral_const_mul,integral_const_mul,
    ← coreDensityInteraction_eq_field hψ hm hJ hs hb]
  simp only [CoulombAnalysis.tfPotential,zero_sub,norm_neg]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_ConditionalPricedUpper
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma coreCoulombAt_scale {N : ℕ} (c : ℝ) (ψ : FormVector N) (y : Space) :
    coreCoulombAt (scaleForm c ψ) y = c^2*coreCoulombAt ψ y := by
  simp only [coreCoulombAt,scaleForm,scaled_norm_sq,mul_div_assoc,integral_const_mul,←Finset.mul_sum]

lemma normalizedCoreField_eq_scaled {N : ℕ} (Z lam : ℝ) {ψ : FormVector N}
    (hm : 0 < formMass ψ) (y : Space) : normalizedCoreField Z lam ψ y =
      Z/‖y‖-lam-coreCoulombAt (scaleForm (Real.sqrt (formMass ψ))⁻¹ ψ) y := by
  rw [coreCoulombAt_scale,inv_pow,Real.sq_sqrt hm.le]
  unfold normalizedCoreField
  field_simp
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RetainedPatchDensity
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma retainedPatch_density_ae {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R) :
    translatedPatchDensity y R (S.card*b⁻¹^3) (retainedPatchLp hb S x y R) =ᵐ[volume]
      retainedSmear b S x := by
  have he := (boundedPatchRepresentative_ae (retainedPatchLp_nonneg hb S x y R)
    (retainedPatchLp_bound hb S x y R)).trans (retainedPatchLp_extension hb S x y hmargin)
  have ht := (measurePreserving_add_left (volume : Measure Space) (-y)).quasiMeasurePreserving.ae he
  filter_upwards [ht] with z hz
  simpa only [translatedPatchDensity,add_neg_cancel_left] using hz

lemma retainedPatchLp_mass {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R) :
    (∫ z, retainedPatchLp hb S x y R z ∂ballMeasure R) = (S.card:ℝ) := by
  rw [←translatedPatchDensity_mass y (retainedPatchLp_nonneg hb S x y R)
    (retainedPatchLp_bound hb S x y R),integral_congr_ae (retainedPatch_density_ae hb S x y hmargin)]
  exact integral_retainedSmear hb S x

lemma retainedPatchLp_kinetic {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R) :
    ‖retainedPatchLp hb S x y R‖^(5/3:ℝ) = retainedPressure b S x := by
  rw [←translatedPatchDensity_kinetic y (retainedPatchLp_nonneg hb S x y R)
    (retainedPatchLp_bound hb S x y R)]
  exact integral_congr_ae ((retainedPatch_density_ae hb S x y hmargin).mono fun z hz => by dsimp only at *; rw [hz])

lemma retainedPatchLp_coulomb {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R) :
    tfCoulombL R (retainedPatchLp hb S x y R) (retainedPatchLp hb S x y R) =
      ∫ p : Space × Space, retainedSmear b S x p.1*retainedSmear b S x p.2/‖p.1-p.2‖ := by
  rw [←translatedPatchDensity_coulomb y (retainedPatchLp_nonneg hb S x y R)
    (retainedPatchLp_bound hb S x y R)]
  have he := retainedPatch_density_ae hb S x y hmargin
  apply integral_congr_ae
  rw [Measure.volume_eq_prod]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae he,
    Measure.quasiMeasurePreserving_snd.ae he] with p h1 h2
  rw [h1,h2]

lemma retainedPatchLp_field {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R)
    (Φ : Space → ℝ) :
    (∫ z, Φ (y+z)*retainedPatchLp hb S x y R z ∂ballMeasure R) =
      ∫ z, Φ z*retainedSmear b S x z := by
  rw [←translatedPatchDensity_field y (retainedPatchLp_nonneg hb S x y R)
    (retainedPatchLp_bound hb S x y R)]
  exact integral_congr_ae ((retainedPatch_density_ae hb S x y hmargin).mono fun z hz => by dsimp only at *; rw [hz])

lemma retainedPatchLp_functional {b R : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R)
    (Φ : TFField R) (field : Space → ℝ) (hΦ : Φ =ᵐ[ballMeasure R] fun z => field (y+z)) (T : ℝ) :
    tfPatchFunctional R T Φ (retainedPatchLp hb S x y R) =
      T*retainedPressure b S x-(∫ z, field z*retainedSmear b S x z)+
      (1/2:ℝ)*(∫ p : Space × Space, retainedSmear b S x p.1*retainedSmear b S x p.2/‖p.1-p.2‖) := by
  rw [tfPatchFunctional,tfPatchLinear_apply,retainedPatchLp_kinetic hb S x y hmargin,
    retainedPatchLp_coulomb hb S x y hmargin]
  have he : (∫ z, Φ z*retainedPatchLp hb S x y R z ∂ballMeasure R) =
      ∫ z, field (y+z)*retainedPatchLp hb S x y R z ∂ballMeasure R :=
    integral_congr_ae (hΦ.mono fun z hz => by dsimp only at *; rw [hz])
  rw [he,retainedPatchLp_field hb S x y hmargin]
  ring

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_OutCutAntisymmetry
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

def outFirstLabels (N M : ℕ) : Fin (M+N) → Fin 2 :=
  joinLists (fun _ : Fin M => 1) (fun _ : Fin N => 0)

lemma coreCutLabels_blockSwap (N M : ℕ) :
    coreCutLabels N M ∘ blockSwap N M = outFirstLabels N M := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j <;>
    simp only [Function.comp_apply,blockSwap_left,blockSwap_right,coreCutLabels,
      outFirstLabels,joinLists_left,joinLists_right]

lemma outFirstLabels_invariant {N M : ℕ} (π : Equiv.Perm (Fin M)) :
    outFirstLabels N M ∘ corePerm N π = outFirstLabels N M := by
  change joinLists (fun _ : Fin M => (1 : Fin 2)) (fun _ : Fin N => 0) ∘ corePerm N π = _
  rw [joinLists_corePerm]
  rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_OutRetainedLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OutRetainedLower_scope

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombNeumann CoulombAnalysis

abbrev OuterCutRetention (L : ℕ) := ∀ c : Fin L → Fin 2,
  Spins (cutOutNumber c) → Configuration (cutOutNumber c) → Finset (Fin (cutOutNumber c))

end Work_OutRetainedLower_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialPatchGeometry
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

def radialPatchRetention (L : ℕ) (y : Space) (t b : ℝ) : OuterCutRetention L :=
  fun _ _ u => Finset.univ.filter (fun i => ‖u i-y‖ < t-7*b)

lemma radialPatchRetention_measurable (L : ℕ) (y : Space) (t b : ℝ)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) (i : Fin (cutOutNumber c)) :
    MeasurableSet {u | i ∈ radialPatchRetention L y t b c s u} := by
  simp only [radialPatchRetention,Finset.mem_filter,Finset.mem_univ,true_and]
  exact (isOpen_lt (((continuous_apply i).sub continuous_const).norm) continuous_const).measurableSet

lemma scaledRealPacket_tsupport {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hs : tsupport g ⊆ ball 0 1) : tsupport (scaledRealPacket b g) ⊆ closedBall 0 b := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  simpa only [mem_closedBall,dist_zero_right] using (scaledRealPacket_support hb hs hx).le

lemma radialPatch_nuclear_distance {y : Space} {t b : ℝ} (hb : 0 < b)
    (hy : t ≤ ‖y‖) (z : Space) (hz : z ∈ closedBall y (t-4*b)) : b ≤ ‖z‖ := by
  simp only [mem_closedBall,dist_eq_norm] at hz
  have hh := norm_sub_norm_le y z
  rw [norm_sub_rev y z] at hh
  linarith

lemma radialPatch_retained_margin {L : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c))
    (i : Fin (cutOutNumber c)) (hi : i ∈ radialPatchRetention L y t b c s u) :
    ‖u i-y‖+Real.sqrt 3*b ≤ t-4*b := by
  have hi' : ‖u i-y‖ < t-7*b := (Finset.mem_filter.mp hi).2
  have hs := mul_le_mul_of_nonneg_right sqrt_three_le_three hb.le
  linarith

lemma radialPatch_retained_nuclear {L : ℕ} {y : Space} {t b : ℝ} (hb : 0 < b)
    (hy : t ≤ ‖y‖) (c : Fin L → Fin 2) (s : Spins (cutOutNumber c))
    (u : Configuration (cutOutNumber c)) (i : Fin (cutOutNumber c))
    (hi : i ∈ radialPatchRetention L y t b c s u) : Real.sqrt 3*b ≤ ‖u i‖ := by
  have hi' : ‖u i-y‖ < t-7*b := (Finset.mem_filter.mp hi).2
  have hs := mul_le_mul_of_nonneg_right sqrt_three_le_three hb.le
  have hh := norm_sub_norm_le y (u i)
  rw [norm_sub_rev y (u i)] at hh
  linarith

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_CutCountDomination
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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

def cutDeletedCount {N : ℕ} (y : Space) (t b : ℝ)
    (c : Fin N → Fin 2) (x : Configuration N) : ℝ :=
  ∑ i, if c i ≠ 0 ∧ t-7*b ≤ ‖x i-y‖ then 1 else 0

lemma cutDeletedCount_nonneg {N : ℕ} (y : Space) (t b : ℝ)
    (c : Fin N → Fin 2) (x : Configuration N) : 0 ≤ cutDeletedCount y t b c x := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> norm_num

lemma cutDeletedCount_le {N : ℕ} (y : Space) (t b : ℝ)
    (c : Fin N → Fin 2) (x : Configuration N) : cutDeletedCount y t b c x ≤ N := by
  calc
    _ ≤ ∑ _ : Fin N, (1:ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
    _ = N := by simp

lemma cutDeletedCount_measurable {N : ℕ} (y : Space) (t b : ℝ) (c : Fin N → Fin 2) :
    Measurable (cutDeletedCount y t b c) := by
  apply Finset.measurable_sum; intro i _
  apply Measurable.ite _ measurable_const measurable_const
  by_cases hc : c i ≠ 0
  · simpa [hc] using (measurableSet_le (measurable_const (a := t-7*b))
      (configuration_distance_measurable y i))
  · simp [hc]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialCountSelection
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma rawStripCount_measurable {N : ℕ} (y : Space) (t b : ℝ) :
    Measurable (rawStripCount (N := N) y t b) :=
  slidingCount_measurable (fun i => configuration_distance_measurable y i)
    measurable_const (7*b) b

lemma rawStripCount_nonneg {N : ℕ} (y : Space) (t b : ℝ) (x : Configuration N) :
    0 ≤ rawStripCount y t b x := slidingCount_nonneg _ _ _ _

lemma rawStripCount_le {N : ℕ} (y : Space) (t b : ℝ) (x : Configuration N) :
    rawStripCount y t b x ≤ N := slidingCount_le _ _ _ _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CutOuterLaw
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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

def cutOutPositions {L : ℕ} (c : Fin L → Fin 2) (x : Configuration L) :
    Configuration (cutOutNumber c) :=
  fun i => x (cutOrder c (finSumFinEquiv (Sum.inr i)))

lemma sum_cutOutPositions {L : ℕ} (c : Fin L → Fin 2) (x : Configuration L) (f : Space → ℝ) :
    (∑ i, f (cutOutPositions c x i)) = ∑ i, if c i ≠ 0 then f (x i) else 0 := by
  classical
  have he := Equiv.sum_comp (Fintype.equivFin {i // c i ≠ 0}).symm (fun i => f (x i.val))
  have hs := Finset.sum_subtype (p := fun i => c i ≠ 0) (F := inferInstance) (Finset.univ.filter (fun i => c i ≠ 0))
    (fun _ => by simp) (fun i => f (x i))
  calc
    _ = ∑ i : {i // c i ≠ 0}, f (x i.val) := by
      simpa only [cutOutPositions,cutOrder,Equiv.trans_apply,Equiv.symm_apply_apply,
        Equiv.sumCongr_apply,Sum.map_inr,Equiv.sumCompl_apply_inr] using he
    _ = ∑ i ∈ Finset.univ.filter (fun i => c i ≠ 0), f (x i) := hs.symm
    _ = _ := Finset.sum_filter _ _

def outerDeletedCount {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) : ℝ :=
  ∑ i, if t-7*b ≤ ‖u i-y‖ then 1 else 0

lemma outerDeletedCount_nonneg {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) :
    0 ≤ outerDeletedCount y t b u := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> norm_num

lemma outerDeletedCount_le {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) :
    outerDeletedCount y t b u ≤ M := by
  calc
    _ ≤ ∑ _ : Fin M, (1:ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
    _ = M := by simp

lemma outerDeletedCount_measurable {M : ℕ} (y : Space) (t b : ℝ) :
    Measurable (outerDeletedCount (M := M) y t b) := by
  apply Finset.measurable_sum; intro i _
  exact Measurable.ite (measurableSet_le measurable_const (configuration_distance_measurable y i))
    measurable_const measurable_const

lemma outerDeletedCount_cutOutPositions {L : ℕ} (y : Space) (t b : ℝ)
    (c : Fin L → Fin 2) (x : Configuration L) :
    outerDeletedCount y t b (cutOutPositions c x) = cutDeletedCount y t b c x := by
  rw [outerDeletedCount,sum_cutOutPositions c x (fun z => if t-7*b ≤ ‖z-y‖ then 1 else 0)]
  unfold cutDeletedCount
  apply Finset.sum_congr rfl; intro i _
  split_ifs <;> simp_all

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_DeletedFieldBudget
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma sum_deleted_field_le_max {M : ℕ} (u : Configuration M) (y : Space) (t b : ℝ)
    (f : Fin M → ℝ) {F : ℝ} (hF : ∀ i, f i ≤ F) :
    (∑ i, f i)-(∑ i ∈ Finset.univ.filter (fun i => ‖u i-y‖ < t-7*b), f i) ≤
      F*outerDeletedCount y t b u := by
  classical
  simp only [Finset.sum_filter,←Finset.sum_sub_distrib,outerDeletedCount,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : ‖u i-y‖ < t-7*b
  · simp only [hi,ite_eq_left,not_le.mpr hi,ite_false,mul_zero,sub_self,le_refl]
  · simp only [hi,ite_false,not_lt.mp hi,ite_eq_left,mul_one,sub_zero]
    exact hF i

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_PatchWeakPoisson
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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

namespace CoulombAtom
open CoulombAnalysis

theorem normalizedCoreField_weak_laplacian {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {g : Space → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) (Z lam : ℝ) :
    (∫ y, normalizedCoreField Z lam ψ y*Δ g y) =
      (Z*formMass ψ*(-(4*Real.pi*g 0))-
        ∑ s, ∑ i : Fin N, ∫ x, ‖ψ.value s x‖^2*(-(4*Real.pi*g (x i))))/formMass ψ := by
  obtain ⟨B,hB⟩ := (tfLaplacian_compact hg hcg).exists_bound_of_continuous (tfLaplacian_continuous hg)
  rw [normalizedCoreField_pairing hψ (tfLaplacian_continuous hg).measurable hcg
    (tfLaplacian_support hg) (fun x => by simpa only [Real.norm_eq_abs] using hB x),
    compact_laplacian_mass hg hcg,mul_zero,sub_zero,tfPotential_laplacian hg hcg]
  simp only [coreDensityInteraction]
  simp_rw [tfPotential_laplacian hg hcg]

theorem normalizedCoreField_weak_harmonic {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) {g : Space → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) (h0 : g 0 = 0)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hgA : ∀ z ∈ A, g z = 0) (Z lam : ℝ) :
    (∫ y, normalizedCoreField Z lam ψ y*Δ g y) = 0 := by
  rw [normalizedCoreField_weak_laplacian hψ hg hcg Z lam,h0]
  have hz : ∀ s, ∀ i : Fin N, (∫ x, ‖ψ.value s x‖^2*(-(4*Real.pi*g (x i)))) = 0 := by
    intro s i
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    by_cases hx : x i ∈ A
    · simp [hgA (x i) hx]
    · simp [(hcore x i hx s).1]
  simp only [hz,Finset.sum_const_zero,mul_zero,neg_zero,sub_self,zero_div]

end CoulombAtom

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma normalizedCoreField_weak_harmonic_ball {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (A : Set Space)
    (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (y : Space) (R : ℝ) (hnuc : (0 : Space) ∉ ball y R)
    (hsep : ∀ a ∈ A, a ∉ ball y R)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 R) (Z lam : ℝ) :
    (∫ x, normalizedCoreField Z lam ψ (y+x)*Δ g x ∂ballMeasure R) = 0 := by
  let G : Space → ℝ := fun z => g (-y+z)
  have hG : ContDiff ℝ 2 G := hg.comp (contDiff_const.add contDiff_id)
  have hcG : HasCompactSupport G := hcg.comp_homeomorph (Homeomorph.addLeft (-y))
  have hz (a : Space) (ha : a ∉ ball y R) : G a = 0 := by
    apply Function.notMem_support.mp
    intro hn
    have hh := hs (subset_tsupport g hn)
    apply ha
    simpa only [mem_ball,dist_eq_norm,sub_zero,neg_add_eq_sub] using hh
  have he := normalizedCoreField_weak_harmonic hψ hG hcG (hz 0 hnuc) A hcore
    (fun a ha => hz a (hsep a ha)) Z lam
  have hl : Δ G = fun z => Δ g (-y+z) := tfLaplacian_translate g (-y)
  rw [hl] at he
  have hi := integral_add_left_eq_self (μ := volume)
    (fun z => normalizedCoreField Z lam ψ z*Δ g (-y+z)) y
  have he' : (∫ x, normalizedCoreField Z lam ψ (y+x)*Δ g x) = 0 := by
    simpa only [neg_add_cancel_left] using hi.trans he
  rw [ballMeasure,← integral_indicator measurableSet_ball]
  convert he' using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext x
  by_cases hx : x ∈ ball (0 : Space) R
  · simp [hx]
  · have hx0 : Δ g x = 0 := Function.notMem_support.mp
      (fun hh => hx (hs (tfLaplacian_support hg hh)))
    simp [hx,hx0]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_InnerPotential
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar
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

 lemma sourcePotential_pairing_integrable (mu : Measure Space) [IsFiniteMeasure mu]
    {h d : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) (hd : 0 < d)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hsg : tsupport g ⊆ {y | h+d ≤ ‖y‖}) :
    Integrable (fun p : Space × Space => (‖p.2-p.1‖)⁻¹*Δ g p.2)
      (mu.prod volume) := by
  have hi : Integrable (Δ g) := (tfLaplacian_continuous hg).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg)
  apply ((integrable_const (d⁻¹) : Integrable (fun _ : Space => d⁻¹) mu).mul_prod hi.norm).mono'
    (by have hc := tfLaplacian_continuous hg; fun_prop)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (by have hc := tfLaplacian_continuous hg; fun_prop)
    (by have hc := tfLaplacian_continuous hg; fun_prop))).mpr
  filter_upwards [hs] with a ha
  apply ae_of_all
  intro y
  rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  by_cases hz : Δ g y = 0
  · simp only [hz,norm_zero,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right
      (inv_anti₀ hd (inner_source_separation ha (hsg (tfLaplacian_support hg hz)))) (norm_nonneg _)

 lemma sourcePotential_weak_harmonic_separated (mu : Measure Space) [IsFiniteMeasure mu]
    {h d : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h) (hd : 0 < d)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hsg : tsupport g ⊆ {y | h+d ≤ ‖y‖}) :
    (∫ y, sourcePotential mu y*Δ g y) = 0 := by
  have hf := sourcePotential_pairing_integrable mu hs hd hg hcg hsg
  have he : (∫ y, sourcePotential mu y*Δ g y) =
      ∫ a, ∫ y, (‖y-a‖)⁻¹*Δ g y ∂volume ∂mu := by
    simp only [sourcePotential,← integral_mul_const]
    exact (integral_integral_swap hf).symm
  rw [he]
  apply integral_eq_zero_of_ae
  filter_upwards [hs] with a ha
  have hga : g a = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hh : h+d ≤ ‖a‖ := hsg hm
    linarith
  have hh := tfPotential_laplacian hg hcg a
  change (∫ y, Δ g y/‖a-y‖) = _ at hh
  simpa [norm_sub_rev,div_eq_mul_inv,mul_comm,hga] using hh

 theorem sourcePotential_weak_harmonic_exterior (mu : Measure Space) [IsFiniteMeasure mu]
    {h : ℝ} (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hsg : tsupport g ⊆ {y | h < ‖y‖}) :
    (∫ y, sourcePotential mu y*Δ g y) = 0 := by
  obtain ⟨d,hd,hdg⟩ := compact_exterior_separated hcg hsg
  exact sourcePotential_weak_harmonic_separated mu hs hd hg hcg hdg

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_InnerExterior
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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

 lemma sourceField_weak_harmonic (Z : ℝ) (mu : Measure Space) [IsFiniteMeasure mu]
     {h : ℝ} (hh : 0 ≤ h) (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h)
     {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
     (hsg : tsupport g ⊆ {y | h < ‖y‖}) :
     (∫ y, sourceField Z mu y*Δ g y) = 0 := by
   have hg0 : g 0 = 0 := by
     apply image_eq_zero_of_notMem_tsupport
     intro ht
     have hf : h < ‖(0 : Space)‖ := hsg ht
     simp only [norm_zero,not_lt_of_ge hh] at hf
   have hi : Integrable (fun y : Space => (Z/‖y‖)*Δ g y) :=
     continuousOn_mul_integrable_support hcg
       ((continuousOn_const.div continuous_norm.continuousOn
         (fun y hy => ne_of_gt (hh.trans_lt (hsg hy)))))
       (tfLaplacian_continuous hg) (tfLaplacian_support hg)
   have hj : Integrable (fun y : Space => sourcePotential mu y*Δ g y) :=
     continuousOn_mul_integrable_support hcg
       ((sourcePotential_continuousOn_exterior mu hs).mono hsg)
       (tfLaplacian_continuous hg) (tfLaplacian_support hg)
   have hn : (∫ y : Space, (Z/‖y‖)*Δ g y) = 0 := by
     have he : (fun y : Space => (Z/‖y‖)*Δ g y) =
         fun y => Z*(Δ g y/‖(0 : Space)-y‖) := by
       funext y
       simp only [zero_sub,norm_neg]
       ring
     rw [he,integral_const_mul]
     have ht := tfPotential_laplacian hg hcg (0 : Space)
     change (∫ y, Δ g y/‖(0 : Space)-y‖) = _ at ht
     rw [ht,hg0,mul_zero,neg_zero,mul_zero]
   simp only [sourceField,sub_mul]
   rw [integral_sub hi hj,hn,sourcePotential_weak_harmonic_exterior mu hs hg hcg hsg,sub_self]

 lemma sourceField_sub_const_weak (Z e : ℝ) (mu : Measure Space) [IsFiniteMeasure mu]
     {h : ℝ} (hh : 0 ≤ h) (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h)
     {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
     (hsg : tsupport g ⊆ {y | h < ‖y‖}) :
     (∫ y, (sourceField Z mu y-e)*Δ g y) = 0 := by
   have hi := continuousOn_mul_integrable_support hcg
     ((sourceField_continuousOn Z mu hh hs).mono hsg)
     (tfLaplacian_continuous hg) (tfLaplacian_support hg)
   have hj : Integrable (fun x => e*Δ g x) := ((tfLaplacian_continuous hg).integrable_of_hasCompactSupport
     (tfLaplacian_compact hg hcg)).const_mul e
   simp_rw [sub_mul]
   rw [integral_sub hi hj,sourceField_weak_harmonic Z mu hh hs hg hcg hsg,
     integral_const_mul,compact_laplacian_mass hg hcg,mul_zero,sub_self]

 theorem sourceField_exterior_comparison (Z : ℝ) (mu : Measure Space) [IsFiniteMeasure mu]
     {h R C : ℝ} (hh : 0 ≤ h) (hR : h < R) (hC : 0 ≤ C)
     (hs : ∀ᵐ a ∂mu, ‖a‖ ≤ h)
     (hb : ∀ y : Space, ‖y‖ = R → sourceField Z mu y ≤ C)
     {y : Space} (hy : R ≤ ‖y‖) : sourceField Z mu y ≤ C*R/‖y‖ := by
   have hRp : 0 < R := hh.trans_lt hR
   by_cases hfield : sourceField Z mu y ≤ 0
   · exact hfield.trans (div_nonneg (mul_nonneg hC hRp.le) (norm_nonneg y))
   apply le_of_forall_pos_le_add
   intro e he
   let T := max (‖y‖+1) ((|Z-C*R|+1)/e)
   have hyT : ‖y‖ < T := lt_of_lt_of_le (by linarith) (le_max_left _ _)
   have hRT : R < T := hy.trans_lt hyT
   have hT : 0 < T := hRp.trans hRT
   have hTe : |Z-C*R|+1 ≤ e*T := by
     have hv := (div_le_iff₀ he).mp (le_max_right (‖y‖+1) ((|Z-C*R|+1)/e))
     simpa only [T,mul_comm] using hv
   let K : Set Space := closedBall 0 T \ ball 0 R
   let v : Space → ℝ := fun x => sourceField (Z-C*R) mu x-e
   have hK : IsCompact K := (isCompact_closedBall (0 : Space) T).diff isOpen_ball
   have hKr : ∀ x ∈ K, R ≤ ‖x‖ := by
     intro x hx
     exact le_of_not_gt (fun ht => hx.2 (mem_ball_zero_iff.mpr ht))
   have hKT : ∀ x ∈ K, ‖x‖ ≤ T := fun _ hx => mem_closedBall_zero_iff.mp hx.1
   have hsub : K ⊆ {x | h < ‖x‖} := fun x hx => hR.trans_le (hKr x hx)
   have hiv : ContinuousOn v K := ((sourceField_continuousOn (Z-C*R) mu hh hs).mono hsub).sub continuousOn_const
   have hvi : ∀ x ∈ K, x ∉ interior K → v x ≤ 0 := by
     intro x hx hxi
     have hnorm : ‖x‖ = R ∨ ‖x‖ = T := by
       by_contra hne
       push Not at hne
       have hrx : R < ‖x‖ := lt_of_le_of_ne (hKr x hx) hne.1.symm
       have hxt : ‖x‖ < T := lt_of_le_of_ne (hKT x hx) hne.2
       have ho : IsOpen {z : Space | R < ‖z‖ ∧ ‖z‖ < T} :=
         (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
       apply hxi
       exact mem_interior.mpr ⟨{z : Space | R < ‖z‖ ∧ ‖z‖ < T},
         (fun z hz => ⟨mem_closedBall_zero_iff.mpr hz.2.le,
           fun hg => not_lt_of_ge hz.1.le (mem_ball_zero_iff.mp hg)⟩),ho,⟨hrx,hxt⟩⟩
     rcases hnorm with hrx | hxt
     · have hhx := hb x hrx
       have hex : v x = sourceField Z mu x-C-e := by
         dsimp [v,sourceField]
         rw [hrx]
         field_simp
         ring
       rw [hex]
       linarith
     · have hv := sourceField_le_nuclear (Z-C*R) mu x
       have hbound : (Z-C*R)/‖x‖ ≤ e := by
         rw [hxt]
         exact (div_le_iff₀ hT).mpr ((le_abs_self _).trans (by linarith [hTe]))
       dsimp [v]
       linarith
   have hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
       tsupport g ⊆ interior K ∩ {x | 0 < v x} → (∀ x, 0 ≤ g x) →
       0 ≤ ∫ x, v x*Δ g x := by
     intro g hg hcg hsg _
     exact (sourceField_sub_const_weak (Z-C*R) e mu hh hs hg hcg
       (hsg.trans (inter_subset_left.trans (interior_subset.trans hsub)))).ge
   have hvy := weak_subharmonic_positive_compact hK hiv hvi hw y
     (show y ∈ K from ⟨mem_closedBall_zero_iff.mpr hyT.le,
       fun ht => not_lt_of_ge hy (mem_ball_zero_iff.mp ht)⟩)
   have heq : v y = sourceField Z mu y-C*R/‖y‖-e := by
     dsimp [v,sourceField]
     ring
   rw [heq] at hvy
   linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RetainedInnerMassBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma rawBallCount_le_retainedPatch_mass {N : ℕ} {b a r R : ℝ} (hb : 0 < b)
    (hr : a+Real.sqrt 3*b ≤ r) (hR : r ≤ R)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    (hS : ∀ i, ‖x i-y‖ < a → i ∈ S) :
    rawBallCount y a x ≤ ∫ z in ball 0 r, retainedPatchLp hb S x y R z ∂ballMeasure R := by
  classical
  let T : Finset (Fin N) := Finset.univ.filter (fun i => ‖x i-y‖ < a)
  have hT : T ⊆ S := fun i hi => hS i (Finset.mem_filter.mp hi).2
  have hm : ∀ i ∈ T, ‖x i-y‖+Real.sqrt 3*b ≤ r := by
    intro i hi
    have hi0 := (Finset.mem_filter.mp hi).2
    linarith
  have he : rawBallCount y a x = (T.card:ℝ) := by
    exact Finset.sum_boole _ _
  rw [he]
  have hi : Integrable (fun z => retainedSmear b T x (y+z)) (ballMeasure r) :=
    (retainedPatch_memLp hb T x y r).integrable (Fact.out : (1:ENNReal) ≤ 5/3)
  have hj : Integrable (fun z => retainedSmear b S x (y+z)) (ballMeasure r) :=
    (retainedPatch_memLp hb S x y r).integrable (Fact.out : (1:ENNReal) ≤ 5/3)
  have hmass : (∫ z, retainedSmear b T x (y+z) ∂ballMeasure r) = (T.card:ℝ) :=
    (integral_congr_ae (retainedPatchLp_ae hb T x y r)).symm.trans
      (retainedPatchLp_mass hb T x y hm)
  rw [integral_congr_ae (ae_restrict_of_ae (retainedPatchLp_ae hb S x y R))]
  change _ ≤ ∫ z, retainedSmear b S x (y+z) ∂((volume.restrict (ball 0 R)).restrict (ball 0 r))
  rw [Measure.restrict_restrict_of_subset (ball_subset_ball hR)]
  change _ ≤ ∫ z, retainedSmear b S x (y+z) ∂ballMeasure r
  rw [←hmass]
  exact integral_mono hi hj (fun z => retainedSmear_mono hb hT x (y+z))

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_LocalWidthKernel
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LocalWidthKernel_scope

open Set Metric
open scoped NNReal

lemma widthKernel_ne_zero_distance {t : Space → ℝ} (ht : ∀ x, 0 < t x)
    {h : Space → ℝ} (hs : Function.support h ⊆ closedBall 0 1)
    {x y : Space} (hx : widthKernel t h x y ≠ 0) : ‖x-y‖ ≤ t x := by
  have hh : h ((t x)⁻¹ • (y-x)) ≠ 0 := by
    intro H; exact hx (by simp [widthKernel,H])
  have hr := hs hh
  simp only [mem_closedBall,dist_zero_right,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (ht x).le),norm_sub_rev y x] at hr
  rwa [inv_mul_eq_div,div_le_one (ht x)] at hr

lemma widthKernel_eq_zero_of_far {t : Space → ℝ} (ht : ∀ x, 0 < t x)
    {h : Space → ℝ} (hs : Function.support h ⊆ closedBall 0 1)
    {x y : Space} (hx : t x < ‖x-y‖) : widthKernel t h x y = 0 := by
  by_contra hn
  exact (not_le.mpr hx) (widthKernel_ne_zero_distance ht hs hn)

lemma widthKernel_support_local {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1/2)
    {h : Space → ℝ} (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    Function.support (fun x => widthKernel t h x y) ⊆ closedBall y (2*t y) := by
  intro x hx
  have ha := widthKernel_ne_zero_distance hp hs hx
  have hd := ht.dist_le_mul x y
  have hb : t x-t y ≤ (T:ℝ)*‖x-y‖ := by
    simpa only [Real.dist_eq,dist_eq_norm] using (le_abs_self (t x-t y)).trans hd
  have hc := mul_le_mul_of_nonneg_right hT (norm_nonneg (x-y))
  simp only [mem_closedBall,dist_eq_norm]
  linarith

lemma widthKernel_clamp {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1)
    {h : Space → ℝ} (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    (fun x => widthKernel t h x y) =
      (fun x => widthKernel (fun z => max (t z) (t y/2)) h x y) := by
  funext x
  by_cases hx : t y/2 ≤ t x
  · simp only [widthKernel,max_eq_left hx]
  have hx' : t x < t y/2 := lt_of_not_ge hx
  have hd := ht.dist_le_mul y x
  have hb : t y-t x ≤ (T:ℝ)*‖x-y‖ := by
    simpa only [Real.dist_eq,dist_eq_norm,norm_sub_rev y x] using (le_abs_self (t y-t x)).trans hd
  have hc := mul_le_mul_of_nonneg_right hT (norm_nonneg (x-y))
  have hf : t y/2 < ‖x-y‖ := by linarith
  have hz := widthKernel_eq_zero_of_far hp hs (hx'.trans hf)
  have hp' (z : Space) : 0 < max (t z) (t y/2) := (hp z).trans_le (le_max_left _ _)
  have hf' : max (t x) (t y/2) < ‖x-y‖ := by rwa [max_eq_right hx'.le]
  rw [hz,widthKernel_eq_zero_of_far hp' hs hf']

lemma widthKernel_local_lipschitz {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1/2)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    LipschitzWith ⟨(24*M+24*(H:ℝ))*(t y)⁻¹^4, by positivity⟩
      (fun x => widthKernel t h x y) := by
  rw [widthKernel_clamp ht hp (by linarith) hs y]
  have hq : 0 < t y/2 := half_pos (hp y)
  have hl (x : Space) : t y/2 ≤ max (t x) (t y/2) := le_max_right _ _
  apply (widthKernel_lipschitz (ht.max_const (t y/2)) hq hl hh hM hb hs y).weaken
  change (3*M*(T:ℝ)+(H:ℝ)*(1+(T:ℝ)))*(t y/2)⁻¹^4 ≤
    (24*M+24*(H:ℝ))*(t y)⁻¹^4
  have hcoeff : 16*(3*M*(T:ℝ)+(H:ℝ)*(1+(T:ℝ))) ≤ 24*M+24*(H:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hT hM,mul_le_mul_of_nonneg_left hT H.coe_nonneg]
  have he : (t y/2)⁻¹^4 = 16*(t y)⁻¹^4 := by rw [inv_div]; ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (inv_nonneg.mpr (hp y).le) 4)]

end Work_LocalWidthKernel_scope

open MeasureTheory Set Metric
open scoped NNReal ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_IntegrableCutTower
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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

def rawLocalPotential {N : ℕ} (y : Space) (q : ℝ) (x : Configuration N) : ℝ :=
  ∑ i, if ‖x i-y‖ < q then 1/‖x i-y‖ else 0

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_PatchContinuity
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar
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

lemma coreCoulombAt_continuousOn_separated {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (A B : Set Space)
    (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ a ∈ A, ∀ z ∈ B, d ≤ ‖a-z‖) : ContinuousOn (coreCoulombAt ψ) B := by
  apply continuousOn_finsetSum
  intro s _
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_of_dominated (bound := fun x => ‖ψ.value s x‖^2/d)
  · intro z _
    exact (((hψ.1 s).aestronglyMeasurable.aemeasurable.norm.pow_const 2).div
      (((continuous_apply i).sub continuous_const).norm.aemeasurable)).aestronglyMeasurable
  · intro z hz
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (norm_nonneg _))]
      by_cases hi : x i ∈ A
      · exact div_le_div_of_nonneg_left (sq_nonneg _) hd (hsep _ hi _ hz)
      · simp only [(hc x i hi s).1,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,le_refl]
  · exact ((hψ.1 s).integrable_norm_pow (by decide)).div_const d
  · exact Eventually.of_forall fun x => by
      by_cases hi : x i ∈ A
      · exact continuousOn_const.div
          ((continuous_const.sub continuous_id).norm.continuousOn)
          (fun z hz => (hd.trans_le (hsep _ hi _ hz)).ne')
      · simp only [(hc x i hi s).1,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div]
        exact continuousOn_const

lemma normalizedCoreField_continuousOn_patch {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (A : Set Space)
    (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (y : Space) (R : ℝ) {d r : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ) :
    ContinuousOn (fun x => normalizedCoreField Z lam ψ (y+x)) (closedBall 0 R) := by
  have hcore := coreCoulombAt_continuousOn_separated hψ A (closedBall y R) hc hd hsep
  have hh : ContinuousOn (normalizedCoreField Z lam ψ) (closedBall y R) :=
    ((continuousOn_const.div continuous_norm.continuousOn
      (fun z hz => (hr.trans_le (hnuc _ hz)).ne')).sub hcore |>.div_const _).sub continuousOn_const
  exact hh.comp (continuous_const.add continuous_id).continuousOn (fun x hx => by
    simpa only [mem_closedBall,dist_eq_norm,sub_zero,add_sub_cancel_left] using hx)

lemma actualPatchField_continuousOn {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (A : Set Space)
    (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (y : Space) (R : ℝ) {d r : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ)
    (f : TFLp (ballMeasure R)) :
    ContinuousOn (fun x => normalizedCoreField Z lam ψ (y+x)-tfBallPotential R f x)
      (closedBall 0 R) :=
  (normalizedCoreField_continuousOn_patch hψ A hc y R hd hr hnuc hsep Z lam).sub
    (tfBallPotential_continuous R f).continuousOn

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_DeletedPotential
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom

def outerDeletedPotential {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) : ℝ :=
  ∑ i, if t-7*b ≤ ‖u i-y‖ then 1/‖u i-y‖ else 0

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

def restrictWeakGraph (v : ι → E) (j : κ → ι) (F : weakGraph v) : weakGraph (v ∘ j) :=
  ⟨WithLp.toLp 2 (fun k => F.val (k.map j)), (mem_weakGraph _ _).mpr
    (fun k => (mem_weakGraph _ _).mp F.property (j k))⟩

end Restriction

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RootMomentCauchyBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
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

 def localOffsetMass (D : ℝ) (y : Space) : ℝ :=
    max (1/(localCellRadius y)^3) 1+Real.sqrt (D*localCellRadius y)

lemma localOffsetMass_one_le (D : ℝ) (y : Space) : 1 ≤ localOffsetMass D y := by
  unfold localOffsetMass
  linarith [le_max_right (1/localCellRadius y^3) 1,Real.sqrt_nonneg (D*localCellRadius y)]

lemma exists_localCountStencil : ∃ T : Finset Space,
    (∀ v ∈ T, ‖v‖ ≤ 32) ∧ ∀ x : Space, ‖x‖ ≤ 32 → ∃ v ∈ T, ‖x-v‖ < 1/4 := by
  classical
  let S := closedBall (0 : Space) 32
  have hc : S ⊆ ⋃ v : S, ball (v : Space) (1/4) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,by simp⟩
  obtain ⟨t,ht⟩ := (isCompact_closedBall (0 : Space) (32:ℝ)).elim_finite_subcover
    (fun v : S => ball (v : Space) (1/4)) (fun _ => isOpen_ball) hc
  refine ⟨t.image (fun v : S => (v : Space)),?_,?_⟩
  · intro v hv
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
    simpa only [S,mem_closedBall_iff_norm,sub_zero] using w.property
  · intro x hx
    have hxs : x ∈ S := by simpa only [S,mem_closedBall_iff_norm,sub_zero] using hx
    obtain ⟨v,hv,hxv⟩ := mem_iUnion₂.mp (ht hxs)
    exact ⟨v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,mem_ball_iff_norm.mp hxv⟩

 def localCountStencil : Finset Space := Classical.choose exists_localCountStencil
lemma localCountStencil_norm {v : Space} (hv : v ∈ localCountStencil) : ‖v‖ ≤ 32 :=
  (Classical.choose_spec exists_localCountStencil).1 v hv
lemma localCountStencil_cover {x : Space} (hx : ‖x‖ ≤ 32) :
    ∃ v ∈ localCountStencil, ‖x-v‖ < 1/4 :=
  (Classical.choose_spec exists_localCountStencil).2 x hx

lemma rawBallCount_le_cover {N : ℕ} (x : Configuration N) (y : Space) (R : ℝ)
    (T : Finset Space) (r : Space → ℝ)
    (hcover : ∀ z : Space, ‖z-y‖ < R → ∃ v ∈ T, ‖z-v‖ < r v) :
    rawBallCount y R x ≤ ∑ v ∈ T, rawBallCount v (r v) x := by
  classical
  unfold rawBallCount
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : ‖x i-y‖ < R
  · rw [ite_eq_left hx]
    obtain ⟨v,hv,hiv⟩ := hcover (x i) hx
    have hh := Finset.single_le_sum (f := fun w => if ‖x i-w‖ < r w then (1:ℝ) else 0)
      (fun _ _ => by split_ifs <;> norm_num) hv
    simpa only [ite_eq_left hiv] using hh
  · rw [ite_eq_right hx]
    exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FockKineticReindexBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

 def unorderedOutKinetic {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L) : ℝ :=
  (1/2:ℝ)*∑ b : Fin L → Fin 2, ∑ s : Spins L, ∑ i : Fin L,
    if b i = 1 then (∑ a : Fin 3, ∫ x,
      ‖(multiplyForm (spatialProduct p hp b) ψ).gradient s i a x‖^2) else 0

open MeasureTheory Filter
open scoped BigOperators

 def localGradientTrace {L : ℕ} (ψ : FormVector L) (q : SmoothMultiplier spaceDirections) : ℝ :=
   ∑ s : Spins L, ∑ i : Fin L, ∑ a : Fin 3,
     ∫ x : Configuration L, q.value (x i)^2*‖ψ.gradient s i a x‖^2

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BallAverageKernelBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BallAverageKernel_barrier_scope

open MeasureTheory Set Metric

open CoulombAnalysis

lemma space_closedBall_real (y : Space) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (closedBall y R) = R^3*(Real.pi*4/3) := by
  rw [Measure.real,EuclideanSpace.volume_closedBall_fin_three,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hR,ENNReal.toReal_ofReal (by positivity)]

def ballAverageKernel (R : ℝ) : Space → ℝ :=
  (closedBall 0 R).indicator (fun _ => 1/(R^3*(Real.pi*4/3)))

lemma ballAverageKernel_measurable (R : ℝ) : Measurable (ballAverageKernel R) :=
  measurable_const.indicator isClosed_closedBall.measurableSet

lemma ballAverageKernel_nonneg {R : ℝ} (hR : 0 < R) (z : Space) : 0 ≤ ballAverageKernel R z := by
  apply indicator_nonneg
  intro _ _
  positivity

lemma ballAverageKernel_support (R : ℝ) (z : Space) (hz : ballAverageKernel R z ≠ 0) : ‖z‖ ≤ R := by
  by_contra hh
  have hn : z ∉ closedBall (0:Space) R := by simpa only [mem_closedBall,dist_zero_right] using hh
  exact hz (by simp [ballAverageKernel,hn])

lemma ballAverageKernel_bound {R : ℝ} (hR : 0 < R) (z : Space) :
    |ballAverageKernel R z| ≤ 1/(R^3*(Real.pi*4/3)) := by
  by_cases hz : z ∈ closedBall (0:Space) R
  · simp only [ballAverageKernel,indicator_of_mem hz,abs_of_pos (by positivity : 0 < 1/(R^3*(Real.pi*4/3))),le_refl]
  · simp only [ballAverageKernel,indicator_of_notMem hz,abs_zero]
    positivity

lemma ballAverageKernel_radial (R : ℝ) : IsRadial (ballAverageKernel R) := by
  intro x y hxy
  simp only [ballAverageKernel,indicator,mem_closedBall,dist_zero_right,hxy]

lemma ballAverageKernel_mass {R : ℝ} (hR : 0 < R) : ∫ z, ballAverageKernel R z = 1 := by
  unfold ballAverageKernel
  rw [integral_indicator isClosed_closedBall.measurableSet,integral_const,
    Measure.real,Measure.restrict_apply_univ,smul_eq_mul,←Measure.real,space_closedBall_real 0 hR.le]
  field_simp

end Work_BallAverageKernel_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

lemma joinLists_empty {α : Type*} {N : ℕ} (x : Fin N → α) (y : Fin 0 → α) :
    joinLists x y = x := by
  funext i
  have hi : finSumFinEquiv (Sum.inl i : Fin N ⊕ Fin 0) = i := Fin.ext rfl
  simpa only [hi] using joinLists_left x y i

open MeasureTheory Set Metric
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CellCountSupremumBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators

namespace CoulombAtom

def localCountCoverConstant : ℝ := 1+64*(localCountStencil.card:ℝ)^2
lemma localCountCoverConstant_one_le : 1 ≤ localCountCoverConstant := by
  unfold localCountCoverConstant
  nlinarith [sq_nonneg (localCountStencil.card:ℝ)]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CellScaleBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma localOffsetMass_cube_le (D : ℝ) (y : Space) :
    1/(localCellRadius y)^3 ≤ localOffsetMass D y := by
  unfold localOffsetMass
  linarith [le_max_left (1/localCellRadius y^3) 1, Real.sqrt_nonneg (D*localCellRadius y)]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FreshInnerCountsBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter Metric
open scoped BigOperators

open MeasureTheory Set Filter Metric
open scoped BigOperators ContDiff

open CoulombAnalysis CoulombNeumann

def localPatchDensityCap (R : ℝ) : ℝ :=
  (tfPatchCapConstant/R^4/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)

lemma localPatchDensityCap_nonneg (R : ℝ) : 0 ≤ localPatchDensityCap R := by
  unfold localPatchDensityCap
  apply Real.rpow_nonneg
  exact div_nonneg (div_nonneg tfPatchCapConstant_pos.le (by positivity))
    (mul_nonneg (by norm_num) tfKinetic_pos.le)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_CellDensityBoundBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

 def cellDensityMassConstant : ℝ := (tfPatchCapConstant/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*(64*(Real.pi*4/3))
lemma cellDensityMassConstant_pos : 0 < cellDensityMassConstant := by
  unfold cellDensityMassConstant
  have hK := tfKinetic_pos
  have hC := tfPatchCapConstant_pos
  positivity

lemma cell_density_mass_bound {a m R : ℝ} (ha : 0 < a) (haR : a ≤ R) (h3 : 1/a^3 ≤ m) :
    localPatchDensityCap R*((4*a)^3*(Real.pi*4/3)) ≤ cellDensityMassConstant*m := by
  have hR := lt_of_lt_of_le ha haR
  let C := (tfPatchCapConstant/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)
  have hc : 0 ≤ C := by dsimp [C]; exact Real.rpow_nonneg (div_nonneg tfPatchCapConstant_pos.le (mul_nonneg (by norm_num) tfKinetic_pos.le)) _
  have hscale : localPatchDensityCap R = C/R^6 := by
    unfold localPatchDensityCap
    have he : tfPatchCapConstant/R^4/((5/3:ℝ)*tfKinetic) = (tfPatchCapConstant/((5/3:ℝ)*tfKinetic))/R^4 := by ring
    rw [he,cap_reaction_scale (div_nonneg tfPatchCapConstant_pos.le (mul_nonneg (by norm_num) tfKinetic_pos.le)) hR]
  have hh : localPatchDensityCap R ≤ C/a^6 := by
    rw [hscale]
    gcongr
  calc _ ≤ (C/a^6)*((4*a)^3*(Real.pi*4/3)) := by gcongr
       _ = cellDensityMassConstant*(1/a^3) := by unfold cellDensityMassConstant; dsimp [C]; field_simp; ring
       _ ≤ cellDensityMassConstant*m := mul_le_mul_of_nonneg_left h3 cellDensityMassConstant_pos.le

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_ActualUpperDeficitBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter Set
open scoped Topology

open CoulombAnalysis

 def quantumUpperDeficitConstant : ℝ :=
  1+(100000:ℝ)^4*(tfPatchCapConstant+1)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierDataSelectionBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAtom CoulombAnalysis CoulombObservation

structure InitialNumerics (Z : ℕ) (s ε G c δ : ℝ) : Prop where
  charge : 1 ≤ Z
  scale_pos : 0 < s
  scale_le : s ≤ 1
  radius_pos : 0 < ε*(Z:ℝ)^(-1/3:ℝ)
  radius_le : ε*(Z:ℝ)^(-1/3:ℝ) ≤ 1
  radius_scale : ε*(Z:ℝ)^(-1/3:ℝ) ≤ s
  radius_relation : (Z:ℝ)*(ε*(Z:ℝ)^(-1/3:ℝ))^3 = ε^3
  budget : 3*(Z:ℝ)*s^(-4:ℝ)+observationFisherConstant*(ε*(Z:ℝ)^(-1/3:ℝ))^(-2.02:ℝ)*
    (Real.log (Real.exp 1/(ε*(Z:ℝ)^(-1/3:ℝ))^40))^5+δ ≤ (Z:ℝ)^(7/3:ℝ)
  interpolation : (48*Real.pi*G*c⁻¹^3)*(ε*(Z:ℝ)^(-1/3:ℝ))^(1-3*masterExponent) ≤ 1/20

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FiniteBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

section
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

def actualInverseCap : ℝ := 100000^4*(16*(tfPatchCapConstant+3))

end
open MeasureTheory Filter Set Metric Laplacian
open scoped Topology
open CoulombAtom CoulombAnalysis

end CoulombBarrier

end

end OAI
end


