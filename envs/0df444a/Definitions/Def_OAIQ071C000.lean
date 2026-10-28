-- Prove2me | Definitions.Def_OAIQ071C000
-- name    : OAIQ071C000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T05:01:01.408447+00:00
-- url     : https://prove2.me/theorems/6e7cd46a-ee0c-4d0b-b981-67f13099e5d5
-- title:
--   Definitions bundle OAIQ071C000 of the split of OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 545 declarations of OpenAI's Lean: 126 definitions, 7 inductive types or structures, 19 instances and 393 theorems. The definitions and types are `OAI.CoulombAnalysis.IsRadial`, `OAI.CoulombAnalysis.NonnegDensity`, `OAI.CoulombAnalysis.PuncturedPoisson`, `OAI.CoulombAnalysis.TFChargeAnchor`, `OAI.CoulombAnalysis.TFField`, `OAI.CoulombAnalysis.TFLp`, `OAI.CoulombAnalysis.TFPriceData`, `OAI.CoulombAnalysis.TFSpace`, `OAI.CoulombAnalysis.TFUnitData`, `OAI.CoulombAnalysis.TFUnitData.charge`, `OAI.CoulombAnalysis.TFUnitData.chargeCap`, `OAI.CoulombAnalysis.TFUnitData.field`, `OAI.CoulombAnalysis.TFUnitData.radialField`, `OAI.CoulombAnalysis.TFUnitData.scale`, `OAI.CoulombAnalysis.TFUnitData.slopeCap`, `OAI.CoulombAnalysis.WeakSingularProfile`, `OAI.CoulombAnalysis.actualTFCoefficient`, `OAI.CoulombAnalysis.annularApproximationError`, `OAI.CoulombAnalysis.annularCoulomb`, `OAI.CoulombAnalysis.ballMeasure`, `OAI.CoulombAnalysis.boundedPatchRepresentative`, `OAI.CoulombAnalysis.coulombFar`, `OAI.CoulombAnalysis.coulombNear`, `OAI.CoulombAnalysis.coulombNearLp`, `OAI.CoulombAnalysis.coulombNearTranslate`, `OAI.CoulombAnalysis.densityWeight`, `OAI.CoulombAnalysis.gaussian`, `OAI.CoulombAnalysis.newtonMul`, `OAI.CoulombAnalysis.newtonMul₁`, `OAI.CoulombAnalysis.radialAxis`, `OAI.CoulombAnalysis.radialMass`, `OAI.CoulombAnalysis.radialMassIntegrand`, `OAI.CoulombAnalysis.radialPotential`, `OAI.CoulombAnalysis.radialTail`, `OAI.CoulombAnalysis.radialTailIntegrand`, `OAI.CoulombAnalysis.radialTrace`, `OAI.CoulombAnalysis.sphereMean`, `OAI.CoulombAnalysis.tfBallFunctional`, `OAI.CoulombAnalysis.tfBallGradient`, `OAI.CoulombAnalysis.tfBallLinear` and 93 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombIonization_Fermionic_Multiplier`, `CoulombIonization_FieldAnalysis_FiniteProfile`, `CoulombIonization_FieldAnalysis_LinearCoulomb`, `CoulombIonization_FieldAnalysis_Nonneg`, `CoulombIonization_FieldAnalysis_PatchWeakPoisson`, `CoulombIonization_FieldAnalysis_PuncturedGreenBarrier`, `CoulombIonization_FieldAnalysis_RadialPower`, `CoulombIonization_FieldAnalysis_SphericalMeanFieldBarrier`, `CoulombIonization_FormDomain_CoulombCoercivity`, `CoulombIonization_FormDomain_FermionicDensity`, `CoulombIonization_FormDomain_Form`, `CoulombIonization_FormDomain_TrialSmoothTest`, `CoulombIonization_FormDomain_WeakChangeVariables`, `CoulombIonization_FormDomain_WeakDerivative`, `CoulombIonization_FormDomain_WeakProduct`, `CoulombIonization_Ionization_ActualTFCoefficient`, `CoulombIonization_Ionization_TFPriceData`, `CoulombIonization_Localization_LipschitzMollifier`, `CoulombIonization_Localization_PacketDensity`, `CoulombIonization_Localization_RadialPacket`, `CoulombIonization_Localization_RadialPacketBase`, `CoulombIonization_RadialBounds_CorrectionPotentialSmallBarrier`, `CoulombIonization_RadialBounds_CoulombBallIntegral`, `CoulombIonization_RadialBounds_PatchMass`, `CoulombIonization_RadialBounds_Radial`, `CoulombIonization_RadialBounds_RadialAxis`, `CoulombIonization_RadialBounds_RadialPotentialSqrtDeriv`, `CoulombIonization_RadialBounds_SquareCompletion`, `CoulombIonization_RadialBounds_WeakSingularProfileBarrier`, `CoulombIonization_ThomasFermi_ActualPatchCap`, `CoulombIonization_ThomasFermi_CompactDirichletBound`, `CoulombIonization_ThomasFermi_Lp`, `CoulombIonization_ThomasFermi_Pairing`, `CoulombIonization_ThomasFermi_PatchCoulombControl`, `CoulombIonization_ThomasFermi_PatchTF`, `CoulombIonization_ThomasFermi_SommerfeldCoefficient`, `CoulombIonization_ThomasFermi_TFNonradialBarrier`, `CoulombIonization_ThomasFermi_TFNonradialOscillation`, `CoulombIonization_ThomasFermi_Tensor`, `CoulombIonization_ThomasFermi_TfDilation`, `CoulombIonization_ThomasFermi_TfEulerDensity`, `CoulombIonization_ThomasFermi_TfIncreasingData`, `CoulombIonization_ThomasFermi_TfInfiniteFieldDominatesDilation`, `CoulombIonization_ThomasFermi_TfPotential`, `CoulombIonization_ThomasFermi_TfPowerIntegralDeriv`, `CoulombIonization_ThomasFermi_TfReactionCoefficient`, `CoulombIonization_ThomasFermi_TfRotate`, `CoulombIonization_ThomasFermi_TfWeight`, `CoulombIonization_Variational_BoundedDensityPotential`, `CoulombIonization_Variational_CoulombNear`, `CoulombIonization_Variational_FatouIntegrable`, `CoulombIonization_Variational_FullCoulomb`, `CoulombIonization_Variational_InsertionSwap`, `CoulombIonization_Variational_PatchBounded`, `CoulombIonization_Variational_RootCoulomb`, `CoulombIonization_Variational_Slices`, `CoulombIonization_Variational_SmoothNewton`, `CoulombIonization_Variational_SpatialRotation`, `CoulombIonization_Variational_SpinJoinEquiv`, `CoulombIonization_Variational_SumPairsHalf`, `CoulombIonization_Variational_TensorLp`, `CoulombIonization_Variational_TruncatedCoulomb`, `CoulombIonization_Variational_WeightedVariance`.
--
--   **Imports.** It imports the published bundle `Def_CoulombIonization`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ071C003`, `OAIQ071C004` and `OAIQ071C005`.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombIonization

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakDerivative
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
section WeakDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]

def IsWeakDerivative (v : E) (f g : E → ℂ) : Prop :=
  ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, f x * Complex.ofReal (lineDeriv ℝ φ x v)) = -(∫ x, g x * (φ x : ℂ))

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma IsWeakDerivative.congr_ae {v : E} {f f' g g' : E → ℂ}
    (h : IsWeakDerivative v f g) (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    IsWeakDerivative v f' g' := by
  intro φ hφ hcφ
  rw [← integral_congr_ae (hf.mono fun x hx => congrArg (· * _) hx),
    ← integral_congr_ae (hg.mono fun x hx => congrArg (· * _) hx)]
  exact h φ hφ hcφ

variable [IsLocallyFiniteMeasure (volume : Measure E)]

def l2Test (φ : E → ℝ) (hφ : MemLp (fun x => (φ x : ℂ)) 2) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] ℂ :=
  innerSL ℂ (hφ.toLp (fun x => (φ x : ℂ)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)] in
lemma l2Test_apply (φ : E → ℝ) (hφ : MemLp (fun x => (φ x : ℂ)) 2)
    (f : Lp ℂ 2 (volume : Measure E)) :
    l2Test φ hφ f = ∫ x, f x * (φ x : ℂ) := by
  change ⟪hφ.toLp (fun x => (φ x : ℂ)), f⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, Complex.conj_ofReal]

lemma test_memLp {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    MemLp (fun x => (φ x : ℂ)) 2 :=
  (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
    (hcφ.comp_left (by simp))

lemma test_deriv_memLp {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (v : E) :
    MemLp (fun x => Complex.ofReal (lineDeriv ℝ φ x v)) 2 := by
  have hEq : (fun x => lineDeriv ℝ φ x v) = fun x => fderiv ℝ φ x v := by
    funext x
    exact (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv
  change MemLp (Complex.ofReal ∘ (fun x => lineDeriv ℝ φ x v)) 2
  rw [hEq]
  exact (Complex.continuous_ofReal.comp
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    ).memLp_of_hasCompactSupport
      (((hcφ.fderiv ℝ).comp_left (g := fun A : E →L[ℝ] ℝ => A v) (by simp)
        ).comp_left (by simp))

variable {ι : Type*} [Fintype ι]

abbrev WeakGraphAmbient (E : Type*) [NormedAddCommGroup E] [MeasureSpace E] (ι : Type*) :=
  PiLp 2 (fun _ : Option ι => Lp ℂ 2 (volume : Measure E))

def weakGraphTest (v : ι → E) (i : ι) (φ : E → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    WeakGraphAmbient E ι →L[ℂ] ℂ :=
  (l2Test (fun x => lineDeriv ℝ φ x (v i)) (test_deriv_memLp hφ hcφ (v i))).comp
      (PiLp.proj 2 (fun _ : Option ι => Lp ℂ 2 (volume : Measure E)) none) +
    (l2Test φ (test_memLp hφ hcφ)).comp
      (PiLp.proj 2 (fun _ : Option ι => Lp ℂ 2 (volume : Measure E)) (some i))

def weakGraph (v : ι → E) : Submodule ℂ (WeakGraphAmbient E ι) :=
  ⨅ (i : ι) (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ),
    (weakGraphTest v i φ hφ hcφ).ker

omit [Fintype ι] in
lemma mem_weakGraph (v : ι → E) (F : WeakGraphAmbient E ι) :
    F ∈ weakGraph v ↔ ∀ i, IsWeakDerivative (v i) (F none) (F (some i)) := by
  simp [weakGraph, weakGraphTest, l2Test_apply, IsWeakDerivative, eq_neg_iff_add_eq_zero]

omit [Fintype ι] in
lemma weakGraph_isClosed (v : ι → E) : IsClosed (weakGraph v : Set (WeakGraphAmbient E ι)) := by
  simp only [weakGraph, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun φ => isClosed_iInter fun hφ =>
    isClosed_iInter fun hcφ => (weakGraphTest v i φ hφ hcφ).isClosed_ker

instance weakGraph_completeSpace (v : ι → E) : CompleteSpace (weakGraph v) :=
  (weakGraph_isClosed v).completeSpace_coe

def weakGraphValue (v : ι → E) : weakGraph v →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (PiLp.proj 2 (fun _ : Option ι => Lp ℂ 2 (volume : Measure E)) none).comp
    (weakGraph v).subtypeL

end WeakDerivative

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakChangeVariables
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

abbrev SectorHilbert (N : ℕ) := PiLp 2 (fun _ : Spins N => Lp ℂ 2 (volume : Measure (Configuration N)))

def permuteConfiguration {N : ℕ} (π : Equiv.Perm (Fin N)) : Configuration N ≃L[ℝ] Configuration N :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin N => Space) π.symm

@[simp] lemma permuteConfiguration_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    permuteConfiguration π x = x ∘ π := by
  ext i
  simp [permuteConfiguration, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft]

lemma permuteConfiguration_preserving {N : ℕ} (π : Equiv.Perm (Fin N)) :
    MeasurePreserving (permuteConfiguration π) := by
  exact volume_measurePreserving_piCongrLeft (fun _ : Fin N => Space) π.symm

def fermionPermutation {N : ℕ} (π : Equiv.Perm (Fin N)) : SectorHilbert N →L[ℂ] SectorHilbert N :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Spins N => Lp ℂ 2 (volume : Measure (Configuration N)))
    ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun s =>
      ((((Equiv.Perm.sign π : ℤ) : ℂ)) •
        (Lp.compMeasurePreservingₗᵢ ℂ (permuteConfiguration π)
          (permuteConfiguration_preserving π)).toContinuousLinearMap).comp
        (PiLp.proj 2 (fun _ : Spins N => Lp ℂ 2 (volume : Measure (Configuration N))) (s ∘ π)))

def fermionSpace (N : ℕ) : Submodule ℂ (SectorHilbert N) :=
  ⨅ π : Equiv.Perm (Fin N), (fermionPermutation π - ContinuousLinearMap.id ℂ _).ker

lemma mem_fermionSpace {N : ℕ} (F : SectorHilbert N) :
    F ∈ fermionSpace N ↔ ∀ π : Equiv.Perm (Fin N), fermionPermutation π F = F := by
  simp [fermionSpace, sub_eq_zero]

lemma fermionSpace_isClosed (N : ℕ) : IsClosed (fermionSpace N : Set (SectorHilbert N)) := by
  simp only [fermionSpace, Submodule.coe_iInf]
  exact isClosed_iInter fun π => (fermionPermutation π - ContinuousLinearMap.id ℂ _).isClosed_ker

abbrev sectorDirections (N : ℕ) : Fin N × Fin 3 → Configuration N := fun k => direction k.1 k.2

instance weakSectorGraph_normedAddCommGroup (N : ℕ) : NormedAddCommGroup (weakGraph (sectorDirections N)) :=
  Submodule.normedAddCommGroup _
instance weakSectorGraph_innerProductSpace (N : ℕ) : InnerProductSpace ℂ (weakGraph (sectorDirections N)) :=
  Submodule.innerProductSpace _
instance weakSectorGraph_normedSpace (N : ℕ) : NormedSpace ℂ (weakGraph (sectorDirections N)) :=
  Submodule.normedSpace _

abbrev SectorGraph (N : ℕ) := PiLp 2 (fun _ : Spins N => weakGraph (sectorDirections N))

instance sectorGraph_normedAddCommGroup (N : ℕ) : NormedAddCommGroup (SectorGraph N) :=
  PiLp.normedAddCommGroup 2 _
instance sectorGraph_innerProductSpace (N : ℕ) : InnerProductSpace ℂ (SectorGraph N) :=
  PiLp.innerProductSpace _
instance sectorGraph_normedSpace (N : ℕ) : NormedSpace ℂ (SectorGraph N) :=
  PiLp.normedSpace 2 ℂ _

def sectorGraphValue (N : ℕ) : SectorGraph N →L[ℂ] SectorHilbert N :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Spins N => Lp ℂ 2 (volume : Measure (Configuration N)))
    ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun s => (weakGraphValue (sectorDirections N)).comp
      (PiLp.proj 2 (fun _ : Spins N => weakGraph (sectorDirections N)) s))

@[simp] lemma sectorGraphValue_apply {N : ℕ} (F : SectorGraph N) (s : Spins N) :
    sectorGraphValue N F s = (F s).val none := rfl

def fermionGraph (N : ℕ) : Submodule ℂ (SectorGraph N) :=
  (fermionSpace N).comap (sectorGraphValue N).toLinearMap

instance fermionGraph_normedAddCommGroup (N : ℕ) : NormedAddCommGroup (fermionGraph N) :=
  Submodule.normedAddCommGroup _
instance fermionGraph_innerProductSpace (N : ℕ) : InnerProductSpace ℂ (fermionGraph N) :=
  Submodule.innerProductSpace _
instance fermionGraph_normedSpace (N : ℕ) : NormedSpace ℂ (fermionGraph N) :=
  Submodule.normedSpace _

lemma fermionGraph_isClosed (N : ℕ) : IsClosed (fermionGraph N : Set (SectorGraph N)) :=
  (fermionSpace_isClosed N).preimage (sectorGraphValue N).continuous

instance fermionGraph_completeSpace (N : ℕ) : CompleteSpace (fermionGraph N) :=
  (fermionGraph_isClosed N).completeSpace_coe

def fermionGraphValue (N : ℕ) : fermionGraph N →L[ℂ] fermionSpace N :=
  ((sectorGraphValue N).comp (fermionGraph N).subtypeL).codRestrict (fermionSpace N)
    (fun F => F.property)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FermionicDensity
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

@[simp] lemma fermionPermutation_apply {N : ℕ} (π : Equiv.Perm (Fin N))
    (F : SectorHilbert N) (s : Spins N) :
    fermionPermutation π F s = (((Equiv.Perm.sign π : ℤ) : ℂ)) •
      Lp.compMeasurePreserving (permuteConfiguration π) (permuteConfiguration_preserving π)
        (F (s ∘ π)) := rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_FatouIntegrable
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
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma integrable_of_nonneg_ae_limit {u : ℕ → α → ℝ} {f : α → ℝ}
    (hi : ∀ n, Integrable (u n) μ) (hf : AEStronglyMeasurable f μ)
    (h0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ u n x) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x)))
    {C : ℝ} (hb : ∀ n, (∫ x, u n x ∂μ) ≤ C) : Integrable f μ := by
  refine ⟨hf, (hasFiniteIntegral_iff_ofReal hf0).mpr ?_⟩
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  calc
    _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (u n x)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with x hx
      exact ((ENNReal.continuous_ofReal.tendsto (f x)).comp hx).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (u n x) ∂μ) atTop :=
      lintegral_liminf_le' (fun n => ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        (hi n).aestronglyMeasurable.aemeasurable)
    _ ≤ ENNReal.ofReal C := by
      apply liminf_le_of_frequently_le'
      exact (Eventually.of_forall fun n => by
        rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (h0 n)]
        exact ENNReal.ofReal_le_ofReal (hb n)).frequently

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SquareCompletion
attribute [-instance] _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution

namespace CoulombAtom

section SquareCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma derivative_norm_sq {f : E → ℂ} {point : E}
    (hf : DifferentiableAt ℝ f point) (v : E) :
    fderiv ℝ (fun y => ‖f y‖ ^ 2) point v = 2 * ⟪f point, fderiv ℝ f point v⟫_ℝ := by
  rw [hf.hasFDerivAt.norm_sq.fderiv]
  simp
  ring

lemma square_completion_pointwise {f : E → ℂ} {point : E}
    (hf : DifferentiableAt ℝ f point)
    (v : E) (b : ℝ) :
    ‖fderiv ℝ f point v + b • f point‖ ^ 2 =
      ‖fderiv ℝ f point v‖ ^ 2 + b ^ 2 * ‖f point‖ ^ 2 +
        b * fderiv ℝ (fun y => ‖f y‖ ^ 2) point v := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, derivative_norm_sq hf, real_inner_comm (fderiv ℝ f point v) (f point)]
  ring

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
lemma integrable_norm_sq_derivative {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hf2 : MemLp f 2) (v : E) (hdf2 : MemLp (fun x => fderiv ℝ f x v) 2) :
    Integrable (fun x => fderiv ℝ (fun y => ‖f y‖ ^ 2) x v) := by
  have hi := (hf2.norm.integrable_mul hdf2.norm).const_mul 2
  apply hi.mono'
    (((hf.norm_sq ℝ).continuous_fderiv (by simp)).clm_apply continuous_const
      ).aestronglyMeasurable
  filter_upwards [] with x
  rw [derivative_norm_sq (hf.differentiable (by simp) x), norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)

lemma square_completion_integral_of_memLp {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hf2 : MemLp f 2) {b : E → ℝ} (hb : ContDiff ℝ ∞ b) (v : E)
    (hdf2 : MemLp (fun x => fderiv ℝ f x v) 2)
    {B D : ℝ} (hbnd : ∀ x, ‖b x‖ ≤ B)
    (hdbnd : ∀ x, ‖fderiv ℝ b x v‖ ≤ D) :
    (∫ x, ‖fderiv ℝ f x v + b x • f x‖ ^ 2) =
      (∫ x, ‖fderiv ℝ f x v‖ ^ 2) + (∫ x, (b x) ^ 2 * ‖f x‖ ^ 2) -
        (∫ x, fderiv ℝ b x v * ‖f x‖ ^ 2) := by
  let q : E → ℝ := fun x => ‖f x‖ ^ 2
  have hq : ContDiff ℝ ∞ q := hf.norm_sq ℝ
  have iq : Integrable q := hf2.norm.integrable_sq
  have ik := hdf2.norm.integrable_sq
  have ibq : Integrable (fun x => (b x) ^ 2 * q x) :=
    iq.bdd_mul (hb.continuous.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbnd x) _)
  have idbq : Integrable (fun x => fderiv ℝ b x v * q x) :=
    iq.bdd_mul (((hb.continuous_fderiv (by simp)).clm_apply continuous_const
      ).aestronglyMeasurable) (Eventually.of_forall hdbnd)
  have ibdq : Integrable (fun x => b x * fderiv ℝ q x v) :=
    (integrable_norm_sq_derivative hf hf2 v hdf2).bdd_mul hb.continuous.aestronglyMeasurable
      (Eventually.of_forall hbnd)
  have ibq' : Integrable (fun x => b x * q x) :=
    iq.bdd_mul hb.continuous.aestronglyMeasurable (Eventually.of_forall hbnd)
  have hip : (∫ x, b x * fderiv ℝ q x v) = -(∫ x, fderiv ℝ b x v * q x) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable idbq ibdq ibq'
      (fun x _ => hb.differentiable (by simp) x)
      (fun x _ => hq.differentiable (by simp) x)
  calc
    _ = ∫ x, (‖fderiv ℝ f x v‖ ^ 2 + (b x) ^ 2 * q x) +
        b x * fderiv ℝ q x v :=
      integral_congr_ae (Eventually.of_forall fun x =>
        square_completion_pointwise (hf.differentiable (by simp) x) v (b x))
    _ = _ := by
      have hsum := integral_add (ik.add ibq) ibdq
      simp only [Pi.add_apply] at hsum
      rw [hsum, integral_add ik ibq, hip]
      rfl

lemma square_completion_bound_of_memLp {ι : Type*} [Fintype ι]
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (hf2 : MemLp f 2)
    {b : ι → E → ℝ} (hb : ∀ i, ContDiff ℝ ∞ (b i)) (v : ι → E)
    (hdf2 : ∀ i, MemLp (fun x => fderiv ℝ f x (v i)) 2)
    {B D : ι → ℝ} (hbb : ∀ i x, ‖b i x‖ ≤ B i)
    (hdb : ∀ i x, ‖fderiv ℝ (b i) x (v i)‖ ≤ D i)
    {V : E → ℝ} (hVq : Integrable (fun x => V x * ‖f x‖ ^ 2)) {C : ℝ}
    (hbnd : ∀ x, ∑ i, (b i x) ^ 2 ≤ C)
    (hdiv : ∀ x, V x ≤ ∑ i, fderiv ℝ (b i) x (v i)) :
    (∫ x, V x * ‖f x‖ ^ 2) ≤
      (∑ i, ∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2) + C * (∫ x, ‖f x‖ ^ 2) := by
  have iq : Integrable (fun x => ‖f x‖ ^ 2) := hf2.norm.integrable_sq
  have ib (i : ι) : Integrable (fun x => (b i x) ^ 2 * ‖f x‖ ^ 2) :=
    iq.bdd_mul ((hb i).continuous.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbb i x) _)
  have idb (i : ι) : Integrable (fun x => fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2) :=
    iq.bdd_mul (((hb i).continuous_fderiv (by simp)).clm_apply continuous_const
      ).aestronglyMeasurable (Eventually.of_forall (hdb i))
  have hbound (i : ι) : (∫ x, fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2) ≤
      (∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2) + (∫ x, (b i x) ^ 2 * ‖f x‖ ^ 2) := by
    have hn : 0 ≤ (∫ x : E, ‖fderiv ℝ f x (v i) + b i x • f x‖ ^ 2) :=
      integral_nonneg (fun x : E => sq_nonneg _)
    rw [square_completion_integral_of_memLp hf hf2 (hb i) (v i) (hdf2 i)
      (hbb i) (hdb i)] at hn
    linarith
  calc
    _ ≤ ∫ x, ∑ i, fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2 := by
      apply integral_mono hVq (integrable_finsetSum _ fun i _ => idb i)
      intro x
      simpa only [Finset.sum_mul, Pi.mul_apply] using
        mul_le_mul_of_nonneg_right (hdiv x) (sq_nonneg ‖f x‖)
    _ = ∑ i, ∫ x, fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2 :=
      integral_finsetSum _ fun i _ => idb i
    _ ≤ ∑ i, ((∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2) +
        (∫ x, (b i x) ^ 2 * ‖f x‖ ^ 2)) := Finset.sum_le_sum fun i _ => hbound i
    _ = (∑ i, ∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2) +
        ∫ x, ∑ i, (b i x) ^ 2 * ‖f x‖ ^ 2 := by
      rw [Finset.sum_add_distrib, integral_finsetSum _ fun i _ => ib i]
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      rw [← integral_const_mul]
      apply integral_mono (integrable_finsetSum _ fun i _ => ib i) (iq.const_mul C)
      intro x
      simpa only [Finset.sum_mul, Pi.mul_apply] using
        mul_le_mul_of_nonneg_right (hbnd x) (sq_nonneg ‖f x‖)

end SquareCompletion

def regularizedRadius (ε : ℝ) (x : Space) : ℝ := Real.sqrt (‖x‖ ^ 2 + ε ^ 2)

def radialField (ε : ℝ) (a : Fin 3) (x : Space) : ℝ := x a / regularizedRadius ε x

lemma regularizedRadius_pos {ε : ℝ} (hε : 0 < ε) (x : Space) :
    0 < regularizedRadius ε x := by
  apply Real.sqrt_pos.2
  positivity

lemma regularizedRadius_sq (ε : ℝ) (x : Space) :
    regularizedRadius ε x ^ 2 = ‖x‖ ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)

lemma regularizedRadius_smooth {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (regularizedRadius ε) := by
  apply (contDiff_id.norm_sq ℝ |>.add contDiff_const).sqrt
  intro x
  positivity

lemma radialField_smooth {ε : ℝ} (hε : 0 < ε) (a : Fin 3) :
    ContDiff ℝ ∞ (radialField ε a) :=
  (EuclideanSpace.proj a).contDiff.div (regularizedRadius_smooth hε)
    (fun x => (regularizedRadius_pos hε x).ne')

lemma radialField_fderiv {ε : ℝ} (hε : 0 < ε) (a : Fin 3) (x : Space) :
    fderiv ℝ (radialField ε a) x (EuclideanSpace.single a 1) =
      (regularizedRadius ε x)⁻¹ - (x a) ^ 2 / (regularizedRadius ε x) ^ 3 := by
  have ht := ((hasFDerivAt_id (𝕜 := ℝ) x).norm_sq).add_const (ε ^ 2)
  have hs := (Real.hasDerivAt_sqrt (by positivity : ‖x‖ ^ 2 + ε ^ 2 ≠ 0)
    ).comp_hasFDerivAt x ht
  have hi := (hasDerivAt_inv (regularizedRadius_pos hε x).ne').comp_hasFDerivAt x hs
  have hp := ((EuclideanSpace.proj a).hasFDerivAt (x := x)).mul hi
  change (fderiv ℝ ((EuclideanSpace.proj a : Space → ℝ) *
      ((fun y : ℝ => y⁻¹) ∘ regularizedRadius ε)) x) _ = _
  rw [hp.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul]
  simp [EuclideanSpace.proj, regularizedRadius]
  field_simp
  ring

lemma sum_coordinate_sq (x : Space) : ∑ a : Fin 3, (x a) ^ 2 = ‖x‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq x).symm

lemma coordinate_sq_le (x : Space) (a : Fin 3) : (x a) ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [← sum_coordinate_sq]
  exact Finset.single_le_sum (fun b _ => sq_nonneg (x b)) (Finset.mem_univ a)

lemma norm_le_regularizedRadius (ε : ℝ) (x : Space) : ‖x‖ ≤ regularizedRadius ε x := by
  calc
    ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))

lemma le_regularizedRadius {ε : ℝ} (hε : 0 ≤ ε) (x : Space) :
    ε ≤ regularizedRadius ε x := by
  calc
    ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε).symm
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg ‖x‖))

lemma radialField_norm_le {ε : ℝ} (hε : 0 < ε) (a : Fin 3) (x : Space) :
    ‖radialField ε a x‖ ≤ 1 := by
  have hr := regularizedRadius_pos hε x
  have hcoord : |x a| ≤ ‖x‖ := by
    have hh := coordinate_sq_le x a
    nlinarith [abs_nonneg (x a), sq_abs (x a), norm_nonneg x]
  change ‖x a / regularizedRadius ε x‖ ≤ 1
  rw [norm_div, Real.norm_eq_abs, Real.norm_of_nonneg hr.le, div_le_one hr]
  exact hcoord.trans (norm_le_regularizedRadius ε x)

lemma sum_radialField_sq_le {ε : ℝ} (hε : 0 < ε) (x : Space) :
    ∑ a : Fin 3, (radialField ε a x) ^ 2 ≤ 1 := by
  simp only [radialField, div_pow, ← Finset.sum_div, sum_coordinate_sq]
  apply (div_le_one (sq_pos_of_pos (regularizedRadius_pos hε x))).2
  rw [regularizedRadius_sq]
  exact le_add_of_nonneg_right (sq_nonneg ε)

lemma radialField_derivative_bounds {ε : ℝ} (hε : 0 < ε) (a : Fin 3) (x : Space) :
    0 ≤ fderiv ℝ (radialField ε a) x (EuclideanSpace.single a 1) ∧
      fderiv ℝ (radialField ε a) x (EuclideanSpace.single a 1) ≤ ε⁻¹ := by
  let r := regularizedRadius ε x
  have hr : 0 < r := regularizedRadius_pos hε x
  have hxr : (x a) ^ 2 ≤ r ^ 2 := by
    calc
      _ ≤ ‖x‖ ^ 2 := coordinate_sq_le x a
      _ ≤ _ := by rw [regularizedRadius_sq]; exact le_add_of_nonneg_right (sq_nonneg ε)
  have heq : r ^ 2 / r ^ 3 = r⁻¹ := by field_simp
  have hle : (x a) ^ 2 / r ^ 3 ≤ r⁻¹ := by
    rw [← heq]
    exact div_le_div_of_nonneg_right hxr (pow_nonneg hr.le _)
  rw [radialField_fderiv hε]
  constructor
  · exact sub_nonneg.mpr hle
  · calc
      r⁻¹ - (x a) ^ 2 / r ^ 3 ≤ r⁻¹ := sub_le_self _ (by positivity)
      _ ≤ ε⁻¹ := inv_anti₀ hε (le_regularizedRadius hε.le x)

lemma radialField_divergence {ε : ℝ} (hε : 0 < ε) (x : Space) :
    2 * ‖x‖ / (regularizedRadius ε x) ^ 2 ≤
      ∑ a : Fin 3, fderiv ℝ (radialField ε a) x (EuclideanSpace.single a 1) := by
  let r := regularizedRadius ε x
  have hr : 0 < r := regularizedRadius_pos hε x
  have hnr : ‖x‖ ^ 2 ≤ r ^ 2 := by rw [regularizedRadius_sq]; exact le_add_of_nonneg_right (sq_nonneg ε)
  have heq : r ^ 2 / r ^ 3 = r⁻¹ := by field_simp
  have hle : ‖x‖ ^ 2 / r ^ 3 ≤ r⁻¹ := by
    rw [← heq]
    exact div_le_div_of_nonneg_right hnr (pow_nonneg hr.le _)
  have hnorm : ‖x‖ / r ^ 2 ≤ r⁻¹ := by
    calc
      _ ≤ r / r ^ 2 := div_le_div_of_nonneg_right (norm_le_regularizedRadius ε x)
        (sq_nonneg _)
      _ = _ := by field_simp
  simp only [radialField_fderiv hε, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, sum_coordinate_sq]
  change 2 * ‖x‖ / r ^ 2 ≤ 3 * r⁻¹ - ‖x‖ ^ 2 / r ^ 3
  have heq2 : 2 * ‖x‖ / r ^ 2 = 2 * (‖x‖ / r ^ 2) := by ring
  rw [heq2]
  linarith

def regularizedCoulomb (ε : ℝ) (x : Space) : ℝ :=
  ‖x‖ / (regularizedRadius ε x) ^ 2

lemma regularizedCoulomb_nonneg (ε : ℝ) (x : Space) : 0 ≤ regularizedCoulomb ε x := by
  unfold regularizedCoulomb
  positivity

lemma regularizedCoulomb_le {ε : ℝ} (hε : 0 < ε) (x : Space) :
    regularizedCoulomb ε x ≤ ε⁻¹ := by
  let r := regularizedRadius ε x
  have hr : 0 < r := regularizedRadius_pos hε x
  calc
    _ ≤ r / r ^ 2 := div_le_div_of_nonneg_right (norm_le_regularizedRadius ε x) (sq_nonneg _)
    _ = r⁻¹ := by field_simp
    _ ≤ ε⁻¹ := inv_anti₀ hε (le_regularizedRadius hε.le x)

lemma regularizedCoulomb_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (regularizedCoulomb ε) :=
  continuous_norm.div ((regularizedRadius_smooth hε).continuous.pow 2)
    (fun x => pow_ne_zero _ (regularizedRadius_pos hε x).ne')

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_WeightedVariance
attribute [-instance] _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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
section WeightedVariance
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma weighted_integral_norm_sq_le {k : α → ℝ} {f : α → ℂ}
    (hk : Integrable k μ) (hk0 : ∀ᵐ x ∂μ, 0 ≤ k x) (hk1 : ∫ x, k x ∂μ = 1)
    (hkf : Integrable (fun x => k x • f x) μ)
    (hkf2 : Integrable (fun x => k x * ‖f x‖ ^ 2) μ) :
    ‖∫ x, k x • f x ∂μ‖ ^ 2 ≤ ∫ x, k x * ‖f x‖ ^ 2 ∂μ := by
  let m : ℂ := ∫ x, k x • f x ∂μ
  have hi : Integrable (fun x => ⟪m, k x • f x⟫_ℝ) μ := hkf.const_inner m
  have heq (x : α) : k x * ‖f x - m‖ ^ 2 =
      (k x * ‖f x‖ ^ 2 - 2 * ⟪m, k x • f x⟫_ℝ) + k x * ‖m‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm (f x) m]
    ring
  have hzero : 0 ≤ ∫ x, k x * ‖f x - m‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae (hk0.mono fun x hx => mul_nonneg hx (sq_nonneg _))
  have hint : (∫ x, k x * ‖f x - m‖ ^ 2 ∂μ) =
      (∫ x, k x * ‖f x‖ ^ 2 ∂μ) - ‖m‖ ^ 2 := by
    calc
      _ = ∫ x, (k x * ‖f x‖ ^ 2 - 2 * ⟪m, k x • f x⟫_ℝ) +
          k x * ‖m‖ ^ 2 ∂μ := integral_congr_ae (Eventually.of_forall heq)
      _ = ((∫ x, k x * ‖f x‖ ^ 2 ∂μ) - 2 * ⟪m, m⟫_ℝ) + ‖m‖ ^ 2 := by
        have hh := integral_add (hkf2.sub (hi.const_mul 2)) (hk.mul_const (‖m‖ ^ 2))
        simp only [Pi.sub_apply] at hh
        rw [hh, integral_sub hkf2 (hi.const_mul 2), integral_const_mul,
          integral_inner hkf m, integral_mul_const, hk1, one_mul]
      _ = _ := by rw [real_inner_self_eq_norm_sq]; ring
  rw [hint] at hzero
  exact sub_nonneg.mp hzero

end WeightedVariance

section FatouBound
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma integral_le_of_nonneg_ae_limit {u : ℕ → α → ℝ} {f : α → ℝ}
    (hi : ∀ n, Integrable (u n) μ) (hf : Integrable f μ)
    (h0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ u n x) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x)))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, (∫ x, u n x ∂μ) ≤ C) :
    (∫ x, f x ∂μ) ≤ C := by
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_eq_lintegral_ofReal hf hf0]
  calc
    _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (u n x)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with x hx
      exact ((ENNReal.continuous_ofReal.tendsto (f x)).comp hx).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (u n x) ∂μ) atTop :=
      lintegral_liminf_le' (fun n => ENNReal.continuous_ofReal.measurable.comp_aemeasurable
        (hi n).aestronglyMeasurable.aemeasurable)
    _ ≤ ENNReal.ofReal C := by
      apply liminf_le_of_frequently_le'
      exact (Eventually.of_forall fun n => by
        rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (h0 n)]
        exact ENNReal.ofReal_le_ofReal (hb n)).frequently

end FatouBound

section Mollification
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

lemma convolution_l2_contraction {k : E → ℝ} (hk : Continuous k)
    (hkc : HasCompactSupport k) (hk0 : ∀ x, 0 ≤ k x) (hk1 : ∫ x, k x = 1)
    {f : E → ℂ} (hf : MemLp f 2) :
    MemLp (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) 2 ∧
      (∫ x, ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 := by
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)
  let A := ContinuousLinearMap.mul ℝ ℝ
  have hik : Integrable k := hk.integrable_of_hasCompactSupport hkc
  have hif : LocallyIntegrable f := hf.locallyIntegrable (by norm_num)
  have hif2 : Integrable (fun x => ‖f x‖ ^ 2) := hf.norm.integrable_sq
  have hc : Continuous (k ⋆[L] f) := hkc.continuous_convolution_left L hk hif
  have hib : Integrable (k ⋆[A] (fun x => ‖f x‖ ^ 2)) :=
    hik.integrable_convolution A hif2
  have hbound (x : E) : ‖(k ⋆[L] f) x‖ ^ 2 ≤
      (k ⋆[A] (fun x => ‖f x‖ ^ 2)) x := by
    exact weighted_integral_norm_sq_le hik (Eventually.of_forall hk0) hk1
      ((hkc.convolutionExists_left L hk hif x).integrable)
      ((hkc.convolutionExists_left A hk hif2.locallyIntegrable x).integrable)
  have hisq : Integrable (fun x => ‖(k ⋆[L] f) x‖ ^ 2) :=
    hib.mono' (hc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hbound x)
  refine ⟨(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 hisq, ?_⟩
  calc
    _ ≤ ∫ x, (k ⋆[A] (fun x => ‖f x‖ ^ 2)) x := integral_mono hisq hib hbound
    _ = _ := by rw [integral_convolution A hik hif2, hk1]; simp [A]

lemma mollified_weak_derivative {k : E → ℝ} (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) {f g : E → ℂ} (hf : LocallyIntegrable f)
    (v : E)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y v)) =
        -(∫ y, g y * (φ y : ℂ))) (x : E) :
    fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x v =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) x := by
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)
  have hφ : ContDiff ℝ ∞ (fun y => k (x - y)) := hk.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport (fun y => k (x - y)) :=
    hkc.comp_homeomorph (Homeomorph.subLeft x)
  have hdφ (y : E) : lineDeriv ℝ (fun y => k (x - y)) y v =
      -(fderiv ℝ k (x - y) v) := by
    have hh := (hk.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    have hs := (hh.hasLineDerivAt v).lineDeriv
    simpa [Function.comp_def] using hs
  have hw := hweak (fun y => k (x - y)) hφ hcφ
  simp only [hdφ, Complex.ofReal_neg, mul_neg, integral_neg, neg_inj] at hw
  have hid : Integrable (fun y => (L.precompL E) (fderiv ℝ k (x - y)) (f y)) :=
    ((hkc.fderiv ℝ).convolutionExists_left (L.precompL E)
      (hk.continuous_fderiv (by simp)) hf x).integrable_swap
  rw [(hkc.hasFDerivAt_convolution_left L (hk.of_le (by simp)) hf x).fderiv,
    convolution_eq_swap, ContinuousLinearMap.integral_apply hid, convolution_eq_swap]
  simpa only [ContinuousLinearMap.precompL_apply, L, ContinuousLinearMap.lsmul_apply,
    Complex.real_smul, mul_comm] using hw

def shrinkingBump (n : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 * (1 / ((n : ℝ) + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E]
  [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
lemma shrinkingBump_tendsto :
    Tendsto (fun n => (shrinkingBump (E := E) n).rOut) atTop (𝓝 0) := by
  simpa [shrinkingBump] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

lemma weak_square_completion_bound {ι : Type*} [Fintype ι]
    {f : E → ℂ} {g : ι → E → ℂ} (hf : MemLp f 2) (hg : ∀ i, MemLp (g i) 2)
    (v : ι → E)
    (hweak : ∀ i (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v i))) =
        -(∫ y, g i y * (φ y : ℂ)))
    {b : ι → E → ℝ} (hb : ∀ i, ContDiff ℝ ∞ (b i))
    {B D : ι → ℝ} (hbb : ∀ i x, ‖b i x‖ ≤ B i)
    (hdb : ∀ i x, ‖fderiv ℝ (b i) x (v i)‖ ≤ D i)
    {V : E → ℝ} (hV : Continuous V) (hV0 : ∀ x, 0 ≤ V x)
    {BV C : ℝ} (hVC : ∀ x, ‖V x‖ ≤ BV) (hC : 0 ≤ C)
    (hbnd : ∀ x, ∑ i, (b i x) ^ 2 ≤ C)
    (hdiv : ∀ x, V x ≤ ∑ i, fderiv ℝ (b i) x (v i)) :
    (∫ x, V x * ‖f x‖ ^ 2) ≤
      (∑ i, ∫ x, ‖g i x‖ ^ 2) + C * (∫ x, ‖f x‖ ^ 2) := by
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
  · exact add_nonneg (Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _)
      (mul_nonneg hC (integral_nonneg fun x => sq_nonneg _))
  · intro n
    exact (square_completion_bound_of_memLp (hu n) (hu2 n).1 hb v
      (fun i => (hdu2 n i).1) hbb hdb (hVu n) hbnd hdiv).trans
      (add_le_add (Finset.sum_le_sum fun i _ => (hdu2 n i).2)
        (mul_le_mul_of_nonneg_left (hu2 n).2 hC))

end Mollification

lemma regularizedCoulomb_tendsto {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (x : Space) :
    Tendsto (fun n => regularizedCoulomb (ε n) x) atTop (𝓝 (1 / ‖x‖)) := by
  by_cases hx : x = 0
  · simp [hx, regularizedCoulomb]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hh := (tendsto_const_nhds (x := ‖x‖) (f := atTop)).div
      (tendsto_const_nhds.add (hε.pow 2))
      (by simpa using pow_ne_zero 2 hn : ‖x‖ ^ 2 + (0 : ℝ) ^ 2 ≠ 0)
    have heq : ‖x‖ / (‖x‖ ^ 2 + (0 : ℝ) ^ 2) = 1 / ‖x‖ := by
      simp only [zero_pow (by decide : 2 ≠ 0), add_zero]
      field_simp
    change Tendsto (fun n : ℕ => ‖x‖ / (‖x‖ ^ 2 + ε n ^ 2)) atTop
      (𝓝 (‖x‖ / (‖x‖ ^ 2 + (0 : ℝ) ^ 2))) at hh
    simpa only [regularizedCoulomb, regularizedRadius_sq, heq] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LinearCoulomb
attribute [-instance] _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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
section LinearCoulomb
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
lemma linear_radialField_fderiv (P : E →L[ℝ] Space) (v : E) {ε : ℝ}
    (hε : 0 < ε) (a : Fin 3) (x : E) :
    fderiv ℝ (fun y => radialField ε a (P y)) x v =
      fderiv ℝ (radialField ε a) (P x) (P v) := by
  have hh := ((radialField_smooth hε a).differentiable (by simp) (P x)).hasFDerivAt.comp x
    (P.hasFDerivAt (x := x))
  change (fderiv ℝ ((radialField ε a) ∘ P) x) _ = _
  rw [hh.fderiv]
  rfl

lemma linear_regularized_coulomb_bound (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1) {Z ε : ℝ}
    (hZ : 0 ≤ Z) (hε : 0 < ε) {f : E → ℂ} {g : Fin 3 → E → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    (∫ x, 2 * Z * regularizedCoulomb ε (P x) * ‖f x‖ ^ 2) ≤
      (∑ a, ∫ x, ‖g a x‖ ^ 2) + Z ^ 2 * (∫ x, ‖f x‖ ^ 2) := by
  let b : Fin 3 → E → ℝ := fun a x => Z * radialField ε a (P x)
  have hb (a : Fin 3) : ContDiff ℝ ∞ (b a) :=
    contDiff_const.mul ((radialField_smooth hε a).comp P.contDiff)
  have hdb (a : Fin 3) (x : E) : fderiv ℝ (b a) x (v a) =
        Z * fderiv ℝ (radialField ε a) (P x) (EuclideanSpace.single a 1) := by
    have hh := ((radialField_smooth hε a).comp P.contDiff).differentiable (by simp) x
    change DifferentiableAt ℝ (fun y : E => radialField ε a (P y)) x at hh
    change (fderiv ℝ (fun y : E => Z * radialField ε a (P y)) x) _ = _
    rw [(hh.hasFDerivAt.const_mul Z).fderiv]
    simp only [smul_apply, smul_eq_mul, linear_radialField_fderiv P _ hε, hPv]
  refine weak_square_completion_bound hf hg v hweak hb
    (B := fun _ => Z) (D := fun _ => Z * ε⁻¹) (BV := 2 * Z * ε⁻¹) (C := Z ^ 2)
    (V := fun x => 2 * Z * regularizedCoulomb ε (P x)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a x
    change ‖Z * radialField ε a (P x)‖ ≤ Z
    rw [norm_mul, Real.norm_of_nonneg hZ]
    exact (mul_le_mul_of_nonneg_left (radialField_norm_le hε a (P x)) hZ).trans_eq
      (mul_one Z)
  · intro a x
    rw [hdb, Real.norm_of_nonneg
      (mul_nonneg hZ (radialField_derivative_bounds hε a (P x)).1)]
    exact mul_le_mul_of_nonneg_left (radialField_derivative_bounds hε a (P x)).2 hZ
  · exact continuous_const.mul ((regularizedCoulomb_continuous hε).comp P.continuous)
  · intro x
    exact mul_nonneg (by positivity) (regularizedCoulomb_nonneg ε (P x))
  · intro x
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (regularizedCoulomb_nonneg ε (P x)))]
    exact mul_le_mul_of_nonneg_left (regularizedCoulomb_le hε (P x)) (by positivity)
  · positivity
  · intro x
    simp only [b, mul_pow, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (sum_radialField_sq_le hε (P x))
      (sq_nonneg Z)).trans_eq (mul_one _)
  · intro x
    simp only [hdb, ← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left (radialField_divergence hε (P x)) hZ
    simpa only [regularizedCoulomb, mul_div_assoc, mul_left_comm Z 2, mul_assoc] using hh

lemma linear_coulomb_integrable (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1)
    {f : E → ℂ} {g : Fin 3 → E → ℂ} (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    Integrable (fun x => ‖f x‖ ^ 2 / ‖P x‖) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have htε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let u : ℕ → E → ℝ := fun n x => regularizedCoulomb (ε n) (P x) * ‖f x‖ ^ 2
  have hi (n : ℕ) : Integrable (u n) := by
    apply hf.norm.integrable_sq.bdd_mul (c := (ε n)⁻¹)
      ((regularizedCoulomb_continuous (hε n)).comp P.continuous).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖regularizedCoulomb (ε n) (P x)‖ ≤ _
      rw [Real.norm_of_nonneg (regularizedCoulomb_nonneg (ε n) (P x))]
      exact regularizedCoulomb_le (hε n) (P x)
  refine integrable_of_nonneg_ae_limit hi
    ((hf.aestronglyMeasurable.norm.pow 2).div₀ P.continuous.norm.aestronglyMeasurable)
    (fun n => Eventually.of_forall fun x => mul_nonneg
      (regularizedCoulomb_nonneg (ε n) (P x)) (sq_nonneg _))
    (Eventually.of_forall fun x => div_nonneg (sq_nonneg _) (norm_nonneg _)) ?_
    (C := (∑ a, ∫ x, ‖g a x‖ ^ 2) + (∫ x, ‖f x‖ ^ 2)) ?_
  · exact Eventually.of_forall fun x => by
      have hh := (regularizedCoulomb_tendsto htε (P x)).mul_const (‖f x‖ ^ 2)
      have heq : (1 / ‖P x‖) * ‖f x‖ ^ 2 = ‖f x‖ ^ 2 / ‖P x‖ := by ring
      simpa only [heq] using hh
  · intro n
    have hb := linear_regularized_coulomb_bound P v hPv (le_refl (0 : ℝ) |>.trans zero_le_one)
      (hε n) hf hg hweak
    have hu0 : 0 ≤ ∫ x, u n x := integral_nonneg fun x => mul_nonneg
      (regularizedCoulomb_nonneg (ε n) (P x)) (sq_nonneg _)
    simp only [mul_one, one_pow, one_mul, mul_assoc, integral_const_mul] at hb
    change 2 * (∫ x, u n x) ≤ _ at hb
    linarith

lemma linear_coulomb_bound (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1) {Z : ℝ} (hZ : 0 ≤ Z)
    {f : E → ℂ} {g : Fin 3 → E → ℂ} (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    2 * Z * (∫ x, ‖f x‖ ^ 2 / ‖P x‖) ≤
      (∑ a, ∫ x, ‖g a x‖ ^ 2) + Z ^ 2 * (∫ x, ‖f x‖ ^ 2) := by
  have hnu := linear_coulomb_integrable P v hPv hf hg hweak
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have htε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let u : ℕ → E → ℝ :=
    fun n x => 2 * Z * regularizedCoulomb (ε n) (P x) * ‖f x‖ ^ 2
  have hi (n : ℕ) : Integrable (u n) := by
    apply hf.norm.integrable_sq.bdd_mul (c := 2 * Z * (ε n)⁻¹)
      (continuous_const.mul ((regularizedCoulomb_continuous (hε n)).comp
        P.continuous)).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖2 * Z * regularizedCoulomb (ε n) (P x)‖ ≤ _
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity)
        (regularizedCoulomb_nonneg (ε n) (P x)))]
      exact mul_le_mul_of_nonneg_left (regularizedCoulomb_le (hε n) (P x)) (by positivity)
  rw [← integral_const_mul]
  apply integral_le_of_nonneg_ae_limit hi (hnu.const_mul (2 * Z))
  · intro n
    exact Eventually.of_forall fun x => mul_nonneg
      (mul_nonneg (by positivity) (regularizedCoulomb_nonneg (ε n) (P x))) (sq_nonneg _)
  · exact Eventually.of_forall fun x => mul_nonneg (by positivity) (by positivity)
  · exact Eventually.of_forall fun x => by
      have hh := ((regularizedCoulomb_tendsto htε (P x)).const_mul (2 * Z)
        ).mul_const (‖f x‖ ^ 2)
      have heq : 2 * Z * (1 / ‖P x‖) * ‖f x‖ ^ 2 =
          2 * Z * (‖f x‖ ^ 2 / ‖P x‖) := by ring
      simpa only [heq] using hh
  · exact add_nonneg (Finset.sum_nonneg fun a _ => integral_nonneg fun x => sq_nonneg _)
      (mul_nonneg (sq_nonneg Z) (integral_nonneg fun x => sq_nonneg _))
  · intro n
    exact linear_regularized_coulomb_bound P v hPv hZ (hε n) hf hg hweak

end LinearCoulomb

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_RootCoulomb
attribute [-instance] _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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
variable {ι : Type*} [Fintype ι]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] [Fintype ι] in
lemma lp_norm_sq (f : Lp ℂ 2 (volume : Measure E)) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
  rw [integral_ofReal]
  rfl

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [Fintype ι] in
lemma div_sqrt_norm_sq (f : E → ℂ) (P : E →L[ℝ] Space) (x : E) :
    ‖f x / (Real.sqrt ‖P x‖ : ℂ)‖ ^ 2 = ‖f x‖ ^ 2 / ‖P x‖ := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (norm_nonneg _)]

def rootCoulombFn (v : ι → E) (P : E →L[ℝ] Space) (F : weakGraph v) : E → ℂ :=
  fun x => F.val none x / (Real.sqrt ‖P x‖ : ℂ)

omit [Fintype ι] in
lemma rootCoulombFn_memLp (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) (F : weakGraph v) :
    MemLp (rootCoulombFn v P F) 2 := by
  have hweak (a : Fin 3) : IsWeakDerivative (v (i a)) (F.val none) (F.val (some (i a))) :=
    (mem_weakGraph v F.val).mp F.property (i a)
  have hm : AEStronglyMeasurable (rootCoulombFn v P F) :=
    (Lp.memLp (F.val none)).aestronglyMeasurable.div₀
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp P.continuous.norm)
        ).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := linear_coulomb_integrable P (fun a => v (i a)) hP
    (Lp.memLp (F.val none)) (fun a => Lp.memLp (F.val (some (i a)))) hweak
  simpa only [rootCoulombFn, div_sqrt_norm_sq] using hi

def rootCoulombLp (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) (F : weakGraph v) :
    Lp ℂ 2 (volume : Measure E) := (rootCoulombFn_memLp v P i hP F).toLp _

omit [Fintype ι] in
lemma rootCoulombLp_norm_sq (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) (F : weakGraph v) :
    ‖rootCoulombLp v P i hP F‖ ^ 2 = ∫ x, ‖F.val none x‖ ^ 2 / ‖P x‖ := by
  rw [lp_norm_sq]
  apply integral_congr_ae
  filter_upwards [(rootCoulombFn_memLp v P i hP F).coeFn_toLp] with x hx
  change rootCoulombLp v P i hP F x = rootCoulombFn v P F x at hx
  rw [hx]
  exact div_sqrt_norm_sq _ P x

omit [Fintype ι] in
lemma rootCoulombLp_add (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) (F G : weakGraph v) :
    rootCoulombLp v P i hP (F + G) = rootCoulombLp v P i hP F + rootCoulombLp v P i hP G := by
  apply Lp.ext
  filter_upwards [(rootCoulombFn_memLp v P i hP (F + G)).coeFn_toLp,
    (rootCoulombFn_memLp v P i hP F).coeFn_toLp,
    (rootCoulombFn_memLp v P i hP G).coeFn_toLp,
    Lp.coeFn_add (rootCoulombLp v P i hP F) (rootCoulombLp v P i hP G),
    Lp.coeFn_add (F.val none) (G.val none)] with x h1 h2 h3 h4 h5
  change rootCoulombLp v P i hP (F + G) x = _ at h1
  rw [h1, h4]
  change _ = (rootCoulombLp v P i hP F x) + (rootCoulombLp v P i hP G x)
  change rootCoulombLp v P i hP F x = _ at h2
  change rootCoulombLp v P i hP G x = _ at h3
  rw [h2, h3]
  change ((F.val none + G.val none) x) / _ = _
  rw [h5]
  exact add_div _ _ _

omit [Fintype ι] in
lemma rootCoulombLp_smul (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) (c : ℂ) (F : weakGraph v) :
    rootCoulombLp v P i hP (c • F) = c • rootCoulombLp v P i hP F := by
  apply Lp.ext
  filter_upwards [(rootCoulombFn_memLp v P i hP (c • F)).coeFn_toLp,
    (rootCoulombFn_memLp v P i hP F).coeFn_toLp,
    Lp.coeFn_smul c (rootCoulombLp v P i hP F),
    Lp.coeFn_smul c (F.val none)] with x h1 h2 h3 h4
  change rootCoulombLp v P i hP (c • F) x = _ at h1
  change rootCoulombLp v P i hP F x = _ at h2
  rw [h1, h3]
  simp only [Pi.smul_apply]
  rw [h2]
  change ((c • F.val none) x) / _ = c • (rootCoulombFn v P F x)
  rw [h4]
  simp only [Pi.smul_apply, smul_eq_mul, rootCoulombFn, mul_div_assoc]

lemma rootCoulombLp_bound (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) (F : weakGraph v) :
    ‖rootCoulombLp v P i hP F‖ ≤ 2 * ‖F‖ := by
  have hb := linear_coulomb_bound P (fun a => v (i a)) hP (Z := 1) (by norm_num)
    (Lp.memLp (F.val none)) (fun a => Lp.memLp (F.val (some (i a))))
    (fun a => (mem_weakGraph v F.val).mp F.property (i a))
  simp only [mul_one, one_mul, one_pow, ← lp_norm_sq, ← rootCoulombLp_norm_sq v P i hP] at hb
  have hc (j : Option ι) : ‖F.val j‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le F.val j) 2
  have hs : (∑ a : Fin 3, ‖F.val (some (i a))‖ ^ 2) ≤ 3 * ‖F‖ ^ 2 := by
    calc
      _ ≤ ∑ _a : Fin 3, ‖F‖ ^ 2 := Finset.sum_le_sum fun _ _ => hc _
      _ = _ := by simp
  nlinarith [hc none, norm_nonneg (rootCoulombLp v P i hP F), norm_nonneg F]

def rootCoulombMap (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) :
    weakGraph v →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := rootCoulombLp v P i hP
      map_add' := rootCoulombLp_add v P i hP
      map_smul' := rootCoulombLp_smul v P i hP }
    2 (rootCoulombLp_bound v P i hP)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_FullCoulomb
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

def electronProjection {N : ℕ} (i : Fin N) : Configuration N →L[ℝ] Space :=
  ContinuousLinearMap.proj i

def graphComponent {N : ℕ} (s : Spins N) (k : Option (Fin N × Fin 3)) :
    fermionGraph N →L[ℂ] Lp ℂ 2 (volume : Measure (Configuration N)) :=
  (PiLp.proj 2 (fun _ : Option (Fin N × Fin 3) => Lp ℂ 2 (volume : Measure (Configuration N))) k
    ).comp ((weakGraph (sectorDirections N)).subtypeL.comp
      ((PiLp.proj 2 (fun _ : Spins N => weakGraph (sectorDirections N)) s).comp
        (fermionGraph N).subtypeL))

@[simp] lemma graphComponent_apply {N : ℕ} (s : Spins N) (k : Option (Fin N × Fin 3))
    (F : fermionGraph N) : graphComponent s k F = (F.val s).val k := rfl

def graphNuclear {N : ℕ} (s : Spins N) (i : Fin N) :
    fermionGraph N →L[ℂ] Lp ℂ 2 (volume : Measure (Configuration N)) :=
  (rootCoulombMap (sectorDirections N) (ContinuousLinearMap.proj i) (fun a => (i, a))
    (by intro a; simp [sectorDirections, direction])).comp
    ((PiLp.proj 2 (fun _ : Spins N => weakGraph (sectorDirections N)) s).comp
      (fermionGraph N).subtypeL)

def graphPair {N : ℕ} (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    fermionGraph N →L[ℂ] Lp ℂ 2 (volume : Measure (Configuration N)) :=
  (rootCoulombMap (sectorDirections N) (electronProjection i - electronProjection j)
    (fun a => (i, a)) (by
      intro a
      change direction i a i - direction i a j = EuclideanSpace.single a 1
      simp [direction, Ne.symm hij])).comp
    ((PiLp.proj 2 (fun _ : Spins N => weakGraph (sectorDirections N)) s).comp
      (fermionGraph N).subtypeL)

def coulombFormOperator (Z : ℝ) (N : ℕ) : fermionGraph N →L[ℂ] fermionGraph N :=
  (1 / 2 : ℂ) • (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
    (graphComponent s (some (i, a))).adjoint.comp (graphComponent s (some (i, a)))) -
  (Z : ℂ) • (∑ s : Spins N, ∑ i : Fin N, (graphNuclear s i).adjoint.comp (graphNuclear s i)) +
  (∑ s : Spins N, ∑ i : Fin N, ∑ j : Fin N,
    if h : i < j then (graphPair s i j (ne_of_lt h)).adjoint.comp (graphPair s i j (ne_of_lt h)) else 0)

def graphFormVector {N : ℕ} (F : fermionGraph N) : FormVector N where
  value := fun s x => (F.val s).val none x
  gradient := fun s i a x => (F.val s).val (some (i, a)) x

attribute [local irreducible] graphComponent graphNuclear graphPair

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoulombCoercivity
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
section CoulombCoercivity

@[simp] lemma fermionGraphValue_apply {N : ℕ} (F : fermionGraph N) (s : Spins N) :
    (fermionGraphValue N F).val s = (F.val s).val none := rfl

attribute [local irreducible] graphComponent graphNuclear graphPair fermionGraphValue

end CoulombCoercivity

lemma fermionPermutation_ae {N : ℕ} (π : Equiv.Perm (Fin N)) (F : SectorHilbert N)
    (s : Spins N) :
    (fun x => fermionPermutation π F s x) =ᵐ[volume]
      fun x => (((Equiv.Perm.sign π : ℤ) : ℂ)) * F (s ∘ π) (x ∘ π) := by
  rw [fermionPermutation_apply]
  filter_upwards [Lp.coeFn_smul (((Equiv.Perm.sign π : ℤ) : ℂ))
    (Lp.compMeasurePreserving (permuteConfiguration π) (permuteConfiguration_preserving π)
      (F (s ∘ π))),
    Lp.coeFn_compMeasurePreserving (F (s ∘ π)) (permuteConfiguration_preserving π)] with x hx hy
  simpa only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, permuteConfiguration_apply] using hx.trans (congrArg
    (fun z : ℂ => (((Equiv.Perm.sign π : ℤ) : ℂ)) * z) hy)

lemma mem_fermionSpace_ae {N : ℕ} (F : SectorHilbert N) :
    F ∈ fermionSpace N ↔ ∀ (π : Equiv.Perm (Fin N)) s, ∀ᵐ x,
      F (s ∘ π) (x ∘ π) = (((Equiv.Perm.sign π : ℤ) : ℂ)) * F s x := by
  rw [mem_fermionSpace]
  constructor
  · intro h π s
    have hp := fermionPermutation_ae π F s
    rw [h π] at hp
    filter_upwards [hp] with x hx
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs
    · simpa [hs] using hx.symm
    · simpa [hs] using congrArg Neg.neg hx.symm
  · intro h π
    apply PiLp.ext
    intro s
    apply Lp.ext
    filter_upwards [fermionPermutation_ae π F s, h π s] with x hx hy
    rw [hx, hy]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;> simp [hs]

def admissibleWeakGraph {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ) (s : Spins N) :
    weakGraph (sectorDirections N) := by
  let F : WeakGraphAmbient (Configuration N) (Fin N × Fin 3) := WithLp.toLp 2 fun k =>
    match k with
    | none => (hψ.1 s).toLp (ψ.value s)
    | some ia => (hψ.2.1 s ia.1 ia.2).toLp (ψ.gradient s ia.1 ia.2)
  refine ⟨F, (mem_weakGraph (sectorDirections N) F).mpr ?_⟩
  intro ia
  exact IsWeakDerivative.congr_ae (hψ.2.2.1 s ia.1 ia.2)
    (hψ.1 s).coeFn_toLp.symm (hψ.2.1 s ia.1 ia.2).coeFn_toLp.symm

@[simp] lemma admissibleWeakGraph_value {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ)
    (s : Spins N) : (admissibleWeakGraph ψ hψ s).val none = (hψ.1 s).toLp (ψ.value s) := rfl

@[simp] lemma admissibleWeakGraph_gradient {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ)
    (s : Spins N) (i : Fin N) (a : Fin 3) :
    (admissibleWeakGraph ψ hψ s).val (some (i, a)) =
      (hψ.2.1 s i a).toLp (ψ.gradient s i a) := rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakProduct
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
  [IsLocallyFiniteMeasure (volume : Measure E)]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] in
lemma smooth_lineDeriv_mul {p φ : E → ℝ} (hp : ContDiff ℝ ∞ p)
    (hφ : ContDiff ℝ ∞ φ) (x v : E) :
    lineDeriv ℝ (fun y => p y * φ y) x v =
      lineDeriv ℝ p x v * φ x + p x * lineDeriv ℝ φ x v := by
  rw [((hp.mul hφ).differentiable (by simp) x).lineDeriv_eq_fderiv,
    (hp.differentiable (by simp) x).lineDeriv_eq_fderiv,
    (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
  change (fderiv ℝ (p * φ) x) v = _
  rw [fderiv_mul (hp.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma IsWeakDerivative.mul_smooth {f g : E → ℂ} {v : E}
    (hw : IsWeakDerivative v f g) (hf : MemLp f 2) (hg : MemLp g 2)
    {p : E → ℝ} (hp : ContDiff ℝ ∞ p) :
    IsWeakDerivative v (fun x => (p x : ℂ) * f x)
      (fun x => (p x : ℂ) * g x + Complex.ofReal (lineDeriv ℝ p x v) * f x) := by
  intro φ hφ hcφ
  have htest := hw (fun x => p x * φ x) (hp.mul hφ) hcφ.mul_left
  have hdφ : Continuous (fun x => lineDeriv ℝ φ x v) := by
    have he : (fun x => lineDeriv ℝ φ x v) = fun x => fderiv ℝ φ x v := by
      funext x
      exact (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv
    rw [he]
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdp : Continuous (fun x => lineDeriv ℝ p x v) := by
    have he : (fun x => lineDeriv ℝ p x v) = fun x => fderiv ℝ p x v := by
      funext x
      exact (hp.differentiable (by simp) x).lineDeriv_eq_fderiv
    rw [he]
    exact (hp.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdφ : HasCompactSupport (fun x => lineDeriv ℝ φ x v) := by
    have he : (fun x => lineDeriv ℝ φ x v) = fun x => fderiv ℝ φ x v := by
      funext x
      exact (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv
    rw [he]
    exact (hcφ.fderiv ℝ).comp_left (g := fun A : E →L[ℝ] ℝ => A v) (by simp)
  have him (q : E → ℝ) (hq : Continuous q) (hcq : HasCompactSupport q)
      (u : E → ℂ) (hu : MemLp u 2) : Integrable (fun x => (q x : ℂ) * u x) := by
    have hq2 : MemLp (fun x => (q x : ℂ)) 2 :=
      (Complex.continuous_ofReal.comp hq).memLp_of_hasCompactSupport
        (hcq.comp_left (g := Complex.ofReal) (by rfl))
    exact hq2.integrable_mul hu
  have i1 := him (fun x => p x * lineDeriv ℝ φ x v)
    (hp.continuous.mul hdφ) hcdφ.mul_left f hf
  have i2 := him (fun x => lineDeriv ℝ p x v * φ x)
    (hdp.mul hφ.continuous) hcφ.mul_left f hf
  have i3 := him (fun x => p x * φ x)
    (hp.continuous.mul hφ.continuous) hcφ.mul_left g hg
  have he1 : (fun x => f x * Complex.ofReal (lineDeriv ℝ (fun y => p y * φ y) x v)) =
      fun x => ((lineDeriv ℝ p x v * φ x : ℝ) : ℂ) * f x +
        ((p x * lineDeriv ℝ φ x v : ℝ) : ℂ) * f x := by
    funext x
    rw [smooth_lineDeriv_mul hp hφ]
    push_cast
    ring
  rw [he1, integral_add i2 i1] at htest
  have he2 : (fun x => g x * ((p x * φ x : ℝ) : ℂ)) =
      fun x => ((p x * φ x : ℝ) : ℂ) * g x := by
    funext x
    ring
  rw [he2] at htest
  have he3 : (fun x => (p x : ℂ) * f x * Complex.ofReal (lineDeriv ℝ φ x v)) =
      fun x => ((p x * lineDeriv ℝ φ x v : ℝ) : ℂ) * f x := by
    funext x
    push_cast
    ring
  have he4 : (fun x => ((p x : ℂ) * g x + Complex.ofReal (lineDeriv ℝ p x v) * f x) * (φ x : ℂ)) =
      fun x => ((p x * φ x : ℝ) : ℂ) * g x +
        ((lineDeriv ℝ p x v * φ x : ℝ) : ℂ) * f x := by
    funext x
    push_cast
    ring
  rw [he3, he4, integral_add i3 i2]
  linear_combination htest

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Multiplier
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
namespace CoulombAtom
section Multiplier
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι]

structure SmoothMultiplier (v : ι → E) where
  value : E → ℝ
  regular : ContDiff ℝ ∞ value
  bound : ∃ C : ℝ, ∀ x, |value x| ≤ C
  gradient_bound : ∀ i, ∃ C : ℝ, ∀ x, |lineDeriv ℝ value x (v i)| ≤ C

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [IsLocallyFiniteMeasure (volume : Measure E)] in
lemma memLp_bounded_mul {p : E → ℝ} (hp : Continuous p)
    (hb : ∃ C : ℝ, ∀ x, |p x| ≤ C) {f : E → ℂ} (hf : MemLp f 2) :
    MemLp (fun x => (p x : ℂ) * f x) 2 := by
  obtain ⟨C, hC⟩ := hb
  have ht : MemLp (fun x => (p x : ℂ)) ⊤ := memLp_top_of_bound
    (Complex.continuous_ofReal.comp hp).aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa using hC x)
  exact hf.mul' ht

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [Fintype ι] in
lemma SmoothMultiplier.derivative_continuous {v : ι → E}
    (p : SmoothMultiplier v) (i : ι) :
    Continuous (fun x => lineDeriv ℝ p.value x (v i)) := by
  have he : (fun x => lineDeriv ℝ p.value x (v i)) =
      fun x => fderiv ℝ p.value x (v i) := by
    funext x
    exact (p.regular.differentiable (by simp) x).lineDeriv_eq_fderiv
  rw [he]
  exact (p.regular.continuous_fderiv (by simp)).clm_apply continuous_const

omit [Fintype ι] in
lemma SmoothMultiplier.value_memLp {v : ι → E} (p : SmoothMultiplier v)
    (F : weakGraph v) : MemLp (fun x => (p.value x : ℂ) * F.val none x) 2 :=
  memLp_bounded_mul p.regular.continuous p.bound (Lp.memLp _)

omit [Fintype ι] in
lemma SmoothMultiplier.gradient_memLp {v : ι → E} (p : SmoothMultiplier v)
    (F : weakGraph v) (i : ι) :
    MemLp (fun x => (p.value x : ℂ) * F.val (some i) x +
      Complex.ofReal (lineDeriv ℝ p.value x (v i)) * F.val none x) 2 :=
  (memLp_bounded_mul p.regular.continuous p.bound (Lp.memLp _)).add
    (memLp_bounded_mul (p.derivative_continuous i) (p.gradient_bound i) (Lp.memLp _))

def SmoothMultiplier.apply {v : ι → E} (p : SmoothMultiplier v) (F : weakGraph v) :
    weakGraph v := by
  let G : WeakGraphAmbient E ι := WithLp.toLp 2 fun k => match k with
    | none => (p.value_memLp F).toLp _
    | some i => (p.gradient_memLp F i).toLp _
  refine ⟨G, (mem_weakGraph v G).mpr ?_⟩
  intro i
  exact (((mem_weakGraph v F.val).mp F.property i).mul_smooth
    (Lp.memLp _) (Lp.memLp _) p.regular).congr_ae
      (p.value_memLp F).coeFn_toLp.symm (p.gradient_memLp F i).coeFn_toLp.symm

omit [Fintype ι] in
lemma SmoothMultiplier.apply_value {v : ι → E} (p : SmoothMultiplier v)
    (F : weakGraph v) :
    ((p.apply F).val none : E → ℂ) =ᵐ[volume] fun x => (p.value x : ℂ) * F.val none x :=
  (p.value_memLp F).coeFn_toLp

end Multiplier

structure FermionMultiplier (N : ℕ) extends SmoothMultiplier (sectorDirections N) where
  symmetric : ∀ (π : Equiv.Perm (Fin N)) (x : Configuration N), value (x ∘ π) = value x

def FermionMultiplier.apply {N : ℕ} (p : FermionMultiplier N) (F : fermionGraph N) :
    fermionGraph N := by
  let G : SectorGraph N := WithLp.toLp 2 fun s => p.toSmoothMultiplier.apply (F.val s)
  refine ⟨G, (mem_fermionSpace_ae (sectorGraphValue N G)).mpr ?_⟩
  intro π s
  have hl := (permuteConfiguration_preserving π).quasiMeasurePreserving.ae
    (p.toSmoothMultiplier.apply_value (F.val (s ∘ π)))
  filter_upwards [hl, p.toSmoothMultiplier.apply_value (F.val s),
    (mem_fermionSpace_ae (sectorGraphValue N F.val)).mp F.property π s] with x hx hy hz
  change (p.toSmoothMultiplier.apply (F.val (s ∘ π))).val none (x ∘ π) =
    (((Equiv.Perm.sign π : ℤ) : ℂ)) * (p.toSmoothMultiplier.apply (F.val s)).val none x
  simp only [sectorGraphValue_apply] at hz
  simp only [permuteConfiguration_apply] at hx
  rw [hx, hy, p.symmetric, hz]
  ring

attribute [local irreducible] graphNuclear graphPair graphComponent FermionMultiplier.apply

attribute [local irreducible] fermionGraphValue coulombFormOperator

attribute [local irreducible] formEnergy graphFormVector

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RadialPower
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
namespace CoulombPDE

lemma second_deriv_nonpos_of_localMax {f : ℝ → ℝ} {x : ℝ}
    (h : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra! hp
  have hmin := isLocalMin_of_deriv_deriv_pos hp h.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [h, hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hz := he.deriv.deriv_eq
  change deriv (deriv f) x = deriv (deriv (fun _ : ℝ => f x)) x at hz
  simp only [deriv_const, deriv_const'] at hz
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma second_deriv_line {f : E → ℝ} {x : E} (h : ContDiffAt ℝ 2 f x) (v : E) :
    deriv (deriv (fun t : ℝ => f (x + t • v))) 0 =
      (fderiv ℝ (fderiv ℝ f) x) v v := by
  let g : ℝ → E := fun t => x + t • v
  have hg (t : ℝ) : HasDerivAt g v t := by
    simpa [g] using ((hasDerivAt_id t).smul_const v).const_add x
  have hg0 : g 0 = x := by simp [g]
  have hc : ContinuousAt g 0 := (hg 0).continuousAt
  have he : deriv (fun t : ℝ => f (g t)) =ᶠ[𝓝 0]
      fun t => fderiv ℝ f (g t) v := by
    have hev := hc.eventually (hg0 ▸ h.eventually (by norm_num))
    filter_upwards [hev] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hg t)).deriv
  rw [he.deriv_eq]
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) (g 0) := by
    rw [hg0]
    exact (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := (hf'.hasFDerivAt.comp_hasDerivAt 0 (hg 0)).clm_apply (hasDerivAt_const 0 v)
  simpa only [Function.comp_def, hg0, map_zero, add_zero] using hd.deriv

lemma second_fderiv_nonpos_of_localMax {f : E → ℝ} {x : E}
    (h : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) (v : E) :
    (fderiv ℝ (fderiv ℝ f) x) v v ≤ 0 := by
  rw [← second_deriv_line h v]
  have hg : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
  have hm' : IsLocalMax (fun t : ℝ => f (x + t • v)) 0 := by
    simpa only [Function.comp_def] using
      (show IsLocalMax f ((fun t : ℝ => x + t • v) 0) by simpa using hm).comp_continuous (g := fun t : ℝ => x + t • v) hg
  exact second_deriv_nonpos_of_localMax hm'
    ((show ContinuousAt f (x + (0 : ℝ) • v) by simpa using h.continuousAt).comp (f := fun t : ℝ => x + t • v) hg)

variable [FiniteDimensional ℝ E]

lemma laplacian_nonpos_of_localMax {f : E → ℝ} {x : E}
    (h : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) : Δ f x ≤ 0 := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_nonpos
  intro i _
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using second_fderiv_nonpos_of_localMax h hm ((stdOrthonormalBasis ℝ E) i)

lemma laplacian_norm_sq (x : E) :
    Δ (fun y : E => ‖y‖ ^ 2) x = 2 * (Module.finrank ℝ E : ℝ) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, fderiv_norm_sq]
  rw [fderiv_const_smul (innerSL ℝ (E := E)).differentiableAt]
  simp only [ContinuousLinearMap.fderiv, smul_apply, nsmul_eq_mul]
  change (∑ i, 2 * @inner ℝ E _ ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) i)) = _
  simp [mul_comm]

theorem compact_maximum_principle [Nontrivial E] {K : Set E} (hK : IsCompact K)
    {u : E → ℝ} (hc : ContinuousOn u K)
    (hd : ∀ x ∈ interior K, ContDiffAt ℝ 2 u x)
    (hl : ∀ x ∈ interior K, 0 < u x → 0 ≤ Δ u x)
    (hb : ∀ x ∈ K, x ∉ interior K → u x ≤ 0) : ∀ x ∈ K, u x ≤ 0 := by
  intro x hx
  by_contra! hp
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let ε : ℝ := u x / (2 * (R ^ 2 + 1))
  have he : 0 < ε := div_pos hp (by positivity)
  have heq : ε * (2 * (R ^ 2 + 1)) = u x := by
    exact div_mul_cancel₀ _ (by positivity)
  let w : E → ℝ := fun y => u y + ε * (‖y‖ ^ 2 - R ^ 2)
  have hwu (y : E) (hy : y ∈ K) : w y ≤ u y := by
    have ht : ‖y‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg y) (hbound y hy) 2
    dsimp [w]
    nlinarith
  have hpx : 0 < w x := by
    dsimp [w]
    nlinarith [mul_nonneg he.le (sq_nonneg ‖x‖)]
  have hwc : ContinuousOn w K := hc.add (by fun_prop)
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hwc
  have hpy : 0 < w y := hpx.trans_le (hmax hx)
  have hiy : y ∈ interior K := by
    by_contra hi
    exact (not_lt_of_ge ((hwu y hy).trans (hb y hy hi))) hpy
  have hdy := hd y hiy
  have hn : ContDiffAt ℝ 2 (fun z : E => ‖z‖ ^ 2) y := (contDiff_norm_sq ℝ).contDiffAt
  have hpert : ContDiffAt ℝ 2 (fun z : E => ε * (‖z‖ ^ 2 - R ^ 2)) y :=
    contDiffAt_const.mul (hn.sub contDiffAt_const)
  change ContDiffAt ℝ 2 (ε • ((fun z : E => ‖z‖ ^ 2) - fun _ => R ^ 2)) y at hpert
  have hs : ContDiffAt ℝ 2 ((fun z : E => ‖z‖ ^ 2) - fun _ => R ^ 2) y :=
    hn.sub contDiffAt_const
  have hwlap : Δ w y = Δ u y + ε * (2 * (Module.finrank ℝ E : ℝ)) := by
    change (Δ (u + ε • ((fun z : E => ‖z‖ ^ 2) - fun _ => R ^ 2)) : E → ℝ) y = _
    rw [hdy.laplacian_add hpert, laplacian_smul ε hs,
      hn.laplacian_sub (show ContDiffAt ℝ 2 (fun _ : E => R ^ 2) y from contDiffAt_const), laplacian_const, laplacian_norm_sq]
    simp
  have hnonpos := laplacian_nonpos_of_localMax (hdy.add hpert)
    (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hiy))
  change Δ w y ≤ 0 at hnonpos
  rw [hwlap] at hnonpos
  have hdim : 0 < (Module.finrank ℝ E : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hnonneg := hl y hiy (hpy.trans_le (hwu y hy))
  nlinarith [mul_pos he (mul_pos (by norm_num : (0 : ℝ) < 2) hdim)]

lemma differentiableAt_deriv_of_contDiffAt {g : ℝ → ℝ} {r : ℝ}
    (h : ContDiffAt ℝ 2 g r) : DifferentiableAt ℝ (deriv g) r := by
  have hc : ContDiffAt ℝ 1 (deriv g) r :=
    (h.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffAt_const
  exact hc.differentiableAt (by norm_num)

omit [FiniteDimensional ℝ E] in
lemma second_deriv_norm_sq_comp {g : ℝ → ℝ} {x : E}
    (h : ContDiffAt ℝ 2 g (‖x‖ ^ 2)) (v : E) :
    (fderiv ℝ (fderiv ℝ (fun y : E => g (‖y‖ ^ 2))) x) v v =
      deriv (deriv g) (‖x‖ ^ 2) * (2 * inner ℝ x v) ^ 2 +
        deriv g (‖x‖ ^ 2) * (2 * ‖v‖ ^ 2) := by
  have hf : ContDiffAt ℝ 2 (fun y : E => g (‖y‖ ^ 2)) x :=
    h.comp x ((contDiff_norm_sq ℝ).contDiffAt)
  rw [← second_deriv_line hf v]
  let l : ℝ → E := fun t => x + t • v
  have hl (t : ℝ) : HasDerivAt l v t := by
    simpa [l] using ((hasDerivAt_id t).smul_const v).const_add x
  have hl0 : l 0 = x := by simp [l]
  have hq (t : ℝ) : HasDerivAt (fun t => ‖l t‖ ^ 2) (2 * inner ℝ (l t) v) t :=
    (hl t).norm_sq
  have hq0 : ‖l 0‖ ^ 2 = ‖x‖ ^ 2 := by rw [hl0]
  have he : deriv (fun t => g (‖l t‖ ^ 2)) =ᶠ[𝓝 0]
      fun t => deriv g (‖l t‖ ^ 2) * (2 * inner ℝ (l t) v) := by
    have hev := (hq 0).continuousAt.eventually (hq0 ▸ h.eventually (by norm_num))
    filter_upwards [hev] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasDerivAt.comp t (hq t)).deriv
  rw [he.deriv_eq]
  have hgd : HasDerivAt (deriv g) (deriv (deriv g) (‖x‖ ^ 2)) (‖l 0‖ ^ 2) := by
    simpa only [hl0] using (differentiableAt_deriv_of_contDiffAt h).hasDerivAt
  have hdg : HasDerivAt (fun t => deriv g (‖l t‖ ^ 2))
      (deriv (deriv g) (‖x‖ ^ 2) * (2 * inner ℝ x v)) 0 := by
    simpa only [Function.comp_def, hl0] using hgd.comp 0 (hq 0)
  have hdi : HasDerivAt (fun t => 2 * inner ℝ (l t) v) (2 * ‖v‖ ^ 2) 0 := by
    simpa only [inner_zero_right, zero_add, real_inner_self_eq_norm_sq] using
      ((hl 0).inner ℝ (hasDerivAt_const 0 v)).const_mul 2
  calc
    _ = (deriv (deriv g) (‖x‖ ^ 2) * (2 * inner ℝ x v)) * (2 * inner ℝ (l 0) v) +
        deriv g (‖l 0‖ ^ 2) * (2 * ‖v‖ ^ 2) := (hdg.mul hdi).deriv
    _ = _ := by rw [hl0]; ring

lemma laplacian_norm_sq_comp {g : ℝ → ℝ} {x : E}
    (h : ContDiffAt ℝ 2 g (‖x‖ ^ 2)) :
    Δ (fun y : E => g (‖y‖ ^ 2)) x =
      4 * ‖x‖ ^ 2 * deriv (deriv g) (‖x‖ ^ 2) +
        2 * (Module.finrank ℝ E : ℝ) * deriv g (‖x‖ ^ 2) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  simp_rw [second_deriv_norm_sq_comp h, (stdOrthonormalBasis ℝ E).norm_eq_one]
  simp only [one_pow, mul_one, mul_pow, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← mul_assoc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [(stdOrthonormalBasis ℝ E).sum_sq_inner_left]
  ring

def radialPower (a : ℝ) (x : E) : ℝ := (‖x‖ ^ 2) ^ a

omit [FiniteDimensional ℝ E] in
lemma radialPower_contDiffAt (a : ℝ) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (radialPower a) x :=
  (contDiff_norm_sq ℝ).contDiffAt.rpow_const_of_ne (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))

lemma laplacian_radialPower (a : ℝ) {x : E} (hx : x ≠ 0) :
    (Δ (radialPower a : E → ℝ) : E → ℝ) x =
      (4 * a * (a - 1) + 2 * (Module.finrank ℝ E : ℝ) * a) * radialPower (a - 1) x := by
  have ht : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hc : ContDiffAt ℝ 2 (fun t : ℝ => t ^ a) (‖x‖ ^ 2) :=
    contDiffAt_id.rpow_const_of_ne ht.ne'
  have hd : deriv (fun t : ℝ => t ^ a) = fun t => a * t ^ (a - 1) :=
    funext (fun t => Real.deriv_rpow_const t a)
  have hdd : deriv (deriv (fun t : ℝ => t ^ a)) (‖x‖ ^ 2) =
      a * (a - 1) * (‖x‖ ^ 2) ^ (a - 2) := by
    rw [hd]
    calc
      _ = a * ((a - 1) * (‖x‖ ^ 2) ^ ((a - 1) - 1)) :=
        ((Real.hasDerivAt_rpow_const (p := a - 1) (Or.inl ht.ne')).const_mul a).deriv
      _ = _ := by rw [show a - 1 - 1 = a - 2 by ring]; ring
  have hmul : ‖x‖ ^ 2 * (‖x‖ ^ 2) ^ (a - 2) = (‖x‖ ^ 2) ^ (a - 1) := by
    rw [Real.rpow_sub ht a 2, Real.rpow_sub ht a 1, Real.rpow_two, Real.rpow_one]
    field_simp
  unfold radialPower
  rw [laplacian_norm_sq_comp hc, hdd, Real.deriv_rpow_const]
  calc
    _ = 4 * a * (a - 1) * (‖x‖ ^ 2 * (‖x‖ ^ 2) ^ (a - 2)) +
        2 * (Module.finrank ℝ E : ℝ) * a * (‖x‖ ^ 2) ^ (a - 1) := by ring
    _ = _ := by rw [hmul]; ring

theorem annular_maximum_principle [Nontrivial E] {a R : ℝ} (ha : 0 < a)
    {u : E → ℝ} (hd : ∀ x, x ≠ 0 → ‖x‖ ≤ R → ContDiffAt ℝ 2 u x)
    (hl : ∀ x, x ≠ 0 → ‖x‖ ≤ R → 0 < u x → 0 ≤ Δ u x)
    (hb : ∀ x, ‖x‖ = a ∨ ‖x‖ = R → u x ≤ 0) :
    ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ R → u x ≤ 0 := by
  let K : Set E := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ R}
  have hk : IsCompact K := by
    have he : K = Metric.closedBall (0 : E) R ∩ {x | a ≤ ‖x‖} := by
      ext x
      simp only [K, mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      exact and_comm
    rw [he]
    exact (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)
  have hn (x : E) (hx : x ∈ K) : x ≠ 0 := by
    have hp : 0 < ‖x‖ := ha.trans_le hx.1
    exact norm_pos_iff.mp hp
  have hb' (x : E) (hx : x ∈ K) (hi : x ∉ interior K) : u x ≤ 0 := by
    apply hb
    by_contra! h
    have ha' : a < ‖x‖ := lt_of_le_of_ne hx.1 h.1.symm
    have hr' : ‖x‖ < R := lt_of_le_of_ne hx.2 h.2
    apply hi
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨ha', hr'⟩)
    exact fun y hy => ⟨hy.1.le, hy.2.le⟩
  have hm := compact_maximum_principle hk
    (fun x hx => (hd x (hn x hx) hx.2).continuousAt.continuousWithinAt)
    (fun x hx => hd x (hn x (interior_subset hx)) (interior_subset hx).2)
    (fun x hx hp => hl x (hn x (interior_subset hx)) (interior_subset hx).2 hp) hb'
  exact fun x hx hr => hm x ⟨hx, hr⟩

theorem punctured_ball_maximum_principle [Nontrivial E] {R : ℝ}
    {u : E → ℝ} (hd : ∀ x, x ≠ 0 → ‖x‖ ≤ R → ContDiffAt ℝ 2 u x)
    (hl : ∀ x, x ≠ 0 → ‖x‖ ≤ R → 0 < u x → 0 ≤ Δ u x)
    (hb : ∀ x, ‖x‖ = R → u x ≤ 0)
    (hz : ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → u x ≤ 0) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ R → u x ≤ 0 := by
  obtain ⟨a, ha, hz⟩ := hz
  intro x hx hr
  by_cases hxa : ‖x‖ ≤ a
  · exact hz x hx hxa
  · apply annular_maximum_principle ha hd hl (fun y hy => ?_) x (le_of_not_ge hxa) hr
    rcases hy with hy | hy
    · exact hz y (norm_pos_iff.mp (hy ▸ ha)) hy.le
    · exact hb y hy

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma radialPower_add (a b : ℝ) {x : E} (hx : x ≠ 0) :
    radialPower (a + b) x = radialPower a x * radialPower b x :=
  Real.rpow_add (sq_pos_of_pos (norm_pos_iff.mpr hx)) a b

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma radialPower_rpow (a b : ℝ) (x : E) :
    (radialPower a x) ^ b = radialPower (a * b) x :=
  (Real.rpow_mul (sq_nonneg ‖x‖) a b).symm

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma radialPower_nonneg (a : ℝ) (x : E) : 0 ≤ radialPower a x :=
  Real.rpow_nonneg (sq_nonneg ‖x‖) a

lemma rpow_three_halves (v : ℝ) (hv : 0 ≤ v) : v ^ (3 / 2 : ℝ) = v * v ^ (1 / 2 : ℝ) := by
  by_cases h : v = 0
  · subst v; norm_num
  · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (lt_of_le_of_ne hv (Ne.symm h)), Real.rpow_one]

lemma rpow_three_halves_lower {B v : ℝ} (hB : 0 ≤ B) (hv : B ≤ v) :
    B ^ (1 / 2 : ℝ) * v ≤ v ^ (3 / 2 : ℝ) := by
  rw [rpow_three_halves v (hB.trans hv)]
  have h := Real.rpow_le_rpow hB hv (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith [mul_nonneg (hB.trans hv) (sub_nonneg.mpr h)]

abbrev Space := EuclideanSpace ℝ (Fin 3)

lemma radial_laplacian_three (a : ℝ) {x : Space} (hx : x ≠ 0) :
    (Δ (radialPower a : Space → ℝ) : Space → ℝ) x =
      (4 * a ^ 2 + 2 * a) * radialPower (a - 1) x := by
  rw [laplacian_radialPower a hx]
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [hdim]
  change (4 * a * (a - 1) + 2 * (3 : ℝ) * a) * radialPower (a - 1) x = _
  ring

def radialCombination (B e s c : ℝ) (x : Space) : ℝ :=
  B * radialPower (-2) x + e * radialPower (-2 - s) x + c

lemma radialCombination_contDiffAt (B e s c : ℝ) {x : Space} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (radialCombination B e s c) x :=
  ((contDiffAt_const.mul (radialPower_contDiffAt _ hx)).add
    (contDiffAt_const.mul (radialPower_contDiffAt _ hx))).add contDiffAt_const

lemma radialCombination_laplacian (B e s c : ℝ) {x : Space} (hx : x ≠ 0) :
    Δ (radialCombination B e s c) x =
      radialPower (-3) x * (12 * B + (12 + 14 * s + 4 * s ^ 2) * e * radialPower (-s) x) := by
  have h1 := radialPower_contDiffAt (-2) hx
  have h2 := radialPower_contDiffAt (-2 - s) hx
  have hb : ContDiffAt ℝ 2 (B • (radialPower (-2) : Space → ℝ)) x :=
    contDiffAt_const.smul h1
  have he : ContDiffAt ℝ 2 (e • (radialPower (-2 - s) : Space → ℝ)) x :=
    contDiffAt_const.smul h2
  have hsum : ContDiffAt ℝ 2 (B • (radialPower (-2) : Space → ℝ) + e • radialPower (-2 - s)) x := hb.add he
  change (Δ ((B • radialPower (-2) + e • radialPower (-2 - s)) + fun _ => c) : Space → ℝ) x = _
  rw [hsum.laplacian_add (show ContDiffAt ℝ 2 (fun _ : Space => c) x from contDiffAt_const), hb.laplacian_add he,
    laplacian_smul B h1, laplacian_smul e h2, laplacian_const,
    radial_laplacian_three _ hx, radial_laplacian_three _ hx]
  norm_num only
  rw [show -2 - s - 1 = -3 + -s by ring, radialPower_add _ _ hx]
  simp only [Pi.zero_apply, add_zero]
  ring

def reaction (d v : ℝ) : ℝ := d * (max (v - 1) 0) ^ (3 / 2 : ℝ)

lemma reaction_monotone {d : ℝ} (hd : 0 ≤ d) : Monotone (reaction d) := by
  intro u v huv
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_max_right _ _)
    (max_le_max (sub_le_sub_right huv 1) le_rfl) (by norm_num)) hd

lemma radialCombination_factor (B e s c : ℝ) {x : Space} (hx : x ≠ 0) :
    radialCombination B e s c x =
      radialPower (-2) x * (B + e * radialPower (-s) x) + c := by
  rw [radialCombination, show -2 - s = -2 + -s by ring, radialPower_add _ _ hx]
  ring

lemma radial_scaled_reaction {v : ℝ} (hv : 0 ≤ v) (x : Space) :
    (radialPower (-2) x * v) ^ (3 / 2 : ℝ) = radialPower (-3) x * v ^ (3 / 2 : ℝ) := by
  rw [Real.mul_rpow (radialPower_nonneg _ _) hv, radialPower_rpow]
  norm_num

lemma upper_barrier_laplacian {d B e s c : ℝ} (hd : 0 ≤ d) (hB : 0 < B)
    (he : 0 ≤ e) (hc : 1 ≤ c) (hq : 12 ≤ d * B ^ (1 / 2 : ℝ))
    (hκ : 12 + 14 * s + 4 * s ^ 2 ≤ d * B ^ (1 / 2 : ℝ))
    {x : Space} (hx : x ≠ 0) :
    Δ (radialCombination B e s c) x ≤ reaction d (radialCombination B e s c x) := by
  let z := e * radialPower (-s) x
  have hz : 0 ≤ z := mul_nonneg he (radialPower_nonneg _ _)
  have hv : 0 < B + z := by positivity
  have hf : radialPower (-2) x * (B + z) ≤ max (radialCombination B e s c x - 1) 0 := by
    apply le_trans _ (le_max_left _ _)
    rw [radialCombination_factor _ _ _ _ hx]
    dsimp [z]
    linarith
  calc
    Δ (radialCombination B e s c) x
        = radialPower (-3) x * (12 * B + (12 + 14 * s + 4 * s ^ 2) * z) := by
          rw [radialCombination_laplacian _ _ _ _ hx]; dsimp [z]; ring
    _ ≤ radialPower (-3) x * (d * B ^ (1 / 2 : ℝ) * (B + z)) := by
      apply mul_le_mul_of_nonneg_left _ (radialPower_nonneg _ _)
      nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hq), mul_nonneg hz (sub_nonneg.mpr hκ)]
    _ ≤ radialPower (-3) x * (d * (B + z) ^ (3 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (radialPower_nonneg _ _)
      calc
        _ = d * (B ^ (1 / 2 : ℝ) * (B + z)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_three_halves_lower hB.le (by linarith)) hd
    _ = d * (radialPower (-2) x * (B + z)) ^ (3 / 2 : ℝ) := by
      rw [radial_scaled_reaction hv.le]; ring
    _ ≤ reaction d (radialCombination B e s c x) := by
      apply mul_le_mul_of_nonneg_left _ hd
      exact Real.rpow_le_rpow (mul_nonneg (radialPower_nonneg _ _) hv.le) hf (by norm_num)

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_SommerfeldCoefficient
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
namespace CoulombPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

def sommerfeldCoefficient (d : ℝ) : ℝ := (12 / d) ^ 2

lemma sommerfeldCoefficient_pos {d : ℝ} (hd : 0 < d) : 0 < sommerfeldCoefficient d := by
  unfold sommerfeldCoefficient
  positivity

lemma sommerfeldCoefficient_half {d : ℝ} (hd : 0 < d) :
    d * (sommerfeldCoefficient d) ^ (1 / 2 : ℝ) = 12 := by
  have hp : 0 ≤ 12 / d := by positivity
  unfold sommerfeldCoefficient
  rw [← Real.rpow_natCast (12 / d) 2, ← Real.rpow_mul hp]
  norm_num
  field_simp

lemma norm_four_mul_radialPower {x : Space} (hx : x ≠ 0) :
    ‖x‖ ^ 4 * radialPower (-2) x = 1 := by
  rw [radialPower, Real.rpow_neg (sq_nonneg ‖x‖) 2, Real.rpow_two]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp

theorem global_punctured_maximum_principle {u : Space → ℝ}
    (hd : ∀ x, x ≠ 0 → ContDiffAt ℝ 2 u x)
    (hl : ∀ x, x ≠ 0 → 0 < u x → 0 ≤ Δ u x)
    (hz : ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → u x ≤ 0)
    (hinfty : ∃ R > 0, ∀ x, R ≤ ‖x‖ → u x ≤ 0) :
    ∀ x, x ≠ 0 → u x ≤ 0 := by
  obtain ⟨R, _hR, hfar⟩ := hinfty
  intro x hx
  by_cases hxr : R ≤ ‖x‖
  · exact hfar x hxr
  · exact punctured_ball_maximum_principle (fun y hy _ => hd y hy)
      (fun y hy _ => hl y hy) (fun y hy => hfar y hy.ge) hz x hx (le_of_not_ge hxr)

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_FiniteProfile
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
namespace CoulombPDE

structure FiniteProfile (d Z : ℝ) (F : Space → ℝ) : Prop where
  regular : ∀ x, x ≠ 0 → ContDiffAt ℝ 2 F x
  equation : ∀ x, x ≠ 0 → Δ F x = reaction d (F x)
  decay : ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → |F x| < ε
  nucleus : ∃ C > 0, ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → |F x - Z / ‖x‖| ≤ C

lemma FiniteProfile.near_pos {d Z : ℝ} {F : Space → ℝ} (h : FiniteProfile d Z F)
    (hZ : 0 < Z) : ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → 0 ≤ F x := by
  obtain ⟨C, hC, a, ha, hn⟩ := h.nucleus
  refine ⟨min a (Z / (C + 1)), lt_min ha (div_pos hZ (by linarith)), ?_⟩
  intro x hx hxa
  have hh := (abs_le.mp (hn x hx (hxa.trans (min_le_left _ _)))).1
  have hxr := (le_div_iff₀ (show 0 < C + 1 by linarith)).mp (hxa.trans (min_le_right _ _))
  have hz : C ≤ Z / ‖x‖ := (le_div_iff₀ (norm_pos_iff.mpr hx)).mpr (by nlinarith [norm_nonneg x])
  linarith

lemma FiniteProfile.nonneg {d Z : ℝ} {F : Space → ℝ} (h : FiniteProfile d Z F)
    (hZ : 0 < Z) (x : Space) (hx : x ≠ 0) : 0 ≤ F x := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let u : Space → ℝ := fun y => -F y - δ
  have hreg (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y :=
    (h.regular y hy).neg.sub contDiffAt_const
  have hl (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
    have hf : F y ≤ 1 := by dsimp [u] at hp; linarith
    have he : reaction d (F y) = 0 := by simp [reaction, max_eq_right (sub_nonpos.mpr hf)]
    change 0 ≤ Δ ((-F) - (fun _ : Space => δ)) y
    have hn : ContDiffAt ℝ 2 (-F) y := (h.regular y hy).neg
    rw [hn.laplacian_sub (show ContDiffAt ℝ 2 (fun _ : Space => δ) y from contDiffAt_const),
      laplacian_neg, Pi.neg_apply, laplacian_const, Pi.zero_apply, h.equation y hy, he]
    norm_num
  have hnear : ∃ a > 0, ∀ y, y ≠ 0 → ‖y‖ ≤ a → u y ≤ 0 := by
    obtain ⟨a, ha, hb⟩ := h.near_pos hZ
    exact ⟨a, ha, fun y hy hr => by dsimp [u]; linarith [hb y hy hr]⟩
  have hfar : ∃ R > 0, ∀ y, R ≤ ‖y‖ → u y ≤ 0 := by
    obtain ⟨R, hR, hb⟩ := h.decay δ hδ
    exact ⟨R, hR, fun y hy => by dsimp [u]; linarith [(abs_lt.mp (hb y hy)).1]⟩
  have hh := global_punctured_maximum_principle hreg hl hnear hfar x hx
  dsimp [u] at hh
  linarith

lemma FiniteProfile.upper {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) (hd : 0 < d) (x : Space) (hx : x ≠ 0) :
    F x ≤ 1 + sommerfeldCoefficient d * radialPower (-2) x := by
  let A := sommerfeldCoefficient d
  have hA : 0 < A := sommerfeldCoefficient_pos hd
  let G := radialCombination A 0 0 1
  have hG (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 G y := radialCombination_contDiffAt _ _ _ _ hy
  have hGl (y : Space) (hy : y ≠ 0) : Δ G y ≤ reaction d (G y) := by
    apply upper_barrier_laplacian hd.le hA (by norm_num) le_rfl
      (le_of_eq (sommerfeldCoefficient_half hd).symm)
    · simpa using le_of_eq (sommerfeldCoefficient_half hd).symm
    · exact hy
  let u : Space → ℝ := fun y => F y - G y
  have hud (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y := (hF.regular y hy).sub (hG y hy)
  have hul (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
    change 0 ≤ Δ (F-G) y
    rw [(hF.regular y hy).laplacian_sub (hG y hy), hF.equation y hy]
    have hm := reaction_monotone hd.le (show G y ≤ F y by dsimp [u] at hp; linarith)
    linarith [hGl y hy]
  have hnear : ∃ a > 0, ∀ y, y ≠ 0 → ‖y‖ ≤ a → u y ≤ 0 := by
    obtain ⟨C, hC, a, ha, hn⟩ := hF.nucleus
    refine ⟨min (min a 1) (A/(|Z|+C+1)),
      lt_min (lt_min ha zero_lt_one) (div_pos hA (by positivity)), ?_⟩
    intro y hy hr
    have hrp := norm_pos_iff.mpr hy
    have hr1 : ‖y‖ ≤ 1 := hr.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hn' := (abs_le.mp (hn y hy (hr.trans ((min_le_left _ _).trans (min_le_left _ _))))).2
    have hs := (le_div_iff₀ (show 0 < |Z|+C+1 by positivity)).mp (hr.trans (min_le_right _ _))
    have hr3 : ‖y‖^3 ≤ ‖y‖ := by nlinarith [sq_nonneg ‖y‖, mul_nonneg (norm_nonneg y) (sub_nonneg.mpr hr1)]
    have hr4 : ‖y‖^4 ≤ ‖y‖ := by
      calc
        ‖y‖^4 = ‖y‖^3 * ‖y‖ := by ring
        _ ≤ ‖y‖ * ‖y‖ := mul_le_mul_of_nonneg_right hr3 (norm_nonneg _)
        _ ≤ ‖y‖ := by nlinarith
    have hf : ‖y‖^4 * F y ≤ Z * ‖y‖^3 + C * ‖y‖^4 := by
      have hh := mul_le_mul_of_nonneg_left hn' (pow_nonneg (norm_nonneg y) 4)
      have he : ‖y‖^4 * (F y - Z/‖y‖) = ‖y‖^4 * F y - Z * ‖y‖^3 := by field_simp
      rw [he] at hh
      linarith
    have hz : Z * ‖y‖^3 ≤ |Z| * ‖y‖ :=
      (mul_le_mul_of_nonneg_right (le_abs_self Z) (pow_nonneg (norm_nonneg y) 3)).trans
        (mul_le_mul_of_nonneg_left hr3 (abs_nonneg Z))
    have hb : ‖y‖^4 * F y ≤ A := by nlinarith [mul_le_mul_of_nonneg_left hr4 hC.le]
    have hg : ‖y‖^4 * (A * radialPower (-2) y) = A := by nlinarith [norm_four_mul_radialPower hy]
    have hh : F y ≤ A * radialPower (-2) y := (mul_le_mul_iff_right₀ (pow_pos hrp 4)).mp (by nlinarith)
    dsimp [u, G, radialCombination]
    linarith
  have hfar : ∃ R > 0, ∀ y, R ≤ ‖y‖ → u y ≤ 0 := by
    obtain ⟨R, hR, hb⟩ := hF.decay 1 zero_lt_one
    refine ⟨R, hR, ?_⟩
    intro y hy
    have hf := (abs_lt.mp (hb y hy)).2
    have hp := mul_nonneg hA.le (radialPower_nonneg (-2) y)
    dsimp [u, G, radialCombination]
    linarith
  have hh := global_punctured_maximum_principle hud hul hnear hfar x hx
  dsimp [u, G, radialCombination, A] at hh
  linarith

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_Nonneg
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
namespace CoulombPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem annular_maximum_principle_on [Nontrivial E] {a R : ℝ}
    {u : E → ℝ} (hd : ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ R → ContDiffAt ℝ 2 u x)
    (hl : ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ R → 0 < u x → 0 ≤ Δ u x)
    (hb : ∀ x, ‖x‖ = a ∨ ‖x‖ = R → u x ≤ 0) :
    ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ R → u x ≤ 0 := by
  let K : Set E := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ R}
  have hk : IsCompact K := by
    have he : K = Metric.closedBall (0 : E) R ∩ {x | a ≤ ‖x‖} := by
      ext x
      simp only [K, mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      exact and_comm
    rw [he]
    exact (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)
  have hb' (x : E) (hx : x ∈ K) (hi : x ∉ interior K) : u x ≤ 0 := by
    apply hb
    by_contra! hh
    have ha' : a < ‖x‖ := lt_of_le_of_ne hx.1 hh.1.symm
    have hr' : ‖x‖ < R := lt_of_le_of_ne hx.2 hh.2
    apply hi
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨ha', hr'⟩)
    exact fun y hy => ⟨hy.1.le, hy.2.le⟩
  have hm := compact_maximum_principle hk
    (fun x hx => (hd x hx.1 hx.2).continuousAt.continuousWithinAt)
    (fun x hx => hd x (interior_subset hx).1 (interior_subset hx).2)
    (fun x hx hp => hl x (interior_subset hx).1 (interior_subset hx).2 hp) hb'
  exact fun x hx hr => hm x ⟨hx, hr⟩

theorem exterior_maximum_principle [Nontrivial E] {a : ℝ} {u : E → ℝ}
    (hd : ∀ x, a ≤ ‖x‖ → ContDiffAt ℝ 2 u x)
    (hl : ∀ x, a ≤ ‖x‖ → 0 < u x → 0 ≤ Δ u x)
    (hb : ∀ x, ‖x‖ = a → u x ≤ 0)
    (hf : ∀ ε > 0, ∃ R, ∀ x, R ≤ ‖x‖ → u x ≤ ε) :
    ∀ x, a ≤ ‖x‖ → u x ≤ 0 := by
  intro x hx
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R, hR⟩ := hf ε hε
  let S := max R ‖x‖
  have hv (y : E) (hy : a ≤ ‖y‖) : ContDiffAt ℝ 2 (fun z => u z - ε) y :=
    (hd y hy).sub contDiffAt_const
  have hl' (y : E) (hy : a ≤ ‖y‖) (_hyS : ‖y‖ ≤ S) (hp : 0 < u y - ε) :
      0 ≤ Δ (fun z => u z - ε) y := by
    have he := (hd y hy).laplacian_sub (show ContDiffAt ℝ 2 (fun _ : E => ε) y from contDiffAt_const)
    simp only [laplacian_const, Pi.zero_apply, sub_zero] at he
    change 0 ≤ (Δ (u - fun _ => ε) : E → ℝ) y
    rw [he]
    exact hl y hy (by linarith)
  have hm := annular_maximum_principle_on (a := a) (R := S)
    (fun y hy _ => hv y hy) hl' (fun y hy => ?_) x hx (le_max_right _ _)
  · simpa using (sub_nonpos.mp hm)
  · rcases hy with hy | hy
    · have hh := hb y hy
      linarith
    · have hh := hR y ((le_max_left R ‖x‖).trans hy.ge)
      linarith

lemma radialPower_half_inv (x : Space) : radialPower (-(1 / 2)) x = ‖x‖⁻¹ := by
  unfold radialPower
  rw [Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_norm]

theorem exterior_harmonic_unique {a : ℝ} {F G : Space → ℝ}
    (hF : ∀ x, a ≤ ‖x‖ → ContDiffAt ℝ 2 F x)
    (hG : ∀ x, a ≤ ‖x‖ → ContDiffAt ℝ 2 G x)
    (hΔ : ∀ x, a ≤ ‖x‖ → Δ F x = Δ G x)
    (hb : ∀ x, ‖x‖ = a → F x = G x)
    (hf : ∀ ε > 0, ∃ R, ∀ x, R ≤ ‖x‖ → |F x - G x| ≤ ε) :
    ∀ x, a ≤ ‖x‖ → F x = G x := by
  have hle {U V : Space → ℝ}
      (hU : ∀ x, a ≤ ‖x‖ → ContDiffAt ℝ 2 U x)
      (hV : ∀ x, a ≤ ‖x‖ → ContDiffAt ℝ 2 V x)
      (he : ∀ x, a ≤ ‖x‖ → Δ U x = Δ V x)
      (hbu : ∀ x, ‖x‖ = a → U x = V x)
      (hf' : ∀ ε > 0, ∃ R, ∀ x, R ≤ ‖x‖ → U x - V x ≤ ε) :
      ∀ x, a ≤ ‖x‖ → U x ≤ V x := by
    intro x hx
    apply sub_nonpos.mp
    apply exterior_maximum_principle (fun y hy => (hU y hy).sub (hV y hy))
      (fun y hy _ => ?_) (fun y hy => by simp [hbu y hy]) hf' x hx
    change 0 ≤ (Δ (U - V) : Space → ℝ) y
    rw [(hU y hy).laplacian_sub (hV y hy), he y hy, sub_self]
  intro x hx
  apply le_antisymm
  · exact hle hF hG hΔ hb (fun ε hε => by
      obtain ⟨R, hR⟩ := hf ε hε
      exact ⟨R, fun y hy => (le_abs_self _).trans (hR y hy)⟩) x hx
  · exact hle hG hF (fun y hy => (hΔ y hy).symm) (fun y hy => (hb y hy).symm)
      (fun ε hε => by
        obtain ⟨R, hR⟩ := hf ε hε
        refine ⟨R, fun y hy => ?_⟩
        have hh := (abs_le.mp (hR y hy)).1
        linarith) x hx

end CoulombPDE

open MeasureTheory Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Slices
attribute [-instance] _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

def joinLists {α : Type*} {N M : ℕ} (x : Fin N → α) (y : Fin M → α) : Fin (N+M) → α :=
  Sum.elim x y ∘ finSumFinEquiv.symm

@[simp] lemma joinLists_left {α : Type*} {N M : ℕ} (x : Fin N → α) (y : Fin M → α)
    (i : Fin N) : joinLists x y (finSumFinEquiv (Sum.inl i)) = x i := by
  simp [joinLists]

@[simp] lemma joinLists_right {α : Type*} {N M : ℕ} (x : Fin N → α) (y : Fin M → α)
    (i : Fin M) : joinLists x y (finSumFinEquiv (Sum.inr i)) = y i := by
  simp [joinLists]

def formMass {N : ℕ} (ψ : FormVector N) : ℝ :=
  ∑ s : Spins N, ∫ x, ‖ψ.value s x‖ ^ 2

def scaleForm {N : ℕ} (c : ℝ) (ψ : FormVector N) : FormVector N where
  value s x := (c : ℂ) * ψ.value s x
  gradient s i a x := (c : ℂ) * ψ.gradient s i a x

lemma scaled_norm_sq (c : ℝ) (z : ℂ) : ‖(c : ℂ) * z‖ ^ 2 = c ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]


open Set Filter Topology InnerProductSpace Laplacian

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_TrialSmoothTest
attribute [-instance] _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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

def smoothForm {N : ℕ} (f : Configuration N → ℂ) : FormVector N where
  value := fun _ => f
  gradient := fun _ i a x => fderiv ℝ f x (direction i a)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpinJoinEquiv
attribute [-instance] _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace
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

def spinJoinEquiv (N M : ℕ) : (Spins N × Spins M) ≃ Spins (N+M) :=
  (Equiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin M => Fin 2)).symm.trans
    (Equiv.piCongrLeft (fun _ : Fin (N+M) => Fin 2) finSumFinEquiv)

@[simp] lemma spinJoinEquiv_apply {N M : ℕ} (s : Spins N) (t : Spins M) :
    spinJoinEquiv N M (s,t) = joinLists s t := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  change (Equiv.piCongrLeft (fun _ : Fin (N+M) => Fin 2) finSumFinEquiv)
    ((Equiv.sumPiEquivProdPi (fun _ : Fin N ⊕ Fin M => Fin 2)).symm (s,t))
      (finSumFinEquiv j) = Sum.elim s t (finSumFinEquiv.symm (finSumFinEquiv j))
  rw [Equiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]
  cases j <;> rfl

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SumPairsHalf
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


def configurationReindex {M N : ℕ} (e : Fin M ≃ Fin N) :
    Configuration M ≃L[ℝ] Configuration N :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin N => Space) e

@[simp] lemma configurationReindex_apply {M N : ℕ} (e : Fin M ≃ Fin N) (x : Configuration M) :
    configurationReindex e x = x ∘ e.symm := by
  ext i
  simp [configurationReindex, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft]

def reindexForm {M N : ℕ} (e : Fin M ≃ Fin N) (ψ : FormVector N) : FormVector M where
  value s x := ψ.value (s ∘ e.symm) (x ∘ e.symm)
  gradient s i a x := ψ.gradient (s ∘ e.symm) (e i) a (x ∘ e.symm)


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_TensorLp
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


def leftList {α : Type*} {N M : ℕ} (x : Fin (N+M) → α) : Fin N → α :=
  fun i => x (finSumFinEquiv (Sum.inl i))
def rightList {α : Type*} {N M : ℕ} (x : Fin (N+M) → α) : Fin M → α :=
  fun i => x (finSumFinEquiv (Sum.inr i))

@[simp] lemma leftList_join {α : Type*} {N M : ℕ} (x : Fin N → α) (y : Fin M → α) :
    leftList (joinLists x y) = x := by ext i; exact joinLists_left x y i
@[simp] lemma rightList_join {α : Type*} {N M : ℕ} (x : Fin N → α) (y : Fin M → α) :
    rightList (joinLists x y) = y := by ext i; exact joinLists_right x y i
@[simp] lemma join_list_parts {α : Type*} {N M : ℕ} (x : Fin (N+M) → α) :
    joinLists (leftList x) (rightList x) = x := by
  ext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j => exact joinLists_left (leftList x) (rightList x) j
  | inr j => exact joinLists_right (leftList x) (rightList x) j

def tensorForm {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) : FormVector (N+M) where
  value s x := ψ.value (leftList s) (leftList x) * φ.value (rightList s) (rightList x)
  gradient s i a x := Sum.elim
    (fun j => ψ.gradient (leftList s) j a (leftList x) * φ.value (rightList s) (rightList x))
    (fun j => ψ.value (leftList s) (leftList x) * φ.gradient (rightList s) j a (rightList x))
    (finSumFinEquiv.symm i)

@[simp] lemma tensorForm_value_join {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (x : Configuration N) (y : Configuration M) :
    (tensorForm ψ φ).value (joinLists s t) (joinLists x y) = ψ.value s x*φ.value t y := by
  simp only [tensorForm,leftList_join,rightList_join]

@[simp] lemma tensorForm_gradient_left {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (x : Configuration N) (y : Configuration M)
    (i : Fin N) (a : Fin 3) :
    (tensorForm ψ φ).gradient (joinLists s t) (finSumFinEquiv (Sum.inl i)) a (joinLists x y) =
      ψ.gradient s i a x*φ.value t y := by
  simp only [tensorForm,leftList_join,rightList_join,Equiv.symm_apply_apply,Sum.elim_inl]

@[simp] lemma tensorForm_gradient_right {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (x : Configuration N) (y : Configuration M)
    (i : Fin M) (a : Fin 3) :
    (tensorForm ψ φ).gradient (joinLists s t) (finSumFinEquiv (Sum.inr i)) a (joinLists x y) =
      ψ.value s x*φ.gradient t i a y := by
  simp only [tensorForm,leftList_join,rightList_join,Equiv.symm_apply_apply,Sum.elim_inr]


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_InsertionSwap
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

def insertionSwap {N : ℕ} (i : Fin (N+1)) : Equiv.Perm (Fin (N+1)) :=
  Equiv.swap i (Fin.last N)

@[simp] lemma insertionSwap_last {N : ℕ} (i : Fin (N+1)) :
    insertionSwap i (Fin.last N) = i := Equiv.swap_apply_right _ _
@[simp] lemma insertionSwap_self {N : ℕ} (i : Fin (N+1)) :
    insertionSwap i i = Fin.last N := Equiv.swap_apply_left _ _
@[simp] lemma insertionSwap_symm {N : ℕ} (i : Fin (N+1)) :
    (insertionSwap i).symm = insertionSwap i := rfl


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


def insertionTerm {N : ℕ} (T : FormVector (N+1)) (i : Fin (N+1)) : FormVector (N+1) :=
  scaleForm (((Equiv.Perm.sign (insertionSwap i) : ℤ) : ℝ))
    (reindexForm (insertionSwap i) T)

@[simp] lemma insertionTerm_value {N : ℕ} (T : FormVector (N+1)) (i : Fin (N+1))
    (s : Spins (N+1)) (x : Configuration (N+1)) :
    (insertionTerm T i).value s x = (((Equiv.Perm.sign (insertionSwap i) : ℤ) : ℂ)) *
      T.value (s ∘ insertionSwap i) (x ∘ insertionSwap i) := by
  simp only [insertionTerm,scaleForm,reindexForm,insertionSwap_symm,Complex.ofReal_intCast]


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Form
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

def FormZeroAt {N : ℕ} (ψ : FormVector N) (x : Configuration N) : Prop :=
  ∀ s, ψ.value s x = 0 ∧ ∀ i a, ψ.gradient s i a x = 0


open MeasureTheory Filter
open scoped BigOperators


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_RadialPacketBase
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

def radialPacketBase (x : Space) : ℂ :=
  (Real.smoothTransition (1 - ‖x‖^2) : ℝ)

lemma radialPacketBase_zero {x : Space} (hx : 1 ≤ ‖x‖) : radialPacketBase x = 0 := by
  have hh : 1 - ‖x‖^2 ≤ 0 := by nlinarith [norm_nonneg x]
  simp only [radialPacketBase, Real.smoothTransition.zero_of_nonpos hh,Complex.ofReal_zero]

def radialPacketSeed (x : Configuration 1) : ℂ := radialPacketBase (x 0)

lemma radialPacketSeed_support {x : Configuration 1} (hx : radialPacketSeed x ≠ 0) :
    ‖x 0‖ < 1 := by
  by_contra hh
  exact hx (radialPacketBase_zero (not_lt.mp hh))

def radialScaledSeed (R : ℝ) (x : Configuration 1) : ℂ := radialPacketSeed (R⁻¹ • x)

def radialScaledRaw (R : ℝ) : FormVector 1 := smoothForm (radialScaledSeed R)

def radialCenterShift (y : Space) : Configuration 1 :=
  fun _ => -y

def radialLocalSeed (y : Space) (R : ℝ) (x : Configuration 1) : ℂ :=
  radialScaledSeed R (x + radialCenterShift y)

def radialLocalRaw (y : Space) (R : ℝ) : FormVector 1 := smoothForm (radialLocalSeed y R)

def radialLocalOrbital (y : Space) (R : ℝ) : FormVector 1 :=
  scaleForm (Real.sqrt (formMass (radialLocalRaw y R)))⁻¹ (radialLocalRaw y R)

lemma radialLocalSeed_support (y : Space) {R : ℝ} (hR : 0 < R) {x : Configuration 1}
    (hx : radialLocalSeed y R x ≠ 0) : ‖x 0-y‖ < R := by
  have hh := radialPacketSeed_support hx
  change ‖R⁻¹ • (x 0 + -y)‖ < 1 at hh
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),← div_eq_inv_mul] at hh
  simpa only [sub_eq_add_neg] using (div_lt_one hR).mp hh

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfWeight
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
section

lemma tf_power_strongConvex {s : ℝ} (_hs : 0 < s) :
    ConvexOn ℝ (Set.Icc 0 s)
      (fun t : ℝ => t ^ (5 / 3 : ℝ) - (5 / 9 : ℝ) * s ^ (-1 / 3 : ℝ) * t ^ 2) := by
  let c : ℝ := (5 / 9 : ℝ) * s ^ (-1 / 3 : ℝ)
  let f' : ℝ → ℝ := fun t => (5 / 3 : ℝ) * t ^ (2 / 3 : ℝ) - 2 * c * t
  let f'' : ℝ → ℝ := fun t => (10 / 9 : ℝ) * t ^ (-1 / 3 : ℝ) - 2 * c
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := f') (f'' := f'') (convex_Icc _ _)
  · exact ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 5 / 3)).sub
      (continuous_const.mul (continuous_id.pow 2))).continuousOn
  · intro t ht
    have ht' : 0 < t := (Set.mem_Ioo.mp (by simpa only [interior_Icc] using ht)).1
    have h1 := Real.hasDerivAt_rpow_const (x := t) (p := (5 / 3 : ℝ)) (Or.inl ht'.ne')
    have h2 := ((hasDerivAt_pow 2 t).const_mul c)
    have hh := (h1.fun_sub h2).hasDerivWithinAt (s := interior (Set.Icc 0 s))
    norm_num at hh
    simpa [f', c, mul_assoc, mul_left_comm, mul_comm] using hh
  · intro t ht
    have ht' : 0 < t := (Set.mem_Ioo.mp (by simpa only [interior_Icc] using ht)).1
    have h1 := (Real.hasDerivAt_rpow_const (x := t) (p := (2 / 3 : ℝ))
      (Or.inl ht'.ne')).const_mul (5 / 3 : ℝ)
    have h2 := (hasDerivAt_id t).const_mul (2 * c)
    have hh := (h1.fun_sub h2).hasDerivWithinAt (s := interior (Set.Icc 0 s))
    norm_num at hh
    convert! hh using 1 <;> simp only [f'', interior_Icc]
    all_goals (norm_num; ring)
  · intro t ht
    have ht' : t ∈ Set.Ioo 0 s := by simpa only [interior_Icc] using ht
    have hp := Real.rpow_le_rpow_of_nonpos ht'.1 ht'.2.le (by norm_num : (-1 / 3 : ℝ) ≤ 0)
    dsimp [f'', c]
    nlinarith

lemma tf_power_midpoint_gap {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (5 / 36 : ℝ) * (a + b) ^ (-1 / 3 : ℝ) * (a - b) ^ 2 ≤
      (a ^ (5 / 3 : ℝ) + b ^ (5 / 3 : ℝ)) / 2 - ((a + b) / 2) ^ (5 / 3 : ℝ) := by
  by_cases hs : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  have hc := tf_power_strongConvex (lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs))
  have h := hc.2 (show a ∈ Set.Icc 0 (a + b) by exact ⟨ha, by linarith⟩)
    (show b ∈ Set.Icc 0 (a + b) by exact ⟨hb, by linarith⟩)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  have he : (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = (a + b) / 2 := by ring
  rw [he] at h
  nlinarith

def tfWeight (a b : ℝ) : ℝ := (a + b) ^ (-1 / 3 : ℝ) * (a - b) ^ 2

lemma tfWeight_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ tfWeight a b :=
  mul_nonneg (Real.rpow_nonneg (add_nonneg ha hb) _) (sq_nonneg _)

lemma tfWeight_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    tfWeight a b ≤ (18 / 5 : ℝ) * (a ^ (5 / 3 : ℝ) + b ^ (5 / 3 : ℝ)) := by
  have h := tf_power_midpoint_gap ha hb
  have hn := Real.rpow_nonneg (div_nonneg (add_nonneg ha hb) (by norm_num : (0 : ℝ) ≤ 2)) (5 / 3 : ℝ)
  dsimp [tfWeight]
  nlinarith

lemma tfWeight_interpolation {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| ^ (5 / 3 : ℝ) =
      (tfWeight a b) ^ (5 / 6 : ℝ) * ((a + b) ^ (5 / 3 : ℝ)) ^ (1 / 6 : ℝ) := by
  by_cases hs : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0, tfWeight]
  have hs' : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
  rw [tfWeight, Real.mul_rpow (Real.rpow_nonneg hs'.le _) (sq_nonneg _),
    ← Real.rpow_mul hs'.le, ← Real.rpow_mul hs'.le]
  have he : ((a - b) ^ 2) ^ (5 / 6 : ℝ) = |a - b| ^ (5 / 3 : ℝ) := by
    rw [← sq_abs, ← Real.rpow_natCast_mul (abs_nonneg (a - b)) 2]
    norm_num
  rw [he]
  symm
  calc
    _ = |a - b| ^ (5 / 3 : ℝ) *
      ((a + b) ^ ((-1 / 3 : ℝ) * (5 / 6)) * (a + b) ^ ((5 / 3 : ℝ) * (1 / 6))) := by ring
    _ = _ := by rw [← Real.rpow_add hs']; norm_num

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma tf_integrable {f : α → ℝ} (hf : MemLp f (5 / 3) μ)
    (hn : ∀ᵐ x ∂μ, 0 ≤ f x) : Integrable (fun x => f x ^ (5 / 3 : ℝ)) μ := by
  have hi := hf.integrable_norm_rpow (by norm_num : (5 / 3 : ENNReal) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num) : (5 / 3 : ENNReal) ≠ ⊤)
  norm_num at hi
  exact hi.congr (hn.mono fun x hx => by simp [abs_of_nonneg hx])

lemma tfWeight_integrable {f g : α → ℝ} (hf : MemLp f (5 / 3) μ)
    (hg : MemLp g (5 / 3) μ) (hnf : ∀ᵐ x ∂μ, 0 ≤ f x) (hng : ∀ᵐ x ∂μ, 0 ≤ g x) :
    Integrable (fun x => tfWeight (f x) (g x)) μ := by
  have hi := ((tf_integrable hf hnf).add (tf_integrable hg hng)).const_mul (18 / 5 : ℝ)
  apply hi.mono'
  · unfold tfWeight
    exact ((hf.aestronglyMeasurable.add hg.aestronglyMeasurable).aemeasurable.pow_const _).aestronglyMeasurable.mul
      ((hf.aestronglyMeasurable.sub hg.aestronglyMeasurable).pow 2)
  · filter_upwards [hnf, hng] with x hfx hgx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (tfWeight_nonneg hfx hgx), Pi.add_apply] using tfWeight_le hfx hgx

lemma tfWeight_integral_gap {f g : α → ℝ} (hf : MemLp f (5 / 3) μ)
    (hg : MemLp g (5 / 3) μ) (hnf : ∀ᵐ x ∂μ, 0 ≤ f x) (hng : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (5 / 36 : ℝ) * (∫ x, tfWeight (f x) (g x) ∂μ) ≤
      ((∫ x, f x ^ (5 / 3 : ℝ) ∂μ) + (∫ x, g x ^ (5 / 3 : ℝ) ∂μ)) / 2 -
      ∫ x, ((f x + g x) / 2) ^ (5 / 3 : ℝ) ∂μ := by
  have hm : MemLp (fun x => (f x + g x) / 2) (5 / 3) μ := by
    simpa only [div_eq_mul_inv, Pi.add_apply] using (hf.add hg).mul_const (2 : ℝ)⁻¹
  have hnm : ∀ᵐ x ∂μ, 0 ≤ (f x + g x) / 2 := by
    filter_upwards [hnf, hng] with x hx hy
    positivity
  have hh := integral_mono_ae ((tfWeight_integrable hf hg hnf hng).const_mul (5 / 36 : ℝ))
    ((((tf_integrable hf hnf).add (tf_integrable hg hng)).div_const 2).sub (tf_integrable hm hnm))
    (show ∀ᵐ x ∂μ, (5 / 36 : ℝ) * tfWeight (f x) (g x) ≤
      (f x ^ (5 / 3 : ℝ) + g x ^ (5 / 3 : ℝ)) / 2 - ((f x + g x) / 2) ^ (5 / 3 : ℝ) from by
      filter_upwards [hnf, hng] with x hx hy
      simpa only [tfWeight, mul_assoc] using tf_power_midpoint_gap hx hy)
  simp only [Pi.sub_apply, Pi.add_apply] at hh
  have hsum : Integrable (fun x => f x ^ (5 / 3 : ℝ) + g x ^ (5 / 3 : ℝ)) μ := by
    exact (tf_integrable hf hnf).add (tf_integrable hg hng)
  have hdiv : Integrable (fun x => (f x ^ (5 / 3 : ℝ) + g x ^ (5 / 3 : ℝ)) / 2) μ := hsum.div_const 2
  rw [integral_const_mul, integral_sub hdiv (tf_integrable hm hnm), integral_div,
    integral_add (tf_integrable hf hnf) (tf_integrable hg hng)] at hh
  exact hh

lemma integrable_rpow_inv_memLp {w : α → ℝ} (hw : Integrable w μ)
    (hwn : ∀ᵐ x ∂μ, 0 ≤ w x) {q : ℝ} (hq : 0 < q) :
    MemLp (fun x => w x ^ (1 / q)) (ENNReal.ofReal q) μ := by
  have hm : AEStronglyMeasurable (fun x => w x ^ (1 / q)) μ :=
    (hw.aestronglyMeasurable.aemeasurable.pow_const _).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm (by positivity) ENNReal.ofReal_ne_top).mp
  apply hw.congr
  filter_upwards [hwn] with x hx
  rw [ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx _),
    ← Real.rpow_mul hx, one_div_mul_cancel hq.ne', Real.rpow_one]

lemma integral_rpow_inv_rpow {w : α → ℝ} (hwn : ∀ᵐ x ∂μ, 0 ≤ w x)
    {q : ℝ} (hq : q ≠ 0) :
    (∫ x, (w x ^ (1 / q)) ^ q ∂μ) = ∫ x, w x ∂μ := by
  apply integral_congr_ae
  filter_upwards [hwn] with x hx
  rw [← Real.rpow_mul hx, one_div_mul_cancel hq, Real.rpow_one]

lemma tfWeight_integral_interpolation {f g : α → ℝ} (hf : MemLp f (5 / 3) μ)
    (hg : MemLp g (5 / 3) μ) (hnf : ∀ᵐ x ∂μ, 0 ≤ f x) (hng : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (∫ x, |f x - g x| ^ (5 / 3 : ℝ) ∂μ) ≤
      (∫ x, tfWeight (f x) (g x) ∂μ) ^ (5 / 6 : ℝ) *
      (∫ x, (f x + g x) ^ (5 / 3 : ℝ) ∂μ) ^ (1 / 6 : ℝ) := by
  have hsum : ∀ᵐ x ∂μ, 0 ≤ (f + g) x := by
    filter_upwards [hnf, hng] with x hx hy
    exact add_nonneg hx hy
  have hsn : ∀ᵐ x ∂μ, 0 ≤ (f x + g x) ^ (5 / 3 : ℝ) :=
    hsum.mono fun x hx => Real.rpow_nonneg hx _
  have hwn : ∀ᵐ x ∂μ, 0 ≤ tfWeight (f x) (g x) := by
    filter_upwards [hnf, hng] with x hx hy
    exact tfWeight_nonneg hx hy
  have hw := integrable_rpow_inv_memLp (tfWeight_integrable hf hg hnf hng) hwn
    (by norm_num : (0 : ℝ) < 6 / 5)
  have hs := integrable_rpow_inv_memLp (tf_integrable (hf.add hg) hsum) hsn
    (by norm_num : (0 : ℝ) < 6)
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (6 / 5 : ℝ).HolderConjugate 6 from Real.holderConjugate_iff.mpr (by norm_num))
    (hwn.mono fun x hx => Real.rpow_nonneg hx (1 / (6 / 5 : ℝ)))
    (hsn.mono fun x hx => Real.rpow_nonneg hx (1 / (6 : ℝ))) hw hs
  rw [integral_rpow_inv_rpow hwn (by norm_num), integral_rpow_inv_rpow hsn (by norm_num)] at hh
  norm_num only [one_div_div, mul_one] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [hnf, hng] with x hx hy
  exact tfWeight_interpolation hx hy

end

open MeasureTheory Filter
open scoped Topology ENNReal

instance tfLpFact : Fact ((1 : ENNReal) ≤ 5 / 3) :=
  ⟨(ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)⟩

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_Lp
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
section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
abbrev TFLp (μ : Measure α) := Lp ℝ (5 / 3) μ

def NonnegDensity (f : TFLp μ) : Prop := ∀ᵐ x ∂μ, 0 ≤ f x

def densityWeight (f g : TFLp μ) : ℝ := ∫ x, tfWeight (f x) (g x) ∂μ

lemma tfLp_norm_rpow (f : TFLp μ) :
    ‖f‖ ^ (5 / 3 : ℝ) = ∫ x, |f x| ^ (5 / 3 : ℝ) ∂μ := by
  have he := (Lp.memLp f).eLpNorm_eq_integral_rpow_norm
    (by norm_num : (5 / 3 : ENNReal) ≠ 0) (ENNReal.div_ne_top (by norm_num) (by norm_num))
  rw [Lp.norm_def, he, ENNReal.toReal_ofReal (by positivity)]
  norm_num
  rw [← Real.rpow_mul (integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _))]
  norm_num

lemma tfLp_norm_rpow_nonneg {f : TFLp μ} (hf : NonnegDensity f) :
    ‖f‖ ^ (5 / 3 : ℝ) = ∫ x, f x ^ (5 / 3 : ℝ) ∂μ := by
  rw [tfLp_norm_rpow]
  exact integral_congr_ae (hf.mono fun x hx => by dsimp only; rw [abs_of_nonneg hx])

lemma nonnegDensity_add {f g : TFLp μ} (hf : NonnegDensity f) (hg : NonnegDensity g) :
    NonnegDensity (f + g) := by
  filter_upwards [Lp.coeFn_add f g, hf, hg] with x he hx hy
  rw [he]
  exact add_nonneg hx hy

lemma densityWeight_nonneg {f g : TFLp μ} (hf : NonnegDensity f) (hg : NonnegDensity g) :
    0 ≤ densityWeight f g := by
  apply integral_nonneg_of_ae
  filter_upwards [hf, hg] with x hx hy
  exact tfWeight_nonneg hx hy

lemma tfLp_interpolation {f g : TFLp μ} (hf : NonnegDensity f) (hg : NonnegDensity g) :
    ‖f - g‖ ^ (5 / 3 : ℝ) ≤
      densityWeight f g ^ (5 / 6 : ℝ) * ‖f + g‖ ^ (5 / 18 : ℝ) := by
  have hi := tfWeight_integral_interpolation (Lp.memLp f) (Lp.memLp g) hf hg
  have hd : ‖f - g‖ ^ (5 / 3 : ℝ) = ∫ x, |f x - g x| ^ (5 / 3 : ℝ) ∂μ := by
    rw [tfLp_norm_rpow]
    exact integral_congr_ae (Lp.coeFn_sub f g |>.mono fun x hx => by dsimp only; rw [hx]; rfl)
  have hs : ‖f + g‖ ^ (5 / 3 : ℝ) = ∫ x, (f x + g x) ^ (5 / 3 : ℝ) ∂μ := by
    rw [tfLp_norm_rpow_nonneg (nonnegDensity_add hf hg)]
    exact integral_congr_ae (Lp.coeFn_add f g |>.mono fun x hx => by dsimp only; rw [hx]; rfl)
  rw [← hd, ← hs, ← Real.rpow_mul (norm_nonneg _)] at hi
  norm_num at hi
  exact hi

lemma isClosed_nonnegDensity : IsClosed ({f | NonnegDensity (μ := μ) f}) := by
  apply isClosed_of_closure_subset
  intro f hf
  obtain ⟨u, hu, huf⟩ := mem_closure_iff_seq_limit.mp hf
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_Lp huf).exists_seq_tendsto_ae
  have hnn : ∀ᵐ x ∂μ, ∀ n, 0 ≤ (u (ns n)) x := ae_all_iff.mpr fun n => hu (ns n)
  filter_upwards [hns, hnn] with x hx hn
  exact ge_of_tendsto hx (Eventually.of_forall hn)

theorem exists_minimizer_of_tf_gap {C : Set (TFLp μ)} (hC : IsClosed C) (hne : C.Nonempty)
    (hn : ∀ f ∈ C, NonnegDensity f)
    (hm : ∀ f ∈ C, ∀ g ∈ C, (1 / 2 : ℝ) • (f + g) ∈ C)
    {F : TFLp μ → ℝ} (hF : ContinuousOn F C) (hbelow : BddBelow (F '' C))
    (hcoercive : ∀ a : ℝ, ∃ B : ℝ, ∀ f ∈ C, F f ≤ a → ‖f‖ ≤ B)
    {T : ℝ} (hT : 0 < T)
    (hgap : ∀ f ∈ C, ∀ g ∈ C,
      T * densityWeight f g ≤ (F f + F g) / 2 - F ((1 / 2 : ℝ) • (f + g))) :
    ∃ f ∈ C, ∀ g ∈ C, F f ≤ F g := by
  obtain ⟨v, hvmono, hvlim, hv⟩ := exists_seq_tendsto_sInf (hne.image F) hbelow
  choose u hu huv using hv
  have hulim : Tendsto (fun n => F (u n)) atTop (𝓝 (sInf (F '' C))) := by
    simpa only [huv] using hvlim
  obtain ⟨B, hB⟩ := hcoercive (v 0)
  have hub (n : ℕ) : ‖u n‖ ≤ B := hB _ (hu n) (by rw [huv]; exact hvmono (Nat.zero_le n))
  have hB0 : 0 ≤ B := (norm_nonneg (u 0)).trans (hub 0)
  have hlow (f) (hf : f ∈ C) : sInf (F '' C) ≤ F f := csInf_le hbelow ⟨f, hf, rfl⟩
  have hvnonneg (n : ℕ) : 0 ≤ v n - sInf (F '' C) := by rw [← huv]; exact sub_nonneg.mpr (hlow _ (hu n))
  have hlim : Tendsto (fun n => ((v n - sInf (F '' C)) / T) ^ (5 / 6 : ℝ) *
      (2 * B) ^ (5 / 18 : ℝ)) atTop (𝓝 0) := by
    have hh := ((hvlim.sub_const (sInf (F '' C))).div_const T).rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 5 / 6))
    simpa using hh.mul_const ((2 * B) ^ (5 / 18 : ℝ))
  have huc : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hεp : 0 < ε ^ (5 / 3 : ℝ) := Real.rpow_pos_of_pos hε _
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const hεp)
    refine ⟨N, fun m hm' n hn' => ?_⟩
    have hw := hgap (u m) (hu m) (u n) (hu n)
    have hmid := hlow _ (hm (u m) (hu m) (u n) (hu n))
    have hvm := hvmono hm'
    have hvn := hvmono hn'
    rw [huv, huv] at hw
    have hweight : densityWeight (u m) (u n) ≤ (v N - sInf (F '' C)) / T := by
      apply (le_div_iff₀ hT).mpr
      nlinarith
    have hib := tfLp_interpolation (hn _ (hu m)) (hn _ (hu n))
    have hsum : ‖u m + u n‖ ≤ 2 * B := (norm_add_le _ _).trans (by linarith [hub m, hub n])
    have hmul : densityWeight (u m) (u n) ^ (5 / 6 : ℝ) * ‖u m + u n‖ ^ (5 / 18 : ℝ) ≤
        ((v N - sInf (F '' C)) / T) ^ (5 / 6 : ℝ) * (2 * B) ^ (5 / 18 : ℝ) := by
      exact mul_le_mul
        (Real.rpow_le_rpow (densityWeight_nonneg (hn _ (hu m)) (hn _ (hu n))) hweight (by norm_num))
        (Real.rpow_le_rpow (norm_nonneg _) hsum (by norm_num))
        (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (div_nonneg (hvnonneg N) hT.le) _)
    rw [dist_eq_norm]
    exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le (by norm_num : (0 : ℝ) < 5 / 3)).mp
      (hib.trans hmul |>.trans_lt (hN N le_rfl))
  obtain ⟨f, huf⟩ := cauchySeq_tendsto_of_complete huc
  have hf : f ∈ C := hC.mem_of_tendsto huf (Eventually.of_forall hu)
  have hfe : F f = sInf (F '' C) := by
    apply tendsto_nhds_unique _ hulim
    exact (hF.continuousWithinAt hf).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨huf, Eventually.of_forall hu⟩)
  exact ⟨f, hf, fun g hg => hfe ▸ hlow g hg⟩

end

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

abbrev TFSpace := EuclideanSpace ℝ (Fin 3)
def ballMeasure (R : ℝ) : Measure TFSpace := volume.restrict (ball 0 R)
instance instIsFiniteMeasureTFSpaceBallMeasure (R : ℝ) : IsFiniteMeasure (ballMeasure R) := by
  apply isFiniteMeasure_restrict.mpr
  exact (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
    (isCompact_closedBall (0 : TFSpace) R).measure_lt_top).ne

lemma norm_inv_power_integrable_ball (R : ℝ) :
    IntegrableOn (fun x : TFSpace => ‖x‖ ^ (-5 / 2 : ℝ)) (ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (by simp [TFSpace])
    (show (5 / 2 : ℝ) < Module.finrank ℝ TFSpace by simp [TFSpace]; norm_num)
    (C := 1)
  · exact Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]; simp [neg_div]
  · exact (measurable_norm.pow_const _).aestronglyMeasurable

lemma coulomb_power_integrable (R : ℝ) :
    Integrable (fun p : TFSpace × TFSpace => ‖p.1 - p.2‖ ^ (-5 / 2 : ℝ))
      ((ballMeasure R).prod (ballMeasure R)) := by
  have h1 := (norm_inv_power_integrable_ball (2 * R)).integrable_indicator measurableSet_ball
  have h2 : Integrable ((ball (0 : TFSpace) R).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (isFiniteMeasure_restrict.mp
      (inferInstance : IsFiniteMeasure (ballMeasure R)))).integrable_indicator measurableSet_ball
  have hm := h1.mul_prod h2
  have ht := (measurePreserving_sub_prod (volume : Measure TFSpace) volume).integrable_comp
    hm.aestronglyMeasurable |>.mpr hm
  rw [ballMeasure, Measure.prod_restrict]
  apply (ht.restrict).mono'
    ((measurable_fst.sub measurable_snd).norm.pow_const _).aestronglyMeasurable
  rw [ae_restrict_iff' (measurableSet_ball.prod measurableSet_ball)]
  exact Eventually.of_forall fun p hp => by
    have hn : p.1 - p.2 ∈ ball (0 : TFSpace) (2 * R) := by
      rw [mem_ball_zero_iff]
      exact (norm_sub_le _ _).trans_lt (by
        have hpx := mem_ball_zero_iff.mp hp.1
        have hpy := mem_ball_zero_iff.mp hp.2
        linarith)
    change ‖‖p.1 - p.2‖ ^ (-5 / 2 : ℝ)‖ ≤
      (ball (0 : TFSpace) (2 * R)).indicator (fun x => ‖x‖ ^ (-5 / 2 : ℝ)) (p.1 - p.2) *
        (ball (0 : TFSpace) R).indicator (fun _ => (1 : ℝ)) p.2
    simp [hn, hp.2, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

lemma coulomb_memLp (R : ℝ) :
    MemLp (fun p : TFSpace × TFSpace => ‖p.1 - p.2‖⁻¹) (5 / 2)
      ((ballMeasure R).prod (ballMeasure R)) := by
  have hm : AEStronglyMeasurable (fun p : TFSpace × TFSpace => ‖p.1 - p.2‖⁻¹)
      ((ballMeasure R).prod (ballMeasure R)) :=
    ((measurable_fst.sub measurable_snd).norm.inv).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, norm_inv, norm_norm,
    Real.inv_rpow (norm_nonneg _), Real.rpow_neg (norm_nonneg _), neg_div] using coulomb_power_integrable R

lemma nuclear_memLp (R : ℝ) : MemLp (fun x : TFSpace => ‖x‖⁻¹) (5 / 2) (ballMeasure R) := by
  have hm : AEStronglyMeasurable (fun x : TFSpace => ‖x‖⁻¹) (ballMeasure R) :=
    measurable_norm.inv.aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm
    (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, norm_inv, norm_norm,
    Real.inv_rpow (norm_nonneg _), Real.rpow_neg (norm_nonneg _), neg_div, ballMeasure, IntegrableOn] using
      norm_inv_power_integrable_ball R

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_Tensor
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
namespace CoulombAnalysis
section Tensor
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite ν]

lemma tf_memLp_prod {f : α → ℝ} {g : β → ℝ} (hf : MemLp f (5 / 3) μ)
    (hg : MemLp g (5 / 3) ν) : MemLp (fun p : α × β => f p.1 * g p.2) (5 / 3) (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : α × β => f p.1 * g p.2) (μ.prod ν) :=
    hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd
  apply (integrable_norm_rpow_iff hm
    (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  have hi := (hf.integrable_norm_rpow (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mul_prod
    (hg.integrable_norm_rpow (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num)))
  simpa only [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] using hi

def tfTensor (f : TFLp μ) (g : TFLp ν) : TFLp (μ.prod ν) :=
  (tf_memLp_prod (Lp.memLp f) (Lp.memLp g)).toLp (fun p => f p.1 * g p.2)

lemma tfTensor_coe (f : TFLp μ) (g : TFLp ν) :
    tfTensor f g =ᵐ[μ.prod ν] fun p => f p.1 * g p.2 := MemLp.coeFn_toLp _

variable [SFinite μ]

lemma tfTensor_norm (f : TFLp μ) (g : TFLp ν) : ‖tfTensor f g‖ = ‖f‖ * ‖g‖ := by
  apply (Real.rpow_left_inj (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (by norm_num : (5 / 3 : ℝ) ≠ 0)).mp
  rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _), tfLp_norm_rpow, tfLp_norm_rpow, tfLp_norm_rpow]
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [tfTensor_coe f g] with p hp
  rw [hp, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

omit [SFinite μ] in
lemma tfTensor_add_left (f₁ f₂ : TFLp μ) (g : TFLp ν) :
    tfTensor (f₁ + f₂) g = tfTensor f₁ g + tfTensor f₂ g := by
  apply Lp.ext
  filter_upwards [tfTensor_coe (f₁ + f₂) g, tfTensor_coe f₁ g, tfTensor_coe f₂ g,
    Lp.coeFn_add (tfTensor f₁ g) (tfTensor f₂ g),
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (Lp.coeFn_add f₁ f₂)] with p hp h1 h2 he ha
  simp only [hp, he, Pi.add_apply, h1, h2, ha, add_mul]

omit [SFinite μ] in
lemma tfTensor_add_right (f : TFLp μ) (g₁ g₂ : TFLp ν) :
    tfTensor f (g₁ + g₂) = tfTensor f g₁ + tfTensor f g₂ := by
  apply Lp.ext
  filter_upwards [tfTensor_coe f (g₁ + g₂), tfTensor_coe f g₁, tfTensor_coe f g₂,
    Lp.coeFn_add (tfTensor f g₁) (tfTensor f g₂),
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae (Lp.coeFn_add g₁ g₂)] with p hp h1 h2 he ha
  simp only [hp, he, Pi.add_apply, h1, h2, ha, mul_add]

omit [SFinite μ] in
lemma tfTensor_smul_left (c : ℝ) (f : TFLp μ) (g : TFLp ν) :
    tfTensor (c • f) g = c • tfTensor f g := by
  apply Lp.ext
  filter_upwards [tfTensor_coe (c • f) g, tfTensor_coe f g,
    Lp.coeFn_smul c (tfTensor f g), (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (Lp.coeFn_smul c f)]
    with p hp he hs hc
  simp only [hp, hs, Pi.smul_apply, smul_eq_mul, he, hc, mul_assoc]

omit [SFinite μ] in
lemma tfTensor_smul_right (c : ℝ) (f : TFLp μ) (g : TFLp ν) :
    tfTensor f (c • g) = c • tfTensor f g := by
  apply Lp.ext
  filter_upwards [tfTensor_coe f (c • g), tfTensor_coe f g,
    Lp.coeFn_smul c (tfTensor f g), (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae (Lp.coeFn_smul c g)]
    with p hp he hs hc
  simp only [hp, hs, Pi.smul_apply, smul_eq_mul, he, hc]
  ring

def tfTensorₗ : TFLp μ →ₗ[ℝ] TFLp ν →ₗ[ℝ] TFLp (μ.prod ν) :=
  LinearMap.mk₂ ℝ tfTensor tfTensor_add_left tfTensor_smul_left
    tfTensor_add_right tfTensor_smul_right

lemma tfTensorₗ_bound (f : TFLp μ) (g : TFLp ν) :
    ‖tfTensorₗ f g‖ ≤ 1 * ‖f‖ * ‖g‖ := by
  change ‖tfTensor f g‖ ≤ _
  rw [tfTensor_norm, one_mul]

def tfTensorL : TFLp μ →L[ℝ] TFLp ν →L[ℝ] TFLp (μ.prod ν) :=
  tfTensorₗ.mkContinuous₂ 1 tfTensorₗ_bound

end Tensor

instance tfDualFact : Fact ((1 : ENNReal) ≤ 5 / 2) :=
  ⟨(ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)⟩
instance tfConjugate : ENNReal.HolderConjugate (5 / 2) (5 / 3) := by
  rw [ENNReal.holderConjugate_iff,
    ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← ENNReal.add_div]
  norm_num [ENNReal.div_self]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_Pairing
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
section Pairing
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def tfPairing (w : α → ℝ) (hw : MemLp w (5 / 2) μ) : TFLp μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ (5 / 2) (5 / 3) (hw.toLp w)

lemma tfPairing_apply (w : α → ℝ) (hw : MemLp w (5 / 2) μ) (f : TFLp μ) :
    tfPairing w hw f = ∫ x, w x * f x ∂μ := by
  rw [tfPairing, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hw.coeFn_toLp] with x hx
  exact congrArg (fun c => c * f x) hx

lemma tfPairing_integrable (w : α → ℝ) (hw : MemLp w (5 / 2) μ) (f : TFLp μ) :
    Integrable (fun x => w x * f x) μ := by
  exact hw.integrable_mul (Lp.memLp f)

end Pairing

def tfCoulombL (R : ℝ) : TFLp (ballMeasure R) →L[ℝ] TFLp (ballMeasure R) →L[ℝ] ℝ :=
  ((tfPairing (fun p : TFSpace × TFSpace => ‖p.1 - p.2‖⁻¹) (coulomb_memLp R)).postcomp
    (TFLp (ballMeasure R))).comp tfTensorL

lemma tfCoulombL_apply (R : ℝ) (f g : TFLp (ballMeasure R)) :
    tfCoulombL R f g = ∫ p : TFSpace × TFSpace, f p.1 * g p.2 / ‖p.1 - p.2‖
      ∂((ballMeasure R).prod (ballMeasure R)) := by
  change tfPairing _ _ (tfTensor f g) = _
  rw [tfPairing_apply]
  apply integral_congr_ae
  filter_upwards [tfTensor_coe f g] with p hp
  rw [hp, div_eq_mul_inv (f p.1 * g p.2) ‖p.1 - p.2‖, mul_comm]

lemma tfCoulomb_integrable (R : ℝ) (f g : TFLp (ballMeasure R)) :
    Integrable (fun p : TFSpace × TFSpace => f p.1 * g p.2 / ‖p.1 - p.2‖)
      ((ballMeasure R).prod (ballMeasure R)) := by
  have hi := tfPairing_integrable _ (coulomb_memLp R) (tfTensor f g)
  apply hi.congr
  filter_upwards [tfTensor_coe f g] with p hp
  rw [hp, div_eq_mul_inv (f p.1 * g p.2) ‖p.1 - p.2‖, mul_comm]


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

section

variable {E : Type*} [NormedAddCommGroup E]

def gaussian (b : ℝ) (x : E) : ℝ := Real.exp (-b * ‖x‖ ^ 2)

lemma gaussian_pos (b : ℝ) (x : E) : 0 < gaussian b x := Real.exp_pos _

lemma gaussian_bound {b : ℝ} (hb : 0 ≤ b) (x : E) : gaussian b x ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (sq_nonneg _))

lemma gaussian_continuous (b : ℝ) : Continuous (gaussian b : E → ℝ) := by
  unfold gaussian
  fun_prop

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma gaussian_integral {b : ℝ} (hb : 0 < b) :
    (∫ x : E, gaussian b x) = (Real.pi / b) ^ ((Module.finrank ℝ E : ℝ) / 2) :=
  GaussianFourier.integral_rexp_neg_mul_sq_norm hb

lemma gaussian_integrable {b : ℝ} (hb : 0 < b) : Integrable (gaussian b : E → ℝ) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussian_integral hb]
  exact ne_of_gt (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gaussian_overlap (b : ℝ) (x y z : E) :
    gaussian (2 * b) (z - x) * gaussian (2 * b) (z - y) =
      gaussian b (x - y) * gaussian (4 * b) (z - (1 / 2 : ℝ) • (x + y)) := by
  simp only [gaussian, ← Real.exp_add]
  congr 1
  simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_right,
    real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

lemma gaussian_overlap_integral {b : ℝ} (hb : 0 < b) (x y : E) :
    (∫ z : E, gaussian (2 * b) (z - x) * gaussian (2 * b) (z - y)) =
      gaussian b (x - y) * (Real.pi / (4 * b)) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
  simp_rw [gaussian_overlap]
  rw [integral_const_mul, integral_sub_right_eq_self, gaussian_integral (by positivity)]

lemma gaussian_overlap_integrable {b : ℝ} (hb : 0 < b) (x y : E) :
    Integrable (fun z : E => gaussian (2 * b) (z - x) * gaussian (2 * b) (z - y)) := by
  simp_rw [gaussian_overlap]
  exact ((gaussian_integrable (E := E) (show 0 < 4 * b by positivity)).comp_sub_right
    ((1 / 2 : ℝ) • (x + y))).const_mul _

lemma integrable_gaussian_quadratic {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 ≤ b) :
    Integrable (fun p : E × E => f p.1 * f p.2 * gaussian b (p.1 - p.2)) := by
  apply (hf.mul_prod hf).mul_bdd (c := 1) ((gaussian_continuous b).comp
    (continuous_fst.sub continuous_snd)).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖gaussian b (p.1 - p.2)‖ ≤ 1
    rw [Real.norm_of_nonneg (gaussian_pos b _).le]
    exact gaussian_bound hb _

lemma integrable_gaussian_triple {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    Integrable (fun p : (E × E) × E => (f p.1.1 * f p.1.2) *
      (gaussian (2 * b) (p.2 - p.1.1) * gaussian (2 * b) (p.2 - p.1.2))) := by
  have hm : AEStronglyMeasurable (fun p : (E × E) × E => (f p.1.1 * f p.1.2) *
      (gaussian (2 * b) (p.2 - p.1.1) * gaussian (2 * b) (p.2 - p.1.2))) := by
    exact ((hf.mul_prod hf).aestronglyMeasurable.comp_fst).mul
      (show Continuous (fun p : (E × E) × E =>
        gaussian (2 * b) (p.2 - p.1.1) * gaussian (2 * b) (p.2 - p.1.2)) from by
          unfold gaussian
          fun_prop).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Eventually.of_forall fun p => (gaussian_overlap_integrable hb p.1 p.2).const_mul (f p.1 * f p.2)
  · have he (p : E × E) : (∫ z : E, ‖(f p.1 * f p.2) *
        (gaussian (2 * b) (z - p.1) * gaussian (2 * b) (z - p.2))‖) =
        (‖f p.1‖ * ‖f p.2‖ * gaussian b (p.1 - p.2)) *
          (Real.pi / (4 * b)) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
      simp only [norm_mul, Real.norm_of_nonneg (gaussian_pos _ _).le]
      rw [integral_const_mul, gaussian_overlap_integral hb]
      ring
    simp_rw [he]
    exact (integrable_gaussian_quadratic hf.norm hb.le).mul_const _

theorem gaussian_quadratic_nonneg {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ ∫ p : E × E, f p.1 * f p.2 * gaussian b (p.1 - p.2) := by
  rcases hb.eq_or_lt with rfl | hb
  · simp only [gaussian, neg_zero, zero_mul, Real.exp_zero, mul_one]
    have h := integral_prod_mul (μ := (volume : Measure E)) (ν := volume) f f
    change 0 ≤ ∫ p : E × E, f p.1 * f p.2 ∂(volume.prod volume)
    rw [h]
    exact mul_self_nonneg (∫ x : E, f x)
  let c : ℝ := (Real.pi / (4 * b)) ^ ((Module.finrank ℝ E : ℝ) / 2)
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  have he : (∫ p : E × E, f p.1 * f p.2 * gaussian b (p.1 - p.2)) * c =
      ∫ z : E, (∫ x : E, f x * gaussian (2 * b) (z - x)) ^ 2 := by
    calc
      _ = ∫ p : E × E, ∫ z : E, (f p.1 * f p.2) *
          (gaussian (2 * b) (z - p.1) * gaussian (2 * b) (z - p.2)) := by
        simp_rw [integral_const_mul, gaussian_overlap_integral hb, ← mul_assoc]
        exact (integral_mul_const _ _).symm
      _ = ∫ z : E, ∫ p : E × E, (f p.1 * f p.2) *
          (gaussian (2 * b) (z - p.1) * gaussian (2 * b) (z - p.2)) :=
        integral_integral_swap (integrable_gaussian_triple hf hb)
      _ = _ := by
        apply integral_congr_ae (Eventually.of_forall fun z => ?_)
        have hp : (fun p : E × E => (f p.1 * f p.2) *
            (gaussian (2 * b) (z - p.1) * gaussian (2 * b) (z - p.2))) =
            (fun p : E × E => (f p.1 * gaussian (2 * b) (z - p.1)) *
              (f p.2 * gaussian (2 * b) (z - p.2))) := by
          funext p; ring
        rw [hp, pow_two]
        exact integral_prod_mul (μ := (volume : Measure E)) (ν := volume)
          (fun x => f x * gaussian (2 * b) (z - x))
          (fun x => f x * gaussian (2 * b) (z - x))
  have hh : (0 : ℝ) ≤ ∫ z : E, (∫ x : E, f x * gaussian (2 * b) (z - x)) ^ 2 :=
    integral_nonneg (fun z : E => sq_nonneg (∫ x : E, f x * gaussian (2 * b) (z - x)))
  rw [← he] at hh
  exact nonneg_of_mul_nonneg_left hh hc

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma coulomb_gaussian_integral (x : E) :
    (∫ t : ℝ, gaussian (t ^ 2) x) = Real.sqrt Real.pi / ‖x‖ := by
  have h (t : ℝ) : gaussian (t ^ 2) x = Real.exp (-(‖x‖ ^ 2) * t ^ 2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [h]
  rw [integral_gaussian, Real.sqrt_div (le_of_lt Real.pi_pos), Real.sqrt_sq (norm_nonneg x)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma coulomb_gaussian_integrable {x : E} (hx : x ≠ 0) :
    Integrable (fun t : ℝ => gaussian (t ^ 2) x) := by
  have h (t : ℝ) : gaussian (t ^ 2) x = Real.exp (-(‖x‖ ^ 2) * t ^ 2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [h]
  exact integrable_exp_neg_mul_sq (sq_pos_of_pos (norm_pos_iff.mpr hx))

variable [Nontrivial E]

lemma ae_off_diagonal : ∀ᵐ p : E × E, p.1 ≠ p.2 := by
  change ∀ᵐ p ∂(volume : Measure E).prod volume, p.1 ≠ p.2
  apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
  exact Eventually.of_forall fun x => by
    apply ae_iff.mpr
    have hs : {y : E | ¬ x ≠ y} = {x} := by
      ext y
      simp [eq_comm]
    change volume {a : E | ¬ x ≠ a} = 0
    rw [hs]
    exact measure_singleton x

theorem coulomb_quadratic_nonneg {f : E → ℝ} (hf : Integrable f)
    (hD : Integrable (fun p : E × E => f p.1 * f p.2 / ‖p.1 - p.2‖)) :
    0 ≤ ∫ p : E × E, f p.1 * f p.2 / ‖p.1 - p.2‖ := by
  let F : (E × E) × ℝ → ℝ := fun p => f p.1.1 * f p.1.2 * gaussian (p.2 ^ 2) (p.1.1 - p.1.2)
  have hm : AEStronglyMeasurable F := by
    apply ((hf.mul_prod hf).aestronglyMeasurable.comp_fst).mul
    have hcont : Continuous (fun p : (E × E) × ℝ => gaussian (p.2 ^ 2) (p.1.1 - p.1.2)) := by
      unfold gaussian
      fun_prop
    exact hcont.aestronglyMeasurable
  have hint (p : E × E) : (∫ t : ℝ, ‖F (p, t)‖) =
      ‖f p.1 * f p.2 / ‖p.1 - p.2‖‖ * Real.sqrt Real.pi := by
    simp only [F, norm_mul, Real.norm_of_nonneg (gaussian_pos _ _).le]
    rw [integral_const_mul, coulomb_gaussian_integral]
    simp only [norm_div, norm_mul, norm_norm]
    ring
  have hF : Integrable F := by
    apply (integrable_prod_iff hm).mpr
    constructor
    · filter_upwards [ae_off_diagonal (E := E)] with p hp
      exact (coulomb_gaussian_integrable (sub_ne_zero.mpr hp)).const_mul (f p.1 * f p.2)
    · simp_rw [hint]
      exact hD.norm.mul_const _
  have he : (∫ p : E × E, f p.1 * f p.2 / ‖p.1 - p.2‖) * Real.sqrt Real.pi =
      ∫ t : ℝ, ∫ p : E × E, f p.1 * f p.2 * gaussian (t ^ 2) (p.1 - p.2) := by
    calc
      _ = ∫ p : E × E, ∫ t : ℝ, F (p, t) := by
        simp_rw [F, integral_const_mul, coulomb_gaussian_integral]
        rw [← integral_mul_const]
        apply integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring
      _ = _ := integral_integral_swap hF
  have hn : (0 : ℝ) ≤ ∫ t : ℝ, ∫ p : E × E, f p.1 * f p.2 * gaussian (t ^ 2) (p.1 - p.2) :=
    integral_nonneg fun t => gaussian_quadratic_nonneg hf (sq_nonneg t)
  rw [← he] at hn
  exact nonneg_of_mul_nonneg_left hn (Real.sqrt_pos.mpr Real.pi_pos)

end

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

def tfExtension (R : ℝ) (f : TFLp (ballMeasure R)) : TFSpace → ℝ :=
  (ball 0 R).indicator f

lemma tfExtension_integrable (R : ℝ) (f : TFLp (ballMeasure R)) : Integrable (tfExtension R f) :=
  IntegrableOn.integrable_indicator ((Lp.memLp f).integrable (Fact.out : (1 : ENNReal) ≤ 5 / 3))
    measurableSet_ball

lemma tfExtension_direct (R : ℝ) (f g : TFLp (ballMeasure R)) (p : TFSpace × TFSpace) :
    tfExtension R f p.1 * tfExtension R g p.2 / ‖p.1 - p.2‖ =
      ((ball (0 : TFSpace) R) ×ˢ ball 0 R).indicator
        (fun p : TFSpace × TFSpace => f p.1 * g p.2 / ‖p.1 - p.2‖) p := by
  classical
  by_cases h1 : p.1 ∈ ball (0 : TFSpace) R <;>
    by_cases h2 : p.2 ∈ ball (0 : TFSpace) R <;> simp [tfExtension, h1, h2]

lemma tfExtension_coulomb_integrable (R : ℝ) (f g : TFLp (ballMeasure R)) :
    Integrable (fun p : TFSpace × TFSpace => tfExtension R f p.1 * tfExtension R g p.2 / ‖p.1 - p.2‖) := by
  simp_rw [tfExtension_direct]
  apply IntegrableOn.integrable_indicator _ (measurableSet_ball.prod measurableSet_ball)
  have hi := tfCoulomb_integrable R f g
  simp only [ballMeasure, Measure.prod_restrict] at hi
  exact hi

lemma tfCoulombL_extension (R : ℝ) (f g : TFLp (ballMeasure R)) :
    tfCoulombL R f g = ∫ p : TFSpace × TFSpace,
      tfExtension R f p.1 * tfExtension R g p.2 / ‖p.1 - p.2‖ := by
  simp_rw [tfExtension_direct]
  rw [integral_indicator (measurableSet_ball.prod measurableSet_ball), tfCoulombL_apply]
  simp only [ballMeasure, Measure.prod_restrict]
  rfl

lemma tfCoulombL_nonneg (R : ℝ) (f : TFLp (ballMeasure R)) : 0 ≤ tfCoulombL R f f := by
  rw [tfCoulombL_extension]
  exact coulomb_quadratic_nonneg (tfExtension_integrable R f) (tfExtension_coulomb_integrable R f f)

lemma tfCoulombL_symmetric (R : ℝ) (f g : TFLp (ballMeasure R)) :
    tfCoulombL R f g = tfCoulombL R g f := by
  rw [tfCoulombL_apply, tfCoulombL_apply]
  rw [← MeasureTheory.integral_prod_swap (f := fun p : TFSpace × TFSpace =>
    g p.1 * f p.2 / ‖p.1 - p.2‖)]
  apply integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp
  rw [norm_sub_rev, mul_comm]

lemma tfCoulombL_midpoint_gap (R : ℝ) (f g : TFLp (ballMeasure R)) :
    0 ≤ (tfCoulombL R f f + tfCoulombL R g g) / 2 -
      tfCoulombL R ((1 / 2 : ℝ) • (f + g)) ((1 / 2 : ℝ) • (f + g)) := by
  have hp := tfCoulombL_nonneg R (f - g)
  simp only [map_sub, sub_apply] at hp
  simp only [map_smul, map_add, smul_apply, add_apply, smul_eq_mul]
  rw [tfCoulombL_symmetric R g f] at hp ⊢
  linarith

def tfBallLinear (R Z η : ℝ) : TFLp (ballMeasure R) →L[ℝ] ℝ :=
  η • tfPairing (fun _ => (1 : ℝ)) (memLp_const 1) -
    Z • tfPairing (fun x : TFSpace => ‖x‖⁻¹) (nuclear_memLp R)

def tfBallFunctional (R T Z η : ℝ) (f : TFLp (ballMeasure R)) : ℝ :=
  T * ‖f‖ ^ (5 / 3 : ℝ) + tfBallLinear R Z η f + (1 / 2 : ℝ) * tfCoulombL R f f

lemma tfBallFunctional_continuous (R T Z η : ℝ) : Continuous (tfBallFunctional R T Z η) := by
  apply Continuous.add
  · exact ((continuous_norm.rpow_const (fun _ => Or.inr (by norm_num))).const_mul T).add
      (tfBallLinear R Z η).continuous
  · exact ((tfCoulombL R).continuous₂.comp (continuous_id.prodMk continuous_id)).const_mul _

lemma tf_power_dominates_linear {T : ℝ} (hT : 0 < T) (L : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, B ≤ r → r ≤ T * r ^ (5 / 3 : ℝ) - L * r := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).eventually (eventually_ge_atTop ((L + 1) / T)))
  refine ⟨max B 0, le_max_right _ _, fun r hr => ?_⟩
  have hr0 : 0 ≤ r := (le_max_right _ _).trans hr
  have hp := hB r ((le_max_left _ _).trans hr)
  have he : r ^ (5 / 3 : ℝ) = r * r ^ (2 / 3 : ℝ) := by
    rw [show (5 / 3 : ℝ) = 1 + 2 / 3 by norm_num,
      Real.rpow_add_of_nonneg hr0 (by norm_num) (by norm_num), Real.rpow_one]
  rw [div_le_iff₀ hT] at hp
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hp hr0]

lemma tfBallFunctional_lower (R T Z η : ℝ) (f : TFLp (ballMeasure R)) :
    T * ‖f‖ ^ (5 / 3 : ℝ) - ‖tfBallLinear R Z η‖ * ‖f‖ ≤ tfBallFunctional R T Z η f := by
  have hL := (tfBallLinear R Z η).le_opNorm f
  have hn := neg_abs_le (tfBallLinear R Z η f)
  have hD := tfCoulombL_nonneg R f
  change |tfBallLinear R Z η f| ≤ _ at hL
  unfold tfBallFunctional
  linarith

lemma tfBallFunctional_bddBelow (R Z η : ℝ) {T : ℝ} (hT : 0 < T) :
    BddBelow (Set.range (tfBallFunctional R T Z η)) := by
  obtain ⟨B, hB0, hB⟩ := tf_power_dominates_linear hT ‖tfBallLinear R Z η‖
  refine ⟨-‖tfBallLinear R Z η‖ * B, ?_⟩
  rintro _ ⟨f, rfl⟩
  apply le_trans _ (tfBallFunctional_lower R T Z η f)
  by_cases hb : B ≤ ‖f‖
  · exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (norm_nonneg _)) hB0).trans
      ((norm_nonneg _).trans (hB _ hb))
  · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hb) (norm_nonneg (tfBallLinear R Z η))
    have hp := mul_nonneg hT.le (Real.rpow_nonneg (norm_nonneg f) (5 / 3 : ℝ))
    linarith

lemma tfBallFunctional_coercive (R Z η a : ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ B : ℝ, ∀ f : TFLp (ballMeasure R), tfBallFunctional R T Z η f ≤ a → ‖f‖ ≤ B := by
  obtain ⟨B, _, hB⟩ := tf_power_dominates_linear hT ‖tfBallLinear R Z η‖
  refine ⟨max B a, fun f hf => ?_⟩
  by_cases hb : B ≤ ‖f‖
  · exact ((hB _ hb).trans ((tfBallFunctional_lower R T Z η f).trans hf)).trans (le_max_right _ _)
  · exact (le_of_not_ge hb).trans (le_max_left _ _)

lemma nonnegDensity_smul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : TFLp μ} (hf : NonnegDensity f) {c : ℝ} (hc : 0 ≤ c) : NonnegDensity (c • f) := by
  filter_upwards [hf, Lp.coeFn_smul c f] with x hx he
  rw [he]
  exact mul_nonneg hc hx

lemma tfLp_midpoint_gap {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : TFLp μ} (hf : NonnegDensity f) (hg : NonnegDensity g) :
    (5 / 36 : ℝ) * densityWeight f g ≤
      (‖f‖ ^ (5 / 3 : ℝ) + ‖g‖ ^ (5 / 3 : ℝ)) / 2 - ‖(1 / 2 : ℝ) • (f + g)‖ ^ (5 / 3 : ℝ) := by
  have hh := tfWeight_integral_gap (Lp.memLp f) (Lp.memLp g) hf hg
  rw [tfLp_norm_rpow_nonneg hf, tfLp_norm_rpow_nonneg hg,
    tfLp_norm_rpow_nonneg (nonnegDensity_smul (nonnegDensity_add hf hg) (by norm_num))]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (f + g), Lp.coeFn_add f g] with x hs ha
  rw [hs, Pi.smul_apply, smul_eq_mul, ha, Pi.add_apply]
  congr 1
  ring

lemma tfBallFunctional_gap (R T Z η : ℝ) (hT : 0 ≤ T) {f g : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hg : NonnegDensity g) :
    (T * (5 / 36 : ℝ)) * densityWeight f g ≤
      (tfBallFunctional R T Z η f + tfBallFunctional R T Z η g) / 2 -
        tfBallFunctional R T Z η ((1 / 2 : ℝ) • (f + g)) := by
  have hk := mul_le_mul_of_nonneg_left (tfLp_midpoint_gap hf hg) hT
  have hD := tfCoulombL_midpoint_gap R f g
  unfold tfBallFunctional
  simp only [map_smul, map_add, smul_apply, add_apply, smul_eq_mul] at hD ⊢
  nlinarith

theorem tfBallFunctional_exists_minimizer (R Z η : ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ f : TFLp (ballMeasure R), NonnegDensity f ∧
      ∀ g : TFLp (ballMeasure R), NonnegDensity g →
        tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g := by
  apply exists_minimizer_of_tf_gap (C := {f | NonnegDensity f}) isClosed_nonnegDensity
  · refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ (5 / 3) (ballMeasure R)] with x hx
    rw [hx]
    exact le_rfl
  · exact fun _ hf => hf
  · exact fun _ hf _ hg => nonnegDensity_smul (nonnegDensity_add hf hg) (by norm_num)
  · exact (tfBallFunctional_continuous R T Z η).continuousOn
  · exact (tfBallFunctional_bddBelow R Z η hT).mono (Set.image_subset_range _ _)
  · intro a
    obtain ⟨B, hB⟩ := tfBallFunctional_coercive R Z η a hT
    exact ⟨B, fun f _ hf => hB f hf⟩
  · exact mul_pos hT (by norm_num : (0 : ℝ) < 5 / 36)
  · exact fun _ hf _ hg => tfBallFunctional_gap R T Z η hT.le hf hg

lemma tfBallFunctional_min_unique (R Z η : ℝ) {T : ℝ} (hT : 0 < T)
    {f g : TFLp (ballMeasure R)} (hf : NonnegDensity f) (hg : NonnegDensity g)
    (hminf : ∀ u, NonnegDensity u → tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η u)
    (hming : ∀ u, NonnegDensity u → tfBallFunctional R T Z η g ≤ tfBallFunctional R T Z η u) : f = g := by
  have hh := nonnegDensity_smul (nonnegDensity_add hf hg) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h1 := hminf _ hh
  have h2 := hming _ hh
  have hgap := tfBallFunctional_gap R T Z η hT.le hf hg
  have hw : densityWeight f g = 0 := by
    apply le_antisymm _ (densityWeight_nonneg hf hg)
    have hp : 0 < T * (5 / 36 : ℝ) := mul_pos hT (by norm_num)
    nlinarith
  have hi := tfLp_interpolation hf hg
  rw [hw, Real.zero_rpow (by norm_num : (5 / 6 : ℝ) ≠ 0), zero_mul] at hi
  have he := le_antisymm hi (Real.rpow_nonneg (norm_nonneg (f - g)) (5 / 3 : ℝ))
  have hz : ‖f - g‖ = 0 := (Real.rpow_eq_zero (norm_nonneg _) (by norm_num)).mp he
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

def tfPowerDerivative (u : ℝ) : ℝ := (5 / 3 : ℝ) * |u| ^ (-1 / 3 : ℝ) * u

lemma tfPowerDerivative_abs (u : ℝ) : |tfPowerDerivative u| = (5 / 3 : ℝ) * |u| ^ (2 / 3 : ℝ) := by
  by_cases hu : u = 0
  · simp [tfPowerDerivative, hu]
  · have ha : 0 < |u| := abs_pos.mpr hu
    rw [tfPowerDerivative, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 3),
      abs_of_nonneg (Real.rpow_nonneg ha.le _)]
    have he := Real.rpow_add ha (-1 / 3) 1
    norm_num at he
    rw [mul_assoc, neg_div, ← he]

lemma tfPowerDerivative_nonneg {u : ℝ} (hu : 0 ≤ u) :
    tfPowerDerivative u = (5 / 3 : ℝ) * u ^ (2 / 3 : ℝ) := by
  rw [← abs_of_nonneg (show 0 ≤ tfPowerDerivative u from by unfold tfPowerDerivative; positivity),
    tfPowerDerivative_abs, abs_of_nonneg hu]

lemma hasDerivAt_tfPower (a b t : ℝ) :
    HasDerivAt (fun s : ℝ => |a + s * b| ^ (5 / 3 : ℝ))
      (tfPowerDerivative (a + t * b) * b) t := by
  have hh : HasDerivAt (fun s : ℝ => a + s * b) b t := by
    simpa using (((hasDerivAt_id t).mul_const b).const_add a)
  have hd := (hasDerivAt_abs_rpow (a + t * b) (by norm_num : (1 : ℝ) < 5 / 3)).comp t hh
  simpa only [Function.comp_def, tfPowerDerivative,
    show (5 / 3 - 2 : ℝ) = -1 / 3 by norm_num] using hd

lemma tfPowerDerivative_bound (a b t : ℝ) (ht : |t| ≤ 1) :
    ‖tfPowerDerivative (a + t * b) * b‖ ≤
      (5 / 3 : ℝ) * (|a| + |b|) ^ (5 / 3 : ℝ) := by
  have hs : 0 ≤ |a| + |b| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hh : |a + t * b| ≤ |a| + |b| := by
    calc
      _ ≤ |a| + |t * b| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul]; nlinarith [mul_le_mul_of_nonneg_right ht (abs_nonneg b)]
  rw [Real.norm_eq_abs, abs_mul, tfPowerDerivative_abs]
  have hp := Real.rpow_le_rpow (abs_nonneg _) hh (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hS : (|a| + |b|) ^ (5 / 3 : ℝ) = (|a| + |b|) ^ (2 / 3 : ℝ) * (|a| + |b|) := by
    rw [show (5 / 3 : ℝ) = 2 / 3 + 1 by norm_num,
      Real.rpow_add_of_nonneg hs (by norm_num) (by norm_num), Real.rpow_one]
  rw [hS]
  nlinarith [mul_le_mul hp (show |b| ≤ |a| + |b| by linarith [abs_nonneg a])
    (abs_nonneg b) (Real.rpow_nonneg hs (2 / 3 : ℝ))]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfDilation
attribute [-instance] _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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
namespace CoulombAtom

def tfDilation (b : ℝ) (ρ : Space → ℝ) (x : Space) : ℝ := b ^ 6 * ρ (b • x)

local instance instIsAddHaarMeasureProdSpaceVolume : Measure.IsAddHaarMeasure (volume : Measure (Space × Space)) := by
  change Measure.IsAddHaarMeasure ((volume : Measure Space).prod volume)
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma space_finrank : Module.finrank ℝ Space = 3 := by simp [Space]

lemma product_finrank : Module.finrank ℝ (Space × Space) = 6 := by
  rw [Module.finrank_prod, space_finrank]

lemma tfDilation_mass {b : ℝ} (hb : 0 < b) (ρ : Space → ℝ) :
    (∫ x, tfDilation b ρ x) = b ^ 3 * ∫ x, ρ x := by
  simp only [tfDilation, integral_const_mul]
  rw [Measure.integral_comp_smul_of_nonneg volume ρ b (hR := hb.le), space_finrank]
  simp only [smul_eq_mul]
  field_simp

lemma tfDilation_kinetic {b : ℝ} (hb : 0 < b) (ρ : Space → ℝ) (x : Space) (hx : 0 ≤ ρ (b • x)) :
    (tfDilation b ρ x) ^ (5 / 3 : ℝ) = b ^ 10 * ρ (b • x) ^ (5 / 3 : ℝ) := by
  rw [tfDilation, Real.mul_rpow (pow_nonneg hb.le _) hx]
  congr 1
  rw [← Real.rpow_natCast b 6, ← Real.rpow_mul hb.le]
  norm_num

lemma tfDilation_nuclear {b : ℝ} (hb : 0 < b) (ρ : Space → ℝ) (x : Space) :
    tfDilation b ρ x / ‖x‖ = b ^ 7 * (ρ (b • x) / ‖b • x‖) := by
  rw [tfDilation, norm_smul, Real.norm_of_nonneg hb.le]
  field_simp

lemma tfDilation_direct {b : ℝ} (hb : 0 < b) (ρ : Space → ℝ) (p : Space × Space) :
    directIntegrand (tfDilation b ρ) p = b ^ 13 * directIntegrand ρ (b • p) := by
  simp only [directIntegrand, tfDilation, Prod.smul_fst, Prod.smul_snd, ← smul_sub,
    norm_smul, Real.norm_of_nonneg hb.le]
  field_simp

lemma tfDilation_admissible {b : ℝ} (hb : 0 < b) {M : ℝ} {ρ : Space → ℝ}
    (hρ : TFAdmissible M ρ) : TFAdmissible (b ^ 3 * M) (tfDilation b ρ) := by
  rcases hρ with ⟨hpos, hint, hmass, hkin, hnuc, hdir⟩
  refine ⟨?_, (hint.comp_smul hb.ne').const_mul _, ?_, ?_, ?_, ?_⟩
  · filter_upwards [(Measure.quasiMeasurePreserving_smul volume hb.ne').ae hpos] with x hx
    exact mul_nonneg (pow_nonneg hb.le _) hx
  · rw [tfDilation_mass hb, hmass]
  · have he : (fun x => (tfDilation b ρ x) ^ (5 / 3 : ℝ)) =ᵐ[volume]
        (fun x => b ^ 10 * ρ (b • x) ^ (5 / 3 : ℝ)) := by
      filter_upwards [(Measure.quasiMeasurePreserving_smul volume hb.ne').ae hpos] with x hx
      exact tfDilation_kinetic hb ρ x hx
    exact ((hkin.comp_smul hb.ne').const_mul _).congr he.symm
  · simp_rw [tfDilation_nuclear hb]
    exact (hnuc.comp_smul hb.ne').const_mul _
  · change Integrable (fun p => directIntegrand (tfDilation b ρ) p)
    simp_rw [tfDilation_direct hb]
    exact (hdir.comp_smul hb.ne').const_mul _

lemma tfDilation_functional {b : ℝ} (hb : 0 < b) (Z : ℝ) (ρ : Space → ℝ)
    (hpos : ∀ᵐ x, 0 ≤ ρ x) :
    tfFunctional (b ^ 3 * Z) (tfDilation b ρ) = b ^ 7 * tfFunctional Z ρ := by
  have hk : (∫ x, (tfDilation b ρ x) ^ (5 / 3 : ℝ)) =
      b ^ 10 * ∫ x, ρ (b • x) ^ (5 / 3 : ℝ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(Measure.quasiMeasurePreserving_smul volume hb.ne').ae hpos] with x hx
    exact tfDilation_kinetic hb ρ x hx
  simp only [tfFunctional, hk, tfDilation_nuclear hb, tfDilation_direct hb, integral_const_mul]
  rw [Measure.integral_comp_smul_of_nonneg volume (fun x : Space => ρ x ^ (5 / 3 : ℝ)) b (hR := hb.le),
    Measure.integral_comp_smul_of_nonneg volume (fun x : Space => ρ x / ‖x‖) b (hR := hb.le),
    Measure.integral_comp_smul_of_nonneg volume (directIntegrand ρ) b (hR := hb.le),
    space_finrank, product_finrank]
  simp only [smul_eq_mul]
  field_simp

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace CoulombAnalysis
open CoulombAtom

lemma tfKinetic_pos : 0 < tfKinetic := by
  unfold tfKinetic
  positivity

lemma tfExtension_nonneg {R : ℝ} {f : TFLp (ballMeasure R)} (hf : NonnegDensity f) :
    ∀ᵐ x, 0 ≤ tfExtension R f x := by
  have hh := (ae_restrict_iff' measurableSet_ball).mp hf
  filter_upwards [hh] with x hx
  by_cases hx' : x ∈ ball (0 : TFSpace) R
  · simpa [tfExtension, hx'] using hx hx'
  · simp [tfExtension, hx']

lemma tfExtension_kinetic (R : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) :
    tfExtension R f x ^ (5 / 3 : ℝ) =
      (ball 0 R).indicator (fun x => f x ^ (5 / 3 : ℝ)) x := by
  classical
  by_cases hx : x ∈ ball (0 : TFSpace) R <;> simp [tfExtension, hx]

lemma tfExtension_nuclear (R : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) :
    tfExtension R f x / ‖x‖ = (ball 0 R).indicator (fun x => f x / ‖x‖) x := by
  classical
  by_cases hx : x ∈ ball (0 : TFSpace) R <;> simp [tfExtension, hx]

lemma tfExtension_kinetic_integrable {R : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) : Integrable (fun x => tfExtension R f x ^ (5 / 3 : ℝ)) := by
  simp_rw [tfExtension_kinetic]
  exact IntegrableOn.integrable_indicator (tf_integrable (Lp.memLp f) hf) measurableSet_ball

lemma tfExtension_nuclear_integrable (R : ℝ) (f : TFLp (ballMeasure R)) :
    Integrable (fun x => tfExtension R f x / ‖x‖) := by
  simp_rw [tfExtension_nuclear]
  apply IntegrableOn.integrable_indicator _ measurableSet_ball
  simpa only [div_eq_inv_mul, ballMeasure, IntegrableOn] using tfPairing_integrable _ (nuclear_memLp R) f

lemma tfExtension_admissible {R : ℝ} {f : TFLp (ballMeasure R)} (hf : NonnegDensity f) :
    TFAdmissible (∫ x, tfExtension R f x) (tfExtension R f) :=
  ⟨tfExtension_nonneg hf, tfExtension_integrable R f, rfl,
    tfExtension_kinetic_integrable hf, tfExtension_nuclear_integrable R f,
    tfExtension_coulomb_integrable R f f⟩

lemma tfExtension_functional {R : ℝ} {f : TFLp (ballMeasure R)} (hf : NonnegDensity f)
    (Z η : ℝ) : tfFunctional Z (tfExtension R f) + η * (∫ x, tfExtension R f x) =
      tfBallFunctional R tfKinetic Z η f := by
  unfold tfFunctional tfBallFunctional tfBallLinear
  rw [tfLp_norm_rpow_nonneg hf, tfCoulombL_extension]
  simp only [sub_apply, smul_apply,
    smul_eq_mul, tfPairing_apply, one_mul]
  have hk : (∫ x, (tfExtension R f x) ^ (5 / 3 : ℝ)) =
      ∫ x, f x ^ (5 / 3 : ℝ) ∂ballMeasure R := by
    simp_rw [tfExtension_kinetic]
    exact integral_indicator measurableSet_ball
  have hn : (∫ x, tfExtension R f x / ‖x‖) =
      ∫ x, ‖x‖⁻¹ * f x ∂ballMeasure R := by
    simp_rw [tfExtension_nuclear, div_eq_inv_mul]
    exact integral_indicator measurableSet_ball
  rw [hk, hn, show (∫ x, tfExtension R f x) = ∫ x, f x ∂ballMeasure R from
    integral_indicator measurableSet_ball]
  dsimp only [directIntegrand]
  ring

lemma tfAdmissible_memLp {M : ℝ} {ρ : Space → ℝ} (hρ : TFAdmissible M ρ) :
    MemLp ρ (5 / 3) := by
  apply (integrable_norm_rpow_iff hρ.2.1.aestronglyMeasurable
    (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  norm_num
  exact hρ.2.2.2.1.congr (hρ.1.mono fun x hx => by dsimp; rw [abs_of_nonneg hx])

lemma tfAdmissible_truncate {M : ℝ} {ρ : Space → ℝ} (hρ : TFAdmissible M ρ) (R : ℝ) :
    ∃ f : TFLp (ballMeasure R), NonnegDensity f ∧ tfExtension R f =ᵐ[volume]
      (ball 0 R).indicator ρ := by
  let hm : MemLp ρ (5 / 3) (ballMeasure R) := (tfAdmissible_memLp hρ).restrict _
  refine ⟨hm.toLp ρ, ?_, ?_⟩
  · filter_upwards [hm.coeFn_toLp, ae_restrict_of_ae hρ.1] with x he hx
    rw [he]
    exact hx
  · have hh := (ae_restrict_iff' measurableSet_ball).mp hm.coeFn_toLp
    filter_upwards [hh] with x hx
    by_cases hx' : x ∈ ball (0 : TFSpace) R
    · simpa [tfExtension, hx'] using hx hx'
    · simp [tfExtension, hx']

lemma tfFunctional_congr_ae (Z : ℝ) {ρ σ : Space → ℝ} (he : ρ =ᵐ[volume] σ) :
    tfFunctional Z ρ = tfFunctional Z σ := by
  have hk := integral_congr_ae (he.fun_comp fun t => t ^ (5 / 3 : ℝ))
  dsimp only [Function.comp_def] at hk
  have hn := integral_congr_ae (he.mono fun x hx => congrArg (fun t => t / ‖x‖) hx)
  have hd : directIntegrand ρ =ᵐ[volume] directIntegrand σ := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae he,
      Measure.quasiMeasurePreserving_snd.ae he] with p h1 h2
    simp only [directIntegrand, h1, h2]
  simp only [tfFunctional, hk, hn, integral_congr_ae hd]

lemma tfIndicator_direct (R : ℝ) (ρ : Space → ℝ) (p : Space × Space) :
    directIntegrand ((ball 0 R).indicator ρ) p =
      ((ball (0 : Space) R) ×ˢ ball 0 R).indicator (directIntegrand ρ) p := by
  classical
  by_cases h1 : p.1 ∈ ball (0 : Space) R <;>
    by_cases h2 : p.2 ∈ ball (0 : Space) R <;> simp [directIntegrand, h1, h2]

lemma tfIndicator_kinetic (R : ℝ) (ρ : Space → ℝ) (x : Space) :
    ((ball 0 R).indicator ρ x) ^ (5 / 3 : ℝ) =
      (ball 0 R).indicator (fun x => ρ x ^ (5 / 3 : ℝ)) x := by
  classical
  by_cases hx : x ∈ ball (0 : Space) R <;> simp [hx]

lemma tfIndicator_linear (R Z : ℝ) (ρ : Space → ℝ) (x : Space) :
    (ball 0 R).indicator ρ x - Z * ((ball 0 R).indicator ρ x / ‖x‖) =
      (ball 0 R).indicator (fun x => ρ x - Z * (ρ x / ‖x‖)) x := by
  classical
  by_cases hx : x ∈ ball (0 : Space) R <;> simp [hx]

lemma tfPriced_truncate_le {Z M : ℝ} (hZ : 0 < Z) {ρ : Space → ℝ}
    (hρ : TFAdmissible M ρ) :
    tfFunctional Z ((ball 0 Z).indicator ρ) + (∫ x, (ball 0 Z).indicator ρ x) ≤
      tfFunctional Z ρ + (∫ x, ρ x) := by
  have hk : (∫ x, ((ball 0 Z).indicator ρ x) ^ (5 / 3 : ℝ)) ≤
      ∫ x, ρ x ^ (5 / 3 : ℝ) := by
    simp_rw [tfIndicator_kinetic]
    apply integral_mono_ae (hρ.2.2.2.1.indicator measurableSet_ball) hρ.2.2.2.1
    filter_upwards [hρ.1] with x hx
    by_cases hxb : x ∈ ball (0 : Space) Z
    · simp [hxb]
    · simpa only [indicator_of_notMem hxb] using Real.rpow_nonneg hx (5 / 3 : ℝ)
  have hd : (∫ p, directIntegrand ((ball 0 Z).indicator ρ) p) ≤
      ∫ p, directIntegrand ρ p := by
    simp_rw [tfIndicator_direct]
    apply integral_mono_ae (hρ.2.2.2.2.2.indicator (measurableSet_ball.prod measurableSet_ball)) hρ.2.2.2.2.2
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hρ.1,
      Measure.quasiMeasurePreserving_snd.ae hρ.1] with p h1 h2
    by_cases hp : p ∈ (ball (0 : Space) Z) ×ˢ ball 0 Z
    · simp [hp]
    · simp only [indicator_of_notMem hp]
      exact div_nonneg (mul_nonneg h1 h2) (norm_nonneg _)
  have hlin := hρ.2.1.sub (hρ.2.2.2.2.1.const_mul Z)
  have hnuc : Integrable (fun x => (ball 0 Z).indicator ρ x / ‖x‖) := by
    have he : (fun x => (ball (0 : Space) Z).indicator ρ x / ‖x‖) =
        (ball 0 Z).indicator (fun x => ρ x / ‖x‖) := by
      ext x
      by_cases hx : x ∈ ball (0 : Space) Z <;> simp [hx]
    rw [he]
    exact hρ.2.2.2.2.1.indicator measurableSet_ball
  have hl : (∫ x, (ball 0 Z).indicator ρ x) - Z * (∫ x, (ball 0 Z).indicator ρ x / ‖x‖) ≤
      (∫ x, ρ x) - Z * (∫ x, ρ x / ‖x‖) := by
    rw [← integral_const_mul, ← integral_sub (hρ.2.1.indicator measurableSet_ball) (hnuc.const_mul Z),
      ← integral_const_mul, ← integral_sub hρ.2.1 (hρ.2.2.2.2.1.const_mul Z)]
    simp_rw [tfIndicator_linear]
    apply integral_mono_ae (hlin.indicator measurableSet_ball) hlin
    filter_upwards [hρ.1] with x hx
    by_cases hx' : x ∈ ball (0 : Space) Z
    · simp [hx']
    · rw [indicator_of_notMem hx']
      have hr : Z ≤ ‖x‖ := le_of_not_gt (mt mem_ball_zero_iff.mpr hx')
      have hr0 := hZ.trans_le hr
      have hh : Z / ‖x‖ ≤ 1 := (div_le_one hr0).mpr hr
      dsimp only [Pi.sub_apply]
      have he : Z * (ρ x / ‖x‖) = (Z / ‖x‖) * ρ x := by ring
      rw [he]
      linarith [mul_le_mul_of_nonneg_right hh hx]
  unfold tfFunctional
  nlinarith [mul_le_mul_of_nonneg_left hk tfKinetic_pos.le]

end CoulombAnalysis

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfPowerIntegralDeriv
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
section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma tf_power_integral_hasDerivAt {f h : α → ℝ} (hf : MemLp f (5 / 3) μ)
    (hh : MemLp h (5 / 3) μ) :
    HasDerivAt (fun t : ℝ => ∫ x, |f x + t * h x| ^ (5 / 3 : ℝ) ∂μ)
      (∫ x, tfPowerDerivative (f x) * h x ∂μ) 0 := by
  have hsum : MemLp (fun x => |f x| + |h x|) (5 / 3) μ := hf.norm.add hh.norm
  have hbound : Integrable (fun x => (5 / 3 : ℝ) * (|f x| + |h x|) ^ (5 / 3 : ℝ)) μ :=
    (tf_integrable hsum (Eventually.of_forall fun x => add_nonneg (abs_nonneg _) (abs_nonneg _))).const_mul _
  have hi := hf.integrable_norm_rpow (by norm_num : (5 / 3 : ENNReal) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
  norm_num at hi
  have hmeas : AEStronglyMeasurable (fun x => tfPowerDerivative (f x) * h x) μ := by
    unfold tfPowerDerivative
    exact ((((hf.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable.const_mul
      _).mul hf.aestronglyMeasurable).mul hh.aestronglyMeasurable)
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t : ℝ => fun x => |f x + t * h x| ^ (5 / 3 : ℝ))
    (F' := fun t : ℝ => fun x => tfPowerDerivative (f x + t * h x) * h x)
    (s := ball (0 : ℝ) 1) (ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall fun t =>
      (((hf.aestronglyMeasurable.add (hh.aestronglyMeasurable.const_mul t)).norm.aemeasurable).pow_const
        _).aestronglyMeasurable)
    (by simpa using hi) (by simpa using hmeas)
    (Eventually.of_forall fun x t ht => tfPowerDerivative_bound (f x) (h x) t
      (le_of_lt (by simpa [Real.dist_eq] using ht))) hbound
    (Eventually.of_forall fun x t _ => hasDerivAt_tfPower (f x) (h x) t)
  simpa using hD.2

lemma tfPowerDerivative_mul_integrable {f h : α → ℝ} (hf : MemLp f (5 / 3) μ)
    (hh : MemLp h (5 / 3) μ) : Integrable (fun x => tfPowerDerivative (f x) * h x) μ := by
  have hsum : MemLp (fun x => |f x| + |h x|) (5 / 3) μ := hf.norm.add hh.norm
  have hi := (tf_integrable hsum (Eventually.of_forall fun x =>
    add_nonneg (abs_nonneg _) (abs_nonneg _))).const_mul (5 / 3 : ℝ)
  apply hi.mono'
  · unfold tfPowerDerivative
    exact ((((hf.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable.const_mul
      _).mul hf.aestronglyMeasurable).mul hh.aestronglyMeasurable)
  · exact Eventually.of_forall fun x => by simpa using tfPowerDerivative_bound (f x) (h x) 0 (by norm_num)

lemma tfLp_kinetic_hasDerivAt (f h : TFLp μ) :
    HasDerivAt (fun t : ℝ => ‖f + t • h‖ ^ (5 / 3 : ℝ))
      (∫ x, tfPowerDerivative (f x) * h x ∂μ) 0 := by
  have he (t : ℝ) : ‖f + t • h‖ ^ (5 / 3 : ℝ) =
      ∫ x, |f x + t * h x| ^ (5 / 3 : ℝ) ∂μ := by
    rw [tfLp_norm_rpow]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f (t • h), Lp.coeFn_smul t h] with x ha hs
    simp only [ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul]
  simp_rw [he]
  exact tf_power_integral_hasDerivAt (Lp.memLp f) (Lp.memLp h)

end

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal


lemma tfBallFunctional_hasDerivAt (R T Z η : ℝ) (f h : TFLp (ballMeasure R)) :
    HasDerivAt (fun t : ℝ => tfBallFunctional R T Z η (f + t • h))
      (T * (∫ x, tfPowerDerivative (f x) * h x ∂ballMeasure R) +
        tfBallLinear R Z η h + tfCoulombL R f h) 0 := by
  have he (t : ℝ) : tfBallFunctional R T Z η (f + t • h) =
      T * ‖f + t • h‖ ^ (5 / 3 : ℝ) +
        (tfBallLinear R Z η f + t * tfBallLinear R Z η h) +
        (1 / 2 : ℝ) * (tfCoulombL R f f + 2 * t * tfCoulombL R f h +
          t * t * tfCoulombL R h h) := by
    simp only [tfBallFunctional, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    rw [tfCoulombL_symmetric R h f]
    ring
  simp_rw [he]
  have hk := (tfLp_kinetic_hasDerivAt f h).const_mul T
  have hl := (((hasDerivAt_id (0 : ℝ)).mul_const (tfBallLinear R Z η h)).const_add (tfBallLinear R Z η f))
  have hq := ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (tfCoulombL R f h)).const_add
    (tfCoulombL R f f)).add (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (tfCoulombL R h h))
  convert! (hk.add hl).add (hq.const_mul (1 / 2 : ℝ)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq]
  ring

lemma hasDerivAt_nonneg_of_right_min {F : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt F d 0)
    (hmin : ∀ t : ℝ, 0 ≤ t → F 0 ≤ F t) : 0 ≤ d := by
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (hmin t ht.le))

lemma tfBallFunctional_variation_nonneg (R T Z η : ℝ) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g)
    {h : TFLp (ballMeasure R)} (hh : NonnegDensity h) :
    0 ≤ T * (∫ x, tfPowerDerivative (f x) * h x ∂ballMeasure R) +
      tfBallLinear R Z η h + tfCoulombL R f h := by
  apply hasDerivAt_nonneg_of_right_min (tfBallFunctional_hasDerivAt R T Z η f h)
  intro t ht
  simpa using hmin (f + t • h) (nonnegDensity_add hf (nonnegDensity_smul hh ht))

lemma tfBallFunctional_variation_self (R T Z η : ℝ) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g) :
    T * (∫ x, tfPowerDerivative (f x) * f x ∂ballMeasure R) +
      tfBallLinear R Z η f + tfCoulombL R f f = 0 := by
  apply IsLocalMin.hasDerivAt_eq_zero (f := fun t : ℝ => tfBallFunctional R T Z η (f + t • f))
    _ (tfBallFunctional_hasDerivAt R T Z η f f)
  have hm : Ioi (-1 : ℝ) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by norm_num)
  filter_upwards [hm] with t ht
  have hn : NonnegDensity (f + t • f) := by
    rw [show f + t • f = (1 + t) • f by rw [add_smul, one_smul]]
    exact nonnegDensity_smul hf (by change -1 < t at ht; linarith)
  simpa using hmin _ hn

def tfBallPotential (R : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) : ℝ :=
  ∫ y, f y / ‖x - y‖ ∂ballMeasure R

lemma tfBallPotential_integrable (R : ℝ) (f : TFLp (ballMeasure R)) :
    Integrable (tfBallPotential R f) (ballMeasure R) := by
  have hm := tf_memLp_prod (μ := ballMeasure R) (memLp_const (1 : ℝ)) (Lp.memLp f)
  have hi := (coulomb_memLp R).integrable_mul hm
  have hi' : Integrable (fun p : TFSpace × TFSpace => f p.2 / ‖p.1 - p.2‖)
      ((ballMeasure R).prod (ballMeasure R)) := by
    apply hi.congr (Eventually.of_forall fun p => ?_)
    dsimp only [Pi.mul_apply]
    ring
  exact hi'.integral_prod_left

lemma tfCoulombL_potential (R : ℝ) (f h : TFLp (ballMeasure R)) :
    tfCoulombL R f h = ∫ x, tfBallPotential R f x * h x ∂ballMeasure R := by
  rw [tfCoulombL_symmetric R f h, tfCoulombL_apply, integral_prod _ (tfCoulomb_integrable R h f)]
  apply integral_congr_ae (Eventually.of_forall fun x => ?_)
  rw [mul_comm (tfBallPotential R f x)]
  unfold tfBallPotential
  rw [← integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only [tfBallPotential]
  ring

lemma tfBallPotential_mul_integrable (R : ℝ) (f h : TFLp (ballMeasure R)) :
    Integrable (fun x => tfBallPotential R f x * h x) (ballMeasure R) := by
  have hi := (tfCoulomb_integrable R h f).integral_prod_left
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  rw [mul_comm (tfBallPotential R f x)]
  unfold tfBallPotential
  rw [← integral_const_mul]
  congr 1
  ext y
  ring

def tfBallGradient (R T Z η : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) : ℝ :=
  T * tfPowerDerivative (f x) + η - Z / ‖x‖ + tfBallPotential R f x

lemma tfBallGradient_integrable (R T Z η : ℝ) (f : TFLp (ballMeasure R)) :
    Integrable (tfBallGradient R T Z η f) (ballMeasure R) := by
  have hi : Integrable (fun x => tfPowerDerivative (f x)) (ballMeasure R) := by
    simpa only [mul_one] using tfPowerDerivative_mul_integrable (Lp.memLp f) (memLp_const (1 : ℝ))
  have hn : Integrable (fun x : TFSpace => Z / ‖x‖) (ballMeasure R) := by
    simpa only [div_eq_mul_inv] using ((nuclear_memLp R).integrable (Fact.out : (1 : ENNReal) ≤ 5 / 2)).const_mul Z
  exact (((hi.const_mul T).add (integrable_const η)).sub hn).add (tfBallPotential_integrable R f)

lemma tfBallGradient_mul_integrable (R T Z η : ℝ) (f h : TFLp (ballMeasure R)) :
    Integrable (fun x => tfBallGradient R T Z η f x * h x) (ballMeasure R) := by
  have hi := (tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp h)).const_mul T
  have hc := ((Lp.memLp h).integrable (Fact.out : (1 : ENNReal) ≤ 5 / 3)).const_mul η
  have hn := (tfPairing_integrable _ (nuclear_memLp R) h).const_mul Z
  apply (((hi.add hc).sub hn).add (tfBallPotential_mul_integrable R f h)).congr
  exact Eventually.of_forall fun x => by dsimp [tfBallGradient]; ring

lemma tfBallGradient_pair (R T Z η : ℝ) (f h : TFLp (ballMeasure R)) :
    (∫ x, tfBallGradient R T Z η f x * h x ∂ballMeasure R) =
      T * (∫ x, tfPowerDerivative (f x) * h x ∂ballMeasure R) +
        tfBallLinear R Z η h + tfCoulombL R f h := by
  have hi := (tfPowerDerivative_mul_integrable (Lp.memLp f) (Lp.memLp h)).const_mul T
  have hc := ((Lp.memLp h).integrable (Fact.out : (1 : ENNReal) ≤ 5 / 3)).const_mul η
  have hn := (tfPairing_integrable _ (nuclear_memLp R) h).const_mul Z
  have he : (fun x => tfBallGradient R T Z η f x * h x) =
      (fun x => T * (tfPowerDerivative (f x) * h x) + η * h x - Z * (‖x‖⁻¹ * h x) +
        tfBallPotential R f x * h x) := by
    ext x
    dsimp only [tfBallGradient]
    ring
  rw [he, integral_add ((hi.fun_add hc).sub' hn) (tfBallPotential_mul_integrable R f h),
    integral_sub (hi.fun_add hc) hn, integral_add hi hc]
  simp only [integral_const_mul, tfBallLinear, sub_apply, smul_apply, smul_eq_mul,
    tfPairing_apply, one_mul, tfCoulombL_potential]
  ring

lemma tfBallGradient_nonneg (R T Z η : ℝ) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g) :
    ∀ᵐ x ∂ballMeasure R, 0 ≤ tfBallGradient R T Z η f x := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (tfBallGradient_integrable R T Z η f)
  intro s hs _
  let hm : MemLp (s.indicator (fun _ : TFSpace => (1 : ℝ))) (5 / 3) (ballMeasure R) :=
    (memLp_const 1).indicator hs
  let h := hm.toLp (s.indicator (fun _ : TFSpace => (1 : ℝ)))
  have hcoe : (fun x => h x) =ᵐ[ballMeasure R] s.indicator (fun _ => (1 : ℝ)) := hm.coeFn_toLp
  have hh : NonnegDensity h := by
    filter_upwards [hcoe] with x hx
    rw [hx]
    exact indicator_nonneg (fun _ _ => zero_le_one) x
  have hp := tfBallFunctional_variation_nonneg R T Z η hf hmin hh
  rw [← tfBallGradient_pair] at hp
  have he : (fun x => tfBallGradient R T Z η f x * h x) =ᵐ[ballMeasure R]
      s.indicator (tfBallGradient R T Z η f) := by
    filter_upwards [hcoe] with x hx
    rw [hx]
    by_cases hx' : x ∈ s <;> simp [hx']
  rwa [integral_congr_ae he, integral_indicator hs] at hp

lemma tfBallGradient_complementarity (R T Z η : ℝ) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g) :
    ∀ᵐ x ∂ballMeasure R, tfBallGradient R T Z η f x * f x = 0 := by
  have hn : ∀ᵐ x ∂ballMeasure R, 0 ≤ tfBallGradient R T Z η f x * f x := by
    filter_upwards [hf, tfBallGradient_nonneg R T Z η hf hmin] with x hfx hgx
    exact mul_nonneg hgx hfx
  apply (integral_eq_zero_iff_of_nonneg_ae hn (tfBallGradient_mul_integrable R T Z η f f)).mp
  rw [tfBallGradient_pair]
  exact tfBallFunctional_variation_self R T Z η hf hmin

theorem tfBallFunctional_euler (R Z η : ℝ) {T : ℝ} (hT : 0 < T)
    {f : TFLp (ballMeasure R)} (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g) :
    ∀ᵐ x ∂ballMeasure R, f x =
      (max (Z / ‖x‖ - tfBallPotential R f x - η) 0 / ((5 / 3 : ℝ) * T)) ^ (3 / 2 : ℝ) := by
  have hA : 0 < (5 / 3 : ℝ) * T := mul_pos (by norm_num) hT
  filter_upwards [hf, tfBallGradient_nonneg R T Z η hf hmin,
    tfBallGradient_complementarity R T Z η hf hmin] with x hfx hgx hcx
  have he : (5 / 3 : ℝ) * T * (f x) ^ (2 / 3 : ℝ) = max (Z / ‖x‖ - tfBallPotential R f x - η) 0 := by
    dsimp only [tfBallGradient] at hgx hcx
    rw [tfPowerDerivative_nonneg hfx] at hgx hcx
    by_cases hf0 : f x = 0
    · simp only [hf0, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), mul_zero, zero_add] at hgx ⊢
      rw [max_eq_right (by linarith)]
    · have hz := (mul_eq_zero.mp hcx).resolve_right hf0
      have hp := Real.rpow_nonneg hfx (2 / 3 : ℝ)
      have hxmax : 0 ≤ Z / ‖x‖ - tfBallPotential R f x - η := by nlinarith
      rw [max_eq_left hxmax]
      nlinarith
  have hdiv : (f x) ^ (2 / 3 : ℝ) = max (Z / ‖x‖ - tfBallPotential R f x - η) 0 / ((5 / 3 : ℝ) * T) :=
    (eq_div_iff hA.ne').mpr (by nlinarith [he])
  rw [← hdiv, ← Real.rpow_mul hfx]
  norm_num


open MeasureTheory Filter
open scoped Topology BigOperators Pointwise

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfPotential
attribute [-instance] _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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
namespace CoulombAnalysis
open CoulombAtom

def tfPotential (ρ : Space → ℝ) (x : Space) : ℝ := ∫ y, ρ y / ‖x - y‖
def tfField (Z : ℝ) (ρ : Space → ℝ) (x : Space) : ℝ := Z / ‖x‖ - tfPotential ρ x

lemma tfPotential_nonneg {ρ : Space → ℝ} (hρ : ∀ᵐ y, 0 ≤ ρ y) (x : Space) :
    0 ≤ tfPotential ρ x := by
  apply integral_nonneg_of_ae
  exact hρ.mono fun y hy => div_nonneg hy (norm_nonneg _)

lemma tfPotential_extension (R : ℝ) (f : TFLp (ballMeasure R)) (x : Space) :
    tfPotential (tfExtension R f) x = tfBallPotential R f x := by
  have he : (fun y => tfExtension R f y / ‖x - y‖) =
      (ball 0 R).indicator (fun y => f y / ‖x - y‖) := by
    ext y
    by_cases hy : y ∈ ball (0 : Space) R <;> simp [tfExtension, hy]
  unfold tfPotential tfBallPotential
  rw [he]
  exact integral_indicator measurableSet_ball

lemma tf_unit_price_extension_euler {Z : ℝ} (hZ : 0 < Z)
    {f : TFLp (ballMeasure Z)} (hf : NonnegDensity f)
    (hmin : ∀ g, NonnegDensity g → tfBallFunctional Z tfKinetic Z 1 f ≤
      tfBallFunctional Z tfKinetic Z 1 g) :
    ∀ᵐ x, tfExtension Z f x =
      (max (tfField Z (tfExtension Z f) x - 1) 0 / ((5 / 3 : ℝ) * tfKinetic)) ^ (3 / 2 : ℝ) := by
  have he := (ae_restrict_iff' measurableSet_ball).mp
    (tfBallFunctional_euler Z Z 1 tfKinetic_pos hf hmin)
  filter_upwards [he] with x hx
  by_cases hx' : x ∈ ball (0 : Space) Z
  · simp only [tfField, tfPotential_extension]
    simpa only [tfExtension, indicator_of_mem hx'] using hx hx'
  · have hr : Z ≤ ‖x‖ := le_of_not_gt (mt mem_ball_zero_iff.mpr hx')
    have hq : Z / ‖x‖ ≤ 1 := (div_le_one (hZ.trans_le hr)).mpr hr
    have hp := tfPotential_nonneg (tfExtension_nonneg hf) x
    have hfield : tfField Z (tfExtension Z f) x - 1 ≤ 0 := by unfold tfField; linarith
    rw [max_eq_right hfield]
    simp [tfExtension, hx']

end CoulombAnalysis

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CoulombNear
attribute [-instance] _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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
namespace CoulombAnalysis

def coulombNear : TFSpace → ℝ := (ball 0 1).indicator (fun x => ‖x‖⁻¹ - 1)
def coulombFar (x : TFSpace) : ℝ := (max ‖x‖ 1)⁻¹

lemma coulombNear_memLp : MemLp coulombNear (5 / 2) := by
  rw [coulombNear, memLp_indicator_iff_restrict measurableSet_ball]
  exact (nuclear_memLp 1).sub (memLp_const 1)

lemma coulombFar_bound (x : TFSpace) : ‖coulombFar x‖ ≤ 1 := by
  rw [coulombFar, norm_inv, Real.norm_of_nonneg (le_trans (by norm_num) (le_max_right _ _))]
  exact inv_le_one_of_one_le₀ (le_max_right _ _)

lemma coulombFar_continuous : Continuous coulombFar := by
  exact (continuous_norm.max continuous_const).inv₀ (fun x =>
    ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (le_max_right ‖x‖ 1)))

lemma coulomb_decompose (x : TFSpace) : ‖x‖⁻¹ = coulombNear x + coulombFar x := by
  by_cases hx : ‖x‖ < 1
  · simp only [coulombNear, indicator_of_mem (mem_ball_zero_iff.mpr hx), coulombFar,
      max_eq_right hx.le, inv_one]
    ring
  · simp only [coulombNear, indicator_of_notMem (mt mem_ball_zero_iff.mp hx), coulombFar,
      max_eq_left (le_of_not_gt hx), zero_add]

def tfSubMap (x : TFSpace) : C(TFSpace, TFSpace) := ⟨fun y => x - y, continuous_const.sub continuous_id⟩
lemma tfSubMap_preserving (x : TFSpace) : MeasurePreserving (tfSubMap x) volume volume :=
  volume.measurePreserving_sub_left x

lemma tfSubMap_continuous : Continuous tfSubMap := by
  exact (⟨fun p : TFSpace × TFSpace => p.1 - p.2, continuous_fst.sub continuous_snd⟩ :
    C(TFSpace × TFSpace, TFSpace)).curry.continuous

def coulombNearLp : Lp ℝ (5 / 2) (volume : Measure TFSpace) := coulombNear_memLp.toLp coulombNear

def coulombNearTranslate (x : TFSpace) : Lp ℝ (5 / 2) (volume : Measure TFSpace) :=
  Lp.compMeasurePreserving (tfSubMap x) (tfSubMap_preserving x) coulombNearLp

lemma coulombNearTranslate_coe (x : TFSpace) :
    coulombNearTranslate x =ᵐ[volume] fun y => coulombNear (x - y) := by
  exact (Lp.coeFn_compMeasurePreserving coulombNearLp (tfSubMap_preserving x)).trans
    ((tfSubMap_preserving x).quasiMeasurePreserving.ae coulombNear_memLp.coeFn_toLp)

lemma coulombNearTranslate_continuous : Continuous coulombNearTranslate := by
  exact continuous_const.compMeasurePreservingLp tfSubMap_continuous tfSubMap_preserving
    (ENNReal.div_ne_top (by norm_num) (by norm_num))

lemma coulombNearMultiply_integrable {ρ : TFSpace → ℝ} (hρ : MemLp ρ (5 / 3)) (x : TFSpace) :
    Integrable (fun y => coulombNear (x - y) * ρ y) := by
  exact (coulombNear_memLp.comp_measurePreserving (tfSubMap_preserving x)).integrable_mul hρ

lemma coulombFarMultiply_integrable {ρ : TFSpace → ℝ} (hρ : Integrable ρ) (x : TFSpace) :
    Integrable (fun y => coulombFar (x - y) * ρ y) := by
  apply hρ.bdd_mul (coulombFar_continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Eventually.of_forall fun y => coulombFar_bound (x - y)

lemma tfPotential_integrable {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    (x : TFSpace) : Integrable (fun y => ρ y / ‖x - y‖) := by
  have hsum := (coulombNearMultiply_integrable hp x).add (coulombFarMultiply_integrable h1 x)
  convert! hsum using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  dsimp
  rw [div_eq_mul_inv, coulomb_decompose]
  ring

lemma tfPotential_continuous {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3)) :
    Continuous (tfPotential ρ) := by
  have hnear : Continuous (fun x => ∫ y, coulombNear (x - y) * ρ y) := by
    let pair := (ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume : Measure TFSpace) (5 / 2) (5 / 3)
    have hc := (pair.flip (hp.toLp ρ)).continuous.comp coulombNearTranslate_continuous
    convert! hc using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    dsimp only [Function.comp_apply, pair, ContinuousLinearMap.flip_apply]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [coulombNearTranslate_coe x, hp.coeFn_toLp] with y hy hρy
    simp only [ContinuousLinearMap.mul_apply', hy, hρy]
  have hfar : Continuous (fun x => ∫ y, ρ y * coulombFar (x - y)) := by
    have hc := (show BddAbove (range fun x => ‖coulombFar x‖) from
      ⟨1, by rintro _ ⟨x, rfl⟩; exact coulombFar_bound x⟩).continuous_convolution_right_of_integrable
        (ContinuousLinearMap.mul ℝ ℝ) h1 coulombFar_continuous
    exact hc
  convert! hnear.add hfar using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  dsimp only [Pi.add_apply]
  rw [← integral_add (coulombNearMultiply_integrable hp x)
    ((coulombFarMultiply_integrable h1 x).congr (Eventually.of_forall fun y => mul_comm _ _))]
  apply integral_congr_ae (Eventually.of_forall fun y => ?_)
  rw [div_eq_mul_inv, coulomb_decompose]
  ring

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution

namespace CoulombAnalysis

def newtonMul : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
def newtonMul₁ : ℝ →L[ℝ] (TFSpace →L[ℝ] ℝ) →L[ℝ] (TFSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.precompR TFSpace newtonMul
lemma fderiv_apply_const_scalar {f : TFSpace → ℝ} {x : TFSpace}
    (hd : DifferentiableAt ℝ (fderiv ℝ f) x) (u v : TFSpace) :
    fderiv ℝ (fun z => fderiv ℝ f z v) x u = fderiv ℝ (fderiv ℝ f) x u v := by
  simp only [fderiv_clm_apply hd (differentiableAt_const v), fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

lemma fderiv_convolution_eval {ρ K : TFSpace → ℝ} (hρ : LocallyIntegrable ρ volume)
    (hK : HasCompactSupport K) (hd : ContDiff ℝ 1 K) (x u : TFSpace) :
    fderiv ℝ (ρ ⋆[newtonMul] K) x u = ∫ y, ρ y * fderiv ℝ K (x - y) u := by
  rw [(hK.hasFDerivAt_convolution_right newtonMul hρ hd x).fderiv]
  have hi := (hK.fderiv ℝ).convolutionExists_right newtonMul₁ hρ
    (hd.continuous_fderiv (by norm_num)) x
  change (∫ t, newtonMul₁ (ρ t) (fderiv ℝ K (x - t))) u = _
  rw [ContinuousLinearMap.integral_apply hi.integrable u]
  rfl

lemma second_fderiv_convolution {ρ K : TFSpace → ℝ} (hρ : LocallyIntegrable ρ volume)
    (hK : HasCompactSupport K) (hd : ContDiff ℝ 2 K) (x u v : TFSpace) :
    fderiv ℝ (fderiv ℝ (ρ ⋆[newtonMul] K)) x u v =
      ∫ y, ρ y * (fderiv ℝ (fderiv ℝ K) (x - y) u v) := by
  have hc : ContDiff ℝ 2 (ρ ⋆[newtonMul] K) := hK.contDiff_convolution_right newtonMul hρ hd
  have hc' := (hc.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  rw [← fderiv_apply_const_scalar hc'.differentiableAt u v]
  have he : (fun z => fderiv ℝ (ρ ⋆[newtonMul] K) z v) =
      ρ ⋆[newtonMul] (fun z => fderiv ℝ K z v) := by
    funext z
    exact fderiv_convolution_eval hρ hK (hd.of_le (by norm_num)) z v
  rw [he]
  have hdk : ContDiff ℝ 1 (fun z => fderiv ℝ K z v) :=
    (hd.fderiv_right (by norm_num)).clm_apply contDiff_const
  rw [fderiv_convolution_eval hρ (hK.fderiv_apply ℝ v) hdk]
  apply integral_congr_ae (Eventually.of_forall fun y => ?_)
  rw [fderiv_apply_const_scalar ((hd.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)).differentiableAt]

lemma second_kernel_integrable {ρ K : TFSpace → ℝ} (hρ : LocallyIntegrable ρ volume)
    (hK : HasCompactSupport K) (hd : ContDiff ℝ 2 K) (x u v : TFSpace) :
    Integrable (fun y => ρ y * (fderiv ℝ (fderiv ℝ K) (x - y) u v)) := by
  have hdk : ContDiff ℝ 1 (fun z => fderiv ℝ K z v) :=
    (hd.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hc : Continuous (fun z => fderiv ℝ (fun w => fderiv ℝ K w v) z u) :=
    (hdk.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi := ((hK.fderiv_apply ℝ v).fderiv_apply ℝ u).convolutionExists_right newtonMul hρ hc x
  convert! hi.integrable using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  exact (congrArg (ρ y * ·) (fderiv_apply_const_scalar
    ((hd.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable
      (by norm_num)).differentiableAt u v)).symm

lemma laplacian_convolution {ρ K : TFSpace → ℝ} (hρ : LocallyIntegrable ρ volume)
    (hK : HasCompactSupport K) (hd : ContDiff ℝ 2 K) (x : TFSpace) :
    Δ (ρ ⋆[newtonMul] K) x = ∫ y, ρ y * Δ K (x - y) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp_rw [second_fderiv_convolution hρ hK hd, Finset.mul_sum]
  rw [integral_finsetSum]
  exact fun i _ => second_kernel_integrable hρ hK hd x _ _

def annularCoulomb (a b : ContDiffBump (0 : TFSpace)) (x : TFSpace) : ℝ :=
  (1 - a x) * b x * ‖x‖⁻¹

lemma annularCoulomb_compact (a b : ContDiffBump (0 : TFSpace)) :
    HasCompactSupport (annularCoulomb a b) := by
  exact b.hasCompactSupport.mul_left.mul_right

lemma annularCoulomb_smooth (a b : ContDiffBump (0 : TFSpace)) :
    ContDiff ℝ 2 (annularCoulomb a b) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [a.eventuallyEq_one] with x hx
    simp [annularCoulomb, hx]
  · have hn : ContDiffAt ℝ 2 (fun x : TFSpace => ‖x‖⁻¹) x :=
      contDiffAt_norm ℝ hx |>.inv (norm_ne_zero_iff.mpr hx)
    exact ((contDiffAt_const.sub a.contDiff.contDiffAt).mul b.contDiff.contDiffAt).mul hn

lemma annularCoulomb_eq (a b : ContDiffBump (0 : TFSpace)) {x : TFSpace}
    (ha : a.rOut ≤ ‖x‖) (hb : ‖x‖ ≤ b.rIn) : annularCoulomb a b x = ‖x‖⁻¹ := by
  simp [annularCoulomb, a.zero_of_le_dist (by simpa using ha),
    b.one_of_mem_closedBall (by simpa using hb)]

lemma annularCoulomb_eventually (a b : ContDiffBump (0 : TFSpace)) {x : TFSpace}
    (ha : a.rOut < ‖x‖) (hb : ‖x‖ < b.rIn) :
    annularCoulomb a b =ᶠ[𝓝 x] fun z => ‖z‖⁻¹ := by
  filter_upwards [continuous_norm.continuousAt.eventually (Ioo_mem_nhds ha hb)] with z hz
  exact annularCoulomb_eq a b hz.1.le hz.2.le

lemma annularCoulomb_laplacian (a b : ContDiffBump (0 : TFSpace)) {x : TFSpace}
    (ha : a.rOut < ‖x‖) (hb : ‖x‖ < b.rIn) : Δ (annularCoulomb a b) x = 0 := by
  have hx : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (a.rOut_pos.trans ha))
  have he := annularCoulomb_eventually a b ha hb
  rw [(laplacian_congr_nhds he).eq_of_nhds]
  have heq : (fun z : TFSpace => ‖z‖⁻¹) = CoulombPDE.radialPower (-(1 / 2)) :=
    funext fun z => (CoulombPDE.radialPower_half_inv z).symm
  rw [heq, CoulombPDE.radial_laplacian_three (-(1 / 2)) hx]
  norm_num

theorem tfPotential_harmonic_separated {ρ : TFSpace → ℝ} (hρ : LocallyIntegrable ρ volume)
    {x : TFSpace} {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hs : ∀ y, ρ y ≠ 0 → a ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ b) :
    ContDiffAt ℝ 2 (tfPotential ρ) x ∧ Δ (tfPotential ρ) x = 0 := by
  let ai : ContDiffBump (0 : TFSpace) := ⟨a / 4, a / 2, by positivity, by linarith⟩
  let bo : ContDiffBump (0 : TFSpace) := ⟨b + 1, b + 2, by positivity, by linarith⟩
  let K := annularCoulomb ai bo
  have hk := annularCoulomb_compact ai bo
  have hdk := annularCoulomb_smooth ai bo
  have he : tfPotential ρ =ᶠ[𝓝 x] (ρ ⋆[newtonMul] K) := by
    filter_upwards [ball_mem_nhds x (show 0 < min (a / 4) (1 / 2 : ℝ) by positivity)] with z hz
    apply integral_congr_ae (Eventually.of_forall fun y => ?_)
    change ρ y / ‖z - y‖ = ρ y * K (z - y)
    by_cases hy : ρ y = 0
    · simp [hy]
    · obtain ⟨hlo, hhi⟩ := hs y hy
      have hz₁ : dist z x < a / 4 := lt_of_lt_of_le hz (min_le_left _ _)
      have hz₂ : dist z x < 1 / 2 := lt_of_lt_of_le hz (min_le_right _ _)
      have hu := dist_triangle z x y
      have hl := dist_triangle x z y
      rw [dist_comm x z] at hl
      simp only [dist_eq_norm] at hz₁ hz₂ hu hl
      have hka : ai.rOut ≤ ‖z - y‖ := by dsimp [ai]; linarith
      have hkb : ‖z - y‖ ≤ bo.rIn := by dsimp [bo]; linarith
      rw [show K (z - y) = ‖z - y‖⁻¹ from annularCoulomb_eq ai bo hka hkb, div_eq_mul_inv]
  refine ⟨(hk.contDiff_convolution_right newtonMul hρ hdk).contDiffAt.congr_of_eventuallyEq he, ?_⟩
  rw [(laplacian_congr_nhds he).eq_of_nhds, laplacian_convolution hρ hk hdk]
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun y => by
    change ρ y * Δ K (x - y) = 0
    by_cases hy : ρ y = 0
    · simp [hy]
    · obtain ⟨hlo, hhi⟩ := hs y hy
      have hka : ai.rOut < ‖x - y‖ := by dsimp [ai]; linarith
      have hkb : ‖x - y‖ < bo.rIn := by dsimp [bo]; linarith
      rw [show Δ K (x - y) = 0 from annularCoulomb_laplacian ai bo hka hkb, mul_zero]

end CoulombAnalysis

open scoped RealInnerProductSpace

lemma exists_orthogonal_map_norm_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (h : ‖x‖ = ‖y‖) : ∃ e : E ≃ₗᵢ[ℝ] E, e x = y := by
  by_cases hxy : x + y = 0
  · refine ⟨LinearIsometryEquiv.neg ℝ, ?_⟩
    change -x = y
    exact neg_eq_iff_add_eq_zero.mpr hxy
  · refine ⟨(ℝ ∙ (x + y)).reflection, ?_⟩
    rw [Submodule.reflection_singleton_apply]
    have hn : ‖x + y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hxy)
    have he : (2 : ℝ) * (inner ℝ (x + y) x / ‖x + y‖ ^ 2) = 1 := by
      rw [← mul_div_assoc]
      apply (div_eq_one_iff_eq hn).mpr
      rw [inner_add_left, real_inner_self_eq_norm_sq, real_inner_comm x y,
        norm_add_sq_real, h]
      ring
    rw [two_smul, ← add_smul, ← two_mul]
    change (2 * (inner ℝ (x + y) x / ‖x + y‖ ^ 2)) • (x + y) - x = y
    rw [he, one_smul]
    abel

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_Radial
attribute [-instance] _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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
namespace CoulombAnalysis

def IsRadial (f : TFSpace → ℝ) : Prop := ∀ x y, ‖x‖ = ‖y‖ → f x = f y

lemma tfPotential_radial {ρ : TFSpace → ℝ} (hr : IsRadial ρ) : IsRadial (tfPotential ρ) := by
  intro x y hxy
  obtain ⟨e, he⟩ := exists_orthogonal_map_norm_eq x y hxy
  unfold tfPotential
  have hi := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun z => ρ z / ‖y - z‖)
  rw [← hi, ← he]
  apply integral_congr_ae (Eventually.of_forall fun z => ?_)
  rw [hr (e z) z (e.norm_map z), ← e.map_sub, e.norm_map]

lemma tfPotential_compact_bound {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    {R : ℝ} (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) {x : TFSpace} (hx : R < ‖x‖) :
    |tfPotential ρ x| ≤ (∫ y, |ρ y|) / (‖x‖ - R) := by
  have hi := tfPotential_integrable h1 hp x
  calc
    _ ≤ ∫ y, |ρ y / ‖x - y‖| := by
      simpa only [tfPotential, Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => ρ y / ‖x - y‖)
    _ ≤ ∫ y, |ρ y| / (‖x‖ - R) := by
      apply integral_mono hi.norm (h1.abs.div_const _)
      intro y
      simp only [Real.norm_eq_abs]
      by_cases hy : ρ y = 0
      · simp [hy]
      · have hb := hs y hy
        have hn : ‖x‖ - R ≤ ‖x - y‖ := by
          have ht := norm_sub_le x y
          have ht' := norm_add_le (x - y) y
          rw [sub_add_cancel] at ht'
          linarith
        rw [abs_div, abs_norm]
        exact div_le_div_of_nonneg_left (abs_nonneg _) (sub_pos.mpr hx) hn
    _ = _ := by simp only [div_eq_mul_inv, integral_mul_const]

lemma tfPotential_compact_mass_bound {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R)
    {x : TFSpace} (hx : R < ‖x‖) :
    |‖x‖ * tfPotential ρ x - ∫ y, ρ y| ≤
      R / (‖x‖ - R) * (∫ y, |ρ y|) := by
  have hi := tfPotential_integrable h1 hp x
  have he : ‖x‖ * tfPotential ρ x - ∫ y, ρ y =
      ∫ y, (‖x‖ * (ρ y / ‖x - y‖) - ρ y) := by
    rw [integral_sub (hi.const_mul _) h1, integral_const_mul]
    rfl
  rw [he]
  calc
    _ ≤ ∫ y, |‖x‖ * (ρ y / ‖x - y‖) - ρ y| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun y => ‖x‖ * (ρ y / ‖x - y‖) - ρ y)
    _ ≤ ∫ y, R / (‖x‖ - R) * |ρ y| := by
      apply integral_mono ((hi.const_mul _).sub' h1).norm (h1.abs.const_mul _)
      intro y
      simp only [Real.norm_eq_abs]
      by_cases hy : ρ y = 0
      · simp [hy]
      · have hb := hs y hy
        have hn : ‖x‖ - R ≤ ‖x - y‖ := by
          have ht' := norm_add_le (x - y) y
          rw [sub_add_cancel] at ht'
          linarith
        have hnpos : 0 < ‖x - y‖ := (sub_pos.mpr hx).trans_le hn
        have hdiff : |‖x‖ - ‖x - y‖| ≤ R := by
          have ht := abs_norm_sub_norm_le x (x - y)
          simp only [sub_sub_cancel] at ht
          exact ht.trans hb
        have hdiv : |‖x‖ / ‖x - y‖ - 1| ≤ R / (‖x‖ - R) := by
          rw [← div_self hnpos.ne', ← sub_div, abs_div, abs_norm]
          exact (div_le_div_of_nonneg_right hdiff (norm_nonneg _)).trans
            (div_le_div_of_nonneg_left hR (sub_pos.mpr hx) hn)
        calc
          _ = |‖x‖ / ‖x - y‖ - 1| * |ρ y| := by rw [← abs_mul]; congr 1; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hdiv (abs_nonneg _)
    _ = _ := integral_const_mul _ _

lemma tfPotential_compact_decay {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    {R : ℝ} (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) :
    ∀ ε > 0, ∃ S > 0, ∀ x, S ≤ ‖x‖ → |tfPotential ρ x| ≤ ε := by
  intro ε hε
  let A := ∫ y, |ρ y|
  have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  let S := max R 0 + 1 + A / ε
  have hS : 0 < S := by dsimp [S]; positivity
  refine ⟨S, hS, ?_⟩
  intro x hx
  have hxr : R < ‖x‖ := by
    have hmax := le_max_left R 0
    have hade := div_nonneg hA hε.le
    dsimp [S] at hx
    linarith
  apply (tfPotential_compact_bound h1 hp hs hxr).trans
  apply (div_le_iff₀ (sub_pos.mpr hxr)).mpr
  have hmax := le_max_left R 0
  have hbound : A / ε ≤ ‖x‖ - R := by dsimp [S] at hx; linarith
  have hh := (div_le_iff₀ hε).mp hbound
  linarith

lemma tfPotential_harmonic_outside {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R)
    {x : TFSpace} (hx : R < ‖x‖) :
    ContDiffAt ℝ 2 (tfPotential ρ) x ∧ Δ (tfPotential ρ) x = 0 := by
  apply tfPotential_harmonic_separated h1.locallyIntegrable (sub_pos.mpr hx)
    (show 0 ≤ ‖x‖ + R by positivity)
  intro y hy
  have hb := hs y hy
  have ht := norm_add_le (x - y) y
  rw [sub_add_cancel] at ht
  exact ⟨by linarith, (norm_sub_le x y).trans (by linarith)⟩

theorem tfPotential_newton_exterior {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) {x : TFSpace} (hx : R < ‖x‖) :
    tfPotential ρ x = (∫ y, ρ y) / ‖x‖ := by
  let a := (R + ‖x‖) / 2
  have haR : R < a := by dsimp [a]; linarith
  have ha : 0 < a := hR.trans_lt haR
  have hax : a ≤ ‖x‖ := by dsimp [a]; linarith
  let e : TFSpace := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hya : ‖a • e‖ = a := by simp [norm_smul, he, abs_of_pos ha]
  let q := a * tfPotential ρ (a • e)
  let G : TFSpace → ℝ := fun y => q * CoulombPDE.radialPower (-(1 / 2)) y
  have hg (y : TFSpace) : G y = q / ‖y‖ := by
    dsimp [G]; rw [CoulombPDE.radialPower_half_inv, div_eq_mul_inv]
  have hy0 (y : TFSpace) (hy : a ≤ ‖y‖) : y ≠ 0 := norm_pos_iff.mp (ha.trans_le hy)
  have hgreg (y : TFSpace) (hy : a ≤ ‖y‖) : ContDiffAt ℝ 2 G y :=
    contDiffAt_const.mul (CoulombPDE.radialPower_contDiffAt _ (hy0 y hy))
  have hglap (y : TFSpace) (hy : a ≤ ‖y‖) : Δ G y = 0 := by
    change (Δ (q • (CoulombPDE.radialPower (-(1 / 2)) : TFSpace → ℝ)) : TFSpace → ℝ) y = 0
    rw [laplacian_smul q (CoulombPDE.radialPower_contDiffAt _ (hy0 y hy)),
      CoulombPDE.radial_laplacian_three _ (hy0 y hy)]
    norm_num
  have hEq := CoulombPDE.exterior_harmonic_unique (a := a)
    (fun y hy => (tfPotential_harmonic_outside h1 hR hs (haR.trans_le hy)).1)
    hgreg (fun y hy => ((tfPotential_harmonic_outside h1 hR hs (haR.trans_le hy)).2).trans
      (hglap y hy).symm) (fun y hy => ?_) (fun ε hε => ?_)
  · have hqm : q = ∫ y, ρ y := by
      apply sub_eq_zero.mp
      apply abs_eq_zero.mp
      apply le_antisymm _ (abs_nonneg _)
      apply le_of_forall_pos_le_add
      intro ε hε
      let A := ∫ y, |ρ y|
      have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
      let S := max a R + 1 + R * A / ε
      have hS : 0 < S := by dsimp [S]; have hh := le_max_left a R; positivity
      have hSa : a ≤ S := by
        dsimp [S]; have hh := le_max_left a R; have ht := div_nonneg (mul_nonneg hR hA) hε.le; linarith
      have hSR : R < S := by
        dsimp [S]; have hh := le_max_right a R; have ht := div_nonneg (mul_nonneg hR hA) hε.le; linarith
      have hSn : ‖S • e‖ = S := by simp [norm_smul, he, abs_of_pos hS]
      have ht := tfPotential_compact_mass_bound h1 hp hR hs (x := S • e) (by simpa only [hSn] using hSR)
      rw [hEq (S • e) (by simpa only [hSn] using hSa), hg, hSn, mul_div_cancel₀ _ hS.ne'] at ht
      apply ht.trans
      have hbound : R * A / ε ≤ S - R := by
        dsimp [S]; have hh := le_max_right a R; linarith
      have hh := (div_le_iff₀ hε).mp hbound
      rw [zero_add, div_mul_eq_mul_div]
      exact (div_le_iff₀ (sub_pos.mpr hSR)).mpr (by linarith)
    rw [hEq x hax, hg, hqm]
  · rw [hg, tfPotential_radial hr y (a • e) (hy.trans hya.symm)]
    dsimp [q]
    rw [hy, mul_div_cancel_left₀ _ ha.ne']
  · obtain ⟨S, hS, hdec⟩ := tfPotential_compact_decay h1 hp hs (ε / 2) (by positivity)
    refine ⟨max S (2 * |q| / ε), ?_⟩
    intro y hy
    have hyS := (le_max_left S (2 * |q| / ε)).trans hy
    have hyn := hS.trans_le hyS
    have hsmall : |q| / ‖y‖ ≤ ε / 2 := by
      have hh := (div_le_iff₀ hε).mp ((le_max_right S (2 * |q| / ε)).trans hy)
      apply (div_le_iff₀ hyn).mpr
      linarith
    have hab : |G y| ≤ ε / 2 := by rw [hg, abs_div, abs_norm]; exact hsmall
    exact (abs_sub _ _).trans (by linarith [hdec y hyS])

lemma tfPotential_harmonic_inside {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    {a R : ℝ} (hR : 0 ≤ R) (hs : ∀ y, ρ y ≠ 0 → a ≤ ‖y‖ ∧ ‖y‖ ≤ R)
    {x : TFSpace} (hx : ‖x‖ < a) :
    ContDiffAt ℝ 2 (tfPotential ρ) x ∧ Δ (tfPotential ρ) x = 0 := by
  apply tfPotential_harmonic_separated h1.locallyIntegrable (sub_pos.mpr hx)
    (show 0 ≤ ‖x‖ + R by positivity)
  intro y hy
  have hb := hs y hy
  have ht := norm_add_le (y - x) x
  rw [sub_add_cancel, norm_sub_rev y x] at ht
  exact ⟨by linarith [hb.1], (norm_sub_le x y).trans (by linarith [hb.2])⟩

theorem tfPotential_newton_interior {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ) {a R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, ρ y ≠ 0 → a ≤ ‖y‖ ∧ ‖y‖ ≤ R) {x : TFSpace} (hx : ‖x‖ ≤ a)
    (ha : 0 < a) : tfPotential ρ x = tfPotential ρ 0 := by
  have hinner (z : TFSpace) (hz : ‖z‖ < a) : tfPotential ρ z = tfPotential ρ 0 := by
    let b := (‖z‖ + a) / 2
    have hb : 0 < b := by dsimp [b]; linarith [norm_nonneg z]
    have hba : b < a := by dsimp [b]; linarith
    have hzb : ‖z‖ ≤ b := by dsimp [b]; linarith
    let e : TFSpace := EuclideanSpace.single 0 1
    have he : ‖e‖ = 1 := by simp [e]
    have heb : ‖b • e‖ = b := by simp [norm_smul, he, abs_of_pos hb]
    let c := tfPotential ρ (b • e)
    have hlocal (y : TFSpace) (hy : ‖y‖ ≤ b) :=
      tfPotential_harmonic_inside h1 hR hs (hy.trans_lt hba)
    have hbound (y : TFSpace) (hy : ‖y‖ = b) : tfPotential ρ y = c :=
      tfPotential_radial hr y (b • e) (hy.trans heb.symm)
    have hle (s : ℝ) : ∀ y ∈ closedBall (0 : TFSpace) b,
        s * (tfPotential ρ y - c) ≤ 0 := by
      apply CoulombPDE.compact_maximum_principle (isCompact_closedBall 0 b)
      · exact (continuous_const.mul ((tfPotential_continuous h1 hp).sub continuous_const)).continuousOn
      · intro y hy
        have hyb : ‖y‖ ≤ b := by simpa using (interior_subset hy : y ∈ closedBall 0 b)
        exact contDiffAt_const.mul (hlocal y hyb |>.1.sub contDiffAt_const)
      · intro y hy _
        have hyb : ‖y‖ ≤ b := by simpa using (interior_subset hy : y ∈ closedBall 0 b)
        change 0 ≤ (Δ (s • (tfPotential ρ - fun _ => c)) : TFSpace → ℝ) y
        have hreg : ContDiffAt ℝ 2 (tfPotential ρ - fun _ => c) y :=
          (hlocal y hyb).1.sub contDiffAt_const
        rw [laplacian_smul s hreg,
          (hlocal y hyb).1.laplacian_sub (show ContDiffAt ℝ 2 (fun _ : TFSpace => c) y from contDiffAt_const),
          (hlocal y hyb).2, laplacian_const]
        simp
      · intro y hy hi
        have hyb : ‖y‖ ≤ b := by simpa using hy
        have hyge : b ≤ ‖y‖ := by
          by_contra! hlt
          exact hi (by rw [interior_closedBall 0 hb.ne']; simpa using hlt)
        simp [hbound y (le_antisymm hyb hyge)]
    have hall (y : TFSpace) (hy : ‖y‖ ≤ b) : tfPotential ρ y = c := by
      have hp' := hle 1 y (by simpa using hy)
      have hm' := hle (-1) y (by simpa using hy)
      linarith
    exact (hall z hzb).trans (hall 0 (by simpa using hb.le)).symm
  have heq : EqOn (tfPotential ρ) (fun _ => tfPotential ρ 0) (ball 0 a) :=
    fun y hy => hinner y (by simpa using hy)
  have hh := heq.closure (tfPotential_continuous h1 hp) continuous_const
  rw [closure_ball 0 ha.ne'] at hh
  exact hh (by simpa using hx)

lemma tfPotential_newton_exterior_closed {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) {x : TFSpace} (hx : R ≤ ‖x‖) :
    tfPotential ρ x = (∫ y, ρ y) / ‖x‖ := by
  have he : EqOn (fun y => tfPotential ρ y * ‖y‖) (fun _ => ∫ y, ρ y)
      (closedBall (0 : TFSpace) R)ᶜ := by
    intro y hy
    have hyr : R < ‖y‖ := by simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hy
    change tfPotential ρ y * ‖y‖ = _
    rw [tfPotential_newton_exterior h1 hp hr hR.le hs hyr,
      div_mul_cancel₀ _ (hR.trans hyr).ne']
  have hclosure := he.closure ((tfPotential_continuous h1 hp).mul continuous_norm) continuous_const
  rw [closure_compl, interior_closedBall 0 hR.ne'] at hclosure
  have hmem : x ∈ (ball (0 : TFSpace) R)ᶜ := by
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hx
  exact (eq_div_iff (hR.trans_le hx).ne').mpr (hclosure hmem)

lemma IsRadial.indicator_norm_le {ρ : TFSpace → ℝ} (hr : IsRadial ρ) (r : ℝ) :
    IsRadial ({y | ‖y‖ ≤ r}.indicator ρ) := by
  intro x y hxy
  simp only [Set.indicator, mem_ofPred_eq, hxy, hr x y hxy]

lemma IsRadial.indicator_norm_gt {ρ : TFSpace → ℝ} (hr : IsRadial ρ) (r : ℝ) :
    IsRadial ({y | r < ‖y‖}.indicator ρ) := by
  intro x y hxy
  simp only [Set.indicator, mem_ofPred_eq, hxy, hr x y hxy]

theorem tfPotential_newton {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    (hr : IsRadial ρ) {R : ℝ} (hR : 0 ≤ R) (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R)
    {x : TFSpace} (hx : x ≠ 0) :
    tfPotential ρ x = (∫ y in {y | ‖y‖ ≤ ‖x‖}, ρ y) / ‖x‖ +
      ∫ y in {y | ‖x‖ < ‖y‖}, ρ y / ‖y‖ := by
  let r := ‖x‖
  have hri : 0 < r := norm_pos_iff.mpr hx
  let ρi := {y | ‖y‖ ≤ r}.indicator ρ
  let ρo := {y | r < ‖y‖}.indicator ρ
  have hmi : MeasurableSet {y : TFSpace | ‖y‖ ≤ r} := measurableSet_le measurable_norm measurable_const
  have hmo : MeasurableSet {y : TFSpace | r < ‖y‖} := measurableSet_lt measurable_const measurable_norm
  have hi1 : Integrable ρi := h1.indicator hmi
  have hip : MemLp ρi (5 / 3) := hp.indicator hmi
  have ho1 : Integrable ρo := h1.indicator hmo
  have hop : MemLp ρo (5 / 3) := hp.indicator hmo
  have hsum (y : TFSpace) : ρ y = ρi y + ρo y := by
    dsimp [ρi, ρo]
    by_cases hy : ‖y‖ ≤ r
    · simp [hy, not_lt.mpr hy]
    · simp [hy, lt_of_not_ge hy]
  have hinside := tfPotential_newton_exterior_closed hi1 hip (hr.indicator_norm_le r) hri
    (fun y hy => by by_contra hn; exact hy (by simp [ρi, hn])) (x := x) le_rfl
  have houtside := tfPotential_newton_interior ho1 hop (hr.indicator_norm_gt r) hR
    (fun y hy => by
      have hy' : r < ‖y‖ := by by_contra hn; exact hy (by simp [ρo, hn])
      have hyρ : ρ y ≠ 0 := by simpa [ρo, hy'] using hy
      exact ⟨hy'.le, hs y hyρ⟩) (x := x) le_rfl hri
  have hpot : tfPotential ρ x = tfPotential ρi x + tfPotential ρo x := by
    unfold tfPotential
    rw [← integral_add (tfPotential_integrable hi1 hip x) (tfPotential_integrable ho1 hop x)]
    apply integral_congr_ae (Eventually.of_forall fun y => ?_)
    rw [hsum y, add_div]
  rw [hpot, hinside, houtside]
  congr 1
  · rw [show ρi = {y | ‖y‖ ≤ r}.indicator ρ from rfl, integral_indicator hmi]
  · unfold tfPotential ρo
    simp only [zero_sub, norm_neg]
    rw [← integral_indicator hmo]
    apply integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : r < ‖y‖ <;> simp [hy]

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PacketDensity
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

def packetDensity (y : Space) (R : ℝ) (x : Space) : ℝ :=
  ∑ s : Spins 1, ‖(radialLocalOrbital y R).value s (fun _ => x)‖^2

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_RadialPacket
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

lemma ae_ne_point (a : Space) : ∀ᵐ z : Space, z ≠ a := by
  rw [ae_iff]
  simp

end Work_RadialPacket_scope

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

end CoulombAtom

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

abbrev SpatialRotation := unitary (Space →L[ℝ] Space)

instance spatialOperatorContinuousStar : ContinuousStar (Space →L[ℝ] Space) :=
  ⟨ContinuousLinearMap.adjoint.continuous⟩

instance spatialRotationCompact : CompactSpace SpatialRotation := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Space →L[ℝ] Space) 1).of_isClosed_subset isClosed_unitary
  intro g hg
  rw [mem_closedBall_zero_iff]
  exact (CStarRing.norm_of_mem_unitary hg).le

instance spatialRotationMeasurable : MeasurableSpace SpatialRotation := borel SpatialRotation
instance spatialRotationBorel : BorelSpace SpatialRotation := ⟨rfl⟩

def rotationMeasure : Measure SpatialRotation := Measure.haarMeasure (⊤ : PositiveCompacts SpatialRotation)

def rotate (g : SpatialRotation) : Space ≃ₗᵢ[ℝ] Space := Unitary.linearIsometryEquiv g

@[simp] lemma rotate_mul (g h : SpatialRotation) (x : Space) :
    rotate (g*h) x = rotate g (rotate h x) := rfl

@[simp] lemma rotate_one (x : Space) : rotate 1 x = x := rfl

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_TruncatedCoulomb
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

def truncatedCoulomb (R : ℝ) : Space → ℝ := (ball 0 R).indicator (fun x => 1/‖x‖)

lemma truncatedCoulomb_nonneg (R : ℝ) (x : Space) : 0 ≤ truncatedCoulomb R x := by
  exact Set.indicator_nonneg (fun _ _ => by positivity) _

lemma truncatedCoulomb_integrable (R : ℝ) : Integrable (truncatedCoulomb R) := by
  have hi := (CoulombAnalysis.nuclear_memLp R).integrable (Fact.out : (1:ENNReal) ≤ 5/2)
  exact (show IntegrableOn (fun x : Space => 1/‖x‖) (ball 0 R) by
    simpa only [CoulombAnalysis.ballMeasure,IntegrableOn,one_div] using hi).integrable_indicator measurableSet_ball

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialAxis
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
namespace CoulombAnalysis

lemma tfSpace_unitBall_volume : volume.real (ball (0 : TFSpace) 1) = 4 * Real.pi / 3 := by
  rw [Measure.real, InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by simp [TFSpace])]
  norm_num [Nat.doubleFactorial]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

lemma tfSpace_radial_integral (f : ℝ → ℝ) :
    ∫ x : TFSpace, f ‖x‖ = 4 * Real.pi * ∫ r in Ioi 0, r ^ 2 * f r := by
  rw [integral_fun_norm_addHaar volume f, tfSpace_unitBall_volume]
  simp only [TFSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma integral_Iic_hasDerivAt {f : ℝ → ℝ} (hf : Integrable f) {r : ℝ}
    (hc : ContinuousAt f r) : HasDerivAt (fun s => ∫ t in Iic s, f t) (f r) r := by
  have he : (fun s => ∫ t in Iic s, f t) =
      fun s => (∫ t in r..s, f t) + ∫ t in Iic r, f t := by
    funext s
    have hh := intervalIntegral.integral_Iic_sub_Iic (hf.integrableOn (s := Iic r))
      (hf.integrableOn (s := Iic s))
    linarith
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right hf.intervalIntegrable
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hc).add_const _

lemma integral_Ioi_hasDerivAt {f : ℝ → ℝ} (hf : Integrable f) {r : ℝ}
    (hc : ContinuousAt f r) : HasDerivAt (fun s => ∫ t in Ioi s, f t) (-f r) r := by
  have he : (fun s => ∫ t in Ioi s, f t) =
      fun s => (∫ t in Ioi r, f t) - ∫ t in r..s, f t := by
    funext s
    have hh := intervalIntegral.integral_Ioi_sub_Ioi' (hf.integrableOn (s := Ioi r))
      (hf.integrableOn (s := Ioi s))
    linarith
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right hf.intervalIntegrable
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hc).const_sub _

def radialAxis : TFSpace := EuclideanSpace.single 0 1

@[simp] lemma radialAxis_norm : ‖radialAxis‖ = 1 := by simp [radialAxis]

def radialTrace (ρ : TFSpace → ℝ) (r : ℝ) : ℝ := ρ (r • radialAxis)

lemma IsRadial.trace {ρ : TFSpace → ℝ} (hr : IsRadial ρ) (x : TFSpace) :
    ρ x = radialTrace ρ ‖x‖ := by
  exact hr x (‖x‖ • radialAxis) (by simp [norm_smul])

lemma radialTrace_continuousAt {ρ : TFSpace → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) : ContinuousAt (radialTrace ρ) r := by
  change ContinuousAt (fun s => ρ (s • radialAxis)) r
  have hg : ContinuousAt (fun s : ℝ => s • radialAxis) r := by fun_prop
  exact ContinuousAt.comp (f := fun s : ℝ => s • radialAxis) (hc (r • radialAxis) (smul_ne_zero hr.ne' (by
    apply norm_ne_zero_iff.mp; rw [radialAxis_norm]; norm_num))) hg

lemma radialTrace_mem2 {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hr : IsRadial ρ) :
    IntegrableOn (fun s : ℝ => s ^ 2 * radialTrace ρ s) (Ioi 0) := by
  have he : (fun x : TFSpace => radialTrace ρ ‖x‖) = ρ := funext fun x => (hr.trace x).symm
  have hi : Integrable (fun x : TFSpace => radialTrace ρ ‖x‖) := by rwa [he]
  have hh := (integrable_fun_norm_addHaar (volume : Measure TFSpace) (f := radialTrace ρ)).mp hi
  simpa only [TFSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul] using hh

lemma radialTrace_mem1 {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    (hr : IsRadial ρ) : IntegrableOn (fun s : ℝ => s * radialTrace ρ s) (Ioi 0) := by
  have hi := tfPotential_integrable h1 hp 0
  simp only [zero_sub, norm_neg] at hi
  have he : (fun x : TFSpace => radialTrace ρ ‖x‖ / ‖x‖) = (fun x => ρ x / ‖x‖) :=
    funext fun x => by rw [← hr.trace]
  have hh := (integrable_fun_norm_addHaar (volume : Measure TFSpace)
    (f := fun s => radialTrace ρ s / s)).mp (he ▸ hi)
  simp only [TFSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul] at hh
  apply hh.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have hn : s ≠ 0 := ne_of_gt (show 0 < s from hs)
  field_simp [hn]

def radialMassIntegrand (ρ : TFSpace → ℝ) : ℝ → ℝ :=
  (Ioi 0).indicator (fun s => s ^ 2 * radialTrace ρ s)

def radialTailIntegrand (ρ : TFSpace → ℝ) : ℝ → ℝ :=
  (Ioi 0).indicator (fun s => s * radialTrace ρ s)

def radialMass (ρ : TFSpace → ℝ) (r : ℝ) : ℝ :=
  4 * Real.pi * ∫ s in Iic r, radialMassIntegrand ρ s

def radialTail (ρ : TFSpace → ℝ) (r : ℝ) : ℝ :=
  4 * Real.pi * ∫ s in Ioi r, radialTailIntegrand ρ s

lemma radialMassIntegrand_integrable {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hr : IsRadial ρ) :
    Integrable (radialMassIntegrand ρ) :=
  (radialTrace_mem2 h1 hr).integrable_indicator measurableSet_Ioi

lemma radialTailIntegrand_integrable {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ) : Integrable (radialTailIntegrand ρ) :=
  (radialTrace_mem1 h1 hp hr).integrable_indicator measurableSet_Ioi

lemma radialMassIntegrand_continuousAt {ρ : TFSpace → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) : ContinuousAt (radialMassIntegrand ρ) r := by
  have he : radialMassIntegrand ρ =ᶠ[𝓝 r] (fun s => s ^ 2 * radialTrace ρ s) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact indicator_of_mem hs _
  exact ((continuousAt_id.pow 2).mul (radialTrace_continuousAt hr hc)).congr he.symm

lemma radialTailIntegrand_continuousAt {ρ : TFSpace → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) : ContinuousAt (radialTailIntegrand ρ) r := by
  have he : radialTailIntegrand ρ =ᶠ[𝓝 r] (fun s => s * radialTrace ρ s) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact indicator_of_mem hs _
  exact (continuousAt_id.mul (radialTrace_continuousAt hr hc)).congr he.symm

lemma radialMass_hasDerivAt {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {r : ℝ} (hrp : 0 < r) :
    HasDerivAt (radialMass ρ) (4 * Real.pi * r ^ 2 * radialTrace ρ r) r := by
  have hh := (integral_Iic_hasDerivAt (radialMassIntegrand_integrable h1 hr)
    (radialMassIntegrand_continuousAt hrp hc)).const_mul (4 * Real.pi)
  unfold radialMass
  simpa [radialMassIntegrand, hrp, mul_assoc] using hh

lemma radialTail_hasDerivAt {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hp : MemLp ρ (5 / 3))
    (hr : IsRadial ρ) (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {r : ℝ} (hrp : 0 < r) :
    HasDerivAt (radialTail ρ) (-(4 * Real.pi * r * radialTrace ρ r)) r := by
  have hh := (integral_Ioi_hasDerivAt (radialTailIntegrand_integrable h1 hp hr)
    (radialTailIntegrand_continuousAt hrp hc)).const_mul (4 * Real.pi)
  unfold radialTail
  simpa [radialTailIntegrand, hrp, mul_assoc, mul_neg] using hh

lemma radialMass_contDiffOn {ρ : TFSpace → ℝ} (h1 : Integrable ρ) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) : ContDiffOn ℝ 1 (radialMass ρ) (Ioi 0) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun r hrp => (radialMass_hasDerivAt h1 hr hc hrp).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  have he : EqOn (deriv (radialMass ρ)) (fun r => 4 * Real.pi * r ^ 2 * radialTrace ρ r) (Ioi 0) :=
    fun r hrp => (radialMass_hasDerivAt h1 hr hc hrp).deriv
  apply ContinuousOn.congr _ (fun r hrp => he hrp)
  exact fun r hrp => ((continuousAt_const.mul (continuousAt_id.pow 2)).mul
    (radialTrace_continuousAt hrp hc)).continuousWithinAt

lemma radialMass_eq_integral {ρ : TFSpace → ℝ} (hr : IsRadial ρ) (r : ℝ) :
    radialMass ρ r = ∫ y in {y : TFSpace | ‖y‖ ≤ r}, ρ y := by
  have hm : MeasurableSet {y : TFSpace | ‖y‖ ≤ r} := measurableSet_le measurable_norm measurable_const
  have he : {y : TFSpace | ‖y‖ ≤ r}.indicator ρ =
      (fun y => (Iic r).indicator (radialTrace ρ) ‖y‖) := by
    funext y
    by_cases hy : ‖y‖ ≤ r <;> simp [hy, hr.trace y]
  rw [← integral_indicator hm, he, tfSpace_radial_integral]
  unfold radialMass
  congr 1
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae (Eventually.of_forall fun s => ?_)
  by_cases hs : 0 < s <;> by_cases hsr : s ≤ r <;> simp [radialMassIntegrand, hs, hsr]

lemma radialTail_eq_integral {ρ : TFSpace → ℝ} (hr : IsRadial ρ) (r : ℝ) :
    radialTail ρ r = ∫ y in {y : TFSpace | r < ‖y‖}, ρ y / ‖y‖ := by
  have hm : MeasurableSet {y : TFSpace | r < ‖y‖} := measurableSet_lt measurable_const measurable_norm
  have he : {y : TFSpace | r < ‖y‖}.indicator (fun y => ρ y / ‖y‖) =
      (fun y => (Ioi r).indicator (fun s => radialTrace ρ s / s) ‖y‖) := by
    funext y
    by_cases hy : r < ‖y‖ <;> simp [hy, hr.trace y]
  rw [← integral_indicator hm, he, tfSpace_radial_integral]
  unfold radialTail
  congr 1
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae (Eventually.of_forall fun s => ?_)
  by_cases hs : 0 < s <;> by_cases hsr : r < s <;> simp [radialTailIntegrand, hs, hsr]
  field_simp [hs.ne']

def radialPotential (ρ : TFSpace → ℝ) (r : ℝ) : ℝ := radialMass ρ r / r + radialTail ρ r

lemma tfPotential_eq_radialPotential {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) {x : TFSpace} (hx : x ≠ 0) :
    tfPotential ρ x = radialPotential ρ ‖x‖ := by
  rw [tfPotential_newton h1 hp hr hR hs hx, radialPotential,
    radialMass_eq_integral hr, radialTail_eq_integral hr]

lemma radialPotential_hasDerivAt {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {r : ℝ} (hrp : 0 < r) :
    HasDerivAt (radialPotential ρ) (-(radialMass ρ r) / r ^ 2) r := by
  have hh := ((radialMass_hasDerivAt h1 hr hc hrp).div (hasDerivAt_id r) hrp.ne').add
    (radialTail_hasDerivAt h1 hp hr hc hrp)
  simp only [id_eq] at hh
  convert hh using 1 <;> (try rfl)
  field_simp [hrp.ne']
  ring

lemma radialPotential_contDiffOn {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) : ContDiffOn ℝ 2 (radialPotential ρ) (Ioi 0) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun r hrp => (radialPotential_hasDerivAt h1 hp hr hc hrp).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  have he : EqOn (deriv (radialPotential ρ)) (fun r => -(radialMass ρ r) / r ^ 2) (Ioi 0) :=
    fun r hrp => (radialPotential_hasDerivAt h1 hp hr hc hrp).deriv
  apply ContDiffOn.congr _ (fun r hrp => he hrp)
  exact (radialMass_contDiffOn h1 hr hc).neg.div (contDiffOn_id.pow 2)
    (fun r hrp => pow_ne_zero _ (ne_of_gt hrp))

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology

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

abbrev TFField (R : ℝ) := Lp ℝ (5 / 2) (ballMeasure R)

def tfPatchPair (R : ℝ) : TFField R →L[ℝ] TFLp (ballMeasure R) →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing (ballMeasure R) (5 / 2) (5 / 3)

lemma tfPatchPair_apply (R : ℝ) (Φ : TFField R) (f : TFLp (ballMeasure R)) :
    tfPatchPair R Φ f = ∫ x, Φ x * f x ∂ballMeasure R := by
  exact ContinuousLinearMap.lpPairing_eq_integral ..

def tfPatchLinear (R : ℝ) (Φ : TFField R) : TFLp (ballMeasure R) →L[ℝ] ℝ :=
  -tfPatchPair R Φ

@[simp] lemma tfPatchLinear_apply (R : ℝ) (Φ : TFField R) (f : TFLp (ballMeasure R)) :
    tfPatchLinear R Φ f = -(∫ x, Φ x * f x ∂ballMeasure R) := by
  simp only [tfPatchLinear, neg_apply, tfPatchPair_apply]

def tfPatchFunctional (R T : ℝ) (Φ : TFField R) (f : TFLp (ballMeasure R)) : ℝ :=
  T * ‖f‖ ^ (5 / 3 : ℝ) + tfPatchLinear R Φ f + (1 / 2 : ℝ) * tfCoulombL R f f

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

@[simp] lemma tfPatchFunctional_zero (R T : ℝ) (Φ : TFField R) :
    tfPatchFunctional R T Φ 0 = 0 := by
  simp only [tfPatchFunctional, map_zero, mul_zero, add_zero, norm_zero]
  rw [Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0), mul_zero]

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

open MeasureTheory Set InnerProductSpace Laplacian
open scoped BigOperators

lemma compact_partial_integration_by_parts {f g : TFSpace → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hcg : HasCompactSupport g)
    (v : TFSpace) :
    (∫ x, f x*fderiv ℝ g x v) = -(∫ x, fderiv ℝ f x v*g x) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hdf.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left)
    ((hf.continuous.mul hdg).integrable_of_hasCompactSupport (hcg.fderiv_apply ℝ v).mul_left)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left)
    (fun x _ => (hf.differentiable (by norm_num)).differentiableAt)
    (fun x _ => (hg.differentiable (by norm_num)).differentiableAt)

def tfPartial (f : TFSpace → ℝ) (i : Fin 3) (x : TFSpace) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

lemma tfPartial_contDiff {f : TFSpace → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin 3) :
    ContDiff ℝ 1 (tfPartial f i) :=
  (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).clm_apply contDiff_const

lemma tfPartial_continuous {f : TFSpace → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    Continuous (tfPartial f i) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma tfPartial_compact {f : TFSpace → ℝ} (hf : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (tfPartial f i) := hf.fderiv_apply ℝ _

lemma tfLaplacian_eq {f : TFSpace → ℝ} (hf : ContDiff ℝ 2 f) :
    Δ f = fun x => ∑ i : Fin 3, tfPartial (tfPartial f i) i x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 3) ℝ)]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  simp only [EuclideanSpace.basisFun_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,tfPartial]
  exact (fderiv_apply_const_scalar
    ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).differentiable
      (by norm_num)).differentiableAt _ _).symm

lemma tfLaplacian_continuous {f : TFSpace → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Δ f) := by
  rw [tfLaplacian_eq hf]
  exact continuous_finsetSum _ (fun i _ => tfPartial_continuous (tfPartial_contDiff hf i) i)

lemma tfLaplacian_compact {f : TFSpace → ℝ} (hf : ContDiff ℝ 2 f)
    (hcf : HasCompactSupport f) : HasCompactSupport (Δ f) := by
  rw [tfLaplacian_eq hf]
  have he : (fun x => ∑ i : Fin 3, tfPartial (tfPartial f i) i x) =
      ∑ i : Fin 3, tfPartial (tfPartial f i) i := by
    funext x
    simp only [Finset.sum_apply]
  rw [he]
  exact HasCompactSupport.finset_sum
    (s := Finset.univ) (f := fun i : Fin 3 => tfPartial (tfPartial f i) i)
    (fun i _ => tfPartial_compact (tfPartial_compact hcf i) i)

lemma compact_second_partial_green {f g : TFSpace → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (i : Fin 3) :
    (∫ x, f x*tfPartial (tfPartial g i) i x) =
      ∫ x, tfPartial (tfPartial f i) i x*g x := by
  have h1 := compact_partial_integration_by_parts (hf.of_le (by norm_num))
    (tfPartial_contDiff hg i) (tfPartial_compact hcg i) (EuclideanSpace.single i 1)
  have h2 := compact_partial_integration_by_parts (tfPartial_contDiff hf i)
    (hg.of_le (by norm_num)) hcg (EuclideanSpace.single i 1)
  change (∫ x, f x*tfPartial (tfPartial g i) i x) =
    -(∫ x, tfPartial f i x*tfPartial g i x) at h1
  change (∫ x, tfPartial f i x*tfPartial g i x) =
    -(∫ x, tfPartial (tfPartial f i) i x*g x) at h2
  rw [h1,h2,neg_neg]

theorem compact_laplacian_green {f g : TFSpace → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    (∫ x, f x*Δ g x) = ∫ x, Δ f x*g x := by
  rw [tfLaplacian_eq hf,tfLaplacian_eq hg]
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (μ := volume)
    (f := fun i x => f x*tfPartial (tfPartial g i) i x) (fun i _ =>
    (hf.continuous.mul (tfPartial_continuous (tfPartial_contDiff hg i) i)).integrable_of_hasCompactSupport
      (tfPartial_compact (tfPartial_compact hcg i) i).mul_left)]
  rw [integral_finsetSum Finset.univ (μ := volume)
    (f := fun i x => tfPartial (tfPartial f i) i x*g x) (fun i _ =>
    ((tfPartial_continuous (tfPartial_contDiff hf i) i).mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left)]
  apply Finset.sum_congr rfl
  intro i _
  exact compact_second_partial_green hf hg hcg i

theorem compact_laplacian_energy {f : TFSpace → ℝ}
    (hf : ContDiff ℝ 2 f) (hcf : HasCompactSupport f) :
    (∫ x, f x*Δ f x) = -(∑ i : Fin 3, ∫ x, (tfPartial f i x)^2) := by
  rw [tfLaplacian_eq hf]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (μ := volume)
    (f := fun i x => f x*tfPartial (tfPartial f i) i x) (fun i _ =>
    (hf.continuous.mul (tfPartial_continuous (tfPartial_contDiff hf i) i)).integrable_of_hasCompactSupport
      (tfPartial_compact (tfPartial_compact hcf i) i).mul_left),←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [tfPartial,pow_two] using compact_partial_integration_by_parts
    (hf.of_le (by norm_num)) (tfPartial_contDiff hf i) (tfPartial_compact hcf i) (EuclideanSpace.single i 1)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialPotentialSqrtDeriv
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
namespace CoulombAnalysis

lemma radialPotential_sqrt_hasDerivAt {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => radialPotential ρ (Real.sqrt t))
      (-(radialMass ρ (Real.sqrt s)) / (2 * (Real.sqrt s) ^ 3)) s := by
  have hh := (radialPotential_hasDerivAt h1 hp hr hc (Real.sqrt_pos.mpr hs)).comp s
    (Real.hasDerivAt_sqrt hs.ne')
  convert hh using 1 <;> (try rfl)
  field_simp [Real.sqrt_ne_zero'.mpr hs]

lemma radialPotential_sqrt_deriv {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {s : ℝ} (hs : 0 < s) :
    deriv (fun t => radialPotential ρ (Real.sqrt t)) s =
      -(radialMass ρ (Real.sqrt s)) / (2 * (Real.sqrt s) ^ 3) :=
  (radialPotential_sqrt_hasDerivAt h1 hp hr hc hs).deriv

lemma radialPotential_sqrt_second {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {s : ℝ} (hs : 0 < s) :
    deriv (deriv (fun t => radialPotential ρ (Real.sqrt t))) s =
      -Real.pi * radialTrace ρ (Real.sqrt s) / (Real.sqrt s) ^ 2 +
        3 * radialMass ρ (Real.sqrt s) / (4 * (Real.sqrt s) ^ 5) := by
  have he : deriv (fun t => radialPotential ρ (Real.sqrt t)) =ᶠ[𝓝 s]
      fun t => -(radialMass ρ (Real.sqrt t)) / (2 * (Real.sqrt t) ^ 3) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact radialPotential_sqrt_deriv h1 hp hr hc ht
  rw [he.deriv_eq]
  have hm := (radialMass_hasDerivAt h1 hr hc (Real.sqrt_pos.mpr hs)).comp s
    (Real.hasDerivAt_sqrt hs.ne')
  have ht := ((Real.hasDerivAt_sqrt hs.ne').pow 3).const_mul 2
  have hh := hm.neg.div ht (by
    change 2 * Real.sqrt s ^ 3 ≠ 0
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Real.sqrt_ne_zero'.mpr hs)))
  change HasDerivAt (fun t => -radialMass ρ (Real.sqrt t) / (2 * (Real.sqrt t) ^ 3)) _ s at hh
  rw [hh.deriv]
  simp only [Pi.pow_apply, Pi.neg_apply, Function.comp_apply]
  field_simp [Real.sqrt_ne_zero'.mpr hs]
  ring

theorem tfPotential_poisson {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5 / 3)) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R) {x : TFSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (tfPotential ρ) x ∧ Δ (tfPotential ρ) x = -(4 * Real.pi * ρ x) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let g : ℝ → ℝ := fun s => radialPotential ρ (Real.sqrt s)
  have hg : ContDiffAt ℝ 2 g (‖x‖ ^ 2) := by
    have hrp := (radialPotential_contDiffOn h1 hp hr hc).contDiffAt (Ioi_mem_nhds hn)
    have hsq : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := Real.sqrt_sq (norm_nonneg x)
    have hrp' : ContDiffAt ℝ 2 (radialPotential ρ) (Real.sqrt (‖x‖ ^ 2)) := by rwa [hsq]
    exact hrp'.comp (‖x‖ ^ 2) (Real.contDiffAt_sqrt (pow_ne_zero _ hn.ne'))
  have he : tfPotential ρ =ᶠ[𝓝 x] (fun y => g (‖y‖ ^ 2)) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    dsimp [g]
    rw [Real.sqrt_sq (norm_nonneg y)]
    exact tfPotential_eq_radialPotential h1 hp hr hR hs hy
  have hfull : ContDiffAt ℝ 2 (fun y : TFSpace => g (‖y‖ ^ 2)) x :=
    hg.comp x (contDiff_norm_sq ℝ).contDiffAt
  refine ⟨hfull.congr_of_eventuallyEq he, ?_⟩
  rw [(laplacian_congr_nhds he).eq_of_nhds, CoulombPDE.laplacian_norm_sq_comp hg]
  dsimp only [g]
  rw [radialPotential_sqrt_deriv h1 hp hr hc (sq_pos_of_pos hn),
    radialPotential_sqrt_second h1 hp hr hc (sq_pos_of_pos hn), Real.sqrt_sq (norm_nonneg x),
    ← hr.trace x]
  have hdim : Module.finrank ℝ TFSpace = 3 := by simp [TFSpace]
  rw [hdim]
  norm_num only [Nat.cast_ofNat]
  field_simp [hn.ne']
  ring

end CoulombAnalysis

open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian

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

lemma newtonInverse_locallyIntegrable :
    LocallyIntegrable (fun x : TFSpace => ‖x‖⁻¹) := by
  apply locallyIntegrable_of_norm_le_rpow (C := (1:ℝ)) (α := (1:ℝ))
    (by simp [TFSpace]) (by simp [TFSpace])
  · exact Eventually.of_forall fun x => by simp [Real.rpow_neg_one]
  · exact measurable_norm.inv.aestronglyMeasurable

lemma tfPotential_eq_convolution (ρ : TFSpace → ℝ) :
    tfPotential ρ = ρ ⋆[newtonMul] (fun x : TFSpace => ‖x‖⁻¹) := by
  funext x
  simp only [tfPotential,convolution,newtonMul,ContinuousLinearMap.mul_apply',div_eq_mul_inv]

lemma tfPotential_contDiff {ρ : TFSpace → ℝ} {n : ℕ∞}
    (hρ : ContDiff ℝ n ρ) (hc : HasCompactSupport ρ) :
    ContDiff ℝ n (tfPotential ρ) := by
  rw [tfPotential_eq_convolution]
  exact hc.contDiff_convolution_left newtonMul hρ newtonInverse_locallyIntegrable

lemma tfPotential_poisson_global {ρ : TFSpace → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hc : HasCompactSupport ρ) (hr : IsRadial ρ) :
    Δ (tfPotential ρ) = fun x => -(4*Real.pi*ρ x) := by
  obtain ⟨R,hR,hRs⟩ := hc.isCompact.isBounded.exists_pos_norm_lt
  have hs : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ R := fun y hy =>
    (hRs y (subset_tsupport ρ hy)).le
  apply Measure.eq_of_ae_eq (μ := volume) _ (tfLaplacian_continuous (tfPotential_contDiff hρ hc))
    ((continuous_const.mul hρ.continuous).neg)
  filter_upwards [CoulombAtom.ae_ne_point (0 : TFSpace)] with x hx
  exact (tfPotential_poisson (hρ.continuous.integrable_of_hasCompactSupport hc)
    (hρ.continuous.memLp_of_hasCompactSupport hc) hr (fun _ _ => hρ.continuous.continuousAt)
    hR.le hs hx).2

end CoulombAnalysis

end Work_SmoothNewton_scope

open MeasureTheory Filter Set Metric InnerProductSpace Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis

lemma shrinking_density_test_limit {η : ℕ → TFSpace → ℝ} {r : ℕ → ℝ}
    (hc : ∀ n, Continuous (η n)) (hcompact : ∀ n, HasCompactSupport (η n))
    (hn : ∀ n x, 0 ≤ η n x) (hm : ∀ n, ∫ x, η n x = 1)
    (hs : ∀ n x, η n x ≠ 0 → ‖x‖ ≤ r n) (hr : Tendsto r atTop (𝓝 0))
    {g : TFSpace → ℝ} (hg : Continuous g) :
    Tendsto (fun n => ∫ x, η n x*g x) atTop (𝓝 (g 0)) := by
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨d,hd,heps⟩ := (Metric.continuousAt_iff.mp hg.continuousAt) (e/2) (half_pos he)
  filter_upwards [hr.eventually (gt_mem_nhds hd)] with n hnsmall
  have hi : Integrable (η n) := (hc n).integrable_of_hasCompactSupport (hcompact n)
  have hi2 : Integrable (fun x => η n x*g x) := ((hc n).mul hg).integrable_of_hasCompactSupport (hcompact n).mul_right
  have heq : (∫ x, η n x*g x)-g 0 = ∫ x, η n x*(g x-g 0) := by
    simp_rw [mul_sub]
    rw [integral_sub hi2 (hi.mul_const _),integral_mul_const,hm,one_mul]
  have hb : ‖∫ x, η n x*(g x-g 0)‖ ≤ e/2 := by
    have hh := norm_integral_le_of_norm_le (hi.const_mul (e/2))
      (Eventually.of_forall fun x => (show ‖η n x*(g x-g 0)‖ ≤ (e/2)*η n x from by
        by_cases hx : η n x = 0
        · simp [hx]
        · rw [norm_mul,Real.norm_of_nonneg (hn n x),Real.norm_eq_abs]
          have hgx : |g x-g 0| < e/2 := by
            apply heps
            simpa only [dist_zero_right] using (hs n x hx).trans_lt hnsmall
          nlinarith [mul_le_mul_of_nonneg_left hgx.le (hn n x)]))
    simpa only [integral_const_mul,hm,mul_one] using hh
  rw [dist_eq_norm,heq]
  exact hb.trans_lt (half_lt_self he)

end CoulombAnalysis

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

lemma compact_laplacian_mass {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    (∫ x, Δ g x) = 0 := by
  simpa using compact_laplacian_green (f := fun _ => (1 : ℝ)) contDiff_const hg hcg

end CoulombAnalysis

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_PuncturedGreenBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology

open CoulombAtom

def PuncturedPoisson (u f : Space → ℝ) : Prop :=
  ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
    tsupport g ⊆ {0}ᶜ → (∫ x, u x*Δ g x) = ∫ x, f x*g x

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoulombBallIntegral
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

lemma integral_norm_rpow_ball {R p : ℝ} (hR : 0 < R) (hp : -3 < p) :
    (∫ x : TFSpace in ball 0 R, ‖x‖^p) =
      (4*Real.pi/(p+3))*R^(p+3) := by
  rw [← integral_indicator measurableSet_ball]
  have he : (ball (0 : TFSpace) R).indicator (fun x => ‖x‖^p) =
      fun x => (Iio R).indicator (fun r : ℝ => r^p) ‖x‖ := by
    funext x
    simp only [indicator,mem_ball_zero_iff,mem_Iio]
  rw [he,tfSpace_radial_integral]
  have hind : (fun r : ℝ => r^2*((Iio R).indicator (fun z : ℝ => z^p) r)) =
      (Iio R).indicator (fun r : ℝ => r^2*r^p) := by
    funext r
    by_cases h : r < R <;> simp [h]
  rw [hind,integral_indicator measurableSet_Iio]
  have hset : Iio R ∩ Ioi (0:ℝ) = Ioo 0 R := by ext r; simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo]; tauto
  rw [Measure.restrict_restrict measurableSet_Iio,hset]
  have he2 : (∫ r : ℝ in Ioo 0 R, r^2*r^p) = ∫ r : ℝ in Ioo 0 R, r^(p+2) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only
    rw [← Real.rpow_natCast r 2,← Real.rpow_add hr.1]
    congr 1
    ring
  rw [he2,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hR.le]
  rw [integral_rpow (Or.inl (by linarith : -1 < p+2))]
  rw [Real.zero_rpow (by linarith : p+2+1 ≠ 0)]
  have hp3 : p+2+1 = p+3 := by ring
  rw [hp3]
  ring

lemma integral_coulomb_ball {R : ℝ} (hR : 0 < R) :
    (∫ x : TFSpace in ball 0 R, ‖x‖⁻¹) = 2*Real.pi*R^2 := by
  have hh := integral_norm_rpow_ball hR (by norm_num : (-3:ℝ) < -1)
  norm_num [Real.rpow_neg_one] at hh
  rw [hh]
  ring

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BoundedDensityPotential
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

def truncatedInvSquare (R : ℝ) : TFSpace → ℝ :=
  (ball 0 R).indicator (fun x => ‖x‖⁻¹^2)

lemma truncatedInvSquare_nonneg (R : ℝ) (x : TFSpace) : 0 ≤ truncatedInvSquare R x :=
  indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma truncatedInvSquare_integrable (R : ℝ) : Integrable (truncatedInvSquare R) := by
  have hi : IntegrableOn (fun x : TFSpace => ‖x‖^(-2:ℝ)) (ball 0 R) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp [TFSpace])
      (by norm_num [TFSpace] : (2:ℝ) < Module.finrank ℝ TFSpace) (C := 1)
    · exact Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),one_mul]
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  have hh := hi.integrable_indicator measurableSet_ball
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  norm_num [truncatedInvSquare,Real.rpow_neg,Real.rpow_two,inv_pow]

lemma truncatedInvSquare_integral {R : ℝ} (hR : 0 < R) :
    (∫ x, truncatedInvSquare R x) = 4*Real.pi*R := by
  rw [truncatedInvSquare,integral_indicator measurableSet_ball]
  have hh := integral_norm_rpow_ball hR (by norm_num : (-3:ℝ) < -2)
  norm_num [Real.rpow_neg,Real.rpow_two,inv_pow] at hh
  simpa only [inv_pow] using hh

lemma bounded_support_memLp {ρ : TFSpace → ℝ} (hm : Measurable ρ) {M S : ℝ}
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    (hs : Function.support ρ ⊆ ball 0 S) (p : ENNReal) : MemLp ρ p := by
  have hc : HasCompactSupport ρ := HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : TFSpace) S) (hs.trans ball_subset_closedBall)
  exact hc.memLp_of_bound hm.aestronglyMeasurable M
    (Eventually.of_forall fun z => by simpa only [Real.norm_of_nonneg (hn z)] using hb z)

lemma bounded_support_integrable {ρ : TFSpace → ℝ} (hm : Measurable ρ) {M S : ℝ}
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    (hs : Function.support ρ ⊆ ball 0 S) : Integrable ρ :=
  memLp_one_iff_integrable.mp (bounded_support_memLp hm hn hb hs 1)

lemma coulomb_inv_difference {x y z : TFSpace} (hx : z ≠ x) (hy : z ≠ y) :
    |‖x-z‖⁻¹-‖y-z‖⁻¹| ≤ ‖x-y‖*(‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2 := by
  have ha : 0 < ‖x-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx.symm)
  have hb : 0 < ‖y-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy.symm)
  have he : ‖x-z‖⁻¹-‖y-z‖⁻¹ = (‖y-z‖-‖x-z‖)/(‖x-z‖*‖y-z‖) := by field_simp
  have hd : |‖y-z‖-‖x-z‖| ≤ ‖x-y‖ := by
    have hh := abs_norm_sub_norm_le (y-z) (x-z)
    simpa only [sub_sub_sub_cancel_right,norm_sub_rev] using hh
  rw [he,abs_div,abs_of_nonneg (mul_nonneg ha.le hb.le)]
  calc
    _ ≤ ‖x-y‖/(‖x-z‖*‖y-z‖) := div_le_div_of_nonneg_right hd (mul_nonneg ha.le hb.le)
    _ = ‖x-y‖*(‖x-z‖⁻¹*‖y-z‖⁻¹) := by ring
    _ ≤ ‖x-y‖*((‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      nlinarith [sq_nonneg (‖x-z‖⁻¹-‖y-z‖⁻¹)]
    _ = _ := by ring

lemma support_distance_lt {ρ : TFSpace → ℝ} {S : ℝ}
    (hs : Function.support ρ ⊆ ball 0 S) {x z : TFSpace} (hx : ‖x‖ ≤ S) (hz : ρ z ≠ 0) :
    ‖x-z‖ < 2*S := by
  have hh : ‖z‖ < S := mem_ball_zero_iff.mp (hs hz)
  exact (norm_sub_le x z).trans_lt (by linarith)

theorem bounded_density_potential_le {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M S : ℝ} (hM : 0 ≤ M) (hS : 0 < S) (hn : ∀ z, 0 ≤ ρ z)
    (hb : ∀ z, ρ z ≤ M) (hs : Function.support ρ ⊆ ball 0 S)
    (x : TFSpace) (hx : ‖x‖ ≤ S) : tfPotential ρ x ≤ 8*Real.pi*M*S^2 := by
  have hk := (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable (2*S)).aestronglyMeasurable
    |>.mpr (truncatedCoulomb_integrable (2*S))
  have hi := tfPotential_integrable (bounded_support_integrable hm hn hb hs)
    (bounded_support_memLp hm hn hb hs (5/3)) x
  have hh : (∫ z, ρ z/‖x-z‖) ≤ ∫ z, M*truncatedCoulomb (2*S) (x-z) := by
    apply integral_mono hi (hk.const_mul M)
    intro z
    change ρ z/‖x-z‖ ≤ M*truncatedCoulomb (2*S) (x-z)
    by_cases hz : ρ z = 0
    · simp only [hz,zero_div]
      exact mul_nonneg hM (truncatedCoulomb_nonneg _ _)
    · rw [truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr (support_distance_lt hs hx hz))]
      exact (div_le_div_of_nonneg_right (hb z) (norm_nonneg _)).trans_eq (by ring)
  change (∫ z, ρ z/‖x-z‖) ≤ _
  apply hh.trans_eq
  rw [integral_const_mul,integral_sub_left_eq_self,truncatedCoulomb,integral_indicator measurableSet_ball]
  simp only [one_div]
  rw [integral_coulomb_ball (by linarith : 0 < 2*S)]
  ring

theorem bounded_density_potential_difference {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M S : ℝ} (hM : 0 ≤ M) (hS : 0 < S) (hn : ∀ z, 0 ≤ ρ z)
    (hb : ∀ z, ρ z ≤ M) (hs : Function.support ρ ⊆ ball 0 S)
    (x y : TFSpace) (hx : ‖x‖ ≤ S) (hy : ‖y‖ ≤ S) :
    |tfPotential ρ x-tfPotential ρ y| ≤ 8*Real.pi*M*S*‖x-y‖ := by
  have hi (w : TFSpace) := tfPotential_integrable (bounded_support_integrable hm hn hb hs)
    (bounded_support_memLp hm hn hb hs (5/3)) w
  have hk (w : TFSpace) : Integrable (fun z => truncatedInvSquare (2*S) (w-z)) :=
    (tfSubMap_preserving w).integrable_comp (truncatedInvSquare_integrable (2*S)).aestronglyMeasurable
      |>.mpr (truncatedInvSquare_integrable (2*S))
  have he : (∫ z, ρ z/‖x-z‖-ρ z/‖y-z‖) = tfPotential ρ x-tfPotential ρ y :=
    integral_sub (hi x) (hi y)
  rw [←he]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ z, (M*‖x-y‖/2)*(truncatedInvSquare (2*S) (x-z)+truncatedInvSquare (2*S) (y-z)) := by
      apply integral_mono_ae ((hi x).sub (hi y)).abs (((hk x).add (hk y)).const_mul _)
      filter_upwards [volume.ae_ne x,volume.ae_ne y] with z hzx hzy
      change |ρ z/‖x-z‖-ρ z/‖y-z‖| ≤
        (M*‖x-y‖/2)*(truncatedInvSquare (2*S) (x-z)+truncatedInvSquare (2*S) (y-z))
      by_cases hz : ρ z = 0
      · simp only [hz,zero_div,sub_self,abs_zero]
        exact mul_nonneg (by positivity) (add_nonneg (truncatedInvSquare_nonneg _ _) (truncatedInvSquare_nonneg _ _))
      · rw [truncatedInvSquare,indicator_of_mem (mem_ball_zero_iff.mpr (support_distance_lt hs hx hz)),
          indicator_of_mem (mem_ball_zero_iff.mpr (support_distance_lt hs hy hz))]
        rw [div_eq_mul_inv,div_eq_mul_inv,←mul_sub,abs_mul,abs_of_nonneg (hn z)]
        calc
          _ ≤ ρ z*(‖x-y‖*(‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2) :=
            mul_le_mul_of_nonneg_left (coulomb_inv_difference hzx hzy) (hn z)
          _ ≤ M*(‖x-y‖*(‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2) :=
            mul_le_mul_of_nonneg_right (hb z) (by positivity)
          _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul,integral_add (hk x) (hk y),integral_sub_left_eq_self,integral_sub_left_eq_self,
        truncatedInvSquare_integral (by linarith : 0 < 2*S)]
      ring

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_SphericalMeanFieldBarrier
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

def sphereMean (f : Space → ℝ) (p : Space) : ℝ :=
  ∫ g : SpatialRotation, f (rotate g p) ∂rotationMeasure

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfRotate
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
namespace CoulombAnalysis

lemma tf_rotation_preserving (R : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) :
    MeasurePreserving e (ballMeasure R) (ballMeasure R) := by
  have he : e ⁻¹' ball (0 : TFSpace) R = ball 0 R := by
    ext x; simp
  have hp : MeasurePreserving e (volume : Measure TFSpace) volume := e.measurePreserving
  have hr := hp.restrict_preimage (s := ball (0 : TFSpace) R) measurableSet_ball
  rw [he] at hr
  exact hr

def tfRotate (R : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace)
    (f : TFLp (ballMeasure R)) : TFLp (ballMeasure R) :=
  Lp.compMeasurePreserving e (tf_rotation_preserving R e) f

lemma tfRotate_coe (R : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (f : TFLp (ballMeasure R)) :
    tfRotate R e f =ᵐ[ballMeasure R] fun x => f (e x) := Lp.coeFn_compMeasurePreserving _ _

lemma tfRotate_norm (R : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (f : TFLp (ballMeasure R)) :
    ‖tfRotate R e f‖ = ‖f‖ := Lp.norm_compMeasurePreserving _ _

lemma tfRotate_nonneg {R : ℝ} (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) : NonnegDensity (tfRotate R e f) := by
  filter_upwards [tfRotate_coe R e f, (tf_rotation_preserving R e).quasiMeasurePreserving.ae hf]
    with x hx hn
  rw [hx]; exact hn

lemma tfRotate_linear (R Z η : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (f : TFLp (ballMeasure R)) :
    tfBallLinear R Z η (tfRotate R e f) = tfBallLinear R Z η f := by
  have hi (g : TFSpace → ℝ) := (tf_rotation_preserving R e).integral_comp
    e.toHomeomorph.measurableEmbedding g
  simp only [tfBallLinear, sub_apply, smul_apply,
    smul_eq_mul, tfPairing_apply]
  congr 1
  · congr 1
    calc
      ∫ x, (1 : ℝ) * tfRotate R e f x ∂ballMeasure R =
        ∫ x, (1 : ℝ) * f (e x) ∂ballMeasure R := integral_congr_ae ((tfRotate_coe R e f).fun_comp _)
      _ = ∫ x, (1 : ℝ) * f x ∂ballMeasure R := hi (fun x => 1 * f x)
  · congr 1
    calc
      ∫ x, ‖x‖⁻¹ * tfRotate R e f x ∂ballMeasure R =
        ∫ x, ‖e x‖⁻¹ * f (e x) ∂ballMeasure R := by
          apply integral_congr_ae
          filter_upwards [tfRotate_coe R e f] with x hx
          rw [hx, e.norm_map]
      _ = ∫ x, ‖x‖⁻¹ * f x ∂ballMeasure R := hi (fun x => ‖x‖⁻¹ * f x)

lemma tfRotate_coulomb (R : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (f g : TFLp (ballMeasure R)) :
    tfCoulombL R (tfRotate R e f) (tfRotate R e g) = tfCoulombL R f g := by
  rw [tfCoulombL_apply, tfCoulombL_apply]
  calc
    _ = ∫ p : TFSpace × TFSpace, f (e p.1) * g (e p.2) / ‖e p.1 - e p.2‖
        ∂(ballMeasure R).prod (ballMeasure R) := by
      apply integral_congr_ae
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ballMeasure R)
        (ν := ballMeasure R)).ae (tfRotate_coe R e f),
        (Measure.quasiMeasurePreserving_snd (μ := ballMeasure R)
        (ν := ballMeasure R)).ae (tfRotate_coe R e g)] with p hf hg
      rw [hf, hg, ← e.map_sub, e.norm_map]
    _ = _ := (tf_rotation_preserving R e |>.prod (tf_rotation_preserving R e)).integral_comp
      (e.toHomeomorph.measurableEmbedding.prodMap e.toHomeomorph.measurableEmbedding)
      (fun p : TFSpace × TFSpace => f p.1 * g p.2 / ‖p.1 - p.2‖)

lemma tfRotate_functional (R T Z η : ℝ) (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (f : TFLp (ballMeasure R)) :
    tfBallFunctional R T Z η (tfRotate R e f) = tfBallFunctional R T Z η f := by
  simp only [tfBallFunctional, tfRotate_norm, tfRotate_linear, tfRotate_coulomb]

lemma tf_minimizer_rotation {R T Z η : ℝ} (hT : 0 < T) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hmin : ∀ g, NonnegDensity g →
      tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g)
    (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) : tfRotate R e f = f := by
  exact tfBallFunctional_min_unique R Z η hT (tfRotate_nonneg e hf) hf
    (fun g hg => by rw [tfRotate_functional]; exact hmin g hg) hmin

lemma tfBallPotential_rotation {R T Z η : ℝ} (hT : 0 < T) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hmin : ∀ g, NonnegDensity g →
      tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g)
    (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (x : TFSpace) :
    tfBallPotential R f (e x) = tfBallPotential R f x := by
  have hrot := tfRotate_coe R e f
  rw [tf_minimizer_rotation hT hf hmin e] at hrot
  unfold tfBallPotential
  calc
    _ = ∫ y, f (e y) / ‖e x - e y‖ ∂ballMeasure R :=
      ((tf_rotation_preserving R e).integral_comp e.toHomeomorph.measurableEmbedding
        (fun y => f y / ‖e x - y‖)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hrot] with y hy
      rw [← hy, ← e.map_sub, e.norm_map]

lemma tfField_extension_rotation {Z : ℝ} {f : TFLp (ballMeasure Z)}
    (hf : NonnegDensity f) (hmin : ∀ g, NonnegDensity g →
      tfBallFunctional Z CoulombAtom.tfKinetic Z 1 f ≤ tfBallFunctional Z CoulombAtom.tfKinetic Z 1 g)
    (e : TFSpace ≃ₗᵢ[ℝ] TFSpace) (x : TFSpace) :
    tfField Z (tfExtension Z f) (e x) = tfField Z (tfExtension Z f) x := by
  simp only [tfField, tfPotential_extension, e.norm_map,
    tfBallPotential_rotation tfKinetic_pos hf hmin]

lemma tfField_extension_radial {Z : ℝ} {f : TFLp (ballMeasure Z)}
    (hf : NonnegDensity f) (hmin : ∀ g, NonnegDensity g →
      tfBallFunctional Z CoulombAtom.tfKinetic Z 1 f ≤ tfBallFunctional Z CoulombAtom.tfKinetic Z 1 g)
    (x y : TFSpace) (hxy : ‖x‖ = ‖y‖) :
    tfField Z (tfExtension Z f) x = tfField Z (tfExtension Z f) y := by
  obtain ⟨e, he⟩ := exists_orthogonal_map_norm_eq x y hxy
  simpa only [he] using (tfField_extension_rotation hf hmin e x).symm

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfEulerDensity
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
namespace CoulombAnalysis
open CoulombAtom

lemma tfAdmissible_congr {M : ℝ} {ρ σ : Space → ℝ} (hρ : TFAdmissible M ρ)
    (he : ρ =ᵐ[volume] σ) : TFAdmissible M σ := by
  refine ⟨?_, hρ.2.1.congr he, (integral_congr_ae he).symm.trans hρ.2.2.1,
    hρ.2.2.2.1.congr (he.mono fun x hx => by dsimp; rw [hx]),
    hρ.2.2.2.2.1.congr (he.mono fun x hx => by dsimp; rw [hx]), ?_⟩
  · filter_upwards [hρ.1, he] with x hx hxe
    rwa [← hxe]
  · apply hρ.2.2.2.2.2.congr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae he,
      Measure.quasiMeasurePreserving_snd.ae he] with p hp hq
    simp only [directIntegrand, hp, hq]

lemma tfPotential_congr {ρ σ : Space → ℝ} (he : ρ =ᵐ[volume] σ) (x : Space) :
    tfPotential ρ x = tfPotential σ x :=
  integral_congr_ae (he.mono fun y hy => by dsimp; rw [hy])

lemma tfField_congr (Z : ℝ) {ρ σ : Space → ℝ} (he : ρ =ᵐ[volume] σ) (x : Space) :
    tfField Z ρ x = tfField Z σ x := by simp only [tfField, tfPotential_congr he]

lemma tfField_continuousAt {M Z : ℝ} {ρ : Space → ℝ} (hρ : TFAdmissible M ρ)
    {x : Space} (hx : x ≠ 0) : ContinuousAt (tfField Z ρ) x :=
  (continuousAt_const.div continuous_norm.continuousAt (norm_ne_zero_iff.mpr hx)).sub
    (tfPotential_continuous hρ.2.1 (tfAdmissible_memLp hρ)).continuousAt

def tfEulerDensity (Z : ℝ) (ρ : Space → ℝ) (x : Space) : ℝ :=
  (max (tfField Z ρ x - 1) 0 / ((5 / 3 : ℝ) * tfKinetic)) ^ (3 / 2 : ℝ)

lemma tfEulerDensity_nonneg (Z : ℝ) (ρ : Space → ℝ) (x : Space) :
    0 ≤ tfEulerDensity Z ρ x := by
  unfold tfEulerDensity
  exact Real.rpow_nonneg (div_nonneg (le_max_right _ _) (mul_pos (by norm_num) tfKinetic_pos).le) _

lemma tfEulerDensity_continuousAt {M Z : ℝ} {ρ : Space → ℝ} (hρ : TFAdmissible M ρ)
    {x : Space} (hx : x ≠ 0) : ContinuousAt (tfEulerDensity Z ρ) x := by
  exact (((tfField_continuousAt hρ hx).sub continuousAt_const).max continuousAt_const |>.div_const _).rpow_const (by norm_num)

lemma tfEulerDensity_support {Z : ℝ} (hZ : 0 < Z) {ρ : Space → ℝ}
    (hρ : ∀ᵐ y, 0 ≤ ρ y) {x : Space} (hx : Z ≤ ‖x‖) : tfEulerDensity Z ρ x = 0 := by
  have hp := tfPotential_nonneg hρ x
  have hn := (div_le_one (hZ.trans_le hx)).mpr hx
  have hh : tfField Z ρ x - 1 ≤ 0 := by unfold tfField; linarith
  simp only [tfEulerDensity, max_eq_right hh, zero_div, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]

theorem tf_unit_price_exists_regular (Z : ℝ) (hZ : 0 < Z) :
    ∃ M : ℝ, ∃ ρ : Space → ℝ, TFAdmissible M ρ ∧
      (∀ M' : ℝ, ∀ σ : Space → ℝ, TFAdmissible M' σ →
        tfFunctional Z ρ + M ≤ tfFunctional Z σ + M') ∧
      (∀ x, 0 ≤ ρ x) ∧
      (∀ x, ρ x = tfEulerDensity Z ρ x) ∧
      (∀ x y, ‖x‖ = ‖y‖ → ρ x = ρ y) ∧
      (∀ x, x ≠ 0 → ContinuousAt ρ x) ∧
      (∀ x, Z ≤ ‖x‖ → ρ x = 0) := by
  obtain ⟨f, hf, hmin⟩ := tfBallFunctional_exists_minimizer Z Z 1 tfKinetic_pos
  let ρ₀ := tfExtension Z f
  let ρ := tfEulerDensity Z ρ₀
  have he : ρ₀ =ᵐ[volume] ρ := tf_unit_price_extension_euler hZ hf hmin
  have ha := tfExtension_admissible hf
  refine ⟨∫ x, ρ₀ x, ρ, tfAdmissible_congr ha he, ?_, tfEulerDensity_nonneg Z ρ₀,
    ?_, ?_, fun x hx => tfEulerDensity_continuousAt ha hx, ?_⟩
  · intro M' σ hσ
    obtain ⟨g, hg, heg⟩ := tfAdmissible_truncate hσ Z
    have hh := hmin g hg
    rw [← tfExtension_functional hf Z 1, ← tfExtension_functional hg Z 1, one_mul, one_mul,
      tfFunctional_congr_ae Z heg, integral_congr_ae heg] at hh
    rw [← tfFunctional_congr_ae Z he]
    exact hh.trans (by simpa only [hσ.2.2.1] using tfPriced_truncate_le hZ hσ)
  · intro x
    exact congrArg (fun t => (max (t - 1) 0 / ((5 / 3 : ℝ) * tfKinetic)) ^ (3 / 2 : ℝ))
      (tfField_congr Z he x)
  · intro x y hxy
    exact congrArg (fun t => (max (t - 1) 0 / ((5 / 3 : ℝ) * tfKinetic)) ^ (3 / 2 : ℝ))
      (tfField_extension_radial hf hmin x y hxy)
  · exact fun x hx => tfEulerDensity_support hZ (tfExtension_nonneg hf) hx

end CoulombAnalysis

open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfReactionCoefficient
attribute [-instance] _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
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
section
open CoulombAtom CoulombPDE

def tfReactionCoefficient : ℝ := 4 * Real.pi * (((5 / 3 : ℝ) * tfKinetic) ^ (3 / 2 : ℝ))⁻¹

lemma tfReactionCoefficient_pos : 0 < tfReactionCoefficient := by
  unfold tfReactionCoefficient
  have ht := tfKinetic_pos
  positivity

lemma tfField_finiteProfile {M Z : ℝ} (hZ : 0 < Z) {ρ : TFSpace → ℝ}
    (ha : TFAdmissible M ρ) (hr : IsRadial ρ)
    (hc : ∀ x, x ≠ 0 → ContinuousAt ρ x)
    (hs : ∀ x, Z ≤ ‖x‖ → ρ x = 0)
    (he : ∀ x, ρ x = tfEulerDensity Z ρ x) :
    FiniteProfile tfReactionCoefficient Z (tfField Z ρ) := by
  have hs' : ∀ y, ρ y ≠ 0 → ‖y‖ ≤ Z := fun y hy => le_of_lt (lt_of_not_ge (fun hh => hy (hs y hh)))
  have hp := tfAdmissible_memLp ha
  have hreg (x : TFSpace) (hx : x ≠ 0) := tfPotential_poisson ha.2.1 hp hr hc hZ.le hs' hx
  have hn (x : TFSpace) (hx : x ≠ 0) : ContDiffAt ℝ 2 (fun y : TFSpace => Z / ‖y‖) x := by
    exact contDiffAt_const.div (contDiffAt_norm ℝ hx) (norm_ne_zero_iff.mpr hx)
  refine ⟨fun x hx => (hn x hx).sub (hreg x hx).1, ?_, ?_, ?_⟩
  · intro x hx
    change Δ ((fun y : TFSpace => Z / ‖y‖) - tfPotential ρ) x =
      reaction tfReactionCoefficient (tfField Z ρ x)
    rw [(hn x hx).laplacian_sub (hreg x hx).1, (hreg x hx).2]
    have heq : (fun y : TFSpace => Z / ‖y‖) = Z • radialPower (-(1/2)) := by
      funext y
      change Z / ‖y‖ = Z * radialPower (-(1/2 : ℝ)) y
      rw [radialPower_half_inv, div_eq_mul_inv]
    rw [heq, laplacian_smul Z (radialPower_contDiffAt _ hx), radial_laplacian_three _ hx]
    norm_num only
    rw [he x]
    unfold reaction tfReactionCoefficient tfEulerDensity
    rw [Real.div_rpow (le_max_right _ _) (mul_pos (by norm_num) tfKinetic_pos).le]
    ring
  · intro ε hε
    obtain ⟨R, hR, hu⟩ := tfPotential_compact_decay ha.2.1 hp hs' (ε/4) (by positivity)
    refine ⟨max R (4*Z/ε), hR.trans_le (le_max_left _ _), ?_⟩
    intro x hx
    have hxn := hR.trans_le ((le_max_left _ _).trans hx)
    have hz : Z / ‖x‖ ≤ ε/4 := by
      have hh := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hx)
      apply (div_le_iff₀ hxn).mpr
      linarith
    have hab := abs_sub (Z/‖x‖) (tfPotential ρ x)
    rw [abs_of_nonneg (div_nonneg hZ.le (norm_nonneg _))] at hab
    unfold tfField
    linarith [hu x ((le_max_left _ _).trans hx)]
  · have hab := ((tfPotential_continuous ha.2.1 hp).abs).continuousAt.eventually
      (eventually_lt_nhds (show |tfPotential ρ 0| < |tfPotential ρ 0| + 1 by linarith))
    obtain ⟨a, ha', hbound⟩ := Metric.eventually_nhds_iff.mp hab
    refine ⟨|tfPotential ρ 0|+1, by positivity, a/2, by positivity, ?_⟩
    intro x _hx hxa
    have hh' := hbound (show dist x 0 < a by simpa only [dist_zero_right] using (show ‖x‖ < a by linarith))
    simpa only [tfField, sub_sub_cancel_left, abs_neg] using hh'.le

end

open MeasureTheory Filter Set Metric Topology
section
open CoulombAtom

structure TFUnitData (Z : ℝ) where
  mass : ℝ
  density : TFSpace → ℝ
  admissible : TFAdmissible mass density
  minimal : ∀ M σ, TFAdmissible M σ → tfFunctional Z density + mass ≤ tfFunctional Z σ + M
  nonneg : ∀ x, 0 ≤ density x
  euler : ∀ x, density x = tfEulerDensity Z density x
  radial : IsRadial density
  continuous : ∀ x, x ≠ 0 → ContinuousAt density x
  support : ∀ x, Z ≤ ‖x‖ → density x = 0

lemma tfUnitData_nonempty (Z : ℝ) (hZ : 0 < Z) : Nonempty (TFUnitData Z) := by
  obtain ⟨M, ρ, ha, hm, hn, he, hr, hc, hs⟩ := tf_unit_price_exists_regular Z hZ
  exact ⟨⟨M, ρ, ha, hm, hn, he, hr, hc, hs⟩⟩

def tfUnitData (Z : ℝ) (hZ : 0 < Z) : TFUnitData Z := Classical.choice (tfUnitData_nonempty Z hZ)

namespace TFUnitData
variable {Z : ℝ} (D : TFUnitData Z)

def field : TFSpace → ℝ := tfField Z D.density
def radialField (r : ℝ) : ℝ := Z/r - radialPotential D.density r
def charge (r : ℝ) : ℝ := Z - radialMass D.density r

lemma finiteProfile (hZ : 0 < Z) : CoulombPDE.FiniteProfile tfReactionCoefficient Z D.field :=
  tfField_finiteProfile hZ D.admissible D.radial D.continuous D.support D.euler

lemma support_le (x : TFSpace) (hx : D.density x ≠ 0) : ‖x‖ ≤ Z :=
  le_of_lt (lt_of_not_ge (fun hh => hx (D.support x hh)))

lemma ray_norm {r : ℝ} (hr : 0 < r) : ‖r • radialAxis‖ = r := by simp [norm_smul, abs_of_pos hr]

lemma ray_ne_zero {r : ℝ} (hr : 0 < r) : r • radialAxis ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [ray_norm hr]; exact hr.ne')

lemma radialField_eq (hZ : 0 < Z) {x : TFSpace} (hx : x ≠ 0) :
    D.radialField ‖x‖ = D.field x := by
  unfold radialField field tfField
  rw [tfPotential_eq_radialPotential D.admissible.2.1 (tfAdmissible_memLp D.admissible)
    D.radial hZ.le D.support_le hx]

lemma radialField_ray (hZ : 0 < Z) {r : ℝ} (hr : 0 < r) :
    D.radialField r = D.field (r • radialAxis) := by
  simpa only [ray_norm hr] using D.radialField_eq hZ (ray_ne_zero hr)

lemma radialField_nonneg (hZ : 0 < Z) {r : ℝ} (hr : 0 < r) : 0 ≤ D.radialField r := by
  rw [D.radialField_ray hZ hr]
  exact (D.finiteProfile hZ).nonneg hZ _ (ray_ne_zero hr)

lemma mass_le_charge (hZ : 0 < Z) : D.mass ≤ Z := by
  have he := tfPotential_newton_exterior_closed D.admissible.2.1 (tfAdmissible_memLp D.admissible)
    D.radial hZ D.support_le (x := Z • radialAxis) (by rw [ray_norm hZ])
  have hn := (D.finiteProfile hZ).nonneg hZ (Z • radialAxis) (ray_ne_zero hZ)
  rw [field, tfField, he, D.admissible.2.2.1, ray_norm hZ, ← sub_div] at hn
  have hh := mul_nonneg hn hZ.le
  rw [div_mul_cancel₀ _ hZ.ne'] at hh
  exact sub_nonneg.mp hh

lemma charge_nonneg (hZ : 0 < Z) (r : ℝ) : 0 ≤ D.charge r := by
  have hi := setIntegral_le_integral (s := {x : TFSpace | ‖x‖ ≤ r}) D.admissible.2.1
    (Eventually.of_forall D.nonneg)
  rw [D.admissible.2.2.1, ← radialMass_eq_integral D.radial] at hi
  unfold charge
  linarith [D.mass_le_charge hZ]

lemma charge_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt D.charge (-(4 * Real.pi * r^2 * radialTrace D.density r)) r := by
  exact (radialMass_hasDerivAt D.admissible.2.1 D.radial D.continuous hr).const_sub Z

lemma radialField_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt D.radialField (-(D.charge r)/r^2) r := by
  have hh := ((hasDerivAt_const r Z).div (hasDerivAt_id r) hr.ne').sub
    (radialPotential_hasDerivAt D.admissible.2.1 (tfAdmissible_memLp D.admissible)
      D.radial D.continuous hr)
  apply hh.congr_deriv
  simp only [id_eq, zero_mul, zero_sub, mul_one]
  unfold charge
  ring

lemma charge_antitone : AntitoneOn D.charge (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (fun r hr => (D.charge_hasDerivAt hr).continuousAt.continuousWithinAt)
    (fun r hr => (D.charge_hasDerivAt (interior_subset hr)).hasDerivWithinAt)
  intro r _hr
  exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (sq_nonneg _)) (D.nonneg _))

lemma charge_bound (hZ : 0 < Z) {r : ℝ} (hr : 0 < r) :
    D.charge r ≤ 2*r*D.radialField (r/2) := by
  obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope D.radialField
    (fun t => -(D.charge t)/t^2) (show r/2 < r by linarith)
    (fun t ht => (D.radialField_hasDerivAt (show 0 < t by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => D.radialField_hasDerivAt (show 0 < t by linarith [ht.1]))
  have hcp : 0 < c := by linarith [hc.1]
  have hq := D.charge_antitone hcp hr hc.2.le
  have hq0 := D.charge_nonneg hZ r
  have hq1 := D.charge_nonneg hZ c
  have hratio : D.charge r/r^2 ≤ D.charge c/c^2 :=
    (div_le_div_of_nonneg_right hq (sq_nonneg r)).trans
      (div_le_div_of_nonneg_left hq1 (sq_pos_of_pos hcp) (by nlinarith [hc.2]))
  have hs : (D.radialField (r/2) - D.radialField r)/(r-r/2) = D.charge c/c^2 := by
    calc
      _ = -((D.radialField r - D.radialField (r/2))/(r-r/2)) := by ring
      _ = -(-(D.charge c)/c^2) := congrArg Neg.neg he.symm
      _ = _ := by ring
  rw [← hs] at hratio
  have hh := (div_le_div_iff₀ (sq_pos_of_pos hr) (show 0 < r-r/2 by linarith)).mp hratio
  have hf := D.radialField_nonneg hZ hr
  nlinarith [mul_nonneg hf (sq_nonneg r)]

lemma radialField_upper (hZ : 0 < Z) {r : ℝ} (hr : 0 < r) :
    D.radialField r ≤ 1 + CoulombPDE.sommerfeldCoefficient tfReactionCoefficient / r^4 := by
  have hh := (D.finiteProfile hZ).upper tfReactionCoefficient_pos (r • radialAxis) (ray_ne_zero hr)
  rw [← D.radialField_ray hZ hr] at hh
  have he := CoulombPDE.norm_four_mul_radialPower (ray_ne_zero hr)
  rw [ray_norm hr] at he
  have he' : CoulombPDE.radialPower (-2) (r • radialAxis) = 1/r^4 := by
    apply (eq_div_iff (pow_ne_zero _ hr.ne')).mpr
    nlinarith
  rwa [he', ← div_eq_mul_one_div] at hh

lemma radialField_le_charge_div {r : ℝ} : D.radialField r ≤ D.charge r / r := by
  have ht : 0 ≤ radialTail D.density r := by
    unfold radialTail
    apply mul_nonneg (by positivity)
    apply setIntegral_nonneg measurableSet_Ioi
    intro s _hs
    unfold radialTailIntegrand
    by_cases hp : 0 < s
    · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hp)]
      exact mul_nonneg hp.le (D.nonneg _)
    · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hp)]
  unfold radialField charge radialPotential
  rw [sub_div]
  linarith

def chargeCap (a : ℝ) : ℝ := 2*a*(1 + CoulombPDE.sommerfeldCoefficient tfReactionCoefficient / (a/2)^4)
def slopeCap (a : ℝ) : ℝ := chargeCap a / a^2

lemma chargeCap_pos {a : ℝ} (ha : 0 < a) : 0 < chargeCap a := by
  unfold chargeCap
  have hh := CoulombPDE.sommerfeldCoefficient_pos tfReactionCoefficient_pos
  positivity

lemma slopeCap_pos {a : ℝ} (ha : 0 < a) : 0 < slopeCap a :=
  div_pos (chargeCap_pos ha) (sq_pos_of_pos ha)

lemma charge_le_cap (hZ : 0 < Z) {a r : ℝ} (ha : 0 < a) (hr : a ≤ r) :
    D.charge r ≤ chargeCap a := by
  apply (D.charge_antitone ha (ha.trans_le hr) hr).trans
  exact (D.charge_bound hZ ha).trans (mul_le_mul_of_nonneg_left
    (D.radialField_upper hZ (show 0 < a/2 by positivity)) (by positivity))

lemma radialField_far_bound (hZ : 0 < Z) {a r : ℝ} (ha : 0 < a) (hr : a ≤ r) :
    D.radialField r ≤ chargeCap a / r :=
  D.radialField_le_charge_div.trans (div_le_div_of_nonneg_right
    (D.charge_le_cap hZ ha hr) (ha.trans_le hr).le)

end TFUnitData
end

open MeasureTheory Filter Set Metric Topology

end CoulombAnalysis

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

def tfIncreasingData (n : ℕ) : TFUnitData (n+1) := tfUnitData (n+1) (by positivity)
def tfIncreasingField (n : ℕ) : ℝ → ℝ := (tfIncreasingData n).radialField
def tfIncreasingCharge (n : ℕ) : ℝ → ℝ := (tfIncreasingData n).charge
def tfInfiniteRadial (r : ℝ) : ℝ := ⨆ n, tfIncreasingField n r

structure TFChargeAnchor where
  charge : ℝ
  index : ℕ → ℕ
  strict : StrictMono index
  limit : Tendsto (fun n => tfIncreasingCharge (index n) 1) atTop (𝓝 charge)

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian

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

def tfSupportRadius : ℝ := TFUnitData.chargeCap 1 + 2

lemma tfSupportRadius_gt_one : 1 < tfSupportRadius := by
  have := TFUnitData.chargeCap_pos (show (0:ℝ) < 1 by norm_num)
  unfold tfSupportRadius
  linarith

lemma TFUnitData.uniform_support {Z : ℝ} (D : TFUnitData Z) (hZ : 0 < Z)
    (x : TFSpace) (hx : tfSupportRadius ≤ ‖x‖) : D.density x = 0 := by
  have hn : 0 < ‖x‖ := (zero_lt_one.trans tfSupportRadius_gt_one).trans_le hx
  have hh := D.radialField_far_bound hZ (show (0:ℝ) < 1 by norm_num)
    ((tfSupportRadius_gt_one.le).trans hx)
  rw [D.radialField_eq hZ (norm_pos_iff.mp hn)] at hh
  have hu : D.field x ≤ 1 := hh.trans ((div_le_one hn).mpr (by
    have hp := TFUnitData.chargeCap_pos (show (0:ℝ) < 1 by norm_num)
    unfold tfSupportRadius at hx
    linarith))
  rw [D.euler, tfEulerDensity, show tfField Z D.density x = D.field x from rfl,
    max_eq_right (by linarith : D.field x - 1 ≤ 0), zero_div]
  exact Real.zero_rpow (by norm_num)

def tfResidualCharge : ℝ := tfSupportRadius * tfInfiniteRadial tfSupportRadius

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

structure TFPriceData (Z μ : ℝ) where
  mass : ℝ
  density : TFSpace → ℝ
  admissible : TFAdmissible mass density
  minimal : ∀ M σ, TFAdmissible M σ → tfFunctional Z density + μ*mass ≤ tfFunctional Z σ + μ*M
  nonneg : ∀ x, 0 ≤ density x
  compact : ∃ R > 0, ∀ x, R ≤ ‖x‖ → density x = 0

def TFUnitData.scale {W b : ℝ} (D : TFUnitData W) (hW : 0 < W) (hb : 0 < b) :
    TFPriceData (b^3*W) (b^4) := by
  refine ⟨b^3*D.mass, tfDilation b D.density, tfDilation_admissible hb D.admissible,
    ?_, fun x => mul_nonneg (pow_nonneg hb.le _) (D.nonneg _), ?_⟩
  · intro M σ hσ
    have ha := tfDilation_admissible (inv_pos.mpr hb) hσ
    have hh := mul_le_mul_of_nonneg_left (D.minimal _ _ ha) (pow_nonneg hb.le 7)
    rw [tfDilation_functional hb W D.density D.admissible.1]
    have he : b⁻¹^3*(b^3*W) = W := by field_simp
    have hf := tfDilation_functional (inv_pos.mpr hb) (b^3*W) σ hσ.1
    rw [he] at hf
    rw [hf] at hh
    nlinarith [show b^7*(b⁻¹^7 * tfFunctional (b^3*W) σ) = tfFunctional (b^3*W) σ by field_simp,
      show b^7*(b⁻¹^3 * M) = b^4*M by field_simp]
  · refine ⟨tfSupportRadius/b, div_pos (zero_lt_one.trans tfSupportRadius_gt_one) hb, fun x hx => ?_⟩
    have hn : tfSupportRadius ≤ ‖b • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hb.le]
      nlinarith [(div_le_iff₀ hb).mp hx]
    rw [tfDilation, D.uniform_support hW _ hn, mul_zero]

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_ActualTFCoefficient
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
namespace CoulombAnalysis
open CoulombAtom

def actualTFCoefficient : ℝ := (3/7:ℝ)*tfResidualCharge^(-4/3:ℝ)

end CoulombAnalysis

open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators

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

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff NNReal Topology

lemma compact_continuous_bound {g : TFSpace → ℝ} (hg : Continuous g)
    (hcg : HasCompactSupport g) : ∃ B : ℝ, ∀ x, ‖g x‖ ≤ B := by
  obtain ⟨B,hB⟩ := hcg.isCompact.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max B 0,fun x => ?_⟩
  by_cases hx : x ∈ tsupport g
  · exact (hB x hx).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
    exact le_max_right _ _

end CoulombAnalysis

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

def boundedPatchRepresentative (R B : ℝ) (f : TFLp (ballMeasure R)) : TFSpace → ℝ :=
  (ball 0 R).indicator (fun x => min (max (f x) 0) (max B 0))

lemma boundedPatchRepresentative_measurable (R B : ℝ) (f : TFLp (ballMeasure R)) :
    Measurable (boundedPatchRepresentative R B f) :=
  ((Lp.stronglyMeasurable f).measurable.max measurable_const).min measurable_const
    |>.indicator measurableSet_ball

lemma boundedPatchRepresentative_nonneg (R B : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) :
    0 ≤ boundedPatchRepresentative R B f x :=
  indicator_nonneg (fun _ _ => le_min (le_max_right _ _) (le_max_right _ _)) x

lemma boundedPatchRepresentative_le (R B : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) :
    boundedPatchRepresentative R B f x ≤ max B 0 := by
  by_cases hx : x ∈ ball (0 : TFSpace) R
  · simp only [boundedPatchRepresentative,indicator_of_mem hx]
    exact min_le_right _ _
  · simp only [boundedPatchRepresentative,indicator_of_notMem hx]
    exact le_max_right _ _

lemma boundedPatchRepresentative_support (R B : ℝ) (f : TFLp (ballMeasure R)) :
    Function.support (boundedPatchRepresentative R B f) ⊆ closedBall 0 R :=
  support_indicator_subset.trans ball_subset_closedBall

lemma boundedPatchRepresentative_ae {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    boundedPatchRepresentative R B f =ᵐ[volume] tfExtension R f := by
  have hh := (ae_restrict_iff' measurableSet_ball).mp (hf.and hb)
  filter_upwards [hh] with x hx
  by_cases hmem : x ∈ ball (0 : TFSpace) R
  · dsimp [boundedPatchRepresentative,tfExtension]
    rw [indicator_of_mem hmem,indicator_of_mem hmem,max_eq_left (hx hmem).1,
      min_eq_left ((hx hmem).2.trans (le_max_left _ _))]
  · simp only [boundedPatchRepresentative,tfExtension,indicator_of_notMem hmem]

lemma boundedPatchRepresentative_mass {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    (∫ x, boundedPatchRepresentative R B f x) = ∫ x, f x ∂ballMeasure R := by
  rw [integral_congr_ae (boundedPatchRepresentative_ae hf hb)]
  exact integral_indicator measurableSet_ball

lemma boundedPatchRepresentative_kinetic {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    (∫ x, (boundedPatchRepresentative R B f x)^(5/3:ℝ)) = ‖f‖^(5/3:ℝ) := by
  rw [tfLp_norm_rpow_nonneg hf]
  have he := boundedPatchRepresentative_ae hf hb
  have he' : (fun x => (boundedPatchRepresentative R B f x)^(5/3:ℝ)) =ᵐ[volume]
      fun x => (tfExtension R f x)^(5/3:ℝ) := he.mono fun _ hx => congrArg (fun t : ℝ => t^(5/3:ℝ)) hx
  rw [integral_congr_ae he']
  simp_rw [tfExtension_kinetic]
  exact integral_indicator measurableSet_ball

lemma boundedPatchRepresentative_coulomb {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    (∫ p : TFSpace × TFSpace, boundedPatchRepresentative R B f p.1 *
      boundedPatchRepresentative R B f p.2 / ‖p.1-p.2‖) = tfCoulombL R f f := by
  rw [tfCoulombL_extension]
  have he := boundedPatchRepresentative_ae hf hb
  apply integral_congr_ae
  rw [Measure.volume_eq_prod]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae he,
    Measure.quasiMeasurePreserving_snd.ae he] with p h1 h2
  rw [h1,h2]

lemma boundedPatchRepresentative_field {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) (Φ : TFSpace → ℝ) :
    (∫ x, Φ x*boundedPatchRepresentative R B f x) = ∫ x, Φ x*f x ∂ballMeasure R := by
  have he : (fun x => Φ x*tfExtension R f x) =
      (ball 0 R).indicator (fun x => Φ x*f x) := by
    funext x
    by_cases hx : x ∈ ball (0 : TFSpace) R <;> simp [tfExtension,hx]
  calc
    _ = ∫ x, Φ x*tfExtension R f x := integral_congr_ae
      ((boundedPatchRepresentative_ae hf hb).mono fun x hx => by rw [hx])
    _ = _ := by rw [he]; exact integral_indicator measurableSet_ball

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

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

lemma ballMeasure_ae_ne (R : ℝ) :
    ∀ᵐ p ∂(ballMeasure R).prod (ballMeasure R), p.1 ≠ p.2 := by
  let : NullSingletonClass (ballMeasure R) := by
    dsimp [ballMeasure]
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  apply Eventually.of_forall
  intro x
  have h := (ballMeasure R).ae_ne x
  exact h.mono fun y hy => Ne.symm hy

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_CompactDirichletBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff NNReal

namespace CoulombAnalysis

lemma tfPartial_lipschitz_bound {g : TFSpace → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (i : Fin 3) (x : TFSpace) :
    |tfPartial g i x| ≤ (L:ℝ) := by
  have hh := (fderiv ℝ g x).le_opNorm (EuclideanSpace.single i 1)
  simp only [PiLp.norm_single,norm_one,mul_one] at hh
  exact hh.trans (norm_fderiv_le_of_lipschitz ℝ hg)

lemma tfPartial_support {g : TFSpace → ℝ} (i : Fin 3) :
    Function.support (tfPartial g i) ⊆ tsupport g :=
  subset_tsupport _ |>.trans (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1))

lemma compact_partial_energy_bound {g : TFSpace → ℝ} {L : ℝ≥0} {r : ℝ}
    (hg : ContDiff ℝ 1 g) (hcg : HasCompactSupport g) (hl : LipschitzWith L g)
    (hs : tsupport g ⊆ closedBall 0 r) (i : Fin 3) :
    (∫ x, (tfPartial g i x)^2) ≤ volume.real (closedBall (0 : TFSpace) r)*(L:ℝ)^2 := by
  have hi : Integrable (fun x => (tfPartial g i x)^2) :=
    ((tfPartial_continuous hg i).pow 2).integrable_of_hasCompactSupport
      (by simpa only [pow_two] using (tfPartial_compact hcg i).mul_right (f' := tfPartial g i))
  have hzero : ∀ x, x ∉ closedBall (0 : TFSpace) r → (tfPartial g i x)^2 = 0 := by
    intro x hx
    have hz : tfPartial g i x = 0 := Function.notMem_support.mp (fun hh => hx (hs (tfPartial_support i hh)))
    simp [hz]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    _ ≤ ∫ _x in closedBall (0 : TFSpace) r, (L:ℝ)^2 :=
      integral_mono hi.integrableOn (integrableOn_const (measure_closedBall_lt_top.ne))
        (fun x => by
          have hh := tfPartial_lipschitz_bound hl i x
          nlinarith [sq_abs (tfPartial g i x),abs_nonneg (tfPartial g i x),L.coe_nonneg])
    _ = _ := by rw [setIntegral_const,smul_eq_mul]

lemma compact_dirichlet_bound {g : TFSpace → ℝ} {L : ℝ≥0} {r : ℝ}
    (hg : ContDiff ℝ 1 g) (hcg : HasCompactSupport g) (hl : LipschitzWith L g)
    (hs : tsupport g ⊆ closedBall 0 r) :
    (∑ i : Fin 3, ∫ x, (tfPartial g i x)^2) ≤
      3*volume.real (closedBall (0 : TFSpace) r)*(L:ℝ)^2 := by
  calc
    _ ≤ ∑ _i : Fin 3, volume.real (closedBall (0 : TFSpace) r)*(L:ℝ)^2 :=
      Finset.sum_le_sum (fun i _ => compact_partial_energy_bound hg hcg hl hs i)
    _ = _ := by simp; ring

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CorrectionPotentialSmallBarrier
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
open scoped Topology

open CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom

def annularApproximationError (l a S : ℝ) (x : TFSpace) : ℝ :=
  {x : TFSpace | a ≤ ‖x‖ ∧ ‖x‖ ≤ S}.indicator (fun x => l⁻¹^8/‖x‖^6) x

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

lemma capDenominator_pos {R : ℝ} {x : Space} (hx : ‖x‖ < R) :
    0 < R^2-‖x‖^2 := by nlinarith [norm_nonneg x]

lemma cap_scalar_deriv_four (C d s : ℝ) (hne : d-s ≠ 0) :
    HasDerivAt (fun t : ℝ => C/(d-t)^4) (4*C/(d-s)^5) s := by
  convert! ((hasDerivAt_const s C).div (((hasDerivAt_const s d).sub (hasDerivAt_id s)).pow 4)
    (pow_ne_zero 4 hne)) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  field_simp

lemma cap_scalar_deriv_five (C d s : ℝ) (hne : d-s ≠ 0) :
    HasDerivAt (fun t : ℝ => 4*C/(d-t)^5) (20*C/(d-s)^6) s := by
  convert! ((hasDerivAt_const s (4*C)).div (((hasDerivAt_const s d).sub (hasDerivAt_id s)).pow 5)
    (pow_ne_zero 5 hne)) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  field_simp
  ring

lemma cap_scalar_second (C d s : ℝ) (hne : d-s ≠ 0) :
    deriv (deriv (fun t : ℝ => C/(d-t)^4)) s = 20*C/(d-s)^6 := by
  have he : deriv (fun t : ℝ => C/(d-t)^4) =ᶠ[𝓝 s] fun t => 4*C/(d-t)^5 := by
    filter_upwards [(continuous_const.sub continuous_id).continuousAt.eventually_ne hne] with t ht
    exact (cap_scalar_deriv_four C d t ht).deriv
  rw [he.deriv_eq,(cap_scalar_deriv_five C d s hne).deriv]

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

lemma ballMeasure_integral_eq_of_support {f : Space → ℝ} {R : ℝ}
    (hs : Function.support f ⊆ ball 0 R) : (∫ x, f x ∂ballMeasure R) = ∫ x, f x := by
  rw [ballMeasure,←integral_indicator measurableSet_ball]
  congr 1
  exact indicator_eq_self.2 hs

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

lemma cap_reaction_scale {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R) :
    (A/R^4)^(3/2:ℝ) = A^(3/2:ℝ)/R^6 := by
  rw [Real.div_rpow hA (pow_nonneg hR.le _)]
  congr 1
  rw [←Real.rpow_natCast R 4,←Real.rpow_mul hR.le]
  norm_num

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_WeakSingularProfileBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WeakSingularProfile_barrier_scope

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology

open CoulombPDE

structure WeakSingularProfile (d : ℝ) (F : Space → ℝ) : Prop where
  continuous : ContinuousOn F {0}ᶜ
  equation : PuncturedPoisson F (fun x => reaction d (F x))
  decay : ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → |F x| < ε
  bounds : ∃ c > 0, ∃ C > 0, ∃ R > 0,
    (∀ x, x ≠ 0 → ‖x‖ ≤ R → c * radialPower (-2) x ≤ F x) ∧
    (∀ x, x ≠ 0 → ‖x‖ ≤ R → F x ≤ C * radialPower (-2) x)

end Work_WeakSingularProfile_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombPDE

end CoulombAnalysis

end

end OAI
end


