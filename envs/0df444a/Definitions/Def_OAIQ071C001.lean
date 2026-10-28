-- Prove2me | Definitions.Def_OAIQ071C001
-- name    : OAIQ071C001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T04:58:57.779733+00:00
-- url     : https://prove2.me/theorems/9f14be5f-81ff-463f-af9d-5cb1ca36ea88
-- title:
--   Definitions bundle OAIQ071C001 of the split of OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 542 declarations of OpenAI's Lean: 126 definitions, 1 inductive type or structure, 8 instances and 407 theorems. The definitions and types are `OAI.CoulombAnalysis.instMeasurableSpaceSubtypeAEEqFunRealMemAddSubgroupLpOfFactLeENNRealOfNat_solutions`, `OAI.CoulombAnalysis.tfCapBarrier`, `OAI.CoulombAnalysis.tfDensityCoefficient`, `OAI.CoulombAnalysis.tfPriceLength`, `OAI.CoulombAnalysis.toLpOrZero`, `OAI.CoulombAtom.CoherentIndex`, `OAI.CoulombAtom.CoherentPositiveIndex`, `OAI.CoulombAtom.CompactSpectralIndex`, `OAI.CoulombAtom.LipschitzMultiplier`, `OAI.CoulombAtom.NeumannSpinMode`, `OAI.CoulombAtom.OrbitalHilbert`, `OAI.CoulombAtom.PriceMinimizes`, `OAI.CoulombAtom.QuantumEventSymmetric`, `OAI.CoulombAtom.SmoothRealTest`, `OAI.CoulombAtom.blockSwap`, `OAI.CoulombAtom.coherentFactor`, `OAI.CoulombAtom.coherentOperator`, `OAI.CoulombAtom.coherentPacket`, `OAI.CoulombAtom.coherentVector`, `OAI.CoulombAtom.coherentWeight`, `OAI.CoulombAtom.compactEigenspaceIndex`, `OAI.CoulombAtom.configurationJoin`, `OAI.CoulombAtom.coreObservationAssoc`, `OAI.CoulombAtom.corePerm`, `OAI.CoulombAtom.cutCoreNumber`, `OAI.CoulombAtom.cutOrder`, `OAI.CoulombAtom.cutOutNumber`, `OAI.CoulombAtom.discretePhaseDensity`, `OAI.CoulombAtom.fermiRadius`, `OAI.CoulombAtom.hardyDenom`, `OAI.CoulombAtom.liftCoreOrder`, `OAI.CoulombAtom.localHistoryRadius`, `OAI.CoulombAtom.localHistoryReach`, `OAI.CoulombAtom.masterBaseDistance`, `OAI.CoulombAtom.masterExponent`, `OAI.CoulombAtom.masterWidth`, `OAI.CoulombAtom.momentumCell`, `OAI.CoulombAtom.momentumInterval`, `OAI.CoulombAtom.neumannRemainderConstant`, `OAI.CoulombAtom.pairPotential` and 87 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombIonization_Fermionic_CountableTests`, `CoulombIonization_Fermionic_Multiplier2`, `CoulombIonization_FieldAnalysis_CubeDensity`, `CoulombIonization_FieldAnalysis_CubeRotations`, `CoulombIonization_FieldAnalysis_CubeTiling`, `CoulombIonization_FieldAnalysis_CubeTranslationAverage`, `CoulombIonization_FieldAnalysis_FiniteMean`, `CoulombIonization_FieldAnalysis_HardyField`, `CoulombIonization_FieldAnalysis_NeumannCounts`, `CoulombIonization_FieldAnalysis_NeumannCube`, `CoulombIonization_FieldAnalysis_NeumannFermions`, `CoulombIonization_FieldAnalysis_NeumannGradient`, `CoulombIonization_FieldAnalysis_NeumannPhysical`, `CoulombIonization_FieldAnalysis_NeumannReindex`, `CoulombIonization_FieldAnalysis_NeumannSine`, `CoulombIonization_FieldAnalysis_PauliMomentum`, `CoulombIonization_FieldAnalysis_PhysicalGridMeasurable`, `CoulombIonization_FieldAnalysis_RetainedMeasurable`, `CoulombIonization_FieldAnalysis_RotationTrace`, `CoulombIonization_FieldAnalysis_ScaledSmearPressure`, `CoulombIonization_FieldAnalysis_Vartheta`, `CoulombIonization_FieldAnalysis_WeightedAverage`, `CoulombIonization_FormDomain_CoherentHilbert`, `CoulombIonization_FormDomain_CompactEigenbasis`, `CoulombIonization_FormDomain_LipschitzWeak`, `CoulombIonization_FormDomain_PhysicalGrid`, `CoulombIonization_FormDomain_TrialSmoothTest`, `CoulombIonization_FormDomain_WeakDerivative`, `CoulombIonization_Ionization_IntegratedStability`, `CoulombIonization_Ionization_TFPriceData`, `CoulombIonization_Localization_ArraySymmetry`, `CoulombIonization_Localization_CoherentPackets`, `CoulombIonization_Localization_CoreHistoryCoordinatesBarrier`, `CoulombIonization_Localization_ObservationLikelihood`, `CoulombIonization_Localization_ObservationScoreMoments`, `CoulombIonization_Localization_ObservationSmooth`, `CoulombIonization_Localization_QuantumRawLaw`, `CoulombIonization_Localization_ScoreDirectional`, `CoulombIonization_Localization_SqrtMultiplier`, `CoulombIonization_Localization_SubGaussianMoments`, `CoulombIonization_Localization_WeightedMoments`, `CoulombIonization_RadialBounds_BallAverageKernelBarrier`, `CoulombIonization_RadialBounds_CoreMultiplierLiftBarrier`, `CoulombIonization_RadialBounds_MomentumBall`, `CoulombIonization_RadialBounds_RadialCountSelection`, `CoulombIonization_ThomasFermi_CoherentPhaseBasis`, `CoulombIonization_ThomasFermi_FlatFermionAverage`, `CoulombIonization_ThomasFermi_FlatFermionGradient`, `CoulombIonization_ThomasFermi_PatchGapMeasurable`, `CoulombIonization_ThomasFermi_SelectedScreenedProfileBarrier`, `CoulombIonization_ThomasFermi_TFNonradialBarrier`, `CoulombIonization_ThomasFermi_TFNonradialCap`, `CoulombIonization_Variational_BlockSwap`, `CoulombIonization_Variational_CutCoreNumber`, `CoulombIonization_Variational_Electrostatic`, `CoulombIonization_Variational_MasterWidth`, `CoulombIonization_Variational_PatchMeasurable`, `CoulombIonization_Variational_PhaseBathtub`, `CoulombIonization_Variational_Pointwise`, `CoulombIonization_Variational_RetainedRepulsion`, `CoulombIonization_Variational_SliceLp`, `CoulombIonization_Variational_Slices`, `CoulombIonization_Variational_SmoothTransitionBound`, `CoulombIonization_Variational_SpinSpaceIntegrable`.
--
--   **Imports.** It imports the published bundle `Def_CoulombIonization`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ071C003`, `OAIQ071C004` and `OAIQ071C005`; the statement `OAI.CoulombAtom.actual_priced_particle_bound_three`.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombIonization

section
-- module Solutions.OAIQ071_CI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smooth_derivative_continuous {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (v : E) :
    Continuous (fun x => fderiv ℝ f x v) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

lemma compact_derivative {f : E → ℂ} (hf : HasCompactSupport f) (v : E) :
    HasCompactSupport (fun x => fderiv ℝ f x v) :=
  (hf.fderiv ℝ).comp_left (g := fun A : E →L[ℝ] ℂ => A v) (by rfl)

lemma smooth_complex_ofReal_derivative {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v : E) :
    fderiv ℝ (fun y => (φ y : ℂ)) x v = Complex.ofReal (lineDeriv ℝ φ x v) := by
  rw [(hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
  have h := Complex.ofRealCLM.hasFDerivAt.comp x ((hφ.differentiable (by simp) x).hasFDerivAt)
  exact congrArg (fun A : E →L[ℝ] ℂ => A v) h.fderiv

omit [NormedSpace ℝ E] in
lemma compact_norm_sq {f : E → ℂ} (hcf : HasCompactSupport f) :
    HasCompactSupport (fun x => ‖f x‖ ^ (2 : ℕ)) := by
  apply hcf.comp_left (g := fun z : ℂ => ‖z‖ ^ (2 : ℕ))
  simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

lemma smooth_weak_gradient {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (v : E) :
    (∫ x, f x * Complex.ofReal (lineDeriv ℝ φ x v)) =
      -(∫ x, fderiv ℝ f x v * (φ x : ℂ)) := by
  let g : E → ℂ := fun x => (φ x : ℂ)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hφ
  have hcg : HasCompactSupport g := hcφ.comp_left (g := Complex.ofReal) (by rfl)
  have hdf := smooth_derivative_continuous hf v
  have hdg := smooth_derivative_continuous hg v
  have hdfg : Integrable (fun x => fderiv ℝ f x v * g x) :=
    (hdf.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left
  have hfdg : Integrable (fun x => f x * fderiv ℝ g x v) :=
    (hf.continuous.mul hdg).integrable_of_hasCompactSupport hcf.mul_right
  have hfg : Integrable (fun x => f x * g x) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcf.mul_right
  simpa only [g, smooth_complex_ofReal_derivative hφ] using
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hdfg hfdg hfg
      (fun x _ => hf.differentiable (by simp) x) (fun x _ => hg.differentiable (by simp) x)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_CountableTests
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

abbrev SmoothRealTest (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {φ : E → ℝ // ContDiff ℝ ∞ φ ∧ HasCompactSupport φ}

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_LipschitzWeak
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

lemma mollified_lipschitz_derivative {k p : E → ℝ}
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    {C : NNReal} (hp : LipschitzWith C p) (v x : E) :
    fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] p) x v =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y => lineDeriv ℝ p y v)) x := by
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)
  have hφ : ContDiff ℝ ∞ (fun y => k (x - y)) := hk.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport (fun y => k (x - y)) :=
    hkc.comp_homeomorph (Homeomorph.subLeft x)
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcφ hφ (by simp)
  have hdφ (y : E) : lineDeriv ℝ (fun y => k (x - y)) y (-v) =
      fderiv ℝ k (x - y) v := by
    have hh := (hk.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    simpa [Function.comp_def] using (hh.hasLineDerivAt (-v)).lineDeriv
  have hw := hp.integral_lineDeriv_mul_eq hD hcφ v (μ := volume)
  simp only [hdφ] at hw
  have hid : Integrable (fun y => (L.precompL E) (fderiv ℝ k (x - y)) (p y)) :=
    ((hkc.fderiv ℝ).convolutionExists_left (L.precompL E)
      (hk.continuous_fderiv (by simp)) hp.continuous.locallyIntegrable x).integrable_swap
  rw [(hkc.hasFDerivAt_convolution_left L (hk.of_le (by simp))
      hp.continuous.locallyIntegrable x).fderiv,
    convolution_eq_swap, ContinuousLinearMap.integral_apply hid, convolution_eq_swap]
  simpa only [ContinuousLinearMap.precompL_apply, L, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, mul_comm] using hw.symm

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
lemma convolution_bounded {k p : E → ℝ} (hk : Integrable k)
    (hk0 : ∀ x, 0 ≤ k x) (hk1 : (∫ x, k x) = 1)
    {B : ℝ} (hb : ∀ x, ‖p x‖ ≤ B) (x : E) :
    ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] p) x‖ ≤ B := by
  change ‖∫ y, k y * p (x - y)‖ ≤ B
  calc
    _ ≤ ∫ y, k y * B := norm_integral_le_of_norm_le (hk.mul_const B)
      (Eventually.of_forall fun y => by
        rw [norm_mul, Real.norm_of_nonneg (hk0 y)]
        exact mul_le_mul_of_nonneg_left (hb _) (hk0 y))
    _ = B := by rw [integral_mul_const, hk1, one_mul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
lemma integral_real_mul_tendsto {q : ℕ → E → ℝ} {p : E → ℝ} {f : E → ℂ}
    (hq : ∀ n, AEStronglyMeasurable (q n)) {B : ℝ}
    (hb : ∀ n x, ‖q n x‖ ≤ B)
    (ht : ∀ᵐ x, Tendsto (fun n => q n x) atTop (𝓝 (p x)))
    (hf : Integrable f) :
    Tendsto (fun n => ∫ x, (q n x : ℂ) * f x) atTop
      (𝓝 (∫ x, (p x : ℂ) * f x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => B * ‖f x‖)
  · intro n
    exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable (hq n)).mul
      hf.aestronglyMeasurable)
  · exact hf.norm.const_mul B
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _)
  · filter_upwards [ht] with x hx
    exact (Complex.continuous_ofReal.tendsto _ |>.comp hx).mul tendsto_const_nhds

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
lemma smooth_lineDeriv_continuous {p : E → ℝ} (hp : ContDiff ℝ ∞ p) (v : E) :
    Continuous (fun x => lineDeriv ℝ p x v) := by
  have he : (fun x => lineDeriv ℝ p x v) = fun x => fderiv ℝ p x v := by
    funext x
    exact (hp.differentiable (by simp) x).lineDeriv_eq_fderiv
  rw [he]
  exact (hp.continuous_fderiv (by simp)).clm_apply continuous_const

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Multiplier2
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

structure LipschitzMultiplier (v : ι → E) where
  value : E → ℝ
  constant : NNReal
  lipschitz : LipschitzWith constant value
  bound : ∃ C : ℝ, ∀ x, |value x| ≤ C

end Multiplier

attribute [local irreducible] formEnergy

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CubeTiling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CubeTiling_scope

open MeasureTheory Set
open scoped BigOperators unitInterval

variable {d : Type*} [Fintype d]

def floorCube (z : d → ℤ) : Set (d → ℝ) := {x | ∀ i, ⌊x i⌋ = z i}
def closedCube (z : d → ℤ) : Set (d → ℝ) := Set.univ.pi (fun i => Icc (z i:ℝ) ((z i:ℝ)+1))
def cubeShift (z : d → ℤ) (x : d → I) : d → ℝ := fun i => (z i:ℝ)+(x i:ℝ)

omit [Fintype d] in
lemma floorCube_pi (z : d → ℤ) :
    floorCube z = Set.univ.pi (fun i => Ico (z i:ℝ) ((z i:ℝ)+1)) := by
  ext x
  simp only [floorCube,Set.mem_ofPred_eq,Set.mem_univ_pi,Set.mem_Ico,Int.floor_eq_iff]

lemma floorCube_measurable (z : d → ℤ) : MeasurableSet (floorCube z) := by
  rw [floorCube_pi]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

omit [Fintype d] in
lemma floorCube_disjoint : Pairwise (fun z w : d → ℤ => Disjoint (floorCube z) (floorCube w)) := by
  intro z w h
  rw [Set.disjoint_left]
  intro x hx hy
  apply h
  funext i
  exact (hx i).symm.trans (hy i)

omit [Fintype d] in
lemma floorCube_cover : ⋃ z : d → ℤ, floorCube z = Set.univ := by
  ext x
  simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
  exact ⟨fun i => ⌊x i⌋,fun _ => rfl⟩

lemma floorCube_restrict (z : d → ℤ) :
    volume.restrict (floorCube z) = volume.restrict (closedCube z) := by
  rw [floorCube_pi,closedCube,volume_pi,Measure.restrict_pi_pi,Measure.restrict_pi_pi]
  congr 1
  funext i
  exact Measure.restrict_congr_set Ico_ae_eq_Icc

lemma cubeShift_preserving (z : d → ℤ) :
    MeasurePreserving (cubeShift z) volume (volume.restrict (closedCube z)) := by
  have hs (i : d) : MeasurePreserving (fun x : I => (z i:ℝ)+(x:ℝ))
      volume (volume.restrict (Icc (z i:ℝ) ((z i:ℝ)+1))) := by
    have ha := (measurePreserving_add_left (volume : Measure ℝ) (z i:ℝ)).restrict_preimage
      (measurableSet_Icc : MeasurableSet (Icc (z i:ℝ) ((z i:ℝ)+1)))
    have he : (fun x : ℝ => (z i:ℝ)+x) ⁻¹' Icc (z i:ℝ) ((z i:ℝ)+1) = Icc (0:ℝ) 1 := by
      ext x
      simp only [Set.mem_preimage,Set.mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    rw [he] at ha
    exact ha.comp unitInterval.measurePreserving_coe
  have h := measurePreserving_pi (fun _ : d => (volume : Measure I))
    (fun i => volume.restrict (Icc (z i:ℝ) ((z i:ℝ)+1))) hs
  unfold cubeShift closedCube
  rw [volume_pi,volume_pi,Measure.restrict_pi_pi]
  exact h

lemma integral_cubeShift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : d → ℤ) (f : (d → ℝ) → E) (hf : AEStronglyMeasurable f (volume.restrict (closedCube z))) :
    (∫ x : d → I, f (cubeShift z x)) = ∫ x in floorCube z, f x := by
  rw [floorCube_restrict]
  have h := cubeShift_preserving z
  have hf' : AEStronglyMeasurable f (Measure.map (cubeShift z) volume) := by rwa [h.map_eq]
  simpa only [h.map_eq] using (integral_map h.measurable.aemeasurable hf').symm

end Work_CubeTiling_scope

open MeasureTheory Set Filter
open scoped BigOperators unitInterval Convolution

variable {d : Type*} [Fintype d]

def cubeChar (x : d → ℝ) : ℝ := (floorCube 0).indicator (fun _ => 1) x

def cubeOverlap (x : d → ℝ) : ℝ := ∫ t, cubeChar t*cubeChar (t-x)

lemma cubeChar_measurable : Measurable (cubeChar (d := d)) :=
  measurable_const.indicator (floorCube_measurable 0)

omit [Fintype d] in
lemma cubeChar_nonneg (x : d → ℝ) : 0 ≤ cubeChar x := by
  unfold cubeChar Set.indicator
  split_ifs <;> norm_num

omit [Fintype d] in
lemma cubeChar_le (x : d → ℝ) : cubeChar x ≤ 1 := by
  unfold cubeChar Set.indicator
  split_ifs <;> norm_num

lemma volume_floorCube (z : d → ℤ) : volume (floorCube z) = 1 := by
  rw [floorCube_pi,volume_pi,Measure.pi_pi]
  simp

lemma cubeChar_integrable : Integrable (cubeChar (d := d)) := by
  exact (integrableOn_const (C := (1:ℝ)) (by simp [volume_floorCube])).integrable_indicator (floorCube_measurable 0)

lemma integral_cubeChar : (∫ x : d → ℝ, cubeChar x) = 1 := by
  change (∫ x : d → ℝ, (floorCube 0).indicator (fun _ => (1:ℝ)) x) = 1
  rw [integral_indicator (floorCube_measurable 0),setIntegral_const]
  simp [measureReal_def,volume_floorCube]

lemma cubeOverlap_section_integrable (x : d → ℝ) :
    Integrable (fun t => cubeChar t*cubeChar (t-x)) := by
  rw [show (fun t => cubeChar t*cubeChar (t-x)) = fun t => cubeChar (t-x)*cubeChar t by funext; ring]
  apply cubeChar_integrable.bdd_mul (c := 1) (cubeChar_measurable.comp (measurable_id.sub measurable_const)).aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    change ‖cubeChar (t-x)‖ ≤ 1
    rw [Real.norm_of_nonneg (cubeChar_nonneg _)]; exact cubeChar_le _

lemma cubeOverlap_nonneg (x : d → ℝ) : 0 ≤ cubeOverlap x :=
  integral_nonneg (fun _ => mul_nonneg (cubeChar_nonneg _) (cubeChar_nonneg _))

lemma cubeOverlap_le (x : d → ℝ) : cubeOverlap x ≤ 1 := by
  rw [←integral_cubeChar (d := d)]
  exact integral_mono (cubeOverlap_section_integrable x) cubeChar_integrable
    (fun t => mul_le_of_le_one_right (cubeChar_nonneg _) (cubeChar_le _))

lemma cubeOverlap_measurable : Measurable (cubeOverlap (d := d)) := by
  have hm : Measurable (fun p : (d → ℝ) × (d → ℝ) => cubeChar p.1*cubeChar (p.1-p.2)) :=
    (cubeChar_measurable.comp measurable_fst).mul
      (cubeChar_measurable.comp (measurable_fst.sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

lemma cubeOverlap_convolution : cubeOverlap (d := d) =
    cubeChar ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] (fun x => cubeChar (-x)) := by
  funext x
  unfold cubeOverlap convolution
  congr 1
  funext t
  simp only [ContinuousLinearMap.mul_apply',neg_sub]

lemma cubeOverlap_integrable : Integrable (cubeOverlap (d := d)) := by
  rw [cubeOverlap_convolution]
  exact cubeChar_integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    cubeChar_integrable.comp_neg

lemma integral_cubeOverlap : (∫ x : d → ℝ, cubeOverlap x) = 1 := by
  rw [cubeOverlap_convolution,integral_convolution _ cubeChar_integrable cubeChar_integrable.comp_neg]
  simp only [integral_neg_eq_self,ContinuousLinearMap.mul_apply',integral_cubeChar,one_mul]

omit [Fintype d] in
lemma cubeChar_eq_zero_of_not_mem {x : d → ℝ} (h : x ∉ floorCube 0) : cubeChar x = 0 :=
  indicator_of_notMem h _

omit [Fintype d] in
lemma cubeChar_coord {x : d → ℝ} (h : x ∈ floorCube 0) (i : d) : 0 ≤ x i ∧ x i < 1 := by
  have hi := h i
  simpa only [Pi.zero_apply,Int.floor_eq_iff,Int.cast_zero,zero_add] using hi

lemma cubeOverlap_support_coord (x : d → ℝ) (i : d) (hx : 1 ≤ |x i|) : cubeOverlap x = 0 := by
  unfold cubeOverlap
  have he (t : d → ℝ) : cubeChar t*cubeChar (t-x) = 0 := by
    by_cases ht : t ∈ floorCube 0
    · by_cases hu : t-x ∈ floorCube 0
      · have h1 := cubeChar_coord ht i
        have h2 := cubeChar_coord hu i
        simp only [Pi.sub_apply] at h2
        rcases (le_abs.mp hx) with h | h <;> linarith
      · rw [cubeChar_eq_zero_of_not_mem hu,mul_zero]
    · rw [cubeChar_eq_zero_of_not_mem ht,zero_mul]
  simp only [he,integral_zero]

lemma lintegral_cube_periodization (f : (d → ℝ) → ENNReal) (hf : Measurable f) :
    (∫⁻ t : d → I, ∑' z : d → ℤ, f (cubeShift z t)) = ∫⁻ x, f x := by
  have hm (z : d → ℤ) : AEMeasurable (fun t : d → I => f (cubeShift z t)) :=
    (hf.comp (cubeShift_preserving z).measurable).aemeasurable
  rw [lintegral_tsum hm]
  have he (z : d → ℤ) : (∫⁻ t : d → I, f (cubeShift z t)) = ∫⁻ x in floorCube z, f x := by
    rw [floorCube_restrict]
    exact (cubeShift_preserving z).lintegral_comp hf
  simp only [he]
  rw [←lintegral_iUnion floorCube_measurable floorCube_disjoint, floorCube_cover,Measure.restrict_univ]

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CubeTranslationAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CubeTranslationAverage_scope

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

variable {d : Type*} [Fintype d]

def cubeIndex (x : d → ℝ) : d → ℤ := fun i => ⌊x i⌋

def sameCube (t x y : d → ℝ) : ℝ := if cubeIndex (x-t)=cubeIndex (y-t) then 1 else 0

lemma sameCube_nonneg (t x y : d → ℝ) : 0 ≤ sameCube t x y := by
  unfold sameCube
  split_ifs <;> norm_num

lemma sameCube_le (t x y : d → ℝ) : sameCube t x y ≤ 1 := by
  unfold sameCube
  split_ifs <;> norm_num

omit [Fintype d] in
lemma cubeIndex_measurable : Measurable (cubeIndex (d := d)) :=
  Measurable.of_eval (fun index => Int.measurable_floor.comp (measurable_pi_apply index))

lemma sameCube_measurable : Measurable (fun p : (d → ℝ) × ((d → ℝ) × (d → ℝ)) => sameCube p.1 p.2.1 p.2.2) := by
  unfold sameCube
  exact Measurable.ite (measurableSet_eq_fun
    (cubeIndex_measurable.comp ((measurable_fst.comp measurable_snd).sub measurable_fst))
    (cubeIndex_measurable.comp ((measurable_snd.comp measurable_snd).sub measurable_fst)))
    measurable_const measurable_const

lemma sameCube_t_measurable (x y : d → ℝ) : Measurable (fun t => sameCube t x y) :=
  sameCube_measurable.comp (measurable_id.prodMk (measurable_const.prodMk measurable_const))

lemma sameCube_I_integrable (x y : d → ℝ) :
    Integrable (fun t : d → I => sameCube (fun a => (t a:ℝ)) x y) := by
  apply (integrable_const (1:ℝ)).mono'
    ((sameCube_t_measurable x y).comp (Measurable.of_eval (fun index =>
      measurable_subtype_coe.comp (measurable_pi_apply index)))).aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    change ‖sameCube (fun a => (t a:ℝ)) x y‖ ≤ 1
    rw [Real.norm_of_nonneg (sameCube_nonneg _ _ _)]; exact sameCube_le _ _ _

lemma cubeChar_sub_cubeShift (x : d → ℝ) (t : d → I) (z : d → ℤ) :
    cubeChar (x-cubeShift z t) = if cubeIndex (x-fun a => (t a:ℝ)) = z then 1 else 0 := by
  have he : x-cubeShift z t ∈ floorCube 0 ↔ cubeIndex (x-fun a => (t a:ℝ))=z := by
    simp only [floorCube,mem_ofPred_eq,cubeShift,Pi.sub_apply,Pi.zero_apply,cubeIndex,
      sub_add_eq_sub_sub_swap,Int.floor_sub_intCast,sub_eq_zero,funext_iff]
  unfold cubeChar
  rw [Set.indicator]
  simp only [he]

lemma sameCube_periodization (t : d → I) (x y : d → ℝ) :
    ENNReal.ofReal (sameCube (fun a => (t a:ℝ)) x y) =
      ∑' z : d → ℤ, ENNReal.ofReal (cubeChar (x-cubeShift z t)*cubeChar (y-cubeShift z t)) := by
  classical
  rw [tsum_eq_single (cubeIndex (x-fun a => (t a:ℝ)))]
  · rw [cubeChar_sub_cubeShift,cubeChar_sub_cubeShift]
    simp only [ite_true,one_mul]
    unfold sameCube
    simp only [eq_comm]
  · intro z hz
    rw [cubeChar_sub_cubeShift,ite_eq_right (Ne.symm hz),zero_mul]
    simp

lemma cubeOverlap_alternative (x y : d → ℝ) :
    (∫ s, cubeChar (x-s)*cubeChar (y-s)) = cubeOverlap (x-y) := by
  have he (s : d → ℝ) : cubeChar (x-s)*cubeChar (y-s) =
      (fun t => cubeChar t*cubeChar (t-(x-y))) (x-s) := by
    congr 2
    abel
  simp only [he]
  exact integral_sub_left_eq_self (fun t => cubeChar t*cubeChar (t-(x-y))) volume x

lemma cubeOverlap_alternative_integrable (x y : d → ℝ) :
    Integrable (fun s => cubeChar (x-s)*cubeChar (y-s)) := by
  have hh := (cubeOverlap_section_integrable (x-y)).comp_sub_left x
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  congr 2
  abel

theorem integral_sameCube (x y : d → ℝ) :
    (∫ t : d → I, sameCube (fun a => (t a:ℝ)) x y) = cubeOverlap (x-y) := by
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (fun _ => sameCube_nonneg _ _ _)) (cubeOverlap_nonneg _)).mp
  rw [ofReal_integral_eq_lintegral_ofReal (sameCube_I_integrable x y)
    (Eventually.of_forall (fun _ => sameCube_nonneg _ _ _))]
  simp only [sameCube_periodization]
  have hm : Measurable (fun s : d → ℝ => ENNReal.ofReal (cubeChar (x-s)*cubeChar (y-s))) :=
    ((cubeChar_measurable.comp (measurable_const.sub measurable_id)).mul
      (cubeChar_measurable.comp (measurable_const.sub measurable_id))).ennreal_ofReal
  rw [lintegral_cube_periodization _ hm,
    ←ofReal_integral_eq_lintegral_ofReal (cubeOverlap_alternative_integrable x y)
      (Eventually.of_forall (fun _ => mul_nonneg (cubeChar_nonneg _) (cubeChar_nonneg _))),
    cubeOverlap_alternative]

end Work_CubeTranslationAverage_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate

lemma integral_interval_cos_int (k : ℤ) :
    (∫ x : I, Real.cos (Real.pi*(k:ℝ)*(x:ℝ))) = if k=0 then 1 else 0 := by
  rw [unitInterval.volume_def]
  change (∫ x : Set.Icc (0:ℝ) 1, (fun y : ℝ => Real.cos (Real.pi*(k:ℝ)*y)) x ∂Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap measurableSet_Icc (fun y : ℝ => Real.cos (Real.pi*(k:ℝ)*y)),
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  by_cases hk : k=0
  · simp [hk]
  · rw [ite_eq_right hk,intervalIntegral.integral_comp_mul_left _ (mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hk)),
      integral_cos]
    simp only [mul_zero,mul_one,Real.sin_zero,sub_zero,smul_eq_mul]
    rw [mul_comm Real.pi (k:ℝ),Real.sin_int_mul_pi,mul_zero]

def cosMode (k : ℕ) : C(I,ℝ) where
  toFun x := Real.cos (Real.pi*(k:ℝ)*(x:ℝ))
  continuous_toFun := by fun_prop

lemma cosMode_product_integral (m n : ℕ) :
    (∫ x : I, cosMode m x*cosMode n x) =
      if m=n then (if m=0 then 1 else 1/2) else 0 := by
  have he (x : I) : 2*(cosMode m x*cosMode n x) =
      Real.cos (Real.pi*((((m:ℤ)-(n:ℤ)):ℤ):ℝ)*(x:ℝ)) + Real.cos (Real.pi*((((m:ℤ)+(n:ℤ)):ℤ):ℝ)*(x:ℝ)) := by
    dsimp [cosMode]
    push_cast
    rw [show Real.pi*((m:ℝ)-n)*(x:ℝ) = Real.pi*m*(x:ℝ)-Real.pi*n*(x:ℝ) by ring,
      show Real.pi*((m:ℝ)+n)*(x:ℝ) = Real.pi*m*(x:ℝ)+Real.pi*n*(x:ℝ) by ring]
    nlinarith [Real.two_mul_cos_mul_cos (Real.pi*m*(x:ℝ)) (Real.pi*n*(x:ℝ))]
  have hcm (k : ℤ) : Integrable (fun x : I => Real.cos (Real.pi*(k:ℝ)*(x:ℝ))) :=
    (by fun_prop : Continuous (fun x : I => Real.cos (Real.pi*(k:ℝ)*(x:ℝ)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hh := congrArg (fun f : I → ℝ => ∫ x, f x) (funext he)
  rw [integral_const_mul,integral_add (hcm ((m:ℤ)-n)) (hcm ((m:ℤ)+n)),integral_interval_cos_int,
    integral_interval_cos_int] at hh
  by_cases hmn : m=n
  · subst n
    by_cases hm : m=0
    · simp only [hm,Nat.cast_zero,sub_self,add_zero,ite_true] at hh
      simp only [hm,ite_true]
      linarith
    · have hsum : (m:ℤ)+m ≠ 0 := by omega
      simp only [sub_self,ite_true,ite_eq_right hsum,add_zero] at hh
      simp only [ite_true,ite_eq_right hm]
      linarith
  · have hdiff : (m:ℤ)-n ≠ 0 := by omega
    have hsum : (m:ℤ)+n ≠ 0 := by omega
    simp only [ite_eq_right hdiff,ite_eq_right hsum,add_zero] at hh
    rw [ite_eq_right hmn]
    linarith

def cosNormalization (n : ℕ) : ℝ := if n=0 then 1 else Real.sqrt 2

def neumannMode (n : ℕ) : C(I,ℂ) where
  toFun x := (cosNormalization n*cosMode n x : ℝ)
  continuous_toFun := by unfold cosNormalization; fun_prop

lemma neumannMode_inner (m n : ℕ) :
    (∫ x : I, conj (neumannMode m x)*neumannMode n x) = if m=n then 1 else 0 := by
  simp only [neumannMode,ContinuousMap.coe_mk,Complex.conj_ofReal]
  simp_rw [← Complex.ofReal_mul]
  have he (x : I) : (cosNormalization m*cosMode m x)*(cosNormalization n*cosMode n x) =
      (cosNormalization m*cosNormalization n)*(cosMode m x*cosMode n x) := by ring
  simp_rw [he]
  rw [integral_complex_ofReal (f := fun x : I => (cosNormalization m*cosNormalization n)*(cosMode m x*cosMode n x)),integral_const_mul,cosMode_product_integral]
  by_cases hmn : m=n
  · subst n
    by_cases hm : m=0
    · simp [cosNormalization,hm]
    · simp only [ite_true,ite_eq_right hm,cosNormalization]
      rw [← sq,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
  · simp [hmn]

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_NeumannCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_NeumannCube_scope

open MeasureTheory Set Submodule
open scoped BigOperators unitInterval ComplexConjugate

lemma cosMode_natAbs (k : ℤ) (x : I) :
    cosMode k.natAbs x = Real.cos (Real.pi*(k:ℝ)*(x:ℝ)) := by
  have hk : (k.natAbs:ℝ) = |(k:ℝ)| := by
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  dsimp [cosMode]
  rw [hk]
  have he : Real.pi*|(k:ℝ)| * (x:ℝ) = |Real.pi*(k:ℝ)*(x:ℝ)| := by
    rw [abs_mul,abs_mul,abs_of_nonneg Real.pi_pos.le,abs_of_nonneg x.2.1]
  rw [he,Real.cos_abs]

lemma cosMode_mul (m n : ℕ) (x : I) :
    cosMode m x*cosMode n x = (1/2:ℝ)*
      (cosMode (m+n) x + cosMode ((m:ℤ)-n).natAbs x) := by
  rw [cosMode_natAbs]
  dsimp [cosMode]
  push_cast
  rw [show Real.pi*((m:ℝ)+n)*(x:ℝ) = Real.pi*m*(x:ℝ)+Real.pi*n*(x:ℝ) by ring,
    show Real.pi*((m:ℝ)-n)*(x:ℝ) = Real.pi*m*(x:ℝ)-Real.pi*n*(x:ℝ) by ring]
  nlinarith [Real.two_mul_cos_mul_cos (Real.pi*m*(x:ℝ)) (Real.pi*n*(x:ℝ))]

variable {d : Type*} [Fintype d]

def cubeCosMode (n : d → ℕ) : C(d → I,ℂ) where
  toFun x := ∏ i, (cosMode (n i) (x i) : ℂ)
  continuous_toFun := by fun_prop

@[simp] lemma cubeCosMode_zero : cubeCosMode (fun _ : d => 0) = 1 := by
  ext x
  simp [cubeCosMode,cosMode]

lemma cubeCosMode_mul [DecidableEq d] (m n : d → ℕ) :
    cubeCosMode m*cubeCosMode n = (1/2:ℂ)^Fintype.card d •
      ∑ s : d → Bool, cubeCosMode (fun i => if s i then m i+n i else ((m i:ℤ)-n i).natAbs) := by
  classical
  ext x
  simp only [ContinuousMap.mul_apply,cubeCosMode,ContinuousMap.coe_mk,
    ContinuousMap.smul_apply,ContinuousMap.sum_apply,smul_eq_mul]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← Complex.ofReal_mul,cosMode_mul,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_add]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  congr 1
  have he (i : d) : (cosMode (m i+n i) (x i):ℂ)+cosMode ((m i:ℤ)-n i).natAbs (x i) =
      ∑ s : Bool, (cosMode (if s then m i+n i else ((m i:ℤ)-n i).natAbs) (x i):ℂ) := by
    simp
  simp_rw [he]
  rw [Fintype.prod_sum]

def cosineSpan (d : Type*) [Fintype d] : Submodule ℂ C(d → I,ℂ) :=
  span ℂ (range (cubeCosMode (d := d)))

lemma cubeCosMode_mem (n : d → ℕ) : cubeCosMode n ∈ cosineSpan d :=
  subset_span ⟨n,rfl⟩

lemma cosineSpan_one : (1 : C(d → I,ℂ)) ∈ cosineSpan d := by
  rw [← cubeCosMode_zero]
  exact cubeCosMode_mem _

lemma cosineSpan_mul {f g : C(d → I,ℂ)} (hf : f ∈ cosineSpan d) (hg : g ∈ cosineSpan d) :
    f*g ∈ cosineSpan d := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨m,rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨n,rfl⟩ := hg
      rw [cubeCosMode_mul]
      exact (cosineSpan d).smul_mem _ ((cosineSpan d).sum_mem (fun s _ => cubeCosMode_mem _))
    | zero => simp only [mul_zero]; exact (cosineSpan d).zero_mem
    | add g h hg hh hge hhe => simpa only [mul_add] using (cosineSpan d).add_mem hge hhe
    | smul a g hg hge => simpa only [mul_smul_comm] using (cosineSpan d).smul_mem a hge
  | zero => simp only [zero_mul]; exact (cosineSpan d).zero_mem
  | add f h hf hh hfe hhe => simpa only [add_mul] using (cosineSpan d).add_mem hfe hhe
  | smul a f hf hfe => simpa only [smul_mul_assoc] using (cosineSpan d).smul_mem a hfe

lemma cubeCosMode_star (n : d → ℕ) : star (cubeCosMode n) = cubeCosMode n := by
  ext x
  simp [cubeCosMode]

lemma cosineSpan_star {f : C(d → I,ℂ)} (hf : f ∈ cosineSpan d) : star f ∈ cosineSpan d := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨n,rfl⟩ := hf
    rw [cubeCosMode_star]
    exact cubeCosMode_mem _
  | zero => simp only [star_zero]; exact (cosineSpan d).zero_mem
  | add f g hf hg hfe hge => simpa only [star_add] using (cosineSpan d).add_mem hfe hge
  | smul a f hf hfe => simpa only [star_smul] using (cosineSpan d).smul_mem (star a) hfe

def cosineAlgebra (d : Type*) [Fintype d] : StarSubalgebra ℂ C(d → I,ℂ) where
  carrier := cosineSpan d
  zero_mem' := (cosineSpan d).zero_mem
  add_mem' := (cosineSpan d).add_mem
  one_mem' := cosineSpan_one
  mul_mem' := cosineSpan_mul
  algebraMap_mem' a := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (cosineSpan d).smul_mem a cosineSpan_one
  star_mem' := cosineSpan_star

lemma cubeCosMode_single [DecidableEq d] (i : d) (x : d → I) :
    cubeCosMode (Pi.single i 1) x = (Real.cos (Real.pi*(x i:ℝ)) : ℂ) := by
  simp only [cubeCosMode,ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single i]
  · simp only [Pi.single_eq_same,cosMode,ContinuousMap.coe_mk,Nat.cast_one,mul_one]
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji,cosMode]
  · simp

lemma cosineAlgebra_separatesPoints : (cosineAlgebra d).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
  refine ⟨_,⟨cubeCosMode (Pi.single i 1),cubeCosMode_mem _,rfl⟩,?_⟩
  simp only [cubeCosMode_single,ne_eq,Complex.ofReal_inj]
  intro hh
  have hx : Real.pi*(x i:ℝ) ∈ Icc 0 Real.pi :=
    ⟨mul_nonneg Real.pi_pos.le (x i).2.1, (mul_le_mul_of_nonneg_left (x i).2.2 Real.pi_pos.le).trans_eq (mul_one _)⟩
  have hy : Real.pi*(y i:ℝ) ∈ Icc 0 Real.pi :=
    ⟨mul_nonneg Real.pi_pos.le (y i).2.1, (mul_le_mul_of_nonneg_left (y i).2.2 Real.pi_pos.le).trans_eq (mul_one _)⟩
  exact hi (Subtype.ext (mul_left_cancel₀ Real.pi_ne_zero (Real.injOn_cos hx hy hh)))

lemma cosineSpan_dense : (cosineSpan d).topologicalClosure = ⊤ := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (cosineAlgebra d) cosineAlgebra_separatesPoints
  exact congrArg (fun a : StarSubalgebra ℂ C(d → I,ℂ) => a.toSubalgebra.toSubmodule) h

end Work_NeumannCube_scope

open MeasureTheory Set Submodule
open scoped BigOperators unitInterval ComplexConjugate ENNReal

variable {d : Type*} [Fintype d]

def cubeNeumannMode (n : d → ℕ) : C(d → I,ℂ) where
  toFun x := ∏ i, neumannMode (n i) (x i)
  continuous_toFun := by fun_prop

lemma cosNormalization_pos (n : ℕ) : 0 < cosNormalization n := by
  unfold cosNormalization
  split_ifs <;> positivity

lemma cubeNeumannMode_eq (n : d → ℕ) :
    cubeNeumannMode n = (∏ i, (cosNormalization (n i):ℂ)) • cubeCosMode n := by
  ext x
  simp only [cubeNeumannMode,cubeCosMode,neumannMode,ContinuousMap.coe_mk,
    ContinuousMap.smul_apply,smul_eq_mul,Complex.ofReal_mul,Finset.prod_mul_distrib]

lemma cubeNeumannMode_span : span ℂ (range (cubeNeumannMode (d := d))) = cosineSpan d := by
  apply le_antisymm
  · refine span_le.mpr ?_
    rintro _ ⟨n,rfl⟩
    rw [cubeNeumannMode_eq]
    exact (cosineSpan d).smul_mem _ (cubeCosMode_mem _)
  · refine span_le.mpr ?_
    rintro _ ⟨n,rfl⟩
    have hnon : (∏ i, (cosNormalization (n i):ℂ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact_mod_cast (cosNormalization_pos (n i)).ne'
    have hi : cubeCosMode n = (∏ i, (cosNormalization (n i):ℂ))⁻¹ • cubeNeumannMode n := by
      rw [cubeNeumannMode_eq,smul_smul,inv_mul_cancel₀ hnon,one_smul]
    rw [hi]
    exact (span ℂ (range cubeNeumannMode)).smul_mem _ (subset_span ⟨n,rfl⟩)

lemma cubeNeumannMode_inner (m n : d → ℕ) :
    (∫ x : d → I, conj (cubeNeumannMode m x)*cubeNeumannMode n x) = if m=n then 1 else 0 := by
  classical
  simp only [cubeNeumannMode,ContinuousMap.coe_mk,map_prod,← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod (fun i (x : I) => conj (neumannMode (m i) x)*neumannMode (n i) x)]
  simp_rw [neumannMode_inner]
  by_cases h : m=n
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

abbrev neumannLp (n : d → ℕ) : Lp ℂ 2 (volume : Measure (d → I)) :=
  ContinuousMap.toLp 2 volume ℂ (cubeNeumannMode n)

lemma orthonormal_neumann : Orthonormal ℂ (neumannLp (d := d)) := by
  classical
  rw [orthonormal_iff_ite]
  intro m n
  rw [ContinuousMap.inner_toLp]
  simpa only [mul_comm] using cubeNeumannMode_inner m n

lemma neumannLp_span_dense : (span ℂ (range (neumannLp (d := d)))).topologicalClosure = ⊤ := by
  have hc : (span ℂ (range (cubeNeumannMode (d := d)))).topologicalClosure = ⊤ := by
    rw [cubeNeumannMode_span,cosineSpan_dense]
  simpa only [map_span,ContinuousLinearMap.coe_coe,← range_comp,Function.comp_def] using
    (ContinuousMap.toLp_denseRange ℂ (volume : Measure (d → I)) ℂ (by norm_num : (2:ENNReal) ≠ ⊤)).topologicalClosure_map_submodule hc

def neumannBasis : HilbertBasis (d → ℕ) ℂ (Lp ℂ 2 (volume : Measure (d → I))) :=
  HilbertBasis.mk orthonormal_neumann neumannLp_span_dense.ge

@[simp] lemma neumannBasis_apply (n : d → ℕ) : neumannBasis n = neumannLp n :=
  congrFun (HilbertBasis.coe_mk _ _) n

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_NeumannSine
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

lemma integral_unitInterval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : (∫ x : I, f (x:ℝ)) = ∫ x in (0:ℝ)..1, f x := by
  rw [unitInterval.volume_def]
  change (∫ x : Set.Icc (0:ℝ) 1, f (x:ℝ) ∂Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap measurableSet_Icc f,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

def sineMode (n : ℕ) : C(I,ℂ) where
  toFun x := (Real.sqrt 2*Real.sin (Real.pi*(n+1)*(x:ℝ)) : ℝ)
  continuous_toFun := by fun_prop

lemma sineMode_inner (m n : ℕ) :
    (∫ x : I, conj (sineMode m x)*sineMode n x) = if m=n then 1 else 0 := by
  have he (x : I) : conj (sineMode m x)*sineMode n x =
      ((Real.cos (Real.pi*((((m:ℤ)+1)-((n:ℤ)+1):ℤ):ℝ)*(x:ℝ)) -
      Real.cos (Real.pi*((((m:ℤ)+1)+((n:ℤ)+1):ℤ):ℝ)*(x:ℝ))) : ℝ) := by
    simp only [sineMode,ContinuousMap.coe_mk,Complex.conj_ofReal,← Complex.ofReal_mul]
    congr 1
    push_cast
    rw [show Real.pi*((m:ℝ)+1-((n:ℝ)+1))*(x:ℝ) =
        Real.pi*(m+1)*(x:ℝ)-Real.pi*(n+1)*(x:ℝ) by ring,
      show Real.pi*((m:ℝ)+1+((n:ℝ)+1))*(x:ℝ) =
        Real.pi*(m+1)*(x:ℝ)+Real.pi*(n+1)*(x:ℝ) by ring]
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    calc
      _ = (Real.sqrt 2)^2 * Real.sin (Real.pi*(m+1)*(x:ℝ)) *
          Real.sin (Real.pi*(n+1)*(x:ℝ)) := by ring
      _ = _ := by rw [hs,Real.two_mul_sin_mul_sin]
  simp_rw [he]
  rw [integral_complex_ofReal]
  have hcm (k : ℤ) : Integrable (fun x : I => Real.cos (Real.pi*(k:ℝ)*(x:ℝ))) :=
    (by fun_prop : Continuous (fun x : I => Real.cos (Real.pi*(k:ℝ)*(x:ℝ)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_sub (hcm (((m:ℤ)+1)-((n:ℤ)+1))) (hcm (((m:ℤ)+1)+((n:ℤ)+1))),
    integral_interval_cos_int,integral_interval_cos_int]
  have hsum : ((m:ℤ)+1)+((n:ℤ)+1) ≠ 0 := by omega
  have hdiff : ((m:ℤ)+1)-((n:ℤ)+1) = 0 ↔ m=n := by omega
  simp only [ite_eq_right hsum,sub_zero,hdiff]
  split_ifs <;> norm_num

lemma sine_derivative_pairing {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    (∫ x : I, (Real.sin (Real.pi*n*(x:ℝ)) : ℂ)*deriv f (x:ℝ)) =
      -(Real.pi*n:ℝ)*(∫ x : I, (Real.cos (Real.pi*n*(x:ℝ)) : ℂ)*f (x:ℝ)) := by
  have hu (x : ℝ) : HasDerivAt (fun t : ℝ => (Real.sin (Real.pi*n*t):ℂ))
      ((Real.pi*n*Real.cos (Real.pi*n*x):ℝ):ℂ) x := by
    simpa only [id_eq,mul_one,mul_comm] using (((hasDerivAt_id x).const_mul (Real.pi*n)).sin).ofReal_comp
  have hd : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x (_ : x ∈ uIcc (0:ℝ) 1) => hu x)
    (fun x (_ : x ∈ uIcc (0:ℝ) 1) => (hf.differentiable (by norm_num) x).hasDerivAt)
    ((by fun_prop : Continuous (fun x : ℝ => ((Real.pi*n*Real.cos (Real.pi*n*x):ℝ):ℂ))).intervalIntegrable 0 1)
    (hd.intervalIntegrable 0 1)
  have h0 : Real.sin (Real.pi*n*(0:ℝ)) = 0 := by simp
  have h1 : Real.sin (Real.pi*n*(1:ℝ)) = 0 := by simpa [mul_comm] using Real.sin_nat_mul_pi n
  simp only [h0,h1,Complex.ofReal_zero,zero_mul,sub_zero,zero_sub] at hi
  simp only [Complex.ofReal_mul,mul_assoc,intervalIntegral.integral_const_mul] at hi
  rw [integral_unitInterval (fun x => (Real.sin (Real.pi*n*x):ℂ)*deriv f x),
    integral_unitInterval (fun x => (Real.cos (Real.pi*n*x):ℂ)*f x)]
  simpa only [Complex.ofReal_mul,Complex.ofReal_natCast,neg_mul,mul_assoc] using hi

lemma normalized_sine_derivative_pairing {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ x : I, conj (sineMode (n-1) x)*deriv f (x:ℝ)) =
      -(Real.pi*n:ℝ)*(∫ x : I, conj (neumannMode n x)*f (x:ℝ)) := by
  have hnat : n-1+1=n := by omega
  simp only [sineMode,neumannMode,cosNormalization,ite_eq_right hn,cosMode,
    ContinuousMap.coe_mk,Complex.ofReal_mul,map_mul,Complex.conj_ofReal]
  have hreal : ((n-1:ℕ):ℝ)+1=n := by exact_mod_cast hnat
  simp only [hreal,mul_assoc,integral_const_mul]
  have hp := sine_derivative_pairing hf n
  simp only [mul_assoc] at hp
  rw [hp]
  push_cast
  ring

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

lemma integral_cube_split {d : ℕ} (i : Fin (d+1)) (f : (Fin (d+1) → I) → ℂ)
    (hf : Integrable f) :
    (∫ x, f x) = ∫ y : Fin d → I, ∫ t : I, f (i.insertNth t y) := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => I) i).symm
  rw [← hp.integral_comp' f]
  change (∫ x : I × (Fin d → I), f ((MeasurableEquiv.piFinSuccAbove (fun _ => I) i).symm x)
    ∂volume.prod volume) = _
  exact integral_prod_symm _ (hp.integrable_comp_of_integrable hf)

variable {d : Type*} [Fintype d] [DecidableEq d]

def cubeSineMode (i : d) (n : {n : d → ℕ // n i ≠ 0}) : C(d → I,ℂ) where
  toFun x := ∏ j, if j=i then sineMode (n.1 j-1) (x j) else neumannMode (n.1 j) (x j)
  continuous_toFun := by
    apply continuous_finsetProd
    intro j _
    by_cases hj : j=i <;> simp only [hj,ite_true,ite_false] <;> fun_prop

lemma cubeSineMode_inner (i : d) (m n : {n : d → ℕ // n i ≠ 0}) :
    (∫ x : d → I, conj (cubeSineMode i m x)*cubeSineMode i n x) =
      if m=n then 1 else 0 := by
  classical
  simp only [cubeSineMode,ContinuousMap.coe_mk,map_prod,← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod
    (fun j (x : I) => conj (if j=i then sineMode (m.1 j-1) x else neumannMode (m.1 j) x)*
      (if j=i then sineMode (n.1 j-1) x else neumannMode (n.1 j) x))]
  have he (j : d) : (∫ x : I,
      conj (if j=i then sineMode (m.1 j-1) x else neumannMode (m.1 j) x)*
      (if j=i then sineMode (n.1 j-1) x else neumannMode (n.1 j) x)) =
      if m.1 j=n.1 j then 1 else 0 := by
    by_cases hj : j=i
    · subst j
      simp only [ite_true,sineMode_inner]
      have hm := m.2
      have hn := n.2
      have hh : m.1 i-1=n.1 i-1 ↔ m.1 i=n.1 i := by omega
      simp only [hh]
    · simp only [ite_eq_right hj,neumannMode_inner]
  simp_rw [he]
  by_cases h : m=n
  · simp [h]
  · rw [ite_eq_right h]
    have hh : m.1 ≠ n.1 := fun hh => h (Subtype.ext hh)
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hh
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

abbrev cubeSineLp (i : d) (n : {n : d → ℕ // n i ≠ 0}) :
    Lp ℂ 2 (volume : Measure (d → I)) := ContinuousMap.toLp 2 volume ℂ (cubeSineMode i n)

lemma orthonormal_cubeSine (i : d) : Orthonormal ℂ (cubeSineLp i) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [ContinuousMap.inner_toLp]
  simpa only [mul_comm] using cubeSineMode_inner i m n

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_NeumannGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_NeumannGradient_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

variable {d : ℕ}

lemma cubeNeumannMode_split (i : Fin (d+1)) (n : Fin (d+1) → ℕ)
    (t : I) (y : Fin d → I) :
    cubeNeumannMode n (i.insertNth t y) =
      neumannMode (n i) t * cubeNeumannMode (n ∘ i.succAbove) y := by
  simp only [cubeNeumannMode,ContinuousMap.coe_mk,i.prod_univ_succAbove,
    Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,Function.comp_def]

lemma cubeSineMode_split (i : Fin (d+1)) (n : {n : Fin (d+1) → ℕ // n i ≠ 0})
    (t : I) (y : Fin d → I) :
    cubeSineMode i n (i.insertNth t y) =
      sineMode (n.1 i-1) t * cubeNeumannMode (n.1 ∘ i.succAbove) y := by
  simp [cubeSineMode,cubeNeumannMode,i.prod_univ_succAbove,Fin.succAbove_ne]

lemma coe_insertNth (i : Fin (d+1)) (t : I) (y : Fin d → I) :
    (fun j => (i.insertNth (α := fun _ => I) t y j : ℝ)) = i.insertNth (α := fun _ => ℝ) (t:ℝ) (fun j => (y j:ℝ)) := by
  ext j
  refine i.succAboveCases ?_ (fun k => ?_) j <;> simp

lemma contDiff_insertNth (i : Fin (d+1)) (y : Fin d → ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => i.insertNth (α := fun _ => ℝ) t y) := by
  rw [contDiff_pi]
  intro j
  refine i.succAboveCases ?_ (fun k => ?_) j <;> simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove] <;> fun_prop

lemma hasDerivAt_insertNth (i : Fin (d+1)) (y : Fin d → ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => i.insertNth (α := fun _ => ℝ) t y) (Pi.single i 1) t := by
  rw [hasDerivAt_pi]
  intro j
  refine i.succAboveCases ?_ (fun k => ?_) j
  · simpa only [Fin.insertNth_apply_same,Pi.single_eq_same] using hasDerivAt_id' t
  · simpa only [Fin.insertNth_apply_succAbove,Pi.single_eq_of_ne (Fin.succAbove_ne i k)] using hasDerivAt_const t (y k)

def cubeFunction {f : (Fin (d+1) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) : C(Fin (d+1) → I,ℂ) where
  toFun x := f (fun i => (x i:ℝ))
  continuous_toFun := hf.continuous.comp (by fun_prop)

def cubeGradient {f : (Fin (d+1) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (i : Fin (d+1)) :
    C(Fin (d+1) → I,ℂ) where
  toFun x := fderiv ℝ f (fun j => (x j:ℝ)) (Pi.single i 1)
  continuous_toFun := ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).comp (by fun_prop)

lemma deriv_slice {f : (Fin (d+1) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (i : Fin (d+1)) (y : Fin d → ℝ) (t : ℝ) :
    deriv (fun t => f (i.insertNth t y)) t =
      fderiv ℝ f (i.insertNth t y) (Pi.single i 1) := by
  exact (((hf.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_insertNth i y t)).deriv

lemma cube_derivative_pairing {f : (Fin (d+1) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (i : Fin (d+1)) (n : {n : Fin (d+1) → ℕ // n i ≠ 0}) :
    (∫ x, conj (cubeSineMode i n x)*cubeGradient hf i x) =
      -(Real.pi*n.1 i:ℝ)*(∫ x, conj (cubeNeumannMode n.1 x)*cubeFunction hf x) := by
  have hs : Integrable (fun x => conj (cubeSineMode i n x)*cubeGradient hf i x) :=
    (by fun_prop : Continuous (fun x => conj (cubeSineMode i n x)*cubeGradient hf i x)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : Integrable (fun x => conj (cubeNeumannMode n.1 x)*cubeFunction hf x) :=
    (by fun_prop : Continuous (fun x => conj (cubeNeumannMode n.1 x)*cubeFunction hf x)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_cube_split i _ hs,integral_cube_split i _ hc,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [cubeSineMode_split,cubeNeumannMode_split,map_mul,cubeGradient,cubeFunction,
    ContinuousMap.coe_mk,coe_insertNth]
  have hp := normalized_sine_derivative_pairing
    (hf.comp (contDiff_insertNth i (fun j => (y j:ℝ)))) n.2
  simp only [Function.comp_def,deriv_slice hf] at hp
  simp only [mul_right_comm _ (conj (cubeNeumannMode (n.1 ∘ i.succAbove) y)),integral_mul_const]
  rw [hp]
  ring

end Work_NeumannGradient_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

lemma continuous_toLp_norm_sq {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : C(X,ℂ)) : ‖ContinuousMap.toLp 2 μ ℂ f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),ContinuousMap.inner_toLp]
  simp_rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
  rw [integral_complex_ofReal]
  rfl

variable {d : Type*} [Fintype d]

def neumannCoeff (f : C(d → I,ℂ)) (n : d → ℕ) : ℂ :=
  ∫ x, conj (cubeNeumannMode n x)*f x

lemma neumannCoeff_eq_inner (f : C(d → I,ℂ)) (n : d → ℕ) :
    neumannCoeff f n = inner ℂ (neumannLp n) (ContinuousMap.toLp 2 volume ℂ f) := by
  rw [ContinuousMap.inner_toLp]
  simp only [neumannCoeff,mul_comm]

lemma neumann_parseval (f : C(d → I,ℂ)) :
    (∑' n, ‖neumannCoeff f n‖^2) = ∫ x, ‖f x‖^2 := by
  let v := ContinuousMap.toLp 2 volume ℂ f
  have h := lp.norm_rpow_eq_tsum (p := (2:ENNReal)) (by norm_num)
    (neumannBasis.repr v)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,HilbertBasis.repr_apply_apply,
    neumannBasis_apply,LinearIsometryEquiv.norm_map] at h
  simpa only [v,neumannCoeff_eq_inner,continuous_toLp_norm_sq] using h.symm

lemma neumannCoeff_summable (f : C(d → I,ℂ)) :
    Summable (fun n => ‖neumannCoeff f n‖^2) := by
  simp only [neumannCoeff_eq_inner]
  exact orthonormal_neumann.inner_products_summable _

variable {D : ℕ}

lemma neumann_derivative_bessel {f : (Fin (D+1) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (i : Fin (D+1)) (S : Finset {n : Fin (D+1) → ℕ // n i ≠ 0}) :
    ∑ n ∈ S, (Real.pi*(n.1 i:ℝ))^2*‖neumannCoeff (cubeFunction hf) n.1‖^2 ≤
      ∫ x, ‖cubeGradient hf i x‖^2 := by
  have h := (orthonormal_cubeSine i).sum_inner_products_le
    (s := S) (ContinuousMap.toLp 2 volume ℂ (cubeGradient hf i))
  rw [continuous_toLp_norm_sq] at h
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro n _
  rw [ContinuousMap.inner_toLp]
  have he : (∫ x, cubeGradient hf i x*conj (cubeSineMode i n x)) =
      -(Real.pi*n.1 i:ℝ)*neumannCoeff (cubeFunction hf) n.1 := by
    simpa only [neumannCoeff,mul_comm] using cube_derivative_pairing hf i n
  simp only [he,norm_mul,norm_neg,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem neumann_spectral_lower {f : (Fin (D+1) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (S : Finset (Fin (D+1) → ℕ)) :
    ∑ n ∈ S, (∑ i, (Real.pi*(n i:ℝ))^2)*‖neumannCoeff (cubeFunction hf) n‖^2 ≤
      ∑ i, ∫ x, ‖cubeGradient hf i x‖^2 := by
  classical
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  let S' := S.subtype (fun n => n i ≠ 0)
  have h := neumann_derivative_bessel hf i S'
  refine le_trans (le_of_eq ?_) h
  dsimp only [S']
  rw [Finset.sum_subtype_eq_sum_filter
    (fun n : Fin (D+1) → ℕ => (Real.pi*(n i:ℝ))^2*‖neumannCoeff (cubeFunction hf) n‖^2),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n i = 0 <;> simp [hn]

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_NeumannReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_NeumannReindex_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

variable {d e : Type*} [Fintype d] [Fintype e]

lemma integral_cube_reindex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : d ≃ e) (f : (e → I) → E) :
    (∫ x : d → I, f (x ∘ a.symm)) = ∫ x, f x := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : e => I) a).integral_comp' f
  change (∫ x, f ((MeasurableEquiv.piCongrLeft (fun _ : e => I) a) x)) = _ at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext x
  congr 1
  funext i
  simp only [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_eq_cast,Function.comp_def]
  rfl

lemma cubeNeumannMode_reindex (a : d ≃ e) (n : e → ℕ) (x : d → I) :
    cubeNeumannMode n (x ∘ a.symm) = cubeNeumannMode (n ∘ a) x := by
  simp only [cubeNeumannMode,ContinuousMap.coe_mk,Function.comp_def]
  simpa only [a.symm_apply_apply] using
    (a.prod_comp (fun i => neumannMode (n i) (x (a.symm i)))).symm

def realReindex (a : d ≃ e) : (d → ℝ) ≃L[ℝ] (e → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : e => ℝ) a

omit [Fintype d] [Fintype e] in
lemma realReindex_apply (a : d ≃ e) (x : d → ℝ) : realReindex a x = x ∘ a.symm := by
  funext i
  change (Equiv.piCongrLeft (fun _ : e => ℝ) a) x i = _
  simp only [Equiv.piCongrLeft_apply_eq_cast,Function.comp_def]
  rfl

omit [Fintype d] [Fintype e] in
lemma realReindex_single [DecidableEq d] [DecidableEq e] (a : d ≃ e) (i : d) :
    realReindex a (Pi.single i 1) = Pi.single (a i) 1 := by
  rw [realReindex_apply]
  funext j
  simp only [Function.comp_def,Pi.single_apply]
  simp only [a.symm_apply_eq]

def finiteCubeFunction {f : (d → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) : C(d → I,ℂ) where
  toFun x := f (fun i => (x i:ℝ))
  continuous_toFun := hf.continuous.comp (by fun_prop)

def finiteCubeGradient {f : (d → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (i : d) : C(d → I,ℂ) := by
  classical
  exact {toFun := fun x => fderiv ℝ f (fun j => (x j:ℝ)) (Pi.single i 1)
         continuous_toFun := ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).comp (by fun_prop)}

lemma finiteCubeFunction_reindex {f : (e → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (a : d ≃ e)
    (x : d → I) :
    finiteCubeFunction (hf.comp (realReindex a).contDiff) x = finiteCubeFunction hf (x ∘ a.symm) := by
  simp only [finiteCubeFunction,ContinuousMap.coe_mk,Function.comp_def,realReindex_apply]

lemma finiteCubeGradient_reindex {f : (e → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (a : d ≃ e)
    (i : d) (x : d → I) :
    finiteCubeGradient (hf.comp (realReindex a).contDiff) i x =
      finiteCubeGradient hf (a i) (x ∘ a.symm) := by
  classical
  simp only [finiteCubeGradient,ContinuousMap.coe_mk]
  rw [fderiv_comp _ (hf.differentiable (by simp) _) ((realReindex a).differentiableAt),
    ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    realReindex_single,realReindex_apply]
  rfl

lemma neumannCoeff_reindex {f : (e → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (a : d ≃ e)
    (n : e → ℕ) :
    neumannCoeff (finiteCubeFunction (hf.comp (realReindex a).contDiff)) (n ∘ a) =
      neumannCoeff (finiteCubeFunction hf) n := by
  unfold neumannCoeff
  calc
    _ = ∫ x : d → I, conj (cubeNeumannMode n (x ∘ a.symm))*finiteCubeFunction hf (x ∘ a.symm) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [finiteCubeFunction_reindex hf a x,cubeNeumannMode_reindex]
    _ = _ := integral_cube_reindex a (fun x => conj (cubeNeumannMode n x)*finiteCubeFunction hf x)

lemma cubeGradient_eq_finite {D : ℕ} {f : (Fin (D+1) → ℝ) → ℂ}
    (hf : ContDiff ℝ 1 f) (i : Fin (D+1)) : cubeGradient hf i = finiteCubeGradient hf i := by
  ext x
  simp only [cubeGradient,finiteCubeGradient,ContinuousMap.coe_mk]
  apply congrArg (fderiv ℝ f (fun j => (x j:ℝ)))
  funext j
  by_cases hj : j=i <;> simp [hj]

theorem finite_neumann_spectral_lower {f : (d → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (S : Finset (d → ℕ)) :
    ∑ n ∈ S, (∑ i, (Real.pi*(n i:ℝ))^2)*‖neumannCoeff (finiteCubeFunction hf) n‖^2 ≤
      ∑ i, ∫ x, ‖finiteCubeGradient hf i x‖^2 := by
  classical
  cases isEmpty_or_nonempty d with
  | inl hd => simp
  | inr hd =>
    let D := Fintype.card d-1
    have hc : Fintype.card (Fin (D+1)) = Fintype.card d := by
      simp only [Fintype.card_fin]
      dsimp [D]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
    let a : Fin (D+1) ≃ d := Fintype.equivOfCardEq hc
    let A : (d → ℕ) ↪ (Fin (D+1) → ℕ) :=
      ⟨fun n => n ∘ a,fun n m h => by funext j; simpa using congrFun h (a.symm j)⟩
    have hh := neumann_spectral_lower (hf.comp (realReindex a).contDiff) (S.map A)
    have hl : (∑ n ∈ S.map A, (∑ i, (Real.pi*(n i:ℝ))^2)*
        ‖neumannCoeff (cubeFunction (hf.comp (realReindex a).contDiff)) n‖^2) =
        ∑ n ∈ S, (∑ i, (Real.pi*(n i:ℝ))^2)*‖neumannCoeff (finiteCubeFunction hf) n‖^2 := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro n _
      change (∑ i, (Real.pi*(n (a i):ℝ))^2)*
        ‖neumannCoeff (finiteCubeFunction (hf.comp (realReindex a).contDiff)) (n ∘ a)‖^2 = _
      rw [neumannCoeff_reindex hf a n]
      rw [a.sum_comp (fun i => (Real.pi*(n i:ℝ))^2)]
    have hr : (∑ i, ∫ x, ‖cubeGradient (hf.comp (realReindex a).contDiff) i x‖^2) =
        ∑ i, ∫ x, ‖finiteCubeGradient hf i x‖^2 := by
      calc
        _ = ∑ i : Fin (D+1), ∫ x, ‖finiteCubeGradient hf (a i) x‖^2 := by
          apply Finset.sum_congr rfl
          intro i _
          simp_rw [cubeGradient_eq_finite,finiteCubeGradient_reindex hf a i]
          exact integral_cube_reindex a (fun x => ‖finiteCubeGradient hf (a i) x‖^2)
        _ = _ := a.sum_comp (fun i => ∫ x, ‖finiteCubeGradient hf i x‖^2)
    rwa [hl,hr] at hh

end Work_NeumannReindex_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

variable {d : Type*} [Fintype d]

lemma integral_cube_permute (e : d ≃ d) (f : (d → I) → ℂ) :
    (∫ x, f (x ∘ e)) = ∫ x, f x := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : d => I) e.symm).integral_comp' f
  change (∫ x, f ((MeasurableEquiv.piCongrLeft (fun _ : d => I) e.symm) x)) = _ at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext x
  congr 1
  funext i
  simp only [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply_eq_cast,Equiv.symm_symm,
    Function.comp_def]
  rfl

lemma cubeNeumannMode_permute (e : d ≃ d) (n : d → ℕ) (x : d → I) :
    cubeNeumannMode n (x ∘ e) = cubeNeumannMode (n ∘ e.symm) x := by
  simp only [cubeNeumannMode,ContinuousMap.coe_mk,Function.comp_def]
  simpa only [e.symm_apply_apply] using
    e.prod_comp (fun i => neumannMode (n (e.symm i)) (x i))

variable {N : ℕ}

abbrev particlePermute (e : Equiv.Perm (Fin N)) : Equiv.Perm (Fin N × Fin 3) :=
  e.prodCongr (Equiv.refl (Fin 3))

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoherentPackets
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

def coherentPacket (g : Space → ℂ) (z p x : Space) : ℂ :=
  g (x-z) * Complex.exp ((inner ℝ p x : ℂ) * Complex.I)

lemma coherentPacket_compact {g : Space → ℂ} (hg : HasCompactSupport g) (z p : Space) :
    HasCompactSupport (coherentPacket g z p) := by
  exact (hg.comp_homeomorph (Homeomorph.subRight z)).mul_right

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoherentHilbert
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

abbrev OrbitalHilbert := Lp ℂ 2 (volume : Measure Space)

lemma coherentPacket_memLp {g : Space → ℂ}
    (hg : Continuous g) (hcg : HasCompactSupport g) (z p : Space) :
    MemLp (coherentPacket g z p) 2 := by
  have hc : Continuous (coherentPacket g z p) := by unfold coherentPacket; fun_prop
  exact hc.memLp_of_hasCompactSupport (coherentPacket_compact hcg z p)

def coherentVector {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (q : Space × Space) : OrbitalHilbert :=
  (coherentPacket_memLp hg hcg q.1 q.2).toLp _

end Work_CoherentHilbert_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

def coherentOperator {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) : OrbitalHilbert →L[ℂ] OrbitalHilbert :=
  (((2*Real.pi)^3)⁻¹ : ℝ) • ∫ q, InnerProductSpace.rankOne ℂ
    (coherentVector hg hcg q) (coherentVector hg hcg q) ∂μ

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CompactEigenbasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CompactEigenbasis_scope

open MeasureTheory Filter Module
open scoped BigOperators ComplexConjugate Topology

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def compactEigenspaceIndex (T : H →L[ℂ] H) (μ : ℂ) : Set (Module.End.eigenspace T.toLinearMap μ) :=
  (exists_hilbertBasis ℂ (Module.End.eigenspace T.toLinearMap μ)).choose

abbrev CompactSpectralIndex (T : H →L[ℂ] H) := Σ μ : ℂ, compactEigenspaceIndex T μ

end Work_CompactEigenbasis_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

abbrev CoherentIndex {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) := CompactSpectralIndex (coherentOperator hg hcg μ)

def coherentWeight {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) (i : CoherentIndex hg hcg μ) : ℝ := i.1.re

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_CoherentPhaseBasis
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

def coherentFactor : ℝ := ((2*Real.pi)^3)⁻¹
lemma coherentFactor_pos : 0 < coherentFactor := by unfold coherentFactor; positivity

abbrev CoherentPositiveIndex {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (μ : Measure (Space × Space)) := {i : CoherentIndex hg hcg μ // 0 < coherentWeight hg hcg μ i}

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_MomentumBall
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

lemma space_ball_real_volume {R : ℝ} (hR : 0 ≤ R) :
    volume.real (ball (0 : Space) R) = (4*Real.pi/3)*R^3 := by
  rw [Measure.real,EuclideanSpace.volume_ball_fin_three,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hR,ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

def fermiRadius (ρ : Space → ℝ) (z : Space) : ℝ := (3*Real.pi^2*ρ z)^(1/3 : ℝ)

lemma fermiRadius_nonneg {ρ : Space → ℝ} (hρ : ∀ z, 0 ≤ ρ z) (z : Space) :
    0 ≤ fermiRadius ρ z := Real.rpow_nonneg (mul_nonneg (by positivity) (hρ z)) _

lemma fermiRadius_cube {ρ : Space → ℝ} (hρ : ∀ z, 0 ≤ ρ z) (z : Space) :
    (fermiRadius ρ z)^3 = 3*Real.pi^2*ρ z := by
  rw [fermiRadius,← Real.rpow_mul_natCast (mul_nonneg (by positivity) (hρ z) : 0 ≤ 3*Real.pi^2*ρ z)]
  norm_num

lemma fermiRadius_ball_mass {ρ : Space → ℝ} (hρ : ∀ z, 0 ≤ ρ z) (z : Space) :
    2*coherentFactor*volume.real (ball (0 : Space) (fermiRadius ρ z)) = ρ z := by
  rw [space_ball_real_volume (fermiRadius_nonneg hρ z),fermiRadius_cube hρ z,coherentFactor]
  field_simp [Real.pi_ne_zero]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_PhaseBathtub
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

open MeasureTheory Set Metric
open scoped BigOperators ENNReal

def momentumInterval (n : ℕ) : Set ℝ :=
  Ioo (-Real.pi*(n+1)) (-Real.pi*n) ∪ Ioo (Real.pi*n) (Real.pi*(n+1))

lemma measurableSet_momentumInterval (n : ℕ) : MeasurableSet (momentumInterval n) :=
  measurableSet_Ioo.union measurableSet_Ioo

lemma momentumInterval_abs {n : ℕ} {x : ℝ} (hx : x ∈ momentumInterval n) :
    Real.pi*n < |x| ∧ |x| < Real.pi*(n+1) := by
  have hp := Real.pi_pos
  rcases hx with hx | hx
  · rw [abs_of_neg (by nlinarith [hx.2,mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)] : x < 0)]
    constructor <;> nlinarith [hx.1,hx.2]
  · rw [abs_of_pos (by nlinarith [hx.1,mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)] : 0 < x)]
    exact hx

lemma momentumInterval_disjoint {m n : ℕ} (h : m ≠ n) :
    Disjoint (momentumInterval m) (momentumInterval n) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hh := momentumInterval_abs hx
  have hk := momentumInterval_abs hy
  rcases lt_or_gt_of_ne h with hmn | hnm
  · have hc : (m:ℝ)+1 ≤ n := by exact_mod_cast hmn
    nlinarith [Real.pi_pos]
  · have hc : (n:ℝ)+1 ≤ m := by exact_mod_cast hnm
    nlinarith [Real.pi_pos]

lemma volume_momentumInterval (n : ℕ) : volume (momentumInterval n) = ENNReal.ofReal (2*Real.pi) := by
  unfold momentumInterval
  have hd : Disjoint (Ioo (-Real.pi*(n+1)) (-Real.pi*n)) (Ioo (Real.pi*n) (Real.pi*(n+1))) := by
    rw [Set.disjoint_left]
    intro x hx hy
    nlinarith [hx.2,hy.1,Real.pi_pos]
  rw [measure_union hd measurableSet_Ioo,Real.volume_Ioo,Real.volume_Ioo]
  have h1 : -Real.pi*(n:ℝ)-(-Real.pi*(n+1)) = Real.pi := by ring
  have h2 : Real.pi*((n:ℝ)+1)-Real.pi*n = Real.pi := by ring
  rw [h1,h2,←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

def momentumCell (n : Fin 3 → ℕ) : Set Space :=
  {p | ∀ i, p i ∈ momentumInterval (n i)}

lemma measurableSet_momentumCell (n : Fin 3 → ℕ) : MeasurableSet (momentumCell n) := by
  simp only [momentumCell,Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => (measurableSet_momentumInterval _).preimage (by fun_prop)

lemma volume_momentumCell (n : Fin 3 → ℕ) :
    volume (momentumCell n) = ENNReal.ofReal ((2*Real.pi)^3) := by
  have he : momentumCell n = (WithLp.ofLp : Space → Fin 3 → ℝ) ⁻¹'
      (Set.pi univ (fun i => momentumInterval (n i))) := by ext p; simp [momentumCell]
  rw [he,(PiLp.volume_preserving_ofLp (ι := Fin 3)).measure_preimage ((MeasurableSet.pi (Set.to_countable _) (fun i _ => measurableSet_momentumInterval (n i))).nullMeasurableSet),volume_pi_pi]
  simp only [volume_momentumInterval,Finset.prod_const,Finset.card_fin]
  rw [←ENNReal.ofReal_pow (by positivity)]

lemma momentumCell_disjoint {m n : Fin 3 → ℕ} (h : m ≠ n) :
    Disjoint (momentumCell m) (momentumCell n) := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp h
  rw [Set.disjoint_left]
  intro x hx hy
  exact Set.disjoint_left.mp (momentumInterval_disjoint hi) (hx i) (hy i)

lemma momentumCell_norm_sq {n : Fin 3 → ℕ} {p : Space} (hp : p ∈ momentumCell n) :
    ‖p‖^2 ≤ Real.pi^2*∑ i, ((n i:ℝ)+1)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := (momentumInterval_abs (hp i)).2.le
  calc (p i)^2 = |p i|^2 := (sq_abs _).symm
    _ ≤ (Real.pi*((n i:ℝ)+1))^2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_PauliMomentum
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

abbrev NeumannSpinMode := (Fin 3 → ℕ) × Fin 2

def discretePhaseDensity (S : Finset NeumannSpinMode) (p : Space) : ℝ :=
  coherentFactor*∑ q ∈ S, (momentumCell q.1).indicator (fun _ => (1:ℝ)) p

lemma discretePhaseDensity_nonneg (S : Finset NeumannSpinMode) (p : Space) :
    0 ≤ discretePhaseDensity S p := by
  apply mul_nonneg coherentFactor_pos.le
  apply Finset.sum_nonneg
  intro q _
  exact Set.indicator_nonneg (fun _ _ => by norm_num) p

lemma discretePhaseDensity_pauli (S : Finset NeumannSpinMode) (p : Space) :
    discretePhaseDensity S p ≤ 2*coherentFactor := by
  classical
  let A := S.filter (fun q => p ∈ momentumCell q.1)
  have he : (∑ q ∈ S, (momentumCell q.1).indicator (fun _ => (1:ℝ)) p) = (A.card:ℝ) := by
    simp only [A,Finset.card_filter, Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hp : p ∈ momentumCell q.1 <;> simp [hp]
  have hc : A.card ≤ 2 := by
    have hh : A.card ≤ (Finset.univ : Finset (Fin 2)).card := by
      apply Finset.card_le_card_of_injOn Prod.snd (fun _ _ => Finset.mem_univ _)
      intro q hq r hr hqr
      apply Prod.ext _ hqr
      by_contra hs
      exact Set.disjoint_left.mp (momentumCell_disjoint hs)
        (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hr).2
    simpa using hh
  unfold discretePhaseDensity
  rw [he,mul_comm (2:ℝ)]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) coherentFactor_pos.le

lemma momentumCell_finite (n : Fin 3 → ℕ) : volume (momentumCell n) < ⊤ := by
  rw [volume_momentumCell]
  exact ENNReal.ofReal_lt_top

lemma momentumCell_integrable (n : Fin 3 → ℕ) :
    Integrable ((momentumCell n).indicator (fun _ => (1:ℝ))) := by
  apply (integrable_indicator_iff (measurableSet_momentumCell n)).2
  exact integrableOn_const (momentumCell_finite n).ne

lemma momentumCell_mass (n : Fin 3 → ℕ) :
    coherentFactor*(∫ p : Space, (momentumCell n).indicator (fun _ => (1:ℝ)) p) = 1 := by
  rw [integral_indicator (measurableSet_momentumCell n),integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one,
    volume_momentumCell,ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*Real.pi)^3)]
  exact inv_mul_cancel₀ (by positivity)

lemma discretePhaseDensity_integrable (S : Finset NeumannSpinMode) :
    Integrable (discretePhaseDensity S) := by
  apply Integrable.const_mul
  exact integrable_finsetSum _ (fun q _ => momentumCell_integrable q.1)

lemma discretePhaseDensity_mass (S : Finset NeumannSpinMode) :
    (∫ p, discretePhaseDensity S p) = S.card := by
  unfold discretePhaseDensity
  rw [integral_const_mul,integral_finsetSum _ (fun q _ => momentumCell_integrable q.1),Finset.mul_sum]
  simp only [momentumCell_mass,Finset.sum_const,nsmul_eq_mul,mul_one]

lemma momentumCell_kinetic_integrable (n : Fin 3 → ℕ) :
    IntegrableOn (fun p : Space => ‖p‖^2) (momentumCell n) := by
  let B := Real.pi^2*∑ i, ((n i:ℝ)+1)^2
  have hB : IntegrableOn (fun _ : Space => B) (momentumCell n) :=
    integrableOn_const (momentumCell_finite n).ne
  apply hB.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (measurableSet_momentumCell n)] with p hp
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖p‖)]
  exact momentumCell_norm_sq hp

lemma momentumCell_indicator_kinetic_integrable (n : Fin 3 → ℕ) :
    Integrable ((momentumCell n).indicator (fun p : Space => ‖p‖^2)) :=
  (integrable_indicator_iff (measurableSet_momentumCell n)).2 (momentumCell_kinetic_integrable n)

lemma discretePhaseDensity_kinetic_eq (S : Finset NeumannSpinMode) :
    (fun p => ‖p‖^2*discretePhaseDensity S p) =
      fun p => coherentFactor*∑ q ∈ S, (momentumCell q.1).indicator (fun p : Space => ‖p‖^2) p := by
  ext p
  simp only [discretePhaseDensity,Set.indicator,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> ring

lemma discretePhaseDensity_kinetic_integrable (S : Finset NeumannSpinMode) :
    Integrable (fun p => ‖p‖^2*discretePhaseDensity S p) := by
  rw [discretePhaseDensity_kinetic_eq]
  apply Integrable.const_mul
  exact integrable_finsetSum S fun q _ => momentumCell_indicator_kinetic_integrable q.1

lemma discretePhaseDensity_kinetic_integral (S : Finset NeumannSpinMode) :
    (∫ p, ‖p‖^2*discretePhaseDensity S p) =
      ∑ q ∈ S, coherentFactor*∫ p in momentumCell q.1, ‖p‖^2 := by
  rw [discretePhaseDensity_kinetic_eq,integral_const_mul,
    integral_finsetSum S (fun q _ => momentumCell_indicator_kinetic_integrable q.1),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_indicator (measurableSet_momentumCell q.1)]

lemma momentumCell_kinetic_bound (n : Fin 3 → ℕ) :
    coherentFactor*(∫ p in momentumCell n, ‖p‖^2) ≤ Real.pi^2*∑ i, ((n i:ℝ)+1)^2 := by
  let B := Real.pi^2*∑ i, ((n i:ℝ)+1)^2
  have hB : IntegrableOn (fun _ : Space => B) (momentumCell n) :=
    integrableOn_const (momentumCell_finite n).ne
  have hb : (∫ p in momentumCell n, ‖p‖^2) ≤ ∫ _p in momentumCell n, B :=
    setIntegral_mono_on (momentumCell_kinetic_integrable n) hB
      (measurableSet_momentumCell n) (fun p hp => momentumCell_norm_sq hp)
  have hh := mul_le_mul_of_nonneg_left hb coherentFactor_pos.le
  rw [integral_const] at hh
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,volume_momentumCell,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*Real.pi)^3)] at hh
  have he : coherentFactor*((2*Real.pi)^3*B) = B := by
    unfold coherentFactor
    rw [←mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]
  rwa [he] at hh

end Work_PauliMomentum_scope

open MeasureTheory Set
open scoped BigOperators ENNReal

def neumannRemainderConstant : ℝ := tfKinetic + 3*Real.pi^2/2

lemma neumannRemainderConstant_pos : 0 < neumannRemainderConstant := by
  unfold neumannRemainderConstant
  unfold tfKinetic
  positivity

lemma square_shift_bound (a r : ℝ) (hr : 0 < r) :
    (a+1)^2 ≤ (1+1/r)*a^2+1+r := by
  have h := sq_nonneg (a-r)
  have hd : 0 ≤ (a-r)^2/r := div_nonneg h hr.le
  field_simp at hd ⊢
  nlinarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_NeumannFermions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_NeumannFermions_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

open CoulombAtom
variable {N : ℕ}

def neumannLowerEnergy (N : ℕ) : ℝ :=
  tfKinetic*(N:ℝ)^(5/3:ℝ)-neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))

end Work_NeumannFermions_scope

open MeasureTheory Set
open scoped BigOperators unitInterval ComplexConjugate ENNReal ContDiff

open CoulombAtom

variable {N : ℕ}

lemma coeff_zero_of_exchange
    {Ψ : (Fin N → Fin 2) → C((Fin N × Fin 3) → I,ℂ)}
    (s : Fin N → Fin 2) (n : (Fin N × Fin 3) → ℕ)
    {i j : Fin N}
    (hΨ : ∀ s x, Ψ (s ∘ Equiv.swap i j) (x ∘ particlePermute (Equiv.swap i j)) = -Ψ s x)
    (hs : s i = s j) (hn : ∀ a : Fin 3, n (i,a) = n (j,a)) :
    neumannCoeff (Ψ s) n = 0 := by
  classical
  let e := Equiv.swap i j
  have hse : s ∘ e = s := by
    funext k
    by_cases hki : k=i
    · subst k; simpa [e] using hs.symm
    · by_cases hkj : k=j
      · subst k; simpa [e] using hs
      · simp [e,Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hne : n ∘ (particlePermute e).symm = n := by
    ext ⟨k,a⟩
    by_cases hki : k=i
    · subst k; simpa [e,particlePermute] using (hn a).symm
    · by_cases hkj : k=j
      · subst k; simpa [e,particlePermute] using hn a
      · simp [e,particlePermute,Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hex (x : (Fin N × Fin 3) → I) : Ψ s (x ∘ particlePermute e) = -Ψ s x := by
    have ht := hΨ s x
    change Ψ (s ∘ e) (x ∘ particlePermute e) = -Ψ s x at ht
    rwa [hse] at ht
  have hh := integral_cube_permute (particlePermute e)
    (fun x => conj (cubeNeumannMode n x)*Ψ s x)
  simp only [cubeNeumannMode_permute,hne,hex,mul_neg,integral_neg] at hh
  change -neumannCoeff (Ψ s) n = neumannCoeff (Ψ s) n at hh
  exact neg_eq_self.mp hh

variable {C : Type*} [DecidableEq C]

def CellAntisymmetric (c : Fin N → C)
    (Ψ : (Fin N → Fin 2) → C((Fin N × Fin 3) → I,ℂ)) : Prop :=
  ∀ i j, i ≠ j → c i=c j → ∀ s x,
    Ψ (s ∘ Equiv.swap i j) (x ∘ particlePermute (Equiv.swap i j)) = -Ψ s x

def cellCount (c : Fin N → C) (a : C) : ℕ := (Finset.univ.filter (fun i => c i=a)).card

def cellLowerEnergy (c : Fin N → C) : ℝ :=
  ∑ a ∈ Finset.univ.image c, neumannLowerEnergy (cellCount c a)

lemma cellCount_eq_fintype (c : Fin N → C) (a : C) :
    cellCount c a = Fintype.card {i : Fin N // c i=a} := by
  simp [cellCount,Fintype.card_subtype]

omit [DecidableEq C] in
lemma cell_coeff_injective (c : Fin N → C)
    {Ψ : (Fin N → Fin 2) → C((Fin N × Fin 3) → I,ℂ)} (hΨ : CellAntisymmetric c Ψ)
    (s : Fin N → Fin 2) (n : (Fin N × Fin 3) → ℕ)
    (hc : neumannCoeff (Ψ s) n ≠ 0) (a : C) :
    Function.Injective (fun i : {i : Fin N // c i=a} => ((fun k : Fin 3 => n (i.1,k)),s i.1)) := by
  intro i j h
  apply Subtype.ext
  by_contra hij
  apply hc
  exact coeff_zero_of_exchange s n (hΨ i.1 j.1 hij (i.2.trans j.2.symm))
    (congrArg Prod.snd h) (fun k => congrFun (congrArg Prod.fst h) k)

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_NeumannCounts
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

lemma sum_cellCount (c : Fin N → C) :
    ∑ a ∈ Finset.univ.image c, cellCount c a = N := by
  classical
  have hc (a : C) : cellCount c a = ∑ i ∈ Finset.univ.filter (fun i => c i=a), (1:ℕ) := by simp [cellCount]
  simp_rw [hc]
  rw [Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem c (Finset.mem_univ i))]
  simp

lemma cellCount_le (c : Fin N → C) (a : C) : cellCount c a ≤ N := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin N)

lemma sum_cell_boundary (c : Fin N → C) :
    ∑ a ∈ Finset.univ.image c, ((cellCount c a:ℝ)^(4/3:ℝ)+(cellCount c a:ℝ)) ≤
      (N:ℝ)^(4/3:ℝ)+(N:ℝ) := by
  have hp (x : ℝ) (hx : 0 ≤ x) : x^(4/3:ℝ) = x*x^(1/3:ℝ) := by
    rw [show (4/3:ℝ) = 1+(1/3:ℝ) by norm_num,Real.rpow_add' hx (by norm_num)]
    rw [Real.rpow_one]
  have hn : (∑ a ∈ Finset.univ.image c, (cellCount c a:ℝ)) = N := by
    exact_mod_cast sum_cellCount c
  calc
    _ ≤ ∑ a ∈ Finset.univ.image c, ((cellCount c a:ℝ)*(N:ℝ)^(1/3:ℝ)+(cellCount c a:ℝ)) := by
      apply Finset.sum_le_sum
      intro a _
      rw [hp _ (Nat.cast_nonneg _)]
      have hle : (cellCount c a:ℝ) ≤ (N:ℝ) := by exact_mod_cast cellCount_le c a
      have hr := Real.rpow_le_rpow (Nat.cast_nonneg (cellCount c a)) hle (by norm_num : 0 ≤ (1/3:ℝ))
      have hm := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (cellCount c a))
      linarith
    _ = _ := by rw [Finset.sum_add_distrib,←Finset.sum_mul,hn,hp _ (Nat.cast_nonneg N)]

lemma cellLowerEnergy_bound (c : Fin N → C) :
    tfKinetic*(∑ a ∈ Finset.univ.image c, (cellCount c a:ℝ)^(5/3:ℝ)) -
      neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ)) ≤ cellLowerEnergy c := by
  unfold cellLowerEnergy neumannLowerEnergy
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left (sum_cell_boundary c)
    neumannRemainderConstant_pos.le) _

end Work_NeumannCounts_scope

open MeasureTheory Set
open scoped BigOperators unitInterval

open CoulombAtom
variable {N : ℕ} {C : Type*} [DecidableEq C]

def cellPressure (c : Fin N → C) : ℝ := ∑ i, (cellCount c (c i):ℝ)^(2/3:ℝ)

lemma cellPressure_eq (c : Fin N → C) :
    cellPressure c = ∑ a ∈ Finset.univ.image c, (cellCount c a:ℝ)^(5/3:ℝ) := by
  classical
  unfold cellPressure
  rw [←Finset.sum_fiberwise_of_maps_to (g := c) (t := Finset.univ.image c)
    (fun i _ => Finset.mem_image_of_mem c (Finset.mem_univ i))]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => c i=a), (cellCount c a:ℝ)^(2/3:ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = (cellCount c a:ℝ)*(cellCount c a:ℝ)^(2/3:ℝ) := by simp [cellCount]
    _ = _ := by
      rw [show (5/3:ℝ)=1+(2/3:ℝ) by norm_num,
        Real.rpow_add' (Nat.cast_nonneg _) (by norm_num),Real.rpow_one]

lemma cellPressure_nonneg (c : Fin N → C) : 0 ≤ cellPressure c :=
  Finset.sum_nonneg (fun _i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma cellPressure_le (c : Fin N → C) : cellPressure c ≤ (N:ℝ)^(5/3:ℝ) := by
  calc
    _ ≤ ∑ i : Fin N, (N:ℝ)^(2/3:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast cellCount_le c (c i)) (by norm_num)
    _ = (N:ℝ)*(N:ℝ)^(2/3:ℝ) := by simp
    _ = _ := by
      rw [show (5/3:ℝ)=1+(2/3:ℝ) by norm_num,
        Real.rpow_add' (Nat.cast_nonneg _) (by norm_num),Real.rpow_one]

def pointCell (x : (Fin N × Fin 3) → ℝ) (i : Fin N) : Fin 3 → ℤ := fun a => ⌊x (i,a)⌋
def indexCell (z : (Fin N × Fin 3) → ℤ) (i : Fin N) : Fin 3 → ℤ := fun a => z (i,a)

lemma pointCell_measurable : Measurable (pointCell (N := N)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro a
  exact Int.measurable_floor.comp (measurable_pi_apply (i,a))

lemma flatPressure_measurable : Measurable (fun x : (Fin N × Fin 3) → ℝ => cellPressure (pointCell x)) :=
  (measurable_of_countable (fun c : Fin N → Fin 3 → ℤ => cellPressure c)).comp pointCell_measurable

lemma pointCell_of_mem_floorCube {z : (Fin N × Fin 3) → ℤ} {x : (Fin N × Fin 3) → ℝ}
    (hx : x ∈ floorCube z) : pointCell x = indexCell z := by
  ext i a
  exact hx (i,a)

lemma flatPressure_integrable {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : MemLp f 2) :
    Integrable (fun x => cellPressure (pointCell x)*‖f x‖^2) := by
  apply hf.norm.integrable_sq.bdd_mul flatPressure_measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (cellPressure_nonneg _)]
    exact cellPressure_le _)

lemma integral_floorCube_pressure (z : (Fin N × Fin 3) → ℤ)
    (f : ((Fin N × Fin 3) → ℝ) → ℂ) :
    (∫ x in floorCube z, cellPressure (pointCell x)*‖f x‖^2) =
      cellPressure (indexCell z)*(∫ x in floorCube z, ‖f x‖^2) := by
  rw [←integral_const_mul]
  apply setIntegral_congr_fun (floorCube_measurable z)
  intro x hx
  simp only [pointCell_of_mem_floorCube hx]

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CubeDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CubeDensity_scope

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

variable {N : ℕ} {d : Type*} [Fintype d]

lemma integral_sameCube_y (t x : d → ℝ) : (∫ y, sameCube t x y) = 1 := by
  have he : (fun y => sameCube t x y) =
      fun y => (floorCube (cubeIndex (x-t))).indicator (fun _ => (1:ℝ)) (y-t) := by
    funext y
    have hm : y-t ∈ floorCube (cubeIndex (x-t)) ↔ cubeIndex (x-t)=cubeIndex (y-t) := by
      simp only [floorCube,mem_ofPred_eq,cubeIndex,funext_iff]
      exact forall_congr' (fun i => eq_comm)
    simp only [sameCube,Set.indicator,hm]
  rw [he,integral_sub_right_eq_self,integral_indicator (floorCube_measurable _),setIntegral_const]
  simp [measureReal_def,volume_floorCube]

lemma sameCube_y_integrable (t x : d → ℝ) : Integrable (fun y => sameCube t x y) := by
  have hi := ((integrableOn_const (C := (1:ℝ)) (μ := volume) (s := floorCube (cubeIndex (x-t)))
    (by simp [volume_floorCube])).integrable_indicator (floorCube_measurable _)).comp_sub_right t
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext y
  have hm : y-t ∈ floorCube (cubeIndex (x-t)) ↔ cubeIndex (x-t)=cubeIndex (y-t) := by
    simp only [floorCube,mem_ofPred_eq,cubeIndex,funext_iff]
    exact forall_congr' (fun i => eq_comm)
  simp only [sameCube,Set.indicator,hm]

def cubeDensity (t : d → ℝ) (x : Fin N → d → ℝ) (y : d → ℝ) : ℝ :=
  ∑ i, sameCube t (x i) y

def cubeAssignment (t : d → ℝ) (x : Fin N → d → ℝ) (i : Fin N) : d → ℤ :=
  cubeIndex (x i-t)

lemma cubeDensity_count (t : d → ℝ) (x : Fin N → d → ℝ) (y : d → ℝ) :
    cubeDensity t x y = (cellCount (cubeAssignment t x) (cubeIndex (y-t)):ℝ) := by
  classical
  simp only [cubeDensity,sameCube,cubeAssignment,cellCount]
  rw [Finset.sum_boole]
  congr 1

lemma cubeDensity_nonneg (t : d → ℝ) (x : Fin N → d → ℝ) (y : d → ℝ) :
    0 ≤ cubeDensity t x y := Finset.sum_nonneg (fun _ _ => sameCube_nonneg _ _ _)

lemma cubeDensity_le (t : d → ℝ) (x : Fin N → d → ℝ) (y : d → ℝ) : cubeDensity t x y ≤ N := by
  rw [cubeDensity_count]
  exact_mod_cast cellCount_le (cubeAssignment t x) (cubeIndex (y-t))

lemma cellCount_rpow_query {C : Type*} [DecidableEq C] (c : Fin N → C) (q : C) :
    (cellCount c q:ℝ)^(5/3:ℝ) = ∑ i, if c i=q then (cellCount c (c i):ℝ)^(2/3:ℝ) else 0 := by
  classical
  have he : (∑ i : Fin N, if c i=q then (cellCount c (c i):ℝ)^(2/3:ℝ) else 0) =
      (cellCount c q:ℝ)*(cellCount c q:ℝ)^(2/3:ℝ) := by
    simp_rw [←Finset.sum_filter]
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i => c i=q), (cellCount c q:ℝ)^(2/3:ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = _ := by simp [cellCount]
  rw [he,show (5/3:ℝ)=1+(2/3:ℝ) by norm_num,
    Real.rpow_add' (Nat.cast_nonneg _) (by norm_num),Real.rpow_one]

lemma cubeDensity_rpow (t : d → ℝ) (x : Fin N → d → ℝ) (y : d → ℝ) :
    cubeDensity t x y^(5/3:ℝ) =
      ∑ i, sameCube t (x i) y*(cellCount (cubeAssignment t x) (cubeAssignment t x i):ℝ)^(2/3:ℝ) := by
  rw [cubeDensity_count,cellCount_rpow_query]
  apply Finset.sum_congr rfl
  intro i _
  unfold sameCube cubeAssignment
  split_ifs <;> simp

lemma cubeDensity_rpow_integrable (t : d → ℝ) (x : Fin N → d → ℝ) :
    Integrable (fun y => cubeDensity t x y^(5/3:ℝ)) := by
  simp_rw [cubeDensity_rpow]
  exact integrable_finsetSum _ (fun i _ => (sameCube_y_integrable t (x i)).mul_const _)

theorem integral_cubeDensity_rpow (t : d → ℝ) (x : Fin N → d → ℝ) :
    (∫ y, cubeDensity t x y^(5/3:ℝ)) = cellPressure (cubeAssignment t x) := by
  simp_rw [cubeDensity_rpow]
  rw [integral_finsetSum _ (fun i _ => (sameCube_y_integrable t (x i)).mul_const _)]
  simp only [integral_mul_const,integral_sameCube_y,one_mul,cellPressure]

lemma integral_cubeDensity_t (x : Fin N → d → ℝ) (y : d → ℝ) :
    (∫ t : d → I, cubeDensity (fun a => (t a:ℝ)) x y) = ∑ i, cubeOverlap (x i-y) := by
  unfold cubeDensity
  rw [integral_finsetSum _ (fun i _ => sameCube_I_integrable (x i) y)]
  simp only [integral_sameCube]

end Work_CubeDensity_scope

open MeasureTheory Set Filter
open scoped BigOperators

variable {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]
  {μ : Measure A} {ν : Measure Y} [IsProbabilityMeasure μ] [SFinite ν]

theorem average_pressure
    {f : A → Y → ℝ} (hm : Measurable (Function.uncurry f))
    (hn : ∀ a y, 0 ≤ f a y) {C B : ℝ} (hc : ∀ a y, f a y ≤ C)
    (hi : ∀ a, Integrable (fun y => (f a y)^(5/3:ℝ)) ν)
    (hb : ∀ a, (∫ y, (f a y)^(5/3:ℝ) ∂ν) ≤ B) :
    Integrable (fun y => (∫ a, f a y ∂μ)^(5/3:ℝ)) ν ∧
      (∫ y, (∫ a, f a y ∂μ)^(5/3:ℝ) ∂ν) ≤ ∫ a, (∫ y, (f a y)^(5/3:ℝ) ∂ν) ∂μ := by
  have hpm : Measurable (fun p : A × Y => (f p.1 p.2)^(5/3:ℝ)) :=
    hm.pow_const _
  have hpi : Integrable (fun p : A × Y => (f p.1 p.2)^(5/3:ℝ)) (μ.prod ν) := by
    apply (integrable_prod_iff hpm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hi,?_⟩
    simp only [Real.norm_of_nonneg (Real.rpow_nonneg (hn _ _) _)]
    apply (integrable_const B).mono' hpm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    exact Eventually.of_forall fun a => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun y => Real.rpow_nonneg (hn a y) _))]
      exact hb a
  have hfi (y : Y) : Integrable (fun a => f a y) μ := by
    apply (integrable_const C).mono' (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact Eventually.of_forall (fun a => by change ‖f a y‖ ≤ C; rw [Real.norm_of_nonneg (hn a y)]; exact hc a y)
  have hpiy (y : Y) : Integrable (fun a => (f a y)^(5/3:ℝ)) μ := by
    apply (integrable_const ((max C 0)^(5/3:ℝ))).mono'
      (hpm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact Eventually.of_forall fun a => by
      change ‖(f a y)^(5/3:ℝ)‖ ≤ (max C 0)^(5/3:ℝ)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hn a y) _)]
      exact Real.rpow_le_rpow (hn a y) ((hc a y).trans (le_max_left _ _)) (by norm_num)
  have hj (y : Y) : (∫ a, f a y ∂μ)^(5/3:ℝ) ≤ ∫ a, (f a y)^(5/3:ℝ) ∂μ := by
    apply (convexOn_rpow (by norm_num : (1:ℝ) ≤ 5/3)).map_integral_le
      (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 5/3)).continuousOn isClosed_Ici (Eventually.of_forall (fun a => hn a y)) (hfi y) (hpiy y)
  have han (y : Y) : 0 ≤ (∫ a, f a y ∂μ)^(5/3:ℝ) :=
    Real.rpow_nonneg (integral_nonneg (fun a => hn a y)) _
  have hai : Integrable (fun y => (∫ a, f a y ∂μ)^(5/3:ℝ)) ν := by
    apply hpi.integral_prod_right.mono'
      (hm.stronglyMeasurable.integral_prod_left'.measurable.pow_const _).aestronglyMeasurable
    exact Eventually.of_forall (fun y => by change ‖(∫ a, f a y ∂μ)^(5/3:ℝ)‖ ≤ ∫ a, (f a y)^(5/3:ℝ) ∂μ; rw [Real.norm_of_nonneg (han y)]; exact hj y)
  refine ⟨hai,?_⟩
  calc
    _ ≤ ∫ y, ∫ a, (f a y)^(5/3:ℝ) ∂μ ∂ν := integral_mono hai hpi.integral_prod_right hj
    _ = _ := (integral_integral_swap hpi).symm

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_CubeRotations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CubeRotations_scope

open MeasureTheory Set
open scoped BigOperators

abbrev CubeSpace := EuclideanSpace ℝ (Fin 3)

abbrev CubeRotation := unitary (CubeSpace →L[ℝ] CubeSpace)

instance cubeSpace_continuousStar : ContinuousStar (CubeSpace →L[ℝ] CubeSpace) :=
  ⟨(ContinuousLinearMap.adjoint : (CubeSpace →L[ℝ] CubeSpace) ≃ₗᵢ⋆[ℝ] _).continuous⟩

instance cubeRotation_compact : CompactSpace CubeRotation := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : CubeSpace →L[ℝ] CubeSpace) 1).of_isClosed_subset isClosed_unitary
  intro u hu
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (CStarRing.norm_coe_unitary (⟨u,hu⟩ : CubeRotation)).le

def cubeRotationMeasure : Measure CubeRotation :=
  Measure.haarMeasure (⟨⟨univ,isCompact_univ⟩,by simp⟩ : TopologicalSpace.PositiveCompacts CubeRotation)

instance cubeRotation_probability : IsProbabilityMeasure cubeRotationMeasure :=
  ⟨by exact Measure.haarMeasure_self⟩

instance cubeRotation_leftInvariant : cubeRotationMeasure.IsMulLeftInvariant := by
  unfold cubeRotationMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def rotationIsometry (R : CubeRotation) : CubeSpace ≃ₗᵢ[ℝ] CubeSpace :=
  Unitary.linearIsometryEquiv R

@[simp] lemma rotationIsometry_apply (R : CubeRotation) (x : CubeSpace) :
    rotationIsometry R x = (R : CubeSpace →L[ℝ] CubeSpace) x := rfl

lemma rotationIsometry_continuous : Continuous (fun p : CubeRotation × CubeSpace => rotationIsometry p.1 p.2) :=
  Continuous.clm_apply (continuous_subtype_val.comp continuous_fst) continuous_snd

lemma rotationIsometry_inv_mul (R S : CubeRotation) (x : CubeSpace) :
    rotationIsometry (S*R)⁻¹ (rotationIsometry S x) = rotationIsometry R⁻¹ x := by
  have he : (S*R)⁻¹*S = R⁻¹ := by simp
  have hh := congrArg (fun U : CubeRotation => rotationIsometry U x) he
  exact hh

end Work_CubeRotations_scope

open MeasureTheory Set Filter
open scoped BigOperators

def radialAverage (k : CubeSpace → ℝ) (x : CubeSpace) : ℝ :=
  ∫ R : CubeRotation, k (rotationIsometry R⁻¹ x) ∂cubeRotationMeasure

lemma radialAverage_joint_measurable {k : CubeSpace → ℝ} (hk : Measurable k) :
    Measurable (fun p : CubeRotation × CubeSpace => k (rotationIsometry p.1⁻¹ p.2)) :=
  hk.comp (rotationIsometry_continuous.comp
    ((continuous_inv.comp continuous_fst).prodMk continuous_snd)).measurable

lemma radialAverage_measurable {k : CubeSpace → ℝ} (hk : Measurable k) :
    Measurable (radialAverage k) :=
  (radialAverage_joint_measurable hk).stronglyMeasurable.integral_prod_left'.measurable

lemma radialAverage_section_integrable {k : CubeSpace → ℝ} (hk : Measurable k)
    {B : ℝ} (hB : ∀ x, ‖k x‖ ≤ B) (x : CubeSpace) :
    Integrable (fun R : CubeRotation => k (rotationIsometry R⁻¹ x)) cubeRotationMeasure := by
  apply (integrable_const B).mono'
    ((radialAverage_joint_measurable hk).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  exact Eventually.of_forall (fun R => hB _)

lemma radialAverage_nonneg {k : CubeSpace → ℝ} (hk : ∀ x, 0 ≤ k x) (x : CubeSpace) :
    0 ≤ radialAverage k x := integral_nonneg (fun _ => hk _)

lemma radialAverage_le {k : CubeSpace → ℝ} (hm : Measurable k) (hn : ∀ x, 0 ≤ k x)
    {B : ℝ} (hB : ∀ x, k x ≤ B) (x : CubeSpace) : radialAverage k x ≤ B := by
  have hi := radialAverage_section_integrable hm (fun x => by rw [Real.norm_of_nonneg (hn x)]; exact hB x) x
  calc
    _ ≤ ∫ _R : CubeRotation, B ∂cubeRotationMeasure :=
      integral_mono hi (integrable_const _) (fun _ => hB _)
    _ = B := by simp

lemma radialAverage_rotation (k : CubeSpace → ℝ) (S : CubeRotation) (x : CubeSpace) :
    radialAverage k (rotationIsometry S x) = radialAverage k x := by
  unfold radialAverage
  rw [←integral_mul_left_eq_self (fun R : CubeRotation => k (rotationIsometry R⁻¹ (rotationIsometry S x))) S]
  simp only [rotationIsometry_inv_mul]

lemma radialAverage_radial (k : CubeSpace → ℝ) {x y : CubeSpace} (h : ‖x‖ = ‖y‖) :
    radialAverage k x = radialAverage k y := by
  let S : CubeRotation := Unitary.linearIsometryEquiv.symm ((ℝ ∙ (x-y))ᗮ.reflection)
  have he : rotationIsometry S x = y := by
    change (Unitary.linearIsometryEquiv (Unitary.linearIsometryEquiv.symm _)) x = y
    rw [MulEquiv.apply_symm_apply]
    exact Submodule.reflection_sub h
  rw [←he,radialAverage_rotation]

lemma radialAverage_support {k : CubeSpace → ℝ} {r : ℝ}
    (hs : ∀ x, r ≤ ‖x‖ → k x = 0) (x : CubeSpace) (hx : r ≤ ‖x‖) :
    radialAverage k x = 0 := by
  unfold radialAverage
  have he (R : CubeRotation) : k (rotationIsometry R⁻¹ x) = 0 :=
    hs _ (by simpa only [LinearIsometryEquiv.norm_map] using hx)
  simp only [he,integral_zero]

lemma radialAverage_joint_integrable {k : CubeSpace → ℝ} (hm : Measurable k) (hk : Integrable k) :
    Integrable (fun p : CubeRotation × CubeSpace => k (rotationIsometry p.1⁻¹ p.2))
      (cubeRotationMeasure.prod volume) := by
  apply (integrable_prod_iff (radialAverage_joint_measurable hm).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall (fun R => ((rotationIsometry R⁻¹).measurePreserving.integrable_comp hk.aestronglyMeasurable).2 hk)
  · have he (R : CubeRotation) : (∫ x, ‖k (rotationIsometry R⁻¹ x)‖) = ∫ x, ‖k x‖ :=
      (rotationIsometry R⁻¹).measurePreserving.integral_comp
        (rotationIsometry R⁻¹).toHomeomorph.measurableEmbedding (fun x => ‖k x‖)
    simp only [he]
    exact integrable_const _

lemma integral_radialAverage {k : CubeSpace → ℝ} (hm : Measurable k) (hk : Integrable k) :
    (∫ x, radialAverage k x) = ∫ x, k x := by
  unfold radialAverage
  rw [←integral_integral_swap (radialAverage_joint_integrable hm hk)]
  have he (R : CubeRotation) : (∫ x, k (rotationIsometry R⁻¹ x)) = ∫ x, k x :=
    (rotationIsometry R⁻¹).measurePreserving.integral_comp
      (rotationIsometry R⁻¹).toHomeomorph.measurableEmbedding k
  simp only [he]
  simp

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_FiniteMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators Topology

namespace CoulombNeumann

def finiteMean {ι E : Type*} [Fintype ι] [AddCommMonoid E] [Module ℝ E] (f : ι → E) : E :=
  (Fintype.card ι:ℝ)⁻¹ • ∑ i, f i

lemma finiteMean_const {ι E : Type*} [Fintype ι] [Nonempty ι]
    [AddCommMonoid E] [Module ℝ E] (x : E) : finiteMean (fun _ : ι => x) = x := by
  simp only [finiteMean,Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_smul,inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]

lemma finiteMean_norm_sq_le {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ι → E) :
    ‖finiteMean f‖^2 ≤ finiteMean (fun i => ‖f i‖^2) := by
  have hc : 0 < (Fintype.card ι:ℝ) := by exact_mod_cast Fintype.card_pos
  unfold finiteMean
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hc.le),mul_pow,smul_eq_mul]
  have hn := norm_sum_le Finset.univ f
  have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖f i‖)
  simp only [Finset.card_univ] at hs
  have hsq : ‖∑ i, f i‖^2 ≤ (∑ i,‖f i‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hh := mul_le_mul_of_nonneg_left (hsq.trans hs) (sq_nonneg (Fintype.card ι:ℝ)⁻¹)
  calc
    _ ≤ (Fintype.card ι:ℝ)⁻¹^2*((Fintype.card ι:ℝ)*∑ i, ‖f i‖^2) := hh
    _ = _ := by field_simp

lemma finiteMean_tendsto {ι α E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {l : Filter α}
    {f : α → ι → E} {g : ι → E} (h : ∀ i, Filter.Tendsto (fun a => f a i) l (𝓝 (g i))) :
    Filter.Tendsto (fun a => finiteMean (f a)) l (𝓝 (finiteMean g)) := by
  exact (tendsto_finsetSum Finset.univ (fun i _ => h i)).const_smul _

lemma finiteMean_memLp {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    {μ : Measure α} {f : ι → α → ℂ} (h : ∀ i, MemLp (f i) 2 μ) :
    MemLp (fun x => finiteMean (fun i => f i x)) 2 μ := by
  exact (memLp_finsetSum Finset.univ (fun i _ => h i)).const_smul _

lemma finiteMean_integral_norm_sq_le {ι α : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace α] {μ : Measure α} {f : ι → α → ℂ} (h : ∀ i, MemLp (f i) 2 μ) :
    (∫ x, ‖finiteMean (fun i => f i x)‖^2 ∂μ) ≤ finiteMean (fun i => ∫ x, ‖f i x‖^2 ∂μ) := by
  calc
    _ ≤ ∫ x, finiteMean (fun i => ‖f i x‖^2) ∂μ := by
      apply integral_mono (finiteMean_memLp h).norm.integrable_sq
        ((integrable_finsetSum _ (fun i _ => (h i).norm.integrable_sq)).const_mul _)
      exact fun x => finiteMean_norm_sq_le (fun i => f i x)
    _ = _ := by
      unfold finiteMean
      rw [integral_smul,integral_finsetSum _ (fun i _ => (h i).norm.integrable_sq)]

lemma sum_finiteMean {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid E] [Module ℝ E] (f : κ → ι → E) :
    (∑ j, finiteMean (f j)) = finiteMean (fun i => ∑ j, f j i) := by
  unfold finiteMean
  rw [←Finset.smul_sum,Finset.sum_comm]

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_HardyField
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

def hardyDenom (ε : ℝ) (x : Space) : ℝ := ‖x‖ ^ 2 + ε

lemma hardyDenom_pos {ε : ℝ} (hε : 0 < ε) (x : Space) : 0 < hardyDenom ε x := by
  dsimp [hardyDenom]
  positivity

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_Vartheta
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

def euclideanCubeOverlap (x : CubeSpace) : ℝ := cubeOverlap (WithLp.ofLp x)

lemma euclideanCubeOverlap_measurable : Measurable euclideanCubeOverlap :=
  cubeOverlap_measurable.comp (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable

lemma euclideanCubeOverlap_integrable : Integrable euclideanCubeOverlap :=
  ((PiLp.volume_preserving_ofLp (Fin 3)).integrable_comp cubeOverlap_measurable.aestronglyMeasurable).2 cubeOverlap_integrable

lemma integral_euclideanCubeOverlap : (∫ x, euclideanCubeOverlap x) = 1 := by
  change (∫ x : CubeSpace, cubeOverlap (WithLp.ofLp x)) = 1
  rw [(PiLp.volume_preserving_ofLp (Fin 3)).integral_comp
    (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).measurableEmbedding, integral_cubeOverlap]

lemma euclideanCubeOverlap_support (x : CubeSpace) (hx : Real.sqrt 3 ≤ ‖x‖) :
    euclideanCubeOverlap x = 0 := by
  obtain ⟨i,hi⟩ : ∃ i : Fin 3, 1 ≤ |x i| := by
    by_contra! h
    have hs : ∑ i : Fin 3, (x i)^2 < ∑ _i : Fin 3, (1:ℝ) := by
      apply Finset.sum_lt_sum
      · intro i _
        nlinarith [abs_nonneg (x i),sq_abs (x i),h i]
      · exact ⟨0,Finset.mem_univ _,by nlinarith [abs_nonneg (x 0),sq_abs (x 0),h 0]⟩
    have hh := (Real.sqrt_le_iff.mp hx).2
    rw [EuclideanSpace.real_norm_sq_eq] at hh
    norm_num at hs
    linarith
  exact cubeOverlap_support_coord _ i hi

def vartheta : CubeSpace → ℝ := radialAverage euclideanCubeOverlap

lemma vartheta_measurable : Measurable vartheta := radialAverage_measurable euclideanCubeOverlap_measurable
lemma vartheta_nonneg (x : CubeSpace) : 0 ≤ vartheta x := radialAverage_nonneg (fun _x => cubeOverlap_nonneg _) x
lemma vartheta_le (x : CubeSpace) : vartheta x ≤ 1 := radialAverage_le euclideanCubeOverlap_measurable
  (fun _x => cubeOverlap_nonneg _) (fun _x => cubeOverlap_le _) x
lemma integral_vartheta : (∫ x, vartheta x) = 1 := by
  rw [vartheta,integral_radialAverage euclideanCubeOverlap_measurable euclideanCubeOverlap_integrable,
    integral_euclideanCubeOverlap]
lemma vartheta_radial {x y : CubeSpace} (h : ‖x‖=‖y‖) : vartheta x=vartheta y := radialAverage_radial _ h
lemma vartheta_support (x : CubeSpace) (hx : Real.sqrt 3 ≤ ‖x‖) : vartheta x=0 :=
  radialAverage_support euclideanCubeOverlap_support x hx

def varthetaScaled (b : ℝ) (x : CubeSpace) : ℝ := b⁻¹^3*vartheta (b⁻¹ • x)

lemma varthetaScaled_measurable (b : ℝ) : Measurable (varthetaScaled b) :=
  measurable_const.mul (vartheta_measurable.comp ((continuous_id.const_smul (b⁻¹:ℝ)).measurable))
lemma varthetaScaled_nonneg {b : ℝ} (hb : 0 < b) (x : CubeSpace) : 0 ≤ varthetaScaled b x :=
  mul_nonneg (by positivity) (vartheta_nonneg _)
lemma varthetaScaled_le {b : ℝ} (hb : 0 < b) (x : CubeSpace) : varthetaScaled b x ≤ b⁻¹^3 :=
  mul_le_of_le_one_right (by positivity) (vartheta_le _)
lemma integral_varthetaScaled {b : ℝ} (hb : 0 < b) : (∫ x, varthetaScaled b x) = 1 := by
  unfold varthetaScaled
  rw [integral_const_mul,Measure.integral_comp_smul_of_nonneg volume vartheta b⁻¹ (hR := by positivity)]
  simp [integral_vartheta,hb.ne']
lemma varthetaScaled_radial (b : ℝ) {x y : CubeSpace} (h : ‖x‖=‖y‖) :
    varthetaScaled b x=varthetaScaled b y := by
  unfold varthetaScaled
  exact congrArg (fun z => b⁻¹^3*z) (vartheta_radial (x := b⁻¹ • x) (y := b⁻¹ • y) (by simp only [norm_smul,h]))
lemma varthetaScaled_support {b : ℝ} (hb : 0 < b) (x : CubeSpace)
    (hx : Real.sqrt 3*b ≤ ‖x‖) : varthetaScaled b x=0 := by
  unfold varthetaScaled
  rw [vartheta_support _ (by
    rw [norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ b⁻¹)]
    exact (le_inv_mul_iff₀ hb).2 (by simpa only [mul_comm] using hx)),mul_zero]

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

variable {N : ℕ}

lemma cubeDensity_measurable :
    Measurable (fun p : (Fin 3 → ℝ) × ((Fin N → Fin 3 → ℝ) × (Fin 3 → ℝ)) => cubeDensity p.1 p.2.1 p.2.2) := by
  unfold cubeDensity
  apply Finset.measurable_sum
  intro i _
  have hm : Measurable (fun p : (Fin 3 → ℝ) × ((Fin N → Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      (p.1,(p.2.1 i,p.2.2))) := by fun_prop
  exact (sameCube_measurable (d := Fin 3)).comp hm

lemma cubeAssignment_measurable :
    Measurable (fun p : (Fin 3 → ℝ) × (Fin N → Fin 3 → ℝ) => cubeAssignment p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  exact cubeIndex_measurable.comp (((measurable_pi_apply i).comp measurable_snd).sub measurable_fst)

lemma cubePressure_measurable :
    Measurable (fun p : (Fin 3 → ℝ) × (Fin N → Fin 3 → ℝ) => cellPressure (cubeAssignment p.1 p.2)) :=
  (measurable_of_countable cellPressure).comp cubeAssignment_measurable

lemma cube_t_continuous : Continuous (fun t : Fin 3 → I => fun a => (t a:ℝ)) :=
  continuous_pi (fun a => continuous_subtype_val.comp (continuous_apply a))

lemma translation_average_pressure (x : Fin N → Fin 3 → ℝ) :
    Integrable (fun y => (∑ i, cubeOverlap (x i-y))^(5/3:ℝ)) ∧
    (∫ y, (∑ i, cubeOverlap (x i-y))^(5/3:ℝ)) ≤
      ∫ t : Fin 3 → I, cellPressure (cubeAssignment (fun a => (t a:ℝ)) x) := by
  have hm : Measurable (fun p : (Fin 3 → I) × (Fin 3 → ℝ) =>
      cubeDensity (fun a => (p.1 a:ℝ)) x p.2) :=
    cubeDensity_measurable.comp ((cube_t_continuous.measurable.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))
  have hn (t : Fin 3 → I) (y : Fin 3 → ℝ) : 0 ≤ cubeDensity (fun a => (t a:ℝ)) x y := cubeDensity_nonneg _ _ _
  have hc (t : Fin 3 → I) (y : Fin 3 → ℝ) : cubeDensity (fun a => (t a:ℝ)) x y ≤ N := cubeDensity_le _ _ _
  have hi (t : Fin 3 → I) : Integrable (fun y : Fin 3 → ℝ => cubeDensity (fun a => (t a:ℝ)) x y^(5/3:ℝ)) := cubeDensity_rpow_integrable _ _
  have hb (t : Fin 3 → I) : (∫ y : Fin 3 → ℝ, cubeDensity (fun a => (t a:ℝ)) x y^(5/3:ℝ)) ≤ (N:ℝ)^(5/3:ℝ) := by
    rw [integral_cubeDensity_rpow]
    exact cellPressure_le _
  have h := average_pressure (μ := volume) (ν := volume)
    (f := fun (t : Fin 3 → I) (y : Fin 3 → ℝ) => cubeDensity (fun a => (t a:ℝ)) x y) hm hn hc hi hb
  simpa only [integral_cubeDensity_t,integral_cubeDensity_rpow] using h

def varthetaSmear (x : Fin N → CubeSpace) (y : CubeSpace) : ℝ :=
  ∑ i, vartheta (x i-y)

def rotatedCubeCloud (R : CubeRotation) (x : Fin N → CubeSpace) : Fin N → Fin 3 → ℝ :=
  fun i => WithLp.ofLp (rotationIsometry R⁻¹ (x i))

def translatedPressureAverage (x : Fin N → Fin 3 → ℝ) : ℝ :=
  ∫ t : Fin 3 → I, cellPressure (cubeAssignment (fun a => (t a:ℝ)) x)

lemma translatedPressureAverage_measurable : Measurable (translatedPressureAverage (N := N)) := by
  exact (cubePressure_measurable.comp
    ((cube_t_continuous.measurable.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable.integral_prod_left'.measurable

lemma translatedPressureAverage_nonneg (x : Fin N → Fin 3 → ℝ) : 0 ≤ translatedPressureAverage x :=
  integral_nonneg (fun _ => cellPressure_nonneg _)
lemma translatedPressureAverage_le (x : Fin N → Fin 3 → ℝ) : translatedPressureAverage x ≤ (N:ℝ)^(5/3:ℝ) := by
  have hi : Integrable (fun t : Fin 3 → I => cellPressure (cubeAssignment (fun a => (t a:ℝ)) x)) := by
    apply (integrable_const ((N:ℝ)^(5/3:ℝ))).mono'
      ((cubePressure_measurable.comp (cube_t_continuous.measurable.prodMk measurable_const))).aestronglyMeasurable
    exact Eventually.of_forall (fun t => by change ‖cellPressure _‖ ≤ _; rw [Real.norm_of_nonneg (cellPressure_nonneg _)]; exact cellPressure_le _)
  exact (integral_mono hi (integrable_const _) (fun _ => cellPressure_le _)).trans_eq (by simp)

lemma rotatedCubeCloud_continuous :
    Continuous (fun p : CubeRotation × (Fin N → CubeSpace) => rotatedCubeCloud p.1 p.2) := by
  apply continuous_pi
  intro i
  exact (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp
    (rotationIsometry_continuous.comp ((continuous_inv.comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd)))

lemma varthetaSmear_translation_rotation (x : Fin N → CubeSpace) (y : CubeSpace) :
    varthetaSmear x y = ∫ R : CubeRotation,
      (∑ i, cubeOverlap (rotatedCubeCloud R x i-WithLp.ofLp (rotationIsometry R⁻¹ y))) ∂cubeRotationMeasure := by
  have he (R : CubeRotation) (i : Fin N) :
      cubeOverlap (rotatedCubeCloud R x i-WithLp.ofLp (rotationIsometry R⁻¹ y)) =
        euclideanCubeOverlap (rotationIsometry R⁻¹ (x i-y)) := by
    unfold euclideanCubeOverlap rotatedCubeCloud
    rw [map_sub]
    rfl
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => radialAverage_section_integrable euclideanCubeOverlap_measurable (B := 1)
    (fun z => by change ‖cubeOverlap (WithLp.ofLp z)‖ ≤ 1; rw [Real.norm_of_nonneg (cubeOverlap_nonneg _)]; exact cubeOverlap_le _) (x i-y))]
  rfl

lemma cubeOverlap_sum_le (x : Fin N → Fin 3 → ℝ) (y : Fin 3 → ℝ) :
    (∑ i, cubeOverlap (x i-y)) ≤ N := by
  calc
    _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => cubeOverlap_le _)
    _ = _ := by simp

lemma rotatedCloud_coordinates_preserving (R : CubeRotation) :
    MeasurePreserving (fun y : CubeSpace => WithLp.ofLp (rotationIsometry R⁻¹ y)) :=
  (PiLp.volume_preserving_ofLp (Fin 3)).comp (rotationIsometry R⁻¹).measurePreserving

lemma rotatedCloud_coordinates_embedding (R : CubeRotation) :
    MeasurableEmbedding (fun y : CubeSpace => WithLp.ofLp (rotationIsometry R⁻¹ y)) :=
  (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).measurableEmbedding.comp
    (rotationIsometry R⁻¹).toHomeomorph.measurableEmbedding

lemma rotatedCloud_density_measurable (x : Fin N → CubeSpace) :
    Measurable (fun p : CubeRotation × CubeSpace =>
      ∑ i, cubeOverlap (rotatedCubeCloud p.1 x i-WithLp.ofLp (rotationIsometry p.1⁻¹ p.2))) := by
  apply Finset.measurable_sum
  intro i _
  exact cubeOverlap_measurable.comp
    (((measurable_pi_apply i).comp (rotatedCubeCloud_continuous.measurable.comp
      (measurable_fst.prodMk measurable_const))).sub
        ((PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
          (rotationIsometry_continuous.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd)).measurable))

def radialPressureAverage (x : Fin N → CubeSpace) : ℝ :=
  ∫ R : CubeRotation, translatedPressureAverage (rotatedCubeCloud R x) ∂cubeRotationMeasure

lemma radialPressureAverage_measurable : Measurable (radialPressureAverage (N := N)) :=
  (translatedPressureAverage_measurable.comp rotatedCubeCloud_continuous.measurable).stronglyMeasurable.integral_prod_left'.measurable

lemma radialPressureAverage_nonneg (x : Fin N → CubeSpace) : 0 ≤ radialPressureAverage x :=
  integral_nonneg (fun _ => translatedPressureAverage_nonneg _)

lemma translatedPressureAverage_rotation_integrable (x : Fin N → CubeSpace) :
    Integrable (fun R : CubeRotation => translatedPressureAverage (rotatedCubeCloud R x)) cubeRotationMeasure := by
  apply (integrable_const ((N:ℝ)^(5/3:ℝ))).mono'
    ((translatedPressureAverage_measurable.comp rotatedCubeCloud_continuous.measurable).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  exact Eventually.of_forall (fun R => by
    change ‖translatedPressureAverage _‖ ≤ _
    rw [Real.norm_of_nonneg (translatedPressureAverage_nonneg _)]
    exact translatedPressureAverage_le _)

lemma radialPressureAverage_le (x : Fin N → CubeSpace) : radialPressureAverage x ≤ (N:ℝ)^(5/3:ℝ) := by
  exact (integral_mono (translatedPressureAverage_rotation_integrable x) (integrable_const _)
    (fun _ => translatedPressureAverage_le _)).trans_eq (by simp)

theorem varthetaSmear_pressure (x : Fin N → CubeSpace) :
    Integrable (fun y => varthetaSmear x y^(5/3:ℝ)) ∧
      (∫ y, varthetaSmear x y^(5/3:ℝ)) ≤ radialPressureAverage x := by
  let f (R : CubeRotation) (y : CubeSpace) : ℝ :=
    ∑ i, cubeOverlap (rotatedCubeCloud R x i-WithLp.ofLp (rotationIsometry R⁻¹ y))
  have hn (R : CubeRotation) (y : CubeSpace) : 0 ≤ f R y :=
    Finset.sum_nonneg (fun _ _ => cubeOverlap_nonneg _)
  have hi (R : CubeRotation) : Integrable (fun y => f R y^(5/3:ℝ)) :=
    ((rotatedCloud_coordinates_preserving R).integrable_comp
      (translation_average_pressure (rotatedCubeCloud R x)).1.aestronglyMeasurable).2
        (translation_average_pressure (rotatedCubeCloud R x)).1
  have he (R : CubeRotation) : (∫ y, f R y^(5/3:ℝ)) =
      ∫ y, (∑ i, cubeOverlap (rotatedCubeCloud R x i-y))^(5/3:ℝ) :=
    (rotatedCloud_coordinates_preserving R).integral_comp (rotatedCloud_coordinates_embedding R)
      (fun y => (∑ i, cubeOverlap (rotatedCubeCloud R x i-y))^(5/3:ℝ))
  have hb (R : CubeRotation) : (∫ y, f R y^(5/3:ℝ)) ≤ translatedPressureAverage (rotatedCubeCloud R x) := by
    rw [he]
    exact (translation_average_pressure _).2
  have hp := average_pressure (μ := cubeRotationMeasure) (rotatedCloud_density_measurable x)
    hn (fun R y => cubeOverlap_sum_le _ _)
    hi (fun R => (hb R).trans (translatedPressureAverage_le _))
  have hae (y : CubeSpace) : (∫ R, f R y ∂cubeRotationMeasure) = varthetaSmear x y :=
    (varthetaSmear_translation_rotation x y).symm
  change Integrable (fun y => (∫ R, f R y ∂cubeRotationMeasure)^(5/3:ℝ)) ∧
    (∫ y, (∫ R, f R y ∂cubeRotationMeasure)^(5/3:ℝ)) ≤
      ∫ R, (∫ y, f R y^(5/3:ℝ)) ∂cubeRotationMeasure at hp
  simp_rw [hae] at hp
  refine ⟨hp.1,hp.2.trans ?_⟩
  apply integral_mono_of_nonneg
    (Eventually.of_forall (fun R => integral_nonneg (fun y => Real.rpow_nonneg (hn R y) _)))
    (translatedPressureAverage_rotation_integrable x)
    (Eventually.of_forall hb)

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ScaledSmearPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

namespace CoulombNeumann
variable {N : ℕ}

lemma vartheta_even (x : CubeSpace) : vartheta (-x) = vartheta x :=
  vartheta_radial (norm_neg x)

def physicalSmear (b : ℝ) (x : Fin N → CubeSpace) (y : CubeSpace) : ℝ :=
  ∑ i, varthetaScaled b (y-x i)

lemma physicalSmear_nonneg {b : ℝ} (hb : 0 < b) (x : Fin N → CubeSpace) (y : CubeSpace) :
    0 ≤ physicalSmear b x y := Finset.sum_nonneg (fun _ _ => varthetaScaled_nonneg hb _)
lemma physicalSmear_measurable (b : ℝ) :
    Measurable (fun p : (Fin N → CubeSpace) × CubeSpace => physicalSmear b p.1 p.2) := by
  unfold physicalSmear
  apply Finset.measurable_sum
  intro i _
  exact (varthetaScaled_measurable b).comp
    (measurable_snd.sub ((measurable_pi_apply i).comp measurable_fst))

lemma physicalSmear_scaled (b : ℝ) (x : Fin N → CubeSpace) (y : CubeSpace) :
    physicalSmear b x y = b⁻¹^3*varthetaSmear (fun i => b⁻¹ • x i) (b⁻¹ • y) := by
  unfold physicalSmear varthetaScaled varthetaSmear
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_sub]
  congr 1
  simpa only [neg_sub] using (vartheta_even (b⁻¹ • x i-b⁻¹ • y))

lemma inverse_cube_rpow {b : ℝ} (hb : 0 < b) : (b⁻¹^3)^(5/3:ℝ) = b⁻¹^5 := by
  rw [←Real.rpow_natCast_mul (by positivity : 0 ≤ b⁻¹)]
  norm_num

lemma physicalSmear_rpow {b : ℝ} (hb : 0 < b) (x : Fin N → CubeSpace) (y : CubeSpace) :
    physicalSmear b x y^(5/3:ℝ) = b⁻¹^5*varthetaSmear (fun i => b⁻¹ • x i) (b⁻¹ • y)^(5/3:ℝ) := by
  rw [physicalSmear_scaled,Real.mul_rpow (by positivity)
    (show 0 ≤ varthetaSmear (fun i => b⁻¹ • x i) (b⁻¹ • y) from
      Finset.sum_nonneg (fun _ _ => vartheta_nonneg _)),inverse_cube_rpow hb]

lemma physicalSmear_pressure_integrable {b : ℝ} (hb : 0 < b) (x : Fin N → CubeSpace) :
    Integrable (fun y => physicalSmear b x y^(5/3:ℝ)) := by
  simp_rw [physicalSmear_rpow hb]
  exact ((varthetaSmear_pressure (fun i => b⁻¹ • x i)).1.comp_smul (inv_ne_zero hb.ne')).const_mul _

lemma integral_physicalSmear_pressure {b : ℝ} (hb : 0 < b) (x : Fin N → CubeSpace) :
    (∫ y, physicalSmear b x y^(5/3:ℝ)) = b⁻¹^2*(∫ y, varthetaSmear (fun i => b⁻¹ • x i) y^(5/3:ℝ)) := by
  simp_rw [physicalSmear_rpow hb]
  rw [integral_const_mul,Measure.integral_comp_smul_of_nonneg volume
    (fun y => varthetaSmear (fun i => b⁻¹ • x i) y^(5/3:ℝ)) b⁻¹ (hR := by positivity)]
  simp only [finrank_euclideanSpace_fin,smul_eq_mul]
  field_simp [hb.ne']

def physicalPressure (b : ℝ) (x : Fin N → CubeSpace) : ℝ :=
  ∫ y, physicalSmear b x y^(5/3:ℝ)

def physicalPressureAverage (b : ℝ) (x : Fin N → CubeSpace) : ℝ :=
  b⁻¹^2*radialPressureAverage (fun i => b⁻¹ • x i)

lemma physicalPressure_measurable (b : ℝ) : Measurable (physicalPressure (N := N) b) :=
  ((physicalSmear_measurable b).pow_const _).stronglyMeasurable.integral_prod_right.measurable
lemma physicalPressure_nonneg {b : ℝ} (hb : 0 < b) (x : Fin N → CubeSpace) :
    0 ≤ physicalPressure b x :=
  integral_nonneg (fun y => Real.rpow_nonneg (physicalSmear_nonneg hb x y) _)
lemma physicalPressureAverage_measurable (b : ℝ) : Measurable (physicalPressureAverage (N := N) b) := by
  apply measurable_const.mul
  apply radialPressureAverage_measurable.comp
  exact Measurable.of_eval (fun i => (measurable_pi_apply i).const_smul b⁻¹)
lemma physicalPressureAverage_nonneg (b : ℝ) (x : Fin N → CubeSpace) : 0 ≤ physicalPressureAverage b x :=
  mul_nonneg (sq_nonneg _) (radialPressureAverage_nonneg _)
lemma physicalPressureAverage_le (b : ℝ) (x : Fin N → CubeSpace) :
    physicalPressureAverage b x ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ) :=
  mul_le_mul_of_nonneg_left (radialPressureAverage_le _) (sq_nonneg _)

theorem physicalPressure_le_average {b : ℝ} (hb : 0 < b) (x : Fin N → CubeSpace) :
    physicalPressure b x ≤ physicalPressureAverage b x := by
  unfold physicalPressure physicalPressureAverage
  rw [integral_physicalSmear_pressure hb]
  exact mul_le_mul_of_nonneg_left (varthetaSmear_pressure _).2 (sq_nonneg _)

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SliceLp
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
section SliceLp
variable {E F : Type*} [MeasureSpace E] [MeasureSpace F]
  [SFinite (volume : Measure E)] [SFinite (volume : Measure F)]

lemma memLp_slice_left {f : E × F → ℂ} (hf : MemLp f 2) :
    ∀ᵐ y, MemLp (fun x => f (x, y)) 2 := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  filter_upwards [hf.aestronglyMeasurable.prodMk_right, hi.prod_left_ae] with y hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hi

end SliceLp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Slices
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

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure] in
lemma smooth_test_product {φ : E → ℝ} {ψ : F → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ∞ (fun p : E × F => φ p.1 * ψ p.2) ∧
    HasCompactSupport (fun p : E × F => φ p.1 * ψ p.2) := by
  refine ⟨(hφ.comp contDiff_fst).mul (hψ.comp contDiff_snd), ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact (hcφ.prod hcψ)
  rintro ⟨x,y⟩ hxy
  exact ⟨subset_tsupport _ ((mul_ne_zero_iff.mp hxy).1),
    subset_tsupport _ ((mul_ne_zero_iff.mp hxy).2)⟩

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure] in
lemma lineDeriv_test_product {φ : E → ℝ} {ψ : F → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (v : E) (p : E × F) :
    lineDeriv ℝ (fun p : E × F => φ p.1 * ψ p.2) p (v,0) =
      lineDeriv ℝ φ p.1 v * ψ p.2 := by
  have h1 := (hφ.differentiable (by simp) p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have h2 := (hψ.differentiable (by simp) p.2).hasFDerivAt.comp p hasFDerivAt_snd
  have hh := ((h1.mul h2).hasLineDerivAt (v,0)).lineDeriv
  have he : (φ ∘ Prod.fst * ψ ∘ Prod.snd) = (fun p : E × F => φ p.1 * ψ p.2) := rfl
  rw [he] at hh
  rw [(hφ.differentiable (by simp) p.1).lineDeriv_eq_fderiv]
  simpa [Function.comp_def, Pi.mul_apply, mul_comm] using hh

end

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

def configurationJoin (N M : ℕ) :
    (Configuration N × Configuration M) ≃L[ℝ] Configuration (N+M) :=
  (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin N) (Fin M) (fun _ => Space)).symm.trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (N+M) => Space) finSumFinEquiv)

lemma configurationJoin_preserving (N M : ℕ) : MeasurePreserving (configurationJoin N M) :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin (N+M) => Space) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin N ⊕ Fin M => Space))

def corePerm {N : ℕ} (M : ℕ) (π : Equiv.Perm (Fin N)) : Equiv.Perm (Fin (N+M)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr π (Equiv.refl (Fin M)))

lemma corePerm_sign {N : ℕ} (M : ℕ) (π : Equiv.Perm (Fin N)) :
    Equiv.Perm.sign (corePerm M π) = Equiv.Perm.sign π := by
  simp [corePerm, Equiv.Perm.sign_sumCongr]


open Set Filter Topology InnerProductSpace Laplacian

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Pointwise
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
namespace CoulombAtom

variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma finite_complex_partition (p : J → ℝ) (hp : ∑ j, p j ^ 2 = 1) (z : ℂ) :
    ∑ j, ‖(p j : ℂ) * z‖ ^ 2 = ‖z‖ ^ 2 := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    ← Finset.sum_mul, hp, one_mul]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_TrialSmoothTest
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

lemma norm_real_mul_sq (r : ℝ) (z : ℂ) : ‖(r : ℂ) * z‖ ^ 2 = r ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_Electrostatic
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

def pairPotential {N : ℕ} (x : Configuration N) : ℝ :=
  ∑ i, ∑ j, if j < i then 1 / ‖x i - x j‖ else 0

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_IntegratedStability
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

lemma linearMap_ne_zero_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (P : E →L[ℝ] Space) (hP : P ≠ 0) : ∀ᵐ x : E, P x ≠ 0 := by
  rw [ae_iff]
  have hk : P.toLinearMap.ker ≠ ⊤ := by
    rw [Ne, LinearMap.ker_eq_top]
    intro h
    apply hP
    ext1 x
    exact LinearMap.congr_fun h x
  have he : {a | P a = 0} = (P.toLinearMap.ker : Set E) := by
    ext x
    rfl
  simpa only [not_not, he] using
    Measure.addHaar_submodule (volume : Measure E) P.toLinearMap.ker hk

lemma configuration_ae_nonsingular (N : ℕ) :
    ∀ᵐ x : Configuration N, (∀ i, x i ≠ 0) ∧ Function.Injective x := by
  have h0 : ∀ i : Fin N, ∀ᵐ x : Configuration N, x i ≠ 0 := by
    intro i
    apply linearMap_ne_zero_ae (ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space)
    intro h
    have hh := congrArg (fun F : Configuration N →L[ℝ] Space => F (direction i 0)) h
    have ht := congrArg (fun y : Space => y 0) hh
    simp [direction, EuclideanSpace.single] at ht
  have hp : ∀ i j : Fin N, ∀ᵐ x : Configuration N, i ≠ j → x i ≠ x j := by
    intro i j
    by_cases hij : i = j
    · subst j; exact Eventually.of_forall fun _ => by simp
    · have hh := linearMap_ne_zero_ae
        ((ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space) - ContinuousLinearMap.proj j)
        (by
          intro h
          have hq := congrArg (fun F : Configuration N →L[ℝ] Space => F (direction i 0)) h
          have ht := congrArg (fun y : Space => y 0) hq
          simp [direction, Ne.symm hij, EuclideanSpace.single] at ht)
      filter_upwards [hh] with x hx
      exact fun _ => sub_ne_zero.mp hx
  filter_upwards [ae_all_iff.mpr h0, ae_all_iff.mpr fun i => ae_all_iff.mpr (hp i)] with x hx hxp
  refine ⟨hx, ?_⟩
  intro i j hij
  by_contra h
  exact hxp i j h hij

def PriceMinimizes (E : ℕ → ℝ) (lam : ℝ) (n : ℕ) : Prop :=
  ∀ k : ℕ, E n + lam * n ≤ E k + lam * k

def priceEnergy (E : ℕ → ℝ) (lam : ℝ) : ℝ := sInf (Set.range (fun n : ℕ => E n + lam * n))

theorem priceEnergy_eq_of_minimizes {E : ℕ → ℝ} {lam : ℝ} {n : ℕ}
    (hn : PriceMinimizes E lam n) : priceEnergy E lam = E n + lam * n := by
  have hb : BddBelow (Set.range (fun k : ℕ => E k + lam * k)) := by
    refine ⟨E n + lam * n, ?_⟩
    rintro e ⟨k, rfl⟩
    exact hn k
  apply le_antisymm
  · exact csInf_le hb ⟨n, rfl⟩
  · apply le_csInf (s := Set.range (fun k : ℕ => E k + lam * k)) ⟨_, n, rfl⟩
    rintro e ⟨k, rfl⟩
    exact hn k

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpinSpaceIntegrable
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

lemma sum_ordered_pairs {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then f i j else 0) =
      2 * ∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0 := by
  have he (i j : Fin n) : (if i ≠ j then f i j else 0) =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    by_cases h : i=j
    · subst j; simp
    rcases lt_or_gt_of_ne h with h | h
    · simp only [ite_eq_left h,ite_eq_left (ne_of_lt h),ite_eq_right (not_lt_of_ge h.le),add_zero]
    · simp only [ite_eq_left h,ite_eq_left (ne_of_gt h),ite_eq_right (not_lt_of_ge h.le),zero_add]
  simp_rw [he,Finset.sum_add_distrib]
  have hs : (∑ i : Fin n, ∑ j : Fin n, if j < i then f i j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hf j i]
  rw [hs]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_RetainedRepulsion
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

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma sum_embedding_le_univ {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) {f : κ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ i : ι, f (e i) ≤ ∑ j : κ, f j := by
  classical
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hf i)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RetainedMeasurable
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
open scoped BigOperators unitInterval

open CoulombAtom
variable {N : ℕ}

def FlatAntisymmetric (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ) : Prop :=
  ∀ i j, i ≠ j → ∀ s x,
    f (s ∘ Equiv.swap i j) (x ∘ particlePermute (Equiv.swap i j)) = -f s x

def shiftedFunction (z : (Fin N × Fin 3) → ℤ)
    (f : ((Fin N × Fin 3) → ℝ) → ℂ) (x : (Fin N × Fin 3) → ℝ) : ℂ :=
  f (fun q => (z q:ℝ)+x q)

lemma shiftedFunction_contDiff {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (z : (Fin N × Fin 3) → ℤ) : ContDiff ℝ 1 (shiftedFunction z f) :=
  hf.comp (contDiff_const.add contDiff_id)

lemma shiftedFunction_anti {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (hanti : FlatAntisymmetric f)
    (z : (Fin N × Fin 3) → ℤ) :
    CellAntisymmetric (indexCell z) (fun s => finiteCubeFunction (shiftedFunction_contDiff (hf s) z)) := by
  classical
  intro i j hij hc s x
  change f (s ∘ Equiv.swap i j) (fun q => (z q:ℝ)+(x (particlePermute (Equiv.swap i j) q):ℝ)) =
    -f s (cubeShift z x)
  have hz (q : Fin N × Fin 3) : z (particlePermute (Equiv.swap i j) q) = z q := by
    rcases q with ⟨k,a⟩
    change z (Equiv.swap i j k,a) = z (k,a)
    have he : z (i,a) = z (j,a) := congrFun hc a
    by_cases hi : k=i
    · subst k; simpa using he.symm
    · by_cases hj : k=j
      · subst k; simpa using he
      · rw [Equiv.swap_apply_of_ne_of_ne hi hj]
  convert hanti i j hij s (cubeShift z x) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext q
  simp only [Function.comp_apply,cubeShift,hz]

lemma finiteCubeGradient_value {d : Type*} [Fintype d] [DecidableEq d]
    {f : (d → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (q : d) (x : d → I) :
    finiteCubeGradient hf q x = fderiv ℝ f (fun r => (x r:ℝ)) (Pi.single q 1) := by
  simp only [finiteCubeGradient,ContinuousMap.coe_mk]
  congr 1
  funext r
  by_cases hr : r=q <;> simp [hr]

lemma shiftedFunction_gradient {f : ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ContDiff ℝ 1 f) (z : (Fin N × Fin 3) → ℤ) (q : Fin N × Fin 3)
    (x : (Fin N × Fin 3) → I) :
    finiteCubeGradient (shiftedFunction_contDiff hf z) q x =
      fderiv ℝ f (cubeShift z x) (Pi.single q 1) := by
  classical
  rw [finiteCubeGradient_value]
  change fderiv ℝ (fun y => f ((fun r => (z r:ℝ))+y)) (fun r => (x r:ℝ)) (Pi.single q 1) = _
  have h := ((hf.differentiable (by simp) (cubeShift z x)).hasFDerivAt).comp
    (fun r => (x r:ℝ)) ((hasFDerivAt_const (fun r => (z r:ℝ)) (fun r => (x r:ℝ))).add (hasFDerivAt_id _))
  simpa [Function.comp_def] using congrArg
    (fun L : ((Fin N × Fin 3) → ℝ) →L[ℝ] ℂ => L (Pi.single q 1)) h.fderiv

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_FlatFermionAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators Topology

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

lemma flat_complex_sign_norm (π : Equiv.Perm (Fin N)) :
    ‖(((Equiv.Perm.sign π : ℤ) : ℂ))‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;> simp [hs]

lemma flat_sum_spins_permutation (π : Equiv.Perm (Fin N)) (f : (Fin N → Fin 2) → ℝ) :
    (∑ s : Fin N → Fin 2, f (s ∘ π)) = ∑ s, f s := by
  let e : (Fin N → Fin 2) ≃ (Fin N → Fin 2) :=
    { toFun := fun s => s ∘ π
      invFun := fun s => s ∘ π.symm
      left_inv := fun s => by funext i; simp
      right_inv := fun s => by funext i; simp }
  exact Equiv.sum_comp e f

def flatPermutation (π : Equiv.Perm (Fin N)) :
    ((Fin N × Fin 3) → ℝ) ≃L[ℝ] ((Fin N × Fin 3) → ℝ) :=
  realReindex (particlePermute π).symm

lemma flatPermutation_apply (π : Equiv.Perm (Fin N)) (x : (Fin N × Fin 3) → ℝ) :
    flatPermutation π x = x ∘ particlePermute π := by
  simp only [flatPermutation,realReindex_apply,Equiv.symm_symm]

lemma flatPermutation_preserving (π : Equiv.Perm (Fin N)) :
    MeasurePreserving (flatPermutation π) :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin N × Fin 3 => ℝ) (particlePermute π).symm

lemma flatPermutation_mul (π σ : Equiv.Perm (Fin N)) (x : (Fin N × Fin 3) → ℝ) :
    flatPermutation σ (flatPermutation π x) = flatPermutation (π*σ) x := by
  funext q
  rcases q with ⟨i,a⟩
  simp [flatPermutation_apply,particlePermute,Function.comp_def]

lemma flatPermutation_single (π : Equiv.Perm (Fin N)) (q : Fin N × Fin 3) :
    flatPermutation π (Pi.single q 1) = Pi.single ((particlePermute π).symm q) 1 := by
  classical
  exact realReindex_single _ _

def flatSignedPermutation (π : Equiv.Perm (Fin N))
    (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ)
    (s : Fin N → Fin 2) (x : (Fin N × Fin 3) → ℝ) : ℂ :=
  (((Equiv.Perm.sign π:ℤ):ℂ)) * f (s ∘ π) (flatPermutation π x)

def flatFermionAverage (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ)
    (s : Fin N → Fin 2) (x : (Fin N × Fin 3) → ℝ) : ℂ :=
  finiteMean (fun π : Equiv.Perm (Fin N) => flatSignedPermutation π f s x)

lemma flatSignedPermutation_mul (π σ : Equiv.Perm (Fin N))
    (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ) :
    flatSignedPermutation π (flatSignedPermutation σ f) = flatSignedPermutation (π*σ) f := by
  funext s x
  simp only [flatSignedPermutation,flatPermutation_mul,Equiv.Perm.sign_mul,
    Units.val_mul,Int.cast_mul,Function.comp_def,Equiv.Perm.coe_mul]
  ring

lemma flatFermionAverage_fixed (π : Equiv.Perm (Fin N))
    (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ) :
    flatSignedPermutation π (flatFermionAverage f) = flatFermionAverage f := by
  funext s x
  change (((Equiv.Perm.sign π:ℤ):ℂ)) *
    ((Fintype.card (Equiv.Perm (Fin N)):ℝ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin N), flatSignedPermutation σ f (s ∘ π) (flatPermutation π x)) = _
  rw [mul_smul_comm,Finset.mul_sum]
  change (Fintype.card (Equiv.Perm (Fin N)):ℝ)⁻¹ •
    (∑ σ : Equiv.Perm (Fin N), flatSignedPermutation π (flatSignedPermutation σ f) s x) = _
  simp_rw [flatSignedPermutation_mul]
  unfold flatFermionAverage finiteMean
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft π) _ _ (fun σ => rfl)

lemma flatFermionAverage_anti
    (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ) :
    FlatAntisymmetric (flatFermionAverage f) := by
  intro i j hij s x
  have hh := congrFun (congrFun (flatFermionAverage_fixed (Equiv.swap i j) f) s) x
  simp only [flatSignedPermutation,Equiv.Perm.sign_swap hij,Units.val_neg,
    Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul,flatPermutation_apply] at hh
  exact neg_eq_iff_eq_neg.mp hh

lemma flatSignedPermutation_contDiff
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    {n : WithTop ℕ∞} (hf : ∀ s, ContDiff ℝ n (f s)) (π : Equiv.Perm (Fin N)) (s : Fin N → Fin 2) :
    ContDiff ℝ n (flatSignedPermutation π f s) := by
  exact contDiff_const.mul ((hf (s ∘ π)).comp (flatPermutation π).contDiff)

lemma flatFermionAverage_contDiff
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    {n : WithTop ℕ∞} (hf : ∀ s, ContDiff ℝ n (f s)) (s : Fin N → Fin 2) :
    ContDiff ℝ n (flatFermionAverage f s) := by
  exact contDiff_const.smul (ContDiff.sum (fun π _ => flatSignedPermutation_contDiff hf π s))

lemma flatSignedPermutation_memLp
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, MemLp (f s) 2) (π : Equiv.Perm (Fin N)) (s : Fin N → Fin 2) :
    MemLp (flatSignedPermutation π f s) 2 := by
  exact ((hf (s ∘ π)).comp_measurePreserving (flatPermutation_preserving π)).const_smul
    (((Equiv.Perm.sign π:ℤ):ℂ))

lemma flatFermionAverage_memLp
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, MemLp (f s) 2) (s : Fin N → Fin 2) : MemLp (flatFermionAverage f s) 2 :=
  finiteMean_memLp (fun π => flatSignedPermutation_memLp hf π s)

lemma flatSignedPermutation_mass
    (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ) (π : Equiv.Perm (Fin N)) :
    (∑ s, ∫ x, ‖flatSignedPermutation π f s x‖^2) = ∑ s, ∫ x, ‖f s x‖^2 := by
  simp only [flatSignedPermutation,norm_mul,flat_complex_sign_norm,one_mul]
  calc
    _ = ∑ s, ∫ x, ‖f (s ∘ π) x‖^2 := by
      apply Finset.sum_congr rfl
      intro s _
      exact (flatPermutation_preserving π).integral_comp
        (flatPermutation π).toHomeomorph.measurableEmbedding
        (fun x : (Fin N × Fin 3) → ℝ => ‖f (s ∘ π) x‖^2)
    _ = _ := flat_sum_spins_permutation π (fun s => ∫ x, ‖f s x‖^2)

lemma flatFermionAverage_mass_le
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, MemLp (f s) 2) :
    (∑ s, ∫ x, ‖flatFermionAverage f s x‖^2) ≤ ∑ s, ∫ x, ‖f s x‖^2 := by
  calc
    _ ≤ ∑ s, finiteMean (fun π => ∫ x, ‖flatSignedPermutation π f s x‖^2) := by
      exact Finset.sum_le_sum (fun s _ => finiteMean_integral_norm_sq_le
        (fun π => flatSignedPermutation_memLp hf π s))
    _ = finiteMean (fun π => ∑ s, ∫ x, ‖flatSignedPermutation π f s x‖^2) := by
      simp only [finiteMean,←Finset.smul_sum]
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [flatSignedPermutation_mass]; exact finiteMean_const _

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_FlatFermionGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_FlatFermionGradient_scope

open MeasureTheory Filter
open scoped BigOperators Topology

open CoulombAtom
variable {N : ℕ}

lemma flatSignedPermutation_gradient
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (π : Equiv.Perm (Fin N))
    (s : Fin N → Fin 2) (x : (Fin N × Fin 3) → ℝ) (q : Fin N × Fin 3) :
    fderiv ℝ (flatSignedPermutation π f s) x (Pi.single q 1) =
      (((Equiv.Perm.sign π:ℤ):ℂ)) *
        fderiv ℝ (f (s ∘ π)) (flatPermutation π x) (Pi.single ((particlePermute π).symm q) 1) := by
  change fderiv ℝ (fun y => (((Equiv.Perm.sign π:ℤ):ℂ)) * f (s ∘ π) (flatPermutation π y)) x (Pi.single q 1) = _
  have h := (((hf (s ∘ π)).differentiable (by simp) (flatPermutation π x)).hasFDerivAt.comp x
    (flatPermutation π).hasFDerivAt).const_mul (((Equiv.Perm.sign π:ℤ):ℂ))
  simpa [flatSignedPermutation,ContinuousLinearMap.comp_apply,flatPermutation_single]
    using congrArg (fun L : ((Fin N × Fin 3) → ℝ) →L[ℝ] ℂ => L (Pi.single q 1)) h.fderiv

lemma flatFermionAverage_gradient
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (s : Fin N → Fin 2) (x : (Fin N × Fin 3) → ℝ) (q : Fin N × Fin 3) :
    fderiv ℝ (flatFermionAverage f s) x (Pi.single q 1) =
      finiteMean (fun π : Equiv.Perm (Fin N) =>
        fderiv ℝ (flatSignedPermutation π f s) x (Pi.single q 1)) := by
  change fderiv ℝ (fun y => (Fintype.card (Equiv.Perm (Fin N)):ℝ)⁻¹ •
    ∑ π : Equiv.Perm (Fin N), flatSignedPermutation π f s y) x (Pi.single q 1) = _
  have h := (HasFDerivAt.fun_sum (u := Finset.univ) (fun π _ =>
    ((flatSignedPermutation_contDiff hf π s).differentiable (by simp) x).hasFDerivAt)).const_smul
      (Fintype.card (Equiv.Perm (Fin N)):ℝ)⁻¹
  simpa [flatFermionAverage,finiteMean,Pi.smul_def] using congrArg
    (fun L : ((Fin N × Fin 3) → ℝ) →L[ℝ] ℂ => L (Pi.single q 1)) h.fderiv

lemma flatSignedPermutation_gradient_memLp
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (hg : ∀ s q, MemLp (fun x => fderiv ℝ (f s) x (Pi.single q 1)) 2)
    (π : Equiv.Perm (Fin N)) (s : Fin N → Fin 2) (q : Fin N × Fin 3) :
    MemLp (fun x => fderiv ℝ (flatSignedPermutation π f s) x (Pi.single q 1)) 2 := by
  simp_rw [flatSignedPermutation_gradient hf]
  exact ((hg (s ∘ π) ((particlePermute π).symm q)).comp_measurePreserving
    (flatPermutation_preserving π)).const_smul (((Equiv.Perm.sign π:ℤ):ℂ))

lemma flatFermionAverage_gradient_memLp
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (hg : ∀ s q, MemLp (fun x => fderiv ℝ (f s) x (Pi.single q 1)) 2)
    (s : Fin N → Fin 2) (q : Fin N × Fin 3) :
    MemLp (fun x => fderiv ℝ (flatFermionAverage f s) x (Pi.single q 1)) 2 := by
  simp_rw [flatFermionAverage_gradient hf]
  exact finiteMean_memLp (fun π => flatSignedPermutation_gradient_memLp hf hg π s q)

lemma flatSignedPermutation_kinetic
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (π : Equiv.Perm (Fin N)) :
    (∑ s, ∑ q, ∫ x, ‖fderiv ℝ (flatSignedPermutation π f s) x (Pi.single q 1)‖^2) =
      ∑ s, ∑ q, ∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2 := by
  simp_rw [flatSignedPermutation_gradient hf,norm_mul,flat_complex_sign_norm,one_mul]
  calc
    _ = ∑ s, ∑ q, ∫ x, ‖fderiv ℝ (f (s ∘ π)) x
        (Pi.single ((particlePermute π).symm q) 1)‖^2 := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro q _
      exact (flatPermutation_preserving π).integral_comp
        (flatPermutation π).toHomeomorph.measurableEmbedding
        (fun x : (Fin N × Fin 3) → ℝ => ‖fderiv ℝ (f (s ∘ π)) x
          (Pi.single ((particlePermute π).symm q) 1)‖^2)
    _ = _ := by
      calc
        _ = ∑ s, ∑ q, ∫ x, ‖fderiv ℝ (f (s ∘ π)) x (Pi.single q 1)‖^2 := by
          apply Finset.sum_congr rfl
          intro s _
          exact (particlePermute π).symm.sum_comp
            (fun q => ∫ x, ‖fderiv ℝ (f (s ∘ π)) x (Pi.single q 1)‖^2)
        _ = _ := flat_sum_spins_permutation π (fun s => ∑ q, ∫ x,
          ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2)

lemma flatFermionAverage_kinetic_le
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (hg : ∀ s q, MemLp (fun x => fderiv ℝ (f s) x (Pi.single q 1)) 2) :
    (∑ s, ∑ q, ∫ x, ‖fderiv ℝ (flatFermionAverage f s) x (Pi.single q 1)‖^2) ≤
      ∑ s, ∑ q, ∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2 := by
  simp_rw [flatFermionAverage_gradient hf]
  calc
    _ ≤ ∑ s, ∑ q, finiteMean (fun π => ∫ x,
        ‖fderiv ℝ (flatSignedPermutation π f s) x (Pi.single q 1)‖^2) := by
      apply Finset.sum_le_sum
      intro s _
      exact Finset.sum_le_sum (fun q _ => finiteMean_integral_norm_sq_le
        (fun π => flatSignedPermutation_gradient_memLp hf hg π s q))
    _ = finiteMean (fun π => ∑ s, ∑ q, ∫ x,
        ‖fderiv ℝ (flatSignedPermutation π f s) x (Pi.single q 1)‖^2) := by
      simp_rw [sum_finiteMean]
    _ = _ := by simp_rw [flatSignedPermutation_kinetic hf]; exact finiteMean_const _

end Work_FlatFermionGradient_scope

open MeasureTheory Filter
open scoped BigOperators Topology

open CoulombAtom
variable {N : ℕ}

def FlatAEAntisymmetric (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ) : Prop :=
  ∀ (π : Equiv.Perm (Fin N)) (s : Fin N → Fin 2),
    ∀ᵐ x, f (s ∘ π) (flatPermutation π x) = (((Equiv.Perm.sign π:ℤ):ℂ)) * f s x

lemma flatSignedPermutation_ae_fixed
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : FlatAEAntisymmetric f) (π : Equiv.Perm (Fin N)) (s : Fin N → Fin 2) :
    flatSignedPermutation π f s =ᵐ[volume] f s := by
  filter_upwards [hf π s] with x hx
  unfold flatSignedPermutation
  rw [hx,←mul_assoc]
  have hs : ((((Equiv.Perm.sign π:ℤ):ℂ)) * (((Equiv.Perm.sign π:ℤ):ℂ))) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  rw [hs,one_mul]

lemma flatFermionAverage_ae_fixed
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : FlatAEAntisymmetric f) (s : Fin N → Fin 2) :
    flatFermionAverage f s =ᵐ[volume] f s := by
  have ha : ∀ᵐ x, ∀ π : Equiv.Perm (Fin N), flatSignedPermutation π f s x = f s x :=
    ae_all_iff.mpr (fun π => flatSignedPermutation_ae_fixed hf π s)
  filter_upwards [ha] with x hx
  unfold flatFermionAverage
  simp_rw [hx]
  exact finiteMean_const _

lemma flatFermionAverage_ae_tendsto
    {u : ℕ → (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : FlatAEAntisymmetric f)
    (ht : ∀ s, ∀ᵐ x, Tendsto (fun n => u n s x) atTop (𝓝 (f s x)))
    (s : Fin N → Fin 2) :
    ∀ᵐ x, Tendsto (fun n => flatFermionAverage (u n) s x) atTop (𝓝 (f s x)) := by
  have hp (π : Equiv.Perm (Fin N)) : ∀ᵐ x,
      Tendsto (fun n => flatSignedPermutation π (u n) s x) atTop
        (𝓝 (flatSignedPermutation π f s x)) := by
    filter_upwards [(flatPermutation_preserving π).quasiMeasurePreserving.ae (ht (s ∘ π))] with x hx
    exact hx.const_mul _
  filter_upwards [ae_all_iff.mpr hp,flatFermionAverage_ae_fixed hf s] with x hx he
  rw [←he]
  exact finiteMean_tendsto hx

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_QuantumRawLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace CoulombObservation

def compactNoiseWeight (u : ℝ) : ℝ :=
  if |u| < 1 then Real.exp (-(1 - u^2)⁻¹) else 0

def compactNoiseNormalizer : ℝ := (∫ u, compactNoiseWeight u)⁻¹

def compactNoiseDensity (u : ℝ) : ℝ := compactNoiseNormalizer * compactNoiseWeight u

def compactNoiseLaw : Measure ℝ :=
  volume.withDensity (fun u => ENNReal.ofReal (compactNoiseDensity u))

def compactNoiseScore (u : ℝ) : ℝ :=
  if |u| < 1 then -2*u / (1-u^2)^2 else 0

lemma compactNoiseWeight_measurable : Measurable compactNoiseWeight := by
  unfold compactNoiseWeight
  exact Measurable.ite (measurableSet_lt measurable_abs measurable_const)
    (by fun_prop) measurable_const

lemma compactNoiseScore_measurable : Measurable compactNoiseScore := by
  unfold compactNoiseScore
  exact Measurable.ite (measurableSet_lt measurable_abs measurable_const)
    (by fun_prop) measurable_const

lemma compactNoiseWeight_nonneg (u : ℝ) : 0 ≤ compactNoiseWeight u := by
  unfold compactNoiseWeight
  split_ifs <;> positivity

lemma compactNoiseWeight_le_one (u : ℝ) : compactNoiseWeight u ≤ 1 := by
  unfold compactNoiseWeight
  split_ifs with hu
  · apply Real.exp_le_one_iff.mpr
    have hh : 0 < 1-u^2 := by have := abs_lt.mp hu; nlinarith
    exact neg_nonpos.mpr (inv_nonneg.mpr hh.le)
  · norm_num

lemma compactNoiseWeight_even (u : ℝ) : compactNoiseWeight (-u) = compactNoiseWeight u := by
  simp [compactNoiseWeight]

lemma compactNoiseScore_odd : Function.Odd compactNoiseScore := by
  intro u
  simp only [compactNoiseScore, abs_neg, neg_sq]
  split_ifs <;> ring

lemma compactNoiseWeight_integrable : Integrable compactNoiseWeight := by
  have hi : Integrable ((Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ))) := by
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact integrableOn_const (by rw [Real.volume_Icc]; finiteness)
  refine hi.mono' compactNoiseWeight_measurable.aestronglyMeasurable (ae_of_all _ ?_)
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (compactNoiseWeight_nonneg u)]
  by_cases hu : |u| < 1
  · rw [indicator_of_mem (by have := abs_lt.mp hu; constructor <;> linarith)]
    exact compactNoiseWeight_le_one u
  · rw [compactNoiseWeight, ite_eq_right hu]
    exact indicator_nonneg (fun _ _ => by norm_num) _

lemma compactNoiseWeight_support : Function.support compactNoiseWeight = Ioo (-1) 1 := by
  ext u
  simp only [Function.mem_support, mem_Ioo, compactNoiseWeight]
  by_cases hu : |u| < 1
  · simp [hu, Real.exp_ne_zero, abs_lt.mp hu]
  · have hh : ¬(-1 < u ∧ u < 1) := by simpa only [← abs_lt] using hu
    simp [hu, hh]

lemma compactNoiseWeight_integral_pos : 0 < ∫ u, compactNoiseWeight u := by
  rw [integral_pos_iff_support_of_nonneg compactNoiseWeight_nonneg compactNoiseWeight_integrable,
    compactNoiseWeight_support, Real.volume_Ioo]
  norm_num

lemma compactNoiseNormalizer_pos : 0 < compactNoiseNormalizer :=
  inv_pos.mpr compactNoiseWeight_integral_pos

lemma compactNoiseDensity_nonneg (u : ℝ) : 0 ≤ compactNoiseDensity u :=
  mul_nonneg compactNoiseNormalizer_pos.le (compactNoiseWeight_nonneg u)

lemma compactNoiseDensity_measurable : Measurable compactNoiseDensity :=
  compactNoiseWeight_measurable.const_mul _

lemma compactNoiseDensity_integrable : Integrable compactNoiseDensity :=
  compactNoiseWeight_integrable.const_mul _

lemma compactNoiseDensity_integral : (∫ u, compactNoiseDensity u) = 1 := by
  change (∫ u, compactNoiseNormalizer * compactNoiseWeight u) = 1
  rw [integral_const_mul, compactNoiseNormalizer]
  exact inv_mul_cancel₀ (ne_of_gt compactNoiseWeight_integral_pos)

instance compactNoiseLaw_probability : IsProbabilityMeasure compactNoiseLaw := by
  constructor
  rw [compactNoiseLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal compactNoiseDensity_integrable
      (ae_of_all _ compactNoiseDensity_nonneg), compactNoiseDensity_integral]
  norm_num

lemma compactNoiseLaw_integral (f : ℝ → ℝ) :
    (∫ u, f u ∂compactNoiseLaw) = ∫ u, compactNoiseDensity u * f u := by
  rw [compactNoiseLaw, integral_withDensity_eq_integral_toReal_smul
    compactNoiseDensity_measurable.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (compactNoiseDensity_nonneg _), smul_eq_mul]

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservationSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservationSmooth_scope

open MeasureTheory Set
open scoped ContDiff

lemma compactNoiseWeight_eq_glue (u : ℝ) :
    compactNoiseWeight u = expNegInvGlue (1-u^2) := by
  have hh : |u| < 1 ↔ ¬ 1-u^2 ≤ 0 := by
    rw [not_le, sub_pos, sq_lt_one_iff_abs_lt_one]
  simp only [compactNoiseWeight, expNegInvGlue, hh]
  split_ifs <;> rfl

lemma compactNoiseWeight_contDiff {n : ℕ∞} : ContDiff ℝ n compactNoiseWeight := by
  simp_rw [funext compactNoiseWeight_eq_glue]
  exact expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

lemma compactNoiseDensity_contDiff {n : ℕ∞} : ContDiff ℝ n compactNoiseDensity :=
  contDiff_const.mul compactNoiseWeight_contDiff

lemma compactNoiseWeight_hasDerivAt (u : ℝ) :
    HasDerivAt compactNoiseWeight (compactNoiseScore u * compactNoiseWeight u) u := by
  have hc : HasDerivAt expNegInvGlue ((1-u^2)⁻¹^2 * expNegInvGlue (1-u^2)) (1-u^2) := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 (1-u^2)
  have hh := hc.comp u ((hasDerivAt_const u 1).sub ((hasDerivAt_id u).pow 2))
  simp only [Nat.cast_ofNat, mul_one, zero_sub, id_eq, Nat.reduceSub, pow_one] at hh
  have he : ((((1-u^2)⁻¹^2 * expNegInvGlue (1-u^2)) * -(2*u))) =
      compactNoiseScore u * compactNoiseWeight u := by
    rw [← compactNoiseWeight_eq_glue]
    by_cases hu : |u| < 1
    · simp only [compactNoiseScore, ite_eq_left hu, div_eq_mul_inv, inv_pow]; ring
    · simp [compactNoiseScore, compactNoiseWeight, hu]
  rw [he] at hh
  simpa only [Function.comp_def, Pi.sub_apply, Pi.pow_apply, id_eq, ← compactNoiseWeight_eq_glue] using hh

lemma compactNoiseDensity_hasDerivAt (u : ℝ) :
    HasDerivAt compactNoiseDensity (compactNoiseScore u * compactNoiseDensity u) u := by
  convert! (compactNoiseWeight_hasDerivAt u).const_mul compactNoiseNormalizer using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [compactNoiseDensity]
  ring

end Work_ObservationSmooth_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

def compactNoiseKernel {ι : Type*} [Fintype ι] (u : ι → ℝ) : ℝ :=
  ∏ i, compactNoiseDensity (u i)

lemma compactNoiseKernel_nonneg {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    0 ≤ compactNoiseKernel u := prod_nonneg (fun _ _ => compactNoiseDensity_nonneg _)

lemma compactNoiseKernel_even {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    compactNoiseKernel (-u) = compactNoiseKernel u := by
  simp only [compactNoiseKernel, Pi.neg_apply, compactNoiseDensity, compactNoiseWeight_even]

lemma compactNoiseKernel_contDiff {ι : Type*} [Fintype ι] {n : ℕ∞} :
    ContDiff ℝ n (compactNoiseKernel : (ι → ℝ) → ℝ) := by
  exact contDiff_prod (fun i _ => compactNoiseDensity_contDiff.comp (contDiff_apply ℝ ℝ i))

lemma compactNoiseKernel_integrable {ι : Type*} [Fintype ι] :
    Integrable (compactNoiseKernel : (ι → ℝ) → ℝ) := by
  exact Integrable.fintype_prod (fun _ => compactNoiseDensity_integrable)

lemma compactNoiseKernel_compactSupport {ι : Type*} [Fintype ι] :
    HasCompactSupport (compactNoiseKernel : (ι → ℝ) → ℝ) := by
  classical
  apply HasCompactSupport.intro (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := (-1:ℝ)) (b := 1)))
  intro u hu
  simp only [mem_univ_pi] at hu
  push Not at hu
  obtain ⟨i, hi⟩ := hu
  apply prod_eq_zero (mem_univ i)
  have hh : ¬|u i| < 1 := by
    intro h
    exact hi ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩
  simp [compactNoiseDensity, compactNoiseWeight, hh]

lemma compactNoiseLaw_apply {s : Set ℝ} (hs : MeasurableSet s) :
    compactNoiseLaw s = ENNReal.ofReal (∫ u in s, compactNoiseDensity u) := by
  rw [compactNoiseLaw, withDensity_apply _ hs]
  exact (ofReal_integral_eq_lintegral_ofReal compactNoiseDensity_integrable.integrableOn
    (ae_of_all _ compactNoiseDensity_nonneg)).symm

lemma compactNoiseLaw_pi {ι : Type*} [Fintype ι] :
    Measure.pi (fun _ : ι => compactNoiseLaw) =
      volume.withDensity (fun u : ι → ℝ => ENNReal.ofReal (compactNoiseKernel u)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal compactNoiseKernel_integrable.integrableOn
      (ae_of_all _ compactNoiseKernel_nonneg)]
  simp only [volume_pi, Measure.restrict_pi_pi, compactNoiseKernel,
    integral_fintype_prod_eq_prod, compactNoiseLaw_apply (hs _)]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    integral_nonneg (fun _ => compactNoiseDensity_nonneg _))

lemma compactNoiseLaw_pi_integral {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) :
    (∫ u, f u ∂Measure.pi (fun _ : ι => compactNoiseLaw)) =
      ∫ u, compactNoiseKernel u * f u := by
  rw [compactNoiseLaw_pi, integral_withDensity_eq_integral_toReal_smul
    (compactNoiseKernel_contDiff (n := 0)).continuous.measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (compactNoiseKernel_nonneg _), smul_eq_mul]

lemma compactNoiseKernel_hasFDerivAt {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    HasFDerivAt compactNoiseKernel
      (∑ i, (compactNoiseScore (u i) * compactNoiseKernel u) •
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) u := by
  classical
  have hi (i : ι) : HasFDerivAt (fun v : ι → ℝ => compactNoiseDensity (v i))
      ((compactNoiseScore (u i) * compactNoiseDensity (u i)) •
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) u :=
    by
      convert! HasDerivAt.comp_hasFDerivAt (f := fun v : ι → ℝ => v i) u
        (compactNoiseDensity_hasDerivAt (u i)) (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt using 1
      all_goals try with_reducible_and_instances rfl
  convert! HasFDerivAt.finsetProd (u := univ) (fun i _ => hi i) using 1
  all_goals try with_reducible_and_instances rfl
  apply sum_congr rfl
  intro i _
  rw [smul_smul]
  congr 1
  rw [mul_left_comm, prod_erase_mul _ _ (mem_univ i)]
  rfl

lemma compactNoiseKernel_fderiv_apply {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    fderiv ℝ compactNoiseKernel u v =
      compactNoiseKernel u * ∑ i, compactNoiseScore (u i) * v i := by
  rw [(compactNoiseKernel_hasFDerivAt u).fderiv]
  simp only [_root_.sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservationScoreMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservationScoreMoments_scope

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal NNReal BigOperators

lemma pow_mul_exp_neg_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    t^n * Real.exp (-t) ≤ (n : ℝ)^n := by
  have hf : 0 < (Nat.factorial n : ℝ) := by positivity
  have hh := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp t ht n)
  have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-t)).le
  have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  calc
    _ ≤ (Nat.factorial n : ℝ) := by nlinarith [hh']
    _ ≤ _ := by exact_mod_cast Nat.factorial_le_pow n

lemma compactNoiseScore_weight_bound (u : ℝ) (k : ℕ) :
    compactNoiseScore u ^ (2*k) * compactNoiseWeight u ≤ (32*(k:ℝ)^2)^(2*k) := by
  by_cases hk : k = 0
  · subst k
    simpa using compactNoiseWeight_le_one u
  by_cases hu : |u| < 1
  · have hd : 0 < 1-u^2 := by have := abs_lt.mp hu; nlinarith
    let t : ℝ := (1-u^2)⁻¹
    have ht : 0 ≤ t := inv_nonneg.mpr hd.le
    have hs : |compactNoiseScore u| ≤ 2*t^2 := by
      rw [compactNoiseScore, ite_eq_left hu]
      simp only [abs_div, abs_mul, abs_neg, abs_sq]
      norm_num only [abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]
      dsimp [t]
      rw [inv_pow]
      calc
        _ ≤ 2/(1-u^2)^2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
        _ = _ := by rw [div_eq_mul_inv]
    have hp : compactNoiseScore u^(2*k) ≤ (2*t^2)^(2*k) := by
      have hh := pow_le_pow_left₀ (abs_nonneg _) hs (2*k)
      simpa only [pow_mul, sq_abs] using hh
    have hh := pow_mul_exp_neg_le t ht (4*k)
    calc
      _ = compactNoiseScore u^(2*k) * Real.exp (-t) := by rw [compactNoiseWeight, ite_eq_left hu]
      _ ≤ (2*t^2)^(2*k) * Real.exp (-t) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = 2^(2*k) * (t^(4*k) * Real.exp (-t)) := by
        rw [mul_pow, ← pow_mul]; ring_nf
      _ ≤ 2^(2*k) * ((4*k : ℕ):ℝ)^(4*k) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (2 * (4*(k:ℝ))^2)^(2*k) := by
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        symm
        rw [mul_pow]
        congr 1
        rw [← pow_mul, show 2*(2*k) = 4*k by omega]
      _ = _ := by congr 1; ring
  · simp [compactNoiseScore, compactNoiseWeight, hu]

lemma compactNoiseScore_weight_integrable (k : ℕ) :
    Integrable (fun u => compactNoiseScore u^(2*k) * compactNoiseWeight u) := by
  let B : ℝ := (32*(k:ℝ)^2)^(2*k)
  have hi : Integrable ((Icc (-1:ℝ) 1).indicator (fun _ => B)) := by
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact integrableOn_const (by rw [Real.volume_Icc]; finiteness)
  refine hi.mono' ((compactNoiseScore_measurable.pow_const _).mul
    compactNoiseWeight_measurable).aestronglyMeasurable (ae_of_all _ ?_)
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by rw [pow_mul]; positivity) (compactNoiseWeight_nonneg u))]
  by_cases hu : |u| < 1
  · rw [indicator_of_mem (by have := abs_lt.mp hu; constructor <;> linarith)]
    exact compactNoiseScore_weight_bound u k
  · simp only [compactNoiseWeight, ite_eq_right hu, mul_zero]
    exact indicator_nonneg (fun _ _ => by dsimp [B]; positivity) _

lemma compactNoiseScore_moment_integrable (k : ℕ) :
    Integrable (fun u => compactNoiseScore u^(2*k)) compactNoiseLaw := by
  rw [compactNoiseLaw, integrable_withDensity_iff
    compactNoiseDensity_measurable.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (compactNoiseDensity_nonneg _)]
  simpa only [compactNoiseDensity, mul_left_comm, mul_assoc] using
    (compactNoiseScore_weight_integrable k).const_mul compactNoiseNormalizer

def compactScoreConstant : ℝ := 32 * (1 + 2*compactNoiseNormalizer)

lemma compactScoreConstant_pos : 0 < compactScoreConstant := by
  unfold compactScoreConstant
  have := compactNoiseNormalizer_pos
  positivity

lemma compactNoiseScore_moment_le {k : ℕ} (hk : 0 < k) :
    (∫ u, compactNoiseScore u^(2*k) ∂compactNoiseLaw) ≤
      (compactScoreConstant * (k:ℝ)^2)^(2*k) := by
  let B : ℝ := (32*(k:ℝ)^2)^(2*k)
  have hi : Integrable ((Icc (-1:ℝ) 1).indicator (fun _ => B)) := by
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact integrableOn_const (by rw [Real.volume_Icc]; finiteness)
  have hpoint (u : ℝ) : compactNoiseScore u^(2*k) * compactNoiseWeight u ≤
      (Icc (-1:ℝ) 1).indicator (fun _ => B) u := by
    by_cases hu : |u| < 1
    · rw [indicator_of_mem (by have := abs_lt.mp hu; constructor <;> linarith)]
      exact compactNoiseScore_weight_bound u k
    · simp only [compactNoiseWeight, ite_eq_right hu, mul_zero]
      exact indicator_nonneg (fun _ _ => by dsimp [B]; positivity) _
  have hbound := integral_mono (compactNoiseScore_weight_integrable k) hi hpoint
  rw [integral_indicator measurableSet_Icc, integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc] at hbound
  norm_num at hbound
  have hp : 2*compactNoiseNormalizer ≤ (1+2*compactNoiseNormalizer)^(2*k) := by
    have h1 : 1 ≤ 1+2*compactNoiseNormalizer := by linarith [compactNoiseNormalizer_pos]
    calc
      _ ≤ 1+2*compactNoiseNormalizer := by linarith
      _ ≤ _ := by simpa using pow_le_pow_right₀ h1 (by omega : 1 ≤ 2*k)
  calc
    _ = compactNoiseNormalizer * ∫ u, compactNoiseScore u^(2*k) * compactNoiseWeight u := by
      rw [compactNoiseLaw_integral, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp [compactNoiseDensity]
      ring
    _ ≤ compactNoiseNormalizer * (2*B) := mul_le_mul_of_nonneg_left hbound compactNoiseNormalizer_pos.le
    _ = (2*compactNoiseNormalizer)*B := by ring
    _ ≤ (1+2*compactNoiseNormalizer)^(2*k)*B := mul_le_mul_of_nonneg_right hp (by dsimp [B]; positivity)
    _ = _ := by dsimp [B, compactScoreConstant]; rw [← mul_pow]; congr 1; ring

end Work_ObservationScoreMoments_scope

open MeasureTheory Set
open scoped ENNReal

lemma compactNoiseLaw_neg_preserving :
    MeasurePreserving Neg.neg compactNoiseLaw compactNoiseLaw := by
  refine ⟨measurable_neg, ?_⟩
  ext s hs
  rw [Measure.map_apply measurable_neg hs, compactNoiseLaw,
    withDensity_apply _ (hs.preimage measurable_neg), withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage measurable_neg), ← lintegral_indicator hs]
  have hh := (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp
    (compactNoiseDensity_measurable.ennreal_ofReal.indicator hs)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply lintegral_congr
  intro u
  by_cases hu : -u ∈ s
  · simp only [indicator_of_mem hu, mem_preimage, hu, indicator_of_mem]
    simp [compactNoiseDensity, compactNoiseWeight_even]
  · simp only [indicator_of_notMem hu, mem_preimage, hu, not_false_eq_true, indicator_of_notMem]

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_SubGaussianMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SubGaussianMoments_scope

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal BigOperators

lemma even_pow_le_factorial_exp (x : ℝ) (k : ℕ) :
    x ^ (2 * k) ≤ (Nat.factorial (2 * k) : ℝ) * (Real.exp x + Real.exp (-x)) := by
  have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) (2 * k)
  have hab : |x| ^ (2 * k) = x ^ (2 * k) := by rw [pow_mul, pow_mul, sq_abs]
  rw [hab] at h
  have hf : (0 : ℝ) < (Nat.factorial (2 * k) : ℝ) := by positivity
  have he : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-x)]
    · rw [abs_of_nonpos hx]; linarith [Real.exp_pos x]
  exact (div_le_iff₀ hf).mp (h.trans he) |>.trans_eq (mul_comm _ _)

lemma subGaussian_even_moment_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (h : HasSubgaussianMGF X v μ) {k : ℕ} (hk : 0 < k) :
    Integrable (fun sample => X sample ^ (2 * k)) μ := by
  have hm : MemLp X (2 * k : ℕ) μ := by
    simpa only [NNReal.coe_natCast, ENNReal.coe_natCast] using h.memLp (2 * k : ℕ)
  have hi := hm.integrable_norm_pow (Nat.ne_of_gt (Nat.mul_pos (by norm_num) hk))
  simpa only [Real.norm_eq_abs, pow_mul, sq_abs] using hi

theorem subGaussian_even_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (h : HasSubgaussianMGF X v μ) {k : ℕ} (hk : 0 < k) :
    (∫ sample, X sample ^ (2 * k) ∂μ) ≤ (8 * Real.exp 1 * k * (v : ℝ)) ^ k := by
  by_cases hv : v = 0
  · subst v
    have he := h.ae_eq_zero_of_hasSubgaussianMGF_zero
    have hz : (∫ sample, X sample ^ (2 * k) ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [he] with sample hω
      simp [hω, Nat.ne_of_gt hk]
    simp [hz, Nat.ne_of_gt hk]
  have hvp : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
  let t : ℝ := Real.sqrt ((k : ℝ) / v)
  have ht : 0 < t := Real.sqrt_pos.2 (div_pos hkp hvp)
  have ht2 : t ^ 2 = (k : ℝ) / v := Real.sq_sqrt (div_pos hkp hvp).le
  have he : (v : ℝ) * t ^ 2 / 2 ≤ k := by rw [ht2]; field_simp; nlinarith
  have hexp : Real.exp ((v : ℝ) * t ^ 2 / 2) ≤ Real.exp (1 : ℝ) ^ k := by
    rw [← Real.exp_nat_mul]
    simpa using Real.exp_le_exp.mpr he
  have hi := subGaussian_even_moment_integrable h hk
  have hpoint := integral_mono (hi.const_mul (t ^ (2 * k)))
    (((h.integrable_exp_mul t).add (h.integrable_exp_mul (-t))).const_mul
      (Nat.factorial (2*k) : ℝ))
    (fun sample => by simpa only [Pi.add_apply, mul_pow, neg_mul] using even_pow_le_factorial_exp (t * X sample) k)
  simp only [Pi.add_apply] at hpoint
  rw [integral_const_mul, integral_const_mul, integral_add
    (h.integrable_exp_mul t) (h.integrable_exp_mul (-t))] at hpoint
  have hm1 : (∫ sample, Real.exp (t * X sample) ∂μ) ≤ Real.exp 1 ^ k :=
    (h.mgf_le t).trans hexp
  have hm2 : (∫ sample, Real.exp (-t * X sample) ∂μ) ≤ Real.exp 1 ^ k := by
    have hh := h.mgf_le (-t)
    simp only [neg_sq] at hh
    exact hh.trans hexp
  have hfact : (Nat.factorial (2*k) : ℝ) ≤ ((2*k : ℕ) : ℝ) ^ (2*k) := by
    exact_mod_cast Nat.factorial_le_pow (2*k)
  have hb : t ^ (2*k) * (∫ sample, X sample ^ (2*k) ∂μ) ≤
      ((2*k : ℕ) : ℝ) ^ (2*k) * (2 * Real.exp 1 ^ k) := by
    calc
      _ ≤ (Nat.factorial (2*k) : ℝ) * (2 * Real.exp 1 ^ k) :=
        hpoint.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      _ ≤ _ := mul_le_mul_of_nonneg_right hfact (by positivity)
  have htwo : (2 : ℝ) ≤ 2 ^ k := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.succ_le_iff.mpr hk)
  have hb' : t ^ (2*k) * (∫ sample, X sample ^ (2*k) ∂μ) ≤
      ((8 * Real.exp 1 * k) : ℝ) ^ k * (k : ℝ) ^ k := by
    calc
      _ ≤ ((2*k : ℕ) : ℝ) ^ (2*k) * (2 * Real.exp 1 ^ k) := hb
      _ ≤ ((2*k : ℕ) : ℝ) ^ (2*k) * (2 ^ k * Real.exp 1 ^ k) := by
        gcongr
      _ = _ := by
        push_cast
        rw [pow_mul]
        ring_nf
        rw [show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]
        ring
  have htPow : t ^ (2*k) = ((k : ℝ) / v) ^ k := by rw [pow_mul, ht2]
  rw [htPow] at hb'
  apply (mul_le_mul_iff_right₀ (pow_pos (div_pos hkp hvp) k)).mp
  calc
    _ ≤ ((8 * Real.exp 1 * k) : ℝ) ^ k * (k : ℝ) ^ k := hb'
    _ = _ := by rw [← mul_pow, ← mul_pow]; congr 1; field_simp

end Work_SubGaussianMoments_scope

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

def observationSign (b : Bool) : ℝ := if b then 1 else -1

def signLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance signLaw_probability : IsProbabilityMeasure signLaw := by
  unfold signLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma observationSign_subGaussian : HasSubgaussianMGF observationSign 1 signLaw := by
  have hm : AEMeasurable observationSign signLaw := Measurable.of_discrete.aemeasurable
  have hb : ∀ᵐ b ∂signLaw, observationSign b ∈ Set.Icc (-1) 1 := by
    filter_upwards [] with b
    cases b <;> norm_num [observationSign]
  have hz : (∫ b, observationSign b ∂signLaw) = 0 := by
    rw [signLaw, PMF.integral_eq_sum]
    norm_num [observationSign, Fintype.sum_bool]
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hz
  norm_num at h
  exact h

def signProduct (ι : Type*) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi (fun _ : ι => signLaw)

instance signProduct_probability (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (signProduct ι) := by
  unfold signProduct
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma observationSign_eval_subGaussian {ι : Type*} [Fintype ι] (i : ι) :
    HasSubgaussianMGF (fun ε : ι → Bool => observationSign (ε i)) 1 (signProduct ι) := by
  have hm : AEMeasurable (fun ε : ι → Bool => ε i) (signProduct ι) :=
    (measurable_pi_apply i).aemeasurable
  have hmap : (signProduct ι).map (fun ε => ε i) = signLaw :=
    (measurePreserving_eval (fun _ : ι => signLaw) i).map_eq
  have h : HasSubgaussianMGF observationSign 1
      ((signProduct ι).map (fun ε => ε i)) := hmap ▸ observationSign_subGaussian
  exact HasSubgaussianMGF.of_map hm h

lemma sign_sum_subGaussian {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    HasSubgaussianMGF (fun ε : ι → Bool => ∑ i, a i * observationSign (ε i))
      (∑ i, (NNReal.mk (a i ^ 2) (sq_nonneg (a i)))) (signProduct ι) := by
  have hind : iIndepFun (fun i (ε : ι → Bool) => a i * observationSign (ε i))
      (signProduct ι) := by
    exact iIndepFun_pi (μ := fun _ : ι => signLaw)
      (X := fun i b => a i * observationSign b)
      (fun i => Measurable.of_discrete.aemeasurable)
  apply HasSubgaussianMGF.sum_of_iIndepFun hind
  intro i _
  have h := (observationSign_eval_subGaussian i).const_mul (a i)
  change HasSubgaussianMGF _ (NNReal.mk (a i ^ 2) (sq_nonneg (a i)) * 1) _ at h
  simpa only [mul_one] using h

theorem sign_sum_even_moment_le {ι : Type*} [Fintype ι] (a : ι → ℝ)
    {k : ℕ} (hk : 0 < k) :
    (∫ ε, (∑ i, a i * observationSign (ε i)) ^ (2*k) ∂signProduct ι) ≤
      (8 * Real.exp 1 * k * (∑ i, a i ^ 2)) ^ k := by
  have h := subGaussian_even_moment_le (sign_sum_subGaussian a) hk
  have hc : (↑(∑ i, NNReal.mk (a i ^ 2) (sq_nonneg (a i))) : ℝ) =
      ∑ i, a i ^ 2 := by simp
  rw [hc] at h
  exact h

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_WeightedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WeightedMoments_scope

open MeasureTheory Finset
open scoped BigOperators

lemma weighted_pow_sum_le {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) (k : ℕ) :
    (∑ i, w i * x i) ^ (k+1) ≤ (∑ i, w i) ^ k * ∑ i, w i * x i ^ (k+1) := by
  classical
  let W := ∑ i, w i
  have hW : 0 ≤ W := sum_nonneg (fun i _ => hw i)
  by_cases hzero : W = 0
  · have hwz : ∀ i, w i = 0 := by
      intro i
      have hh : w i ≤ W := single_le_sum (fun j _ => hw j) (mem_univ i)
      linarith [hw i]
    simp [hwz]
  have hWp : 0 < W := lt_of_le_of_ne hW (Ne.symm hzero)
  have hj := (convexOn_pow (𝕜 := ℝ) (k+1)).map_sum_le
    (t := univ) (w := fun i => w i / W) (p := x)
    (fun i _ => div_nonneg (hw i) hW)
    (by rw [← sum_div]; exact div_self hzero)
    (fun i _ => hx i)
  simp only [smul_eq_mul] at hj
  have he (y : ι → ℝ) : (∑ i, w i / W * y i) = (∑ i, w i * y i) / W := by
    rw [sum_div]
    congr 1
    funext i
    ring
  rw [he x, he (fun i => x i ^ (k+1)), div_pow] at hj
  have hj' := (div_le_div_iff₀ (pow_pos hWp (k+1)) hWp).mp hj
  rw [pow_succ W] at hj'
  apply (mul_le_mul_iff_left₀ hWp).mp
  calc
    _ ≤ (∑ i, w i * x i ^ (k + 1)) * (W ^ k * W) := hj'
    _ = _ := by dsimp [W]; ring

lemma integral_weighted_pow_sum_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} (w : ι → ℝ) (X : ι → Ω → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hX : ∀ i sample, 0 ≤ X i sample) (k : ℕ)
    (hi : Integrable (fun sample => (∑ i, w i * X i sample) ^ (k+1)) μ)
    (hXi : ∀ i, Integrable (fun sample => X i sample ^ (k+1)) μ) :
    (∫ sample, (∑ i, w i * X i sample) ^ (k+1) ∂μ) ≤
      (∑ i, w i) ^ k * ∑ i, w i * (∫ sample, X i sample ^ (k+1) ∂μ) := by
  have hs := integrable_finsetSum univ (fun i _ => (hXi i).const_mul (w i))
  have hh := integral_mono hi (hs.const_mul ((∑ i, w i)^k))
    (fun sample => weighted_pow_sum_le w (fun i => X i sample) hw (fun i => hX i sample) k)
  simpa only [integral_const_mul, integral_finsetSum _ (fun i _ =>
    (hXi i).const_mul (w i))] using hh

end Work_WeightedMoments_scope

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

def signFlip (b : Bool) : ℝ ≃ᵐ ℝ :=
  if b then MeasurableEquiv.refl ℝ else MeasurableEquiv.neg ℝ

def signFlipPi {ι : Type*} (ε : ι → Bool) : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
  MeasurableEquiv.piCongrRight (fun i => signFlip (ε i))

lemma signFlip_preserving {μ : Measure ℝ} (hneg : MeasurePreserving Neg.neg μ μ)
    (b : Bool) : MeasurePreserving (signFlip b) μ μ := by
  cases b
  · exact hneg
  · exact MeasurePreserving.id μ

lemma signFlipPi_preserving {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hneg : ∀ i, MeasurePreserving Neg.neg (μ i) (μ i))
    (ε : ι → Bool) :
    MeasurePreserving (signFlipPi ε) (Measure.pi μ) (Measure.pi μ) :=
  measurePreserving_pi μ μ (fun i => signFlip_preserving (hneg i) (ε i))

lemma odd_signFlip {X : ℝ → ℝ} (hodd : Function.Odd X) (b : Bool) (x : ℝ) :
    X (signFlip b x) = observationSign b * X x := by
  cases b <;> simp [signFlip, observationSign, hodd x]

lemma even_moment_integrable_of_memLp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {k : ℕ} (hk : 0 < k)
    (h : MemLp X (2*k : ℕ) μ) : Integrable (fun sample => X sample ^ (2*k)) μ := by
  have hi := h.integrable_norm_pow (show 2*k ≠ 0 by omega)
  simpa only [Real.norm_eq_abs, pow_mul, sq_abs] using hi

lemma coordinate_sum_even_integrable {ι : Type*} [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (X : ι → ℝ → ℝ) (a : ι → ℝ)
    {k : ℕ} (hk : 0 < k) (hi : ∀ i, MemLp (X i) (2*k : ℕ) (μ i)) :
    Integrable (fun x => (∑ i, a i * X i (x i)) ^ (2*k)) (Measure.pi μ) := by
  apply even_moment_integrable_of_memLp hk
  exact memLp_finsetSum univ (fun i _ =>
    ((hi i).comp_measurePreserving (measurePreserving_eval μ i)).const_mul (a i))

lemma odd_coordinate_sum_moment_invariant {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hneg : ∀ i, MeasurePreserving Neg.neg (μ i) (μ i))
    (X : ι → ℝ → ℝ) (hodd : ∀ i, Function.Odd (X i))
    (a : ι → ℝ) (ε : ι → Bool) (k : ℕ) :
    (∫ x, (∑ i, (a i * X i (x i)) * observationSign (ε i)) ^ (2*k) ∂Measure.pi μ) =
      ∫ x, (∑ i, a i * X i (x i)) ^ (2*k) ∂Measure.pi μ := by
  have hp := signFlipPi_preserving μ hneg ε
  have he := hp.integral_comp' (fun x => (∑ i, a i * X i (x i)) ^ (2*k))
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext x
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change a i * X i (x i) * observationSign (ε i) = a i * X i (signFlip (ε i) (x i))
  rw [odd_signFlip (hodd i)]
  ring

lemma integral_finite_swap {Ω β : Type*} [MeasurableSpace Ω]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {μ : Measure Ω} {ν : Measure β} [IsFiniteMeasure ν]
    (F : β → Ω → ℝ) (hi : ∀ b, Integrable (F b) μ) :
    (∫ x, (∫ b, F b x ∂ν) ∂μ) = ∫ b, (∫ x, F b x ∂μ) ∂ν := by
  simp_rw [integral_fintype (μ := ν) Integrable.of_finite]
  simp only [smul_eq_mul]
  rw [integral_finsetSum univ (fun b _ => (hi b).const_mul (ν.real {b}))]
  simp only [integral_const_mul]

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

lemma integral_comp_preserving_of_measurable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {f : α → β} (hf : MeasurePreserving f μ ν) {g : β → ℝ} (hg : Measurable g) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  calc
    _ = ∫ y, g y ∂μ.map f := (integral_map hf.aemeasurable hg.aestronglyMeasurable).symm
    _ = _ := by rw [hf.map_eq]

theorem symmetric_directional_moment_le {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hneg : ∀ i, MeasurePreserving Neg.neg (μ i) (μ i))
    (X : ι → ℝ → ℝ) (hX : ∀ i, Measurable (X i))
    (hodd : ∀ i, Function.Odd (X i)) (a : ι → ℝ) {k : ℕ} (hk : 0 < k)
    (hMem : ∀ i, MemLp (X i) (2*k : ℕ) (μ i))
    (M : ℝ) (hMom : ∀ i, (∫ u, X i u ^ (2*k) ∂μ i) ≤ M^(2*k)) :
    (∫ x, (∑ i, a i * X i (x i)) ^ (2*k) ∂Measure.pi μ) ≤
      (8 * Real.exp 1 * k)^k * (∑ i, a i^2)^k * M^(2*k) := by
  classical
  obtain ⟨l, rfl⟩ : ∃ l, k = l+1 := ⟨k-1, by omega⟩
  let A : ℝ := ∑ i, a i^2
  let Y : (ι → ℝ) → ℝ := fun x => ∑ i, a i^2 * X i (x i)^2
  let L : ℝ := 8 * Real.exp 1 * (l+1)
  let F : (ι → Bool) → (ι → ℝ) → ℝ :=
    fun ε x => (∑ i, (a i * X i (x i)) * observationSign (ε i)) ^ (2*(l+1))
  have hA : 0 ≤ A := sum_nonneg (fun i _ => sq_nonneg (a i))
  have hY : ∀ x, 0 ≤ Y x := fun x =>
    sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hmY : Measurable Y := by
    apply Finset.measurable_sum
    intro i _
    exact ((hX i).comp (measurable_pi_apply i) |>.pow_const 2).const_mul _
  have hXi (i : ι) : Integrable (fun x : ι → ℝ => (X i (x i)^2)^(l+1)) (Measure.pi μ) := by
    have hh := even_moment_integrable_of_memLp hk
      ((hMem i).comp_measurePreserving (measurePreserving_eval μ i))
    simpa only [Function.comp_apply, pow_mul] using hh
  have hJ (x : ι → ℝ) : Y x ^ (l+1) ≤
      A^l * ∑ i, a i^2 * (X i (x i)^2)^(l+1) :=
    weighted_pow_sum_le (fun i => a i^2) (fun i => X i (x i)^2)
      (fun i => sq_nonneg _) (fun i => sq_nonneg _) l
  have hB : Integrable (fun x : ι → ℝ => A^l * ∑ i, a i^2 *
      (X i (x i)^2)^(l+1)) (Measure.pi μ) :=
    (integrable_finsetSum univ (fun i _ => (hXi i).const_mul (a i^2))).const_mul _
  have hiY : Integrable (fun x => Y x^(l+1)) (Measure.pi μ) := by
    refine hB.mono' (hmY.pow_const _).aestronglyMeasurable (ae_of_all _ ?_)
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hY x) _)]
    exact hJ x
  have hiF (ε : ι → Bool) : Integrable (F ε) (Measure.pi μ) := by
    have hh := coordinate_sum_even_integrable μ X
      (fun i => a i * observationSign (ε i)) hk hMem
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    dsimp [F]
    congr 1
    apply sum_congr rfl
    intro i _
    ring
  have hiAvg : Integrable (fun x => ∫ ε, F ε x ∂signProduct ι) (Measure.pi μ) := by
    simp_rw [integral_fintype (μ := signProduct ι) Integrable.of_finite]
    simp only [smul_eq_mul]
    exact integrable_finsetSum univ (fun ε _ => (hiF ε).const_mul ((signProduct ι).real {ε}))
  have havg : (∫ x, (∫ ε, F ε x ∂signProduct ι) ∂Measure.pi μ) =
      ∫ x, (∑ i, a i * X i (x i)) ^ (2*(l+1)) ∂Measure.pi μ := by
    rw [integral_finite_swap F hiF]
    have hh (ε : ι → Bool) : (∫ x, F ε x ∂Measure.pi μ) =
        ∫ x, (∑ i, a i * X i (x i)) ^ (2*(l+1)) ∂Measure.pi μ :=
      odd_coordinate_sum_moment_invariant μ hneg X hodd a ε (l+1)
    simp_rw [hh]
    simp
  have hpoint (x : ι → ℝ) : (∫ ε, F ε x ∂signProduct ι) ≤ L^(l+1) * Y x^(l+1) := by
    have hh := sign_sum_even_moment_le (fun i => a i * X i (x i)) hk
    simpa only [F, Y, L, mul_pow, Nat.cast_add, Nat.cast_one] using hh
  have hAvg := integral_mono hiAvg (hiY.const_mul (L^(l+1))) hpoint
  rw [havg, integral_const_mul] at hAvg
  have hYbound : (∫ x, Y x^(l+1) ∂Measure.pi μ) ≤ A^(l+1) * M^(2*(l+1)) := by
    have hh := integral_weighted_pow_sum_le (fun i => a i^2)
      (fun (i : ι) (x : ι → ℝ) => X i (x i)^2) (fun i => sq_nonneg _)
      (fun i x => sq_nonneg _) l hiY hXi
    have hscalar (i : ι) : (∫ x : ι → ℝ, (X i (x i)^2)^(l+1) ∂Measure.pi μ) ≤
        M^(2*(l+1)) := by
      simp_rw [← pow_mul]
      rw [integral_comp_preserving_of_measurable (measurePreserving_eval μ i)
        ((hX i).pow_const (2*(l+1)))]
      exact hMom i
    calc
      _ ≤ A^l * ∑ i, a i^2 * (∫ x : ι → ℝ, (X i (x i)^2)^(l+1) ∂Measure.pi μ) := hh
      _ ≤ A^l * ∑ i, a i^2 * M^(2*(l+1)) := by
        gcongr with i
        exact hscalar i
      _ = _ := by rw [← sum_mul]; dsimp [A]; ring
  calc
    _ ≤ L^(l+1) * (∫ x, Y x^(l+1) ∂Measure.pi μ) := hAvg
    _ ≤ L^(l+1) * (A^(l+1) * M^(2*(l+1))) :=
      mul_le_mul_of_nonneg_left hYbound (by dsimp [L]; positivity)
    _ = _ := by dsimp [L, A]; push_cast; ring

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ScoreDirectional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ScoreDirectional_scope

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal BigOperators

lemma compactNoiseScore_memLp {k : ℕ} (hk : 0 < k) :
    MemLp compactNoiseScore (2*k : ℕ) compactNoiseLaw := by
  apply (integrable_norm_rpow_iff compactNoiseScore_measurable.aestronglyMeasurable
    (show (2*k : ℕ) ≠ (0:ℝ≥0∞) by exact_mod_cast (by omega : 2*k ≠ 0))
    (by finiteness)).mp
  simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs, pow_mul, sq_abs]
    using compactNoiseScore_moment_integrable k

def observationMomentConstant : ℝ := 8 * Real.exp 1 * compactScoreConstant^2

lemma observationMomentConstant_pos : 0 < observationMomentConstant := by
  unfold observationMomentConstant
  have := compactScoreConstant_pos
  positivity

theorem compactNoiseScore_directional_moment {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {k : ℕ} (hk : 0 < k) :
    (∫ u : ι → ℝ, (∑ i, a i * compactNoiseScore (u i))^(2*k)
      ∂Measure.pi (fun _ => compactNoiseLaw)) ≤
      (observationMomentConstant * (k:ℝ)^5 * (∑ i, a i^2))^k := by
  have hh := symmetric_directional_moment_le (fun _ : ι => compactNoiseLaw)
    (fun _ => compactNoiseLaw_neg_preserving) (fun _ => compactNoiseScore)
    (fun _ => compactNoiseScore_measurable) (fun _ => compactNoiseScore_odd) a hk
    (fun _ => compactNoiseScore_memLp hk) (compactScoreConstant*(k:ℝ)^2)
    (fun _ => compactNoiseScore_moment_le hk)
  refine hh.trans_eq ?_
  rw [pow_mul (compactScoreConstant*(k:ℝ)^2) 2 k, ← mul_pow, ← mul_pow]
  congr 1
  dsimp [observationMomentConstant]
  ring

end Work_ScoreDirectional_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

lemma integral_even_pow_le_mass {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (f : Ω → ℝ) {k : ℕ} (hk : 0 < k)
    (hf : Integrable f μ) (hpow : Integrable (fun x => f x^(2*k)) μ)
    (hp : 0 < μ.real univ) :
    (∫ x, f x ∂μ)^(2*k) ≤ (μ.real univ)^(2*k-1) * ∫ x, f x^(2*k) ∂μ := by
  have : NeZero μ := ⟨fun hz => by simp [hz] at hp⟩
  have hev : Even (2*k) := ⟨k, by omega⟩
  have hh := hev.convexOn_pow (𝕜 := ℝ) |>.map_average_le
    (continuous_pow (2*k)).continuousOn isClosed_univ (ae_of_all _ (fun _ => mem_univ _)) hf hpow
  simp only [average_eq, smul_eq_mul] at hh
  have he : (μ.real univ)^(2*k) = (μ.real univ)^(2*k-1) * μ.real univ := by
    rw [← pow_succ]; congr 1; omega
  calc
    _ = (μ.real univ)^(2*k) * ((μ.real univ)⁻¹ * ∫ x, f x ∂μ)^(2*k) := by
      rw [← mul_pow, mul_inv_cancel_left₀ (ne_of_gt hp)]
    _ ≤ (μ.real univ)^(2*k) * ((μ.real univ)⁻¹ * ∫ x, f x^(2*k) ∂μ) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg hp.le _)
    _ = _ := by rw [he]; field_simp

lemma event_even_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (f : Ω → ℝ) {k : ℕ} (hk : 0 < k)
    (hf : Integrable f μ) (hpow : Integrable (fun x => f x^(2*k)) μ)
    (s : Set Ω) (hp : 0 < μ.real s) :
    (∫ x in s, f x ∂μ)^(2*k) ≤ (μ.real s)^(2*k-1) * ∫ x, f x^(2*k) ∂μ := by
  have hh := integral_even_pow_le_mass f hk hf.integrableOn hpow.integrableOn
    (by simpa only [measureReal_restrict_apply_univ] using hp : 0 < (μ.restrict s).real univ)
  rw [measureReal_restrict_apply_univ] at hh
  refine hh.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hp.le _))
  exact setIntegral_le_integral hpow (ae_of_all _ (fun x => by change 0 ≤ f x^(2*k); rw [pow_mul]; positivity))

theorem compactNoiseScore_event_moment {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {k : ℕ} (hk : 0 < k) (s : Set (ι → ℝ))
    (hp : 0 < (Measure.pi (fun _ : ι => compactNoiseLaw)).real s) :
    (∫ u in s, (∑ i, a i * compactNoiseScore (u i))
      ∂Measure.pi (fun _ => compactNoiseLaw))^(2*k) ≤
      ((Measure.pi (fun _ : ι => compactNoiseLaw)).real s)^(2*k-1) *
        (observationMomentConstant * (k:ℝ)^5 * (∑ i, a i^2))^k := by
  classical
  have hm : MemLp (fun u : ι → ℝ => ∑ i, a i * compactNoiseScore (u i))
      (2*k : ℕ) (Measure.pi (fun _ => compactNoiseLaw)) := by
    apply memLp_finsetSum
    intro i _
    exact ((compactNoiseScore_memLp hk).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => compactNoiseLaw) i)).const_mul (a i)
  have hf := hm.integrable (by exact_mod_cast (show 1 ≤ 2*k by omega))
  have hpow := coordinate_sum_even_integrable (fun _ : ι => compactNoiseLaw)
    (fun _ => compactNoiseScore) a hk (fun _ => compactNoiseScore_memLp hk)
  exact (event_even_moment_le _ hk hf hpow s hp).trans
    (mul_le_mul_of_nonneg_left (compactNoiseScore_directional_moment a hk) (by positivity))

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

lemma compactNoiseScore_eval_integrable {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun u : ι → ℝ => compactNoiseScore (u i))
      (Measure.pi (fun _ => compactNoiseLaw)) := by
  exact ((compactNoiseScore_memLp (by decide : 0 < 1)).comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => compactNoiseLaw) i)).integrable (by norm_num)

def eventScore {J I : Type*} [Fintype J] [Fintype I] (b : J → ℝ)
    (s : Set (J × I → ℝ)) (i : I) : ℝ :=
  ∫ u in s, (∑ j, b j * compactNoiseScore (u (j,i)))
    ∂Measure.pi (fun _ : J × I => compactNoiseLaw)

lemma eventScore_direction {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) (v : I → ℝ) :
    (∫ u in s, (∑ q : J × I, (b q.1 * v q.2) * compactNoiseScore (u q))
      ∂Measure.pi (fun _ => compactNoiseLaw)) = ∑ i, v i * eventScore b s i := by
  classical
  simp only [Fintype.sum_prod_type]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ =>
    ((compactNoiseScore_eval_integrable (j,i)).const_mul (b j * v i)).integrableOn))]
  simp_rw [integral_finsetSum _ (fun i _ =>
    ((compactNoiseScore_eval_integrable (_,i)).const_mul _).integrableOn)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [eventScore]
  rw [integral_finsetSum _ (fun j _ =>
    ((compactNoiseScore_eval_integrable (j,i)).const_mul _).integrableOn), mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [integral_const_mul]
  ring

theorem compactNoise_eventScore_pow {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) {k : ℕ} (hk : 0 < k)
    (hp : 0 < (Measure.pi (fun _ : J × I => compactNoiseLaw)).real s) :
    (∑ i, (eventScore b s i)^2)^k ≤
      ((Measure.pi (fun _ : J × I => compactNoiseLaw)).real s)^(2*k-1) *
        (observationMomentConstant * (k:ℝ)^5 * (∑ j, (b j)^2))^k := by
  classical
  let v := eventScore b s
  let W : ℝ := ∑ i, (v i)^2
  have hW : 0 ≤ W := sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hzero : W = 0
  · change W^k ≤ _
    rw [hzero, zero_pow (by omega)]
    have hC := observationMomentConstant_pos
    positivity
  have hWp : 0 < W := lt_of_le_of_ne hW (Ne.symm hzero)
  have hh := compactNoiseScore_event_moment (fun q : J × I => b q.1 * v q.2) hk s hp
  rw [eventScore_direction] at hh
  have hid : (∑ i, v i * eventScore b s i) = W := by
    dsimp [W, v]; congr 1; funext i; ring
  rw [hid] at hh
  have ha : (∑ q : J × I, (b q.1 * v q.2)^2) = (∑ j, (b j)^2) * W := by
    simp only [Fintype.sum_prod_type, mul_pow]
    simp only [← mul_sum, W, sum_mul]
  rw [ha, ← mul_assoc _ _ W, mul_pow, pow_mul, pow_two] at hh
  change W^k ≤ _
  exact (mul_le_mul_iff_left₀ (pow_pos hWp k)).mp
    (by simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hh)

theorem compactNoise_eventScore_sq {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) {k : ℕ} (hk : 0 < k)
    (hp : 0 < (Measure.pi (fun _ : J × I => compactNoiseLaw)).real s) :
    (∑ i, (eventScore b s i)^2) ≤
      observationMomentConstant * (k:ℝ)^5 * (∑ j, (b j)^2) *
      ((Measure.pi (fun _ : J × I => compactNoiseLaw)).real s) ^
        (2 - (k:ℝ)⁻¹) := by
  let p := (Measure.pi (fun _ : J × I => compactNoiseLaw)).real s
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have he : (2 - (k:ℝ)⁻¹) * k = (2*k-1 : ℕ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*k), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    field_simp
  apply (pow_le_pow_iff_left₀ (sum_nonneg (fun _ _ => sq_nonneg _))
    (by have hC := observationMomentConstant_pos; positivity) (by omega : k ≠ 0)).mp
  rw [mul_pow, ← Real.rpow_natCast (p ^ (2 - (k:ℝ)⁻¹)), ← Real.rpow_mul hp.le, he,
    Real.rpow_natCast, mul_comm]
  exact compactNoise_eventScore_pow b s hk hp

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservationLikelihood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservationLikelihood_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff Convolution

def shiftedObservationEvent {ι : Type*} [Fintype ι] (s : Set (ι → ℝ)) (z : ι → ℝ) :
    Set (ι → ℝ) := (fun u => z + u) ⁻¹' s

lemma shiftedObservationEvent_measurable {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    MeasurableSet (shiftedObservationEvent s z) :=
  hs.preimage (measurable_const.add measurable_id)

def observationLikelihood {ι : Type*} [Fintype ι] (s : Set (ι → ℝ)) : (ι → ℝ) → ℝ :=
  (s.indicator (fun _ => 1)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] compactNoiseKernel

lemma observationLikelihood_eq_probability {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    observationLikelihood s z =
      (Measure.pi (fun _ : ι => compactNoiseLaw)).real (shiftedObservationEvent s z) := by
  rw [observationLikelihood, convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  rw [← integral_add_left_eq_self _ z]
  have he : (fun u : ι → ℝ => s.indicator (fun _ => (1:ℝ)) (z + u) *
      compactNoiseKernel (z - (z + u))) =
      (fun u => compactNoiseKernel u * (shiftedObservationEvent s z).indicator 1 u) := by
    funext u
    rw [show z - (z+u) = -u by abel, compactNoiseKernel_even]
    by_cases hu : z + u ∈ s <;> simp [shiftedObservationEvent, hu, Set.mem_preimage]
  rw [he, ← compactNoiseLaw_pi_integral, integral_indicator_one
    (shiftedObservationEvent_measurable hs z)]

lemma observationLikelihood_nonneg {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    0 ≤ observationLikelihood s z := by
  rw [observationLikelihood_eq_probability hs]
  exact measureReal_nonneg

lemma observationLikelihood_le_one {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    observationLikelihood s z ≤ 1 := by
  rw [observationLikelihood_eq_probability hs]
  exact measureReal_le_one

lemma observationLikelihood_contDiff {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) {n : ℕ∞} :
    ContDiff ℝ n (observationLikelihood s) :=
  compactNoiseKernel_compactSupport.contDiff_convolution_right _
    (continuous_const.locallyIntegrable.indicator hs) compactNoiseKernel_contDiff

lemma observationLikelihood_fderiv {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z v : ι → ℝ) :
    fderiv ℝ (observationLikelihood s) z v =
      -(∫ u in shiftedObservationEvent s z, (∑ i, v i * compactNoiseScore (u i))
        ∂Measure.pi (fun _ : ι => compactNoiseLaw)) := by
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hloc : LocallyIntegrable (s.indicator (fun _ => (1:ℝ))) volume :=
    continuous_const.locallyIntegrable.indicator hs
  have hder := compactNoiseKernel_compactSupport.hasFDerivAt_convolution_right L hloc
    (compactNoiseKernel_contDiff (n := 1)) z
  have hint := (compactNoiseKernel_compactSupport.fderiv ℝ).convolutionExists_right
    (L.precompR (ι → ℝ)) hloc
    ((compactNoiseKernel_contDiff (n := 1)).continuous_fderiv one_ne_zero) z
  change fderiv ℝ ((s.indicator (fun _ => (1:ℝ))) ⋆[L, volume] compactNoiseKernel) z v = _
  rw [hder.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint v]
  simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, L, ContinuousLinearMap.mul_apply', compactNoiseKernel_fderiv_apply]
  rw [← integral_add_left_eq_self _ z]
  rw [← integral_indicator (shiftedObservationEvent_measurable hs z), compactNoiseLaw_pi_integral,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [show z - (z+u) = -u by abel, compactNoiseKernel_even]
  have hodd (r : ℝ) : compactNoiseScore (-r) = -compactNoiseScore r :=
    compactNoiseScore_odd r
  by_cases hu : z + u ∈ s <;>
    simp [Pi.neg_apply, hodd, shiftedObservationEvent, hu, Set.mem_preimage,
      mul_comm, Finset.sum_neg_distrib]

end Work_ObservationLikelihood_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

def observationPlacement {J I : Type*} [Fintype J] [Fintype I] (b : J → ℝ) :
    (I → ℝ) →L[ℝ] (J × I → ℝ) :=
  ContinuousLinearMap.pi (fun q => b q.1 • (ContinuousLinearMap.proj q.2 : (I → ℝ) →L[ℝ] ℝ))

@[simp] lemma observationPlacement_apply {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (x : I → ℝ) (q : J × I) :
    observationPlacement b x q = b q.1 * x q.2 := rfl

def arrayLikelihood {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) (x : I → ℝ) : ℝ :=
  observationLikelihood s (observationPlacement b x)

def arrayScore {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) (x : I → ℝ) : I → ℝ :=
  eventScore b (shiftedObservationEvent s (observationPlacement b x))

lemma arrayLikelihood_eq_probability {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ) :
    arrayLikelihood b s x = (Measure.pi (fun _ : J × I => compactNoiseLaw)).real
      (shiftedObservationEvent s (observationPlacement b x)) :=
  observationLikelihood_eq_probability hs _

lemma arrayLikelihood_nonneg {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ) :
    0 ≤ arrayLikelihood b s x := observationLikelihood_nonneg hs _

lemma arrayLikelihood_le_one {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ) :
    arrayLikelihood b s x ≤ 1 := observationLikelihood_le_one hs _

lemma arrayLikelihood_contDiff {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) {n : ℕ∞} :
    ContDiff ℝ n (arrayLikelihood b s) :=
  (observationLikelihood_contDiff hs).comp (observationPlacement (I := I) b).contDiff

lemma arrayLikelihood_fderiv {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x v : I → ℝ) :
    fderiv ℝ (arrayLikelihood b s) x v = -∑ i, v i * arrayScore b s x i := by
  have hh := ((observationLikelihood_contDiff hs (n := 1)).differentiable one_ne_zero
    (observationPlacement b x)).hasFDerivAt.comp x (observationPlacement b).hasFDerivAt
  change fderiv ℝ (observationLikelihood s ∘ observationPlacement b) x v = _
  rw [hh.fderiv, ContinuousLinearMap.comp_apply, observationLikelihood_fderiv hs]
  simp only [observationPlacement_apply]
  rw [eventScore_direction]
  rfl

lemma eventScore_zero {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) (s : Set (J × I → ℝ))
    (hp : (Measure.pi (fun _ : J × I => compactNoiseLaw)).real s = 0) (i : I) :
    eventScore b s i = 0 := by
  have hμ := (measureReal_eq_zero_iff (μ := Measure.pi (fun _ : J × I => compactNoiseLaw))).mp hp
  simp [eventScore, Measure.restrict_eq_zero.mpr hμ]

lemma arrayScore_sq {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ)
    {k : ℕ} (hk : 0 < k) :
    (∑ i, (arrayScore b s x i)^2) ≤
      observationMomentConstant * (k:ℝ)^5 * (∑ j, (b j)^2) *
        (arrayLikelihood b s x)^(2-(k:ℝ)⁻¹) := by
  rw [arrayLikelihood_eq_probability b hs]
  by_cases hp : 0 < (Measure.pi (fun _ : J × I => compactNoiseLaw)).real
      (shiftedObservationEvent s (observationPlacement b x))
  · exact compactNoise_eventScore_sq b _ hk hp
  have hz : (Measure.pi (fun _ : J × I => compactNoiseLaw)).real
      (shiftedObservationEvent s (observationPlacement b x)) = 0 :=
    le_antisymm (not_lt.mp hp) measureReal_nonneg
  simp only [arrayScore, eventScore_zero b _ hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sum_const_zero]
  have hC := observationMomentConstant_pos
  positivity

lemma arrayScore_sq_one {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s) (x : I → ℝ) :
    (∑ i, (arrayScore b s x i)^2) ≤
      observationMomentConstant * (∑ j, (b j)^2) * arrayLikelihood b s x := by
  simpa only [Nat.cast_one, one_pow, mul_one, inv_one, show (2:ℝ)-1=1 by norm_num, Real.rpow_one] using arrayScore_sq b hs x (k := 1) (by decide)

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ArraySymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ArraySymmetry_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace CoulombObservation

def arrayReindex {J I : Type*} [Fintype J] [Fintype I] (e : Equiv.Perm I) :
    (J × I → ℝ) ≃ᵐ (J × I → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) ((Equiv.refl J).prodCongr e.symm)

@[simp] lemma arrayReindex_apply {J I : Type*} [Fintype J] [Fintype I]
    (e : Equiv.Perm I) (u : J × I → ℝ) (q : J × I) :
    arrayReindex e u q = u (q.1,e q.2) := by
  rcases q with ⟨j,i⟩
  simp [arrayReindex, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft]

lemma arrayReindex_preserving {J I : Type*} [Fintype J] [Fintype I]
    (e : Equiv.Perm I) :
    MeasurePreserving (arrayReindex (J := J) e)
      (Measure.pi (fun _ : J × I => compactNoiseLaw))
      (Measure.pi (fun _ : J × I => compactNoiseLaw)) :=
  measurePreserving_piCongrLeft (fun _ => compactNoiseLaw) _

lemma arrayLikelihood_reindex {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) {s : Set (J × I → ℝ)} (hs : MeasurableSet s)
    (e : Equiv.Perm I) (hinv : ∀ u, arrayReindex (J := J) e u ∈ s ↔ u ∈ s)
    (x : I → ℝ) : arrayLikelihood b s (x ∘ e) = arrayLikelihood b s x := by
  rw [arrayLikelihood_eq_probability b hs, arrayLikelihood_eq_probability b hs]
  unfold Measure.real
  congr 1
  have hset : (arrayReindex (J := J) e) ⁻¹'
      shiftedObservationEvent s (observationPlacement b (x ∘ e)) =
      shiftedObservationEvent s (observationPlacement b x) := by
    ext u
    change observationPlacement b (x ∘ e) + arrayReindex e u ∈ s ↔
      observationPlacement b x + u ∈ s
    have he : observationPlacement b (x ∘ e) + arrayReindex e u =
        arrayReindex e (observationPlacement b x + u) := by
      ext q
      simp only [Pi.add_apply, observationPlacement_apply, Function.comp_apply, arrayReindex_apply]
    rw [he]
    exact hinv _
  rw [← (arrayReindex_preserving e).measure_preimage
    (shiftedObservationEvent_measurable hs _).nullMeasurableSet, hset]

end CoulombObservation

end Work_ArraySymmetry_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom
open CoulombObservation

def QuantumEventSymmetric {N : ℕ} {J : Type*} [Fintype J]
    (s : Set (J × (Fin N × Fin 3) → ℝ)) : Prop :=
  ∀ (π : Equiv.Perm (Fin N)) u,
    arrayReindex (J := J) (π.prodCongr (Equiv.refl (Fin 3))) u ∈ s ↔ u ∈ s

end CoulombAtom

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

section Affine
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

lemma memLp_comp_real_smul {f : E → ℂ} {p : ENNReal} (hf : MemLp f p)
    {b : ℝ} (hb : b ≠ 0) : MemLp (fun x => f (b • x)) p := by
  apply MemLp.comp_of_map (f := fun x : E => b • x) _ ((continuous_id.const_smul b).measurable.aemeasurable)
  rw [Measure.map_addHaar_smul volume hb]
  exact hf.smul_measure (by simp)

lemma memLp_comp_affine {f : E → ℂ} {p : ENNReal} (hf : MemLp f p)
    {b : ℝ} (hb : b ≠ 0) (t : E) : MemLp (fun x => f (b • x+t)) p := by
  exact memLp_comp_real_smul (hf.comp_measurePreserving (measurePreserving_add_right volume t)) hb

lemma integral_comp_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) {b : ℝ} (hb : 0 < b) (t : E) :
    (∫ x, f (b • x+t)) = (b ^ Module.finrank ℝ E)⁻¹ • ∫ x, f x := by
  rw [Measure.integral_comp_smul_of_nonneg volume (fun x => f (x+t)) b (hR := hb.le),
    integral_add_right_eq_self]

end Affine
variable {N : ℕ}

def gridTranslation (t : Fin 3 → ℝ) : (Fin N × Fin 3) → ℝ := fun q => t q.2

def affineGrid (b : ℝ) (t : Fin 3 → ℝ) (x : (Fin N × Fin 3) → ℝ) :=
  b • x + gridTranslation t

def affineGridInv (b : ℝ) (t : Fin 3 → ℝ) (x : (Fin N × Fin 3) → ℝ) :=
  b⁻¹ • (x-gridTranslation t)

@[simp] lemma affineGridInv_affineGrid {b : ℝ} (hb : b ≠ 0) (t : Fin 3 → ℝ)
    (x : (Fin N × Fin 3) → ℝ) : affineGridInv b t (affineGrid b t x) = x := by
  simp [affineGridInv,affineGrid,smul_smul,hb]

@[simp] lemma affineGrid_affineGridInv {b : ℝ} (hb : b ≠ 0) (t : Fin 3 → ℝ)
    (x : (Fin N × Fin 3) → ℝ) : affineGrid b t (affineGridInv b t x) = x := by
  simp [affineGridInv,affineGrid,smul_smul,hb]

lemma affineGrid_anti {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (ha : FlatAntisymmetric f) (b : ℝ) (t : Fin 3 → ℝ) :
    FlatAntisymmetric (fun s x => f s (affineGrid b t x)) := by
  intro i j hij s x
  convert ha i j hij s (affineGrid b t x) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

lemma affineGrid_contDiff (b : ℝ) (t : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (affineGrid (N := N) b t) := by
  change ContDiff ℝ ∞ (fun x : (Fin N × Fin 3) → ℝ => b • x + gridTranslation t)
  exact (contDiff_id.const_smul b).add contDiff_const

lemma affineGrid_fderiv {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (b : ℝ) (t : Fin 3 → ℝ) (x : (Fin N × Fin 3) → ℝ) (q : Fin N × Fin 3) :
    fderiv ℝ (fun y => f (affineGrid b t y)) x (Pi.single q 1) =
      b • fderiv ℝ f (affineGrid b t x) (Pi.single q 1) := by
  have h := (hf.differentiable (by simp) (affineGrid b t x)).hasFDerivAt.comp x
    (((hasFDerivAt_id x).const_smul b).add_const (gridTranslation t))
  have hh := congrArg (fun L : ((Fin N × Fin 3) → ℝ) →L[ℝ] ℂ => L (Pi.single q 1)) h.fderiv
  simpa only [ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearMap.id_apply,map_smul,Function.comp_def] using hh

def gridPressure (b : ℝ) (t : Fin 3 → ℝ) (x : (Fin N × Fin 3) → ℝ) : ℝ :=
  b⁻¹^2 * cellPressure (pointCell (affineGridInv b t x))

lemma gridPressure_nonneg (b : ℝ) (t : Fin 3 → ℝ) (x : (Fin N × Fin 3) → ℝ) :
    0 ≤ gridPressure b t x := mul_nonneg (sq_nonneg _) (cellPressure_nonneg _)

lemma gridPressure_bound (b : ℝ) (t : Fin 3 → ℝ) (x : (Fin N × Fin 3) → ℝ) :
    gridPressure b t x ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ) :=
  mul_le_mul_of_nonneg_left (cellPressure_le _) (sq_nonneg _)

lemma gridPressure_measurable (b : ℝ) (t : Fin 3 → ℝ) :
    Measurable (gridPressure (N := N) b t) := by
  apply measurable_const.mul
  apply flatPressure_measurable.comp
  change Measurable (fun x : (Fin N × Fin 3) → ℝ => b⁻¹ • (x-gridTranslation t))
  exact ((continuous_id.sub continuous_const).const_smul b⁻¹).measurable

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_PhysicalGridMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

namespace CoulombNeumann
variable {N : ℕ}

def physicalGridPressure (b : ℝ) (R : CubeRotation) (t : Fin 3 → I) (x : (Fin N → CubeSpace)) : ℝ :=
  b⁻¹^2*cellPressure (cubeAssignment (fun a => (t a:ℝ)) (rotatedCubeCloud R (fun i => b⁻¹ • x i)))

lemma physicalGridPressure_nonneg (b : ℝ) (R : CubeRotation) (t : Fin 3 → I) (x : (Fin N → CubeSpace)) :
    0 ≤ physicalGridPressure b R t x := mul_nonneg (sq_nonneg _) (cellPressure_nonneg _)
lemma physicalGridPressure_le (b : ℝ) (R : CubeRotation) (t : Fin 3 → I) (x : (Fin N → CubeSpace)) :
    physicalGridPressure b R t x ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ) :=
  mul_le_mul_of_nonneg_left (cellPressure_le _) (sq_nonneg _)

lemma physicalGridCloud_continuous (b : ℝ) :
    Continuous (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) =>
      rotatedCubeCloud p.1.1 (fun i => b⁻¹ • p.2 i)) := by
  have hx : Continuous (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) =>
      fun i => b⁻¹ • p.2 i) :=
    continuous_pi (fun i => ((continuous_apply i).comp continuous_snd).const_smul b⁻¹)
  have hr : Continuous (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) => p.1.1) := by fun_prop
  have hh : Continuous (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) =>
      (p.1.1,fun i => b⁻¹ • p.2 i)) := hr.prodMk hx
  have hcomp := (rotatedCubeCloud_continuous (N := N)).comp hh
  simpa only [Function.comp_def] using hcomp

lemma physicalGridCell_measurable (b : ℝ) :
    Measurable (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) =>
      cellPressure (cubeAssignment (fun a => (p.1.2 a:ℝ))
        (rotatedCubeCloud p.1.1 (fun i => b⁻¹ • p.2 i)))) := by
  have ht : Measurable (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) =>
      fun a => (p.1.2 a:ℝ)) :=
    cube_t_continuous.measurable.comp (measurable_snd.comp measurable_fst)
  have hin := ht.prodMk (physicalGridCloud_continuous (N := N) b).measurable
  have hcomp := (cubePressure_measurable (N := N)).comp hin
  simpa only [Function.comp_def] using hcomp

lemma physicalGridPressure_measurable (b : ℝ) :
    Measurable (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) => physicalGridPressure b p.1.1 p.1.2 p.2) := by
  unfold physicalGridPressure
  exact (physicalGridCell_measurable (N := N) b).const_mul (b⁻¹^2)

lemma physicalGridPressure_fixed_measurable (b : ℝ) (R : CubeRotation) (t : Fin 3 → I) :
    Measurable (physicalGridPressure (N := N) b R t) := by
  let f : (Fin N → CubeSpace) → ((CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace)) := fun x => ((R,t),x)
  have hf : Measurable f := measurable_const.prodMk measurable_id
  have hcomp := (physicalGridPressure_measurable (N := N) b).comp hf
  simpa only [Function.comp_def,f] using hcomp

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RotationTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_RotationTrace_scope

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

lemma sum_norm_sq_basis_eq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E)
    (d : OrthonormalBasis ν ℝ F) (L : E →L[ℝ] F) :
    (∑ i, ‖L (b i)‖^2) = ∑ j, ‖L (c j)‖^2 := by
  have he {α : Type} [Fintype α] (a : OrthonormalBasis α ℝ E) :
      (∑ i, ‖L (a i)‖^2) = ∑ j, ‖L.adjoint (d j)‖^2 := by
    calc
      _ = ∑ i, ∑ j, ⟪d j,L (a i)⟫^2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact (d.sum_sq_inner_right _).symm
      _ = ∑ j, ∑ i, ⟪L.adjoint (d j),a i⟫^2 := by
        rw [Finset.sum_comm]
        simp_rw [ContinuousLinearMap.adjoint_inner_left]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        exact a.sum_sq_inner_left _
  exact (he b).trans (he c).symm

lemma sum_norm_sq_basis_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {ι ν : Type} [Fintype ι] [Fintype ν]
    (b : OrthonormalBasis ι ℝ E) (d : OrthonormalBasis ν ℝ F)
    (R : E ≃ₗᵢ[ℝ] E) (L : E →L[ℝ] F) :
    (∑ i, ‖L (R (b i))‖^2) = ∑ i, ‖L (b i)‖^2 :=
  sum_norm_sq_basis_eq (b.map R) b d L

end Work_RotationTrace_scope

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

open CoulombAtom
variable {N : ℕ}

lemma memLp_fderiv_apply {f : ((Fin N × Fin 3) → ℝ) → ℂ}
    (hg : ∀ q, MemLp (fun x => fderiv ℝ f x (Pi.single q 1)) 2)
    (v : (Fin N × Fin 3) → ℝ) : MemLp (fun x => fderiv ℝ f x v) 2 := by
  classical
  have hv : v = ∑ q, v q • Pi.single q (1:ℝ) := by
    ext q
    simp [Pi.single_apply]
  have he : (fun x => fderiv ℝ f x v) = fun x => ∑ q, v q • fderiv ℝ f x (Pi.single q 1) := by
    funext x
    conv_lhs => rw [hv]
    simp only [map_sum,map_smul]
  rw [he]
  exact memLp_finsetSum _ (fun q _ => (hg q).const_smul (v q))

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_PhysicalGrid
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

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

lemma rotationIsometry_inv (R : CubeRotation) : rotationIsometry R⁻¹ = (rotationIsometry R).symm :=
  map_inv Unitary.linearIsometryEquiv R

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_WeightedAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter

namespace CoulombNeumann
variable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
  {μ : Measure A} {ν : Measure X} [IsProbabilityMeasure μ] [SFinite ν]

lemma bounded_average_section_integrable {P : A → X → ℝ}
    (hm : Measurable (Function.uncurry P)) (hn : ∀ a x, 0 ≤ P a x)
    {B : ℝ} (hb : ∀ a x, P a x ≤ B) (x : X) : Integrable (fun a => P a x) μ := by
  apply (integrable_const B).mono' (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  exact Eventually.of_forall fun a => by
    change ‖P a x‖ ≤ B
    rw [Real.norm_of_nonneg (hn a x)]
    exact hb a x

lemma bounded_average_joint_integrable {P : A → X → ℝ}
    (hm : Measurable (Function.uncurry P)) (hn : ∀ a x, 0 ≤ P a x)
    {B : ℝ} (hb : ∀ a x, P a x ≤ B) {w : X → ℝ} (hw : Integrable w ν) :
    Integrable (fun p : A × X => P p.1 p.2*w p.2) (μ.prod ν) := by
  have hmi : AEStronglyMeasurable (fun p : A × X => P p.1 p.2*w p.2) (μ.prod ν) :=
    hm.aestronglyMeasurable.mul hw.aestronglyMeasurable.comp_snd
  apply (integrable_prod_iff hmi).mpr
  have hi (a : A) : Integrable (fun x => P a x*w x) ν := by
    apply hw.bdd_mul (c := B) (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact Eventually.of_forall (fun x => by change ‖P a x‖ ≤ B; rw [Real.norm_of_nonneg (hn a x)]; exact hb a x)
  refine ⟨Eventually.of_forall hi,?_⟩
  apply (integrable_const (B*(∫ x, ‖w x‖ ∂ν))).mono' hmi.norm.integral_prod_right'
  exact Eventually.of_forall fun a => by
    change ‖∫ x, ‖P a x*w x‖ ∂ν‖ ≤ B*(∫ x, ‖w x‖ ∂ν)
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),←integral_const_mul]
    apply integral_mono (hi a).norm (hw.norm.const_mul B)
    intro x
    change ‖P a x*w x‖ ≤ B*‖w x‖
    rw [norm_mul,Real.norm_of_nonneg (hn a x)]
    exact mul_le_mul_of_nonneg_right (hb a x) (norm_nonneg _)

theorem weighted_average_fubini {P : A → X → ℝ}
    (hm : Measurable (Function.uncurry P)) (hn : ∀ a x, 0 ≤ P a x)
    {B : ℝ} (hb : ∀ a x, P a x ≤ B) {w : X → ℝ} (hw : Integrable w ν) :
    (∫ x, (∫ a, P a x ∂μ)*w x ∂ν) = ∫ a, (∫ x, P a x*w x ∂ν) ∂μ := by
  simp_rw [←integral_mul_const]
  exact (integral_integral_swap (bounded_average_joint_integrable hm hn hb hw)).symm

theorem weighted_average_bound {P : A → X → ℝ}
    (hm : Measurable (Function.uncurry P)) (hn : ∀ a x, 0 ≤ P a x)
    {B : ℝ} (hb : ∀ a x, P a x ≤ B) {w : X → ℝ} (hw : Integrable w ν)
    {T E : ℝ} (h : ∀ a, T*(∫ x, P a x*w x ∂ν) ≤ E) :
    T*(∫ x, (∫ a, P a x ∂μ)*w x ∂ν) ≤ E := by
  rw [weighted_average_fubini hm hn hb hw,←integral_const_mul]
  exact (integral_mono ((bounded_average_joint_integrable hm hn hb hw).integral_prod_left.const_mul T)
    (integrable_const E) h).trans_eq (by simp)

end CoulombNeumann

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

abbrev CubePartition := CubeRotation × (Fin 3 → I)
def cubePartitionMeasure : Measure CubePartition := cubeRotationMeasure.prod volume
instance cubePartition_probability : IsProbabilityMeasure cubePartitionMeasure := by
  unfold cubePartitionMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_TFPriceData
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

def tfPriceLength (μ : ℝ) : ℝ := μ ^ (1/4:ℝ)
lemma tfPriceLength_pos {μ : ℝ} (hμ : 0 < μ) : 0 < tfPriceLength μ := Real.rpow_pos_of_pos hμ _
lemma tfPriceLength_four {μ : ℝ} (hμ : 0 < μ) : tfPriceLength μ ^ 4 = μ := by
  rw [tfPriceLength, ← Real.rpow_natCast _ 4, ← Real.rpow_mul hμ.le]
  norm_num

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CutCoreNumber
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

abbrev cutCoreNumber {L : ℕ} (b : Fin L → Fin 2) : ℕ := Fintype.card {i // b i = 0}
abbrev cutOutNumber {L : ℕ} (b : Fin L → Fin 2) : ℕ := Fintype.card {i // b i ≠ 0}

def cutOrder {L : ℕ} (b : Fin L → Fin 2) :
    Fin (cutCoreNumber b + cutOutNumber b) ≃ Fin L :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr
    (Fintype.equivFin {i // b i = 0}).symm (Fintype.equivFin {i // b i ≠ 0}).symm).trans
      (Equiv.sumCompl (fun i => b i = 0)))

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CoreMultiplierLiftBarrier
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

def liftCoreOrder {K N : ℕ} (M : ℕ) (e : Fin K ≃ Fin N) :
    Fin (K+M) ≃ Fin (N+M) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin M))).trans finSumFinEquiv)

@[simp] lemma liftCoreOrder_left {K N M : ℕ} (e : Fin K ≃ Fin N) (i : Fin K) :
    liftCoreOrder M e (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inl (e i)) := by
  simp [liftCoreOrder]

@[simp] lemma liftCoreOrder_right {K N M : ℕ} (e : Fin K ≃ Fin N) (i : Fin M) :
    liftCoreOrder M e (finSumFinEquiv (Sum.inr i)) = finSumFinEquiv (Sum.inr i) := by
  simp [liftCoreOrder]

lemma liftCoreOrder_symm {K N M : ℕ} (e : Fin K ≃ Fin N) :
    (liftCoreOrder M e).symm = liftCoreOrder M e.symm := by
  rfl

lemma liftCoreOrder_perm_comp {α : Type*} {K N M : ℕ} (e : Fin K ≃ Fin N)
    (π : Equiv.Perm (Fin K)) (f : Fin (K+M) → α) :
    (f ∘ corePerm M π) ∘ (liftCoreOrder M e).symm =
      (f ∘ (liftCoreOrder M e).symm) ∘ corePerm M (e.permCongr π) := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simp [Function.comp_apply,corePerm,liftCoreOrder,Equiv.permCongr_apply]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoreHistoryCoordinatesBarrier
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

def coreObservationAssoc (N K M : ℕ) : Fin (N+(K+M)) ≃ Fin ((N+K)+M) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin N)) finSumFinEquiv.symm).trans
      ((Equiv.sumAssoc (Fin N) (Fin K) (Fin M)).symm.trans
        ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin M))).trans finSumFinEquiv)))

lemma coreObservationAssoc_core {N K M : ℕ} (i : Fin N) :
    coreObservationAssoc N K M (finSumFinEquiv (Sum.inl i)) =
      finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl i))) := by
  simp [coreObservationAssoc]

lemma coreObservationAssoc_middle {N K M : ℕ} (i : Fin K) :
    coreObservationAssoc N K M (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl i)))) =
      finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr i))) := by
  simp [coreObservationAssoc]

lemma coreObservationAssoc_out {N K M : ℕ} (i : Fin M) :
    coreObservationAssoc N K M (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr i)))) =
      finSumFinEquiv (Sum.inr i) := by
  simp [coreObservationAssoc]

lemma coreObservationAssoc_perm_comp {α : Type*} {N K M : ℕ}
    (π : Equiv.Perm (Fin N)) (f : Fin (N+(K+M)) → α) :
    (f ∘ corePerm (K+M) π) ∘ (coreObservationAssoc N K M).symm =
      (f ∘ (coreObservationAssoc N K M).symm) ∘ corePerm M (corePerm K π) := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j =>
    obtain ⟨k,rfl⟩ := finSumFinEquiv.surjective j
    cases k <;> simp [Function.comp_apply,corePerm,coreObservationAssoc,Equiv.permCongr_apply]
  | inr j => simp [Function.comp_apply,corePerm,coreObservationAssoc,Equiv.permCongr_apply]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_SqrtMultiplier
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

def sqrtLikelihoodLipschitzConstant {J I : Type*} [Fintype J] [Fintype I]
    (b : J → ℝ) : ℝ≥0 :=
  ⟨Real.sqrt (observationMomentConstant * (∑ j, (b j)^2) * Fintype.card I),
    Real.sqrt_nonneg _⟩

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SmoothTransitionBound
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

lemma smoothTransition_deriv_zero_of_neg {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have hh : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    (eventually_lt_nhds hx).mono fun _ hy => Real.smoothTransition.zero_of_nonpos hy.le
  simpa only [deriv_const] using hh.deriv_eq

lemma smoothTransition_deriv_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have hh : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    (eventually_gt_nhds hx).mono fun _ hy => Real.smoothTransition.one_of_one_le hy.le
  simpa only [deriv_const] using hh.deriv_eq

lemma smoothTransition_deriv_compact : HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0:ℝ)) (b := 1))
  intro x hx
  constructor
  · by_contra h
    exact hx (smoothTransition_deriv_zero_of_neg (lt_of_not_ge h))
  · by_contra h
    exact hx (smoothTransition_deriv_zero_of_one_lt (lt_of_not_ge h))

lemma smoothTransition_deriv_bounded : ∃ C : ℝ, 0 < C ∧
    ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  obtain ⟨C,hC⟩ := smoothTransition_deriv_compact.exists_bound_of_continuous
    ((Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp))
  refine ⟨1 + |C|, by positivity, fun x => ?_⟩
  exact (hC x).trans (by linarith [le_abs_self C])

def smoothTransitionBound : ℝ := Classical.choose smoothTransition_deriv_bounded

lemma smoothTransitionBound_pos : 0 < smoothTransitionBound :=
  (Classical.choose_spec smoothTransition_deriv_bounded).1

lemma smoothTransition_deriv_le (x : ℝ) :
    |deriv Real.smoothTransition x| ≤ smoothTransitionBound :=
  (Classical.choose_spec smoothTransition_deriv_bounded).2 x

lemma radial_denominator_pos {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    0 < (t+b)^2-t^2 := by nlinarith

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BlockSwap
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

def blockSwap (N M : ℕ) : Fin (M+N) ≃ Fin (N+M) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin M) (Fin N)).trans finSumFinEquiv)

@[simp] lemma blockSwap_left (N M : ℕ) (i : Fin M) :
    blockSwap N M (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inr i) := by
  simp [blockSwap]

@[simp] lemma blockSwap_right (N M : ℕ) (i : Fin N) :
    blockSwap N M (finSumFinEquiv (Sum.inr i)) = finSumFinEquiv (Sum.inl i) := by
  simp [blockSwap]

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_PatchMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped ENNReal

namespace CoulombAnalysis

lemma measurable_of_distance_functions {α β : Type*} [MeasurableSpace α]
    [MetricSpace β] [SecondCountableTopology β] [MeasurableSpace β] [BorelSpace β]
    {f : α → β} (hf : ∀ z, Measurable (fun x => dist (f x) z)) : Measurable f := by
  let S : Set (Set β) := {u | ∃ z r, u = ball z r}
  have hb : IsTopologicalBasis S := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro u ⟨z,r,rfl⟩
      exact isOpen_ball
    · intro z u hzu hu
      obtain ⟨r,hr,hs⟩ := Metric.isOpen_iff.mp hu z hzu
      exact ⟨ball z r,⟨z,r,rfl⟩,mem_ball_self hr,hs⟩
  rw [‹BorelSpace β›.measurable_eq]
  change @Measurable α β _ (borel β) f
  rw [hb.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro u ⟨z,r,rfl⟩
  exact measurableSet_lt (hf z) measurable_const

local instance instMeasurableSpaceSubtypeAEEqFunRealMemAddSubgroupLpOfFactLeENNRealOfNat_solutions {β : Type*} [MeasurableSpace β] (μ : Measure β) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    MeasurableSpace (Lp ℝ p μ) := borel _
local instance instBorelSpaceSubtypeAEEqFunRealMemAddSubgroupLp_solutions {β : Type*} [MeasurableSpace β] (μ : Measure β) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    BorelSpace (Lp ℝ p μ) := ⟨rfl⟩

lemma measurable_memLp_toLp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure β} [SFinite μ] {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ⊤)]
    [SecondCountableTopology (Lp ℝ p μ)] {f : α → β → ℝ}
    (hf : Measurable (Function.uncurry f)) (hp : ∀ a, MemLp (f a) p μ) :
    Measurable (fun a => (hp a).toLp (f a)) := by
  apply measurable_of_distance_functions
  intro z
  have hd : Measurable (fun q : α × β => f q.1 q.2-z q.2) :=
    hf.sub ((Lp.stronglyMeasurable z).measurable.comp measurable_snd)
  have hslice (point : α) : AEStronglyMeasurable (fun x => f point x-z x) μ :=
    (hd.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hh : Measurable (fun a => eLpNorm (fun x => f a x-z x) p μ) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) (Fact.out : p ≠ ⊤)]
    exact ((hd.enorm.pow_const p.toReal).lintegral_prod_right').pow_const _
  convert hh.ennreal_toReal using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  rw [Lp.dist_def]
  congr 1
  apply eLpNorm_congr_ae
  exact (hp a).coeFn_toLp.sub ae_eq_rfl

def toLpOrZero {α β : Type*} [MeasurableSpace β] (μ : Measure β) (p : ℝ≥0∞)
    (f : α → β → ℝ) (a : α) : Lp ℝ p μ :=
  by
    classical
    exact if h : MemLp (f a) p μ then h.toLp (f a) else 0

lemma toLpOrZero_eq {α β : Type*} [MeasurableSpace β] {μ : Measure β}
    {p : ℝ≥0∞} {f : α → β → ℝ} {a : α} (h : MemLp (f a) p μ) :
    toLpOrZero μ p f a = h.toLp (f a) := by simp [toLpOrZero,h]

lemma toLpOrZero_congr {α β : Type*} [MeasurableSpace β] {μ : Measure β}
    {p : ℝ≥0∞} {f g : α → β → ℝ} {a : α} (h : f a =ᵐ[μ] g a) :
    toLpOrZero μ p f a = toLpOrZero μ p g a := by
  by_cases hf : MemLp (f a) p μ
  · have hg := (memLp_congr_ae h).mp hf
    rw [toLpOrZero_eq hf,toLpOrZero_eq hg]
    exact MemLp.toLp_congr hf hg h
  · have hg : ¬ MemLp (g a) p μ := fun hg => hf ((memLp_congr_ae h).mpr hg)
    simp [toLpOrZero,hf,hg]

lemma measurable_toLpOrZero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure β} [SFinite μ] {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ⊤)]
    [SecondCountableTopology (Lp ℝ p μ)] {f : α → β → ℝ}
    (hf : Measurable (Function.uncurry f)) : Measurable (toLpOrZero μ p f) := by
  classical
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hm (a : α) : AEStronglyMeasurable (f a) μ :=
    (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hn : Measurable (fun a => eLpNorm (f a) p μ) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 (Fact.out : p ≠ ⊤)]
    exact ((hf.enorm.pow_const p.toReal).lintegral_prod_right').pow_const _
  let E : Set α := {a | eLpNorm (f a) p μ < ⊤}
  have hE : MeasurableSet E := measurableSet_lt hn measurable_const
  let g : α → β → ℝ := fun a => if a ∈ E then f a else 0
  have hg : Measurable (Function.uncurry g) := by
    convert (hf.piecewise (hE.preimage measurable_fst) (measurable_const (a := (0:ℝ)))) using 1
    all_goals try with_reducible_and_instances rfl
    funext q
    change (if q.1 ∈ E then f q.1 else 0) q.2 = if q.1 ∈ E then f q.1 q.2 else 0
    split <;> rfl
  have hp (a : α) : MemLp (g a) p μ := by
    by_cases ha : a ∈ E
    · simpa only [g,ite_eq_left ha] using (show MemLp (f a) p μ from ⟨hm a, ha⟩)
    · simpa only [g,ite_eq_right ha] using (MemLp.zero : MemLp (0 : β → ℝ) p μ)
  have hh := measurable_memLp_toLp hg hp
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  by_cases ha : a ∈ E
  · have hf' : MemLp (f a) p μ := ⟨hm a, ha⟩
    rw [toLpOrZero_eq hf']
    apply Lp.ext
    have he : (hp a).toLp (g a) =ᵐ[μ] f a := by
      simpa only [g,ite_eq_left ha] using (hp a).coeFn_toLp
    exact hf'.coeFn_toLp.trans he.symm
  · have hf' : ¬ MemLp (f a) p μ := fun hf' => ha hf'.2
    simp only [toLpOrZero,dite_eq_right hf']
    apply Lp.ext
    have he : (hp a).toLp (g a) =ᵐ[μ] (0 : β → ℝ) := by
      simpa only [g,ite_eq_right ha] using (hp a).coeFn_toLp
    exact (Lp.coeFn_zero ℝ p μ).trans he.symm

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

local instance instFactNeENNRealHDivOfNatTop_solutions : Fact ((5/3:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩

end CoulombAnalysis

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

lemma norm_sq_le_of_nonneg {x B : ℝ} (h : 0 ≤ x) (hB : x ≤ B) : ‖x^2‖ ≤ B^2 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ h hB 2

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TFNonradialBarrier
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

def tfCapBarrier (A R : ℝ) (x : Space) : ℝ := A*R^4/(R^2-‖x‖^2)^4

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

lemma exists_tfCapBarrier_radius {A R q : ℝ} (hA : 0 < A) (hR : 0 < R)
    (hq : q < R) (M : ℝ) : ∃ r, 0 < r ∧ q < r ∧ r < R ∧ M ≤ A*R^4/(R^2-r^2)^4 := by
  let B := max M 0+1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right M 0]
  have hMB : M ≤ B := by dsimp [B]; linarith [le_max_left M 0]
  have hd : 0 < A*R^4/B := div_pos (mul_pos hA (pow_pos hR _)) hB
  have hc : Continuous (fun r : ℝ => (R^2-r^2)^4) := by fun_prop
  have hev : ∀ᶠ r in 𝓝 R, (R^2-r^2)^4 < A*R^4/B := by
    apply hc.continuousAt.eventually (gt_mem_nhds _)
    simpa only [sub_self,zero_pow (by decide : (4:ℕ) ≠ 0)] using hd
  obtain ⟨a,b,hab,hs⟩ := hev.exists_Ioo_subset
  obtain ⟨r,hrlo,hrR⟩ := exists_between (show max (max a q) 0 < R from
    max_lt (max_lt hab.1 hq) hR)
  have hr : 0 < r := (le_max_right _ _).trans_lt hrlo
  have har : a < r := (le_max_left a q |>.trans (le_max_left _ _)).trans_lt hrlo
  have hqr : q < r := (le_max_right a q |>.trans (le_max_left _ _)).trans_lt hrlo
  refine ⟨r,hr,hqr,hrR,?_⟩
  have hsmall := (lt_div_iff₀ hB).mp (hs ⟨har,hrR.trans hab.2⟩)
  have hdp : 0 < R^2-r^2 := by nlinarith
  apply (le_div_iff₀ (pow_pos hdp 4)).mpr
  calc
    M*(R^2-r^2)^4 ≤ B*(R^2-r^2)^4 :=
      mul_le_mul_of_nonneg_right hMB (pow_nonneg hdp.le _)
    _ ≤ A*R^4 := by nlinarith

lemma tfCapBarrier_coefficient {k : ℝ} (hk : 0 < k) :
    0 < (80/k)^2 ∧ 80*((80/k)^2) ≤ k*((80/k)^2)^(3/2:ℝ) := by
  have hp : 0 < 80/k := div_pos (by norm_num) hk
  refine ⟨pow_pos hp _,?_⟩
  have he : ((80/k)^2)^(3/2:ℝ) = (80/k)^3 := by
    rw [←Real.rpow_natCast (80/k) 2,←Real.rpow_mul hp.le]
    norm_num
  rw [he]
  apply le_of_eq
  field_simp

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BallAverageKernelBarrier
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

open MeasureTheory Set Metric
open scoped BigOperators

def localHistoryRadius (a : ℝ) (n : ℕ) : ℝ := a/(((n:ℝ)+1)*((n:ℝ)+2))
def localHistoryReach (a : ℝ) (n : ℕ) : ℝ := 4*a*(1-1/((n:ℝ)+1))

lemma localHistoryRadius_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < localHistoryRadius a n := by
  unfold localHistoryRadius
  positivity
lemma localHistoryRadius_le {a : ℝ} (ha : 0 < a) (n : ℕ) : localHistoryRadius a n ≤ a := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  unfold localHistoryRadius
  apply (div_le_iff₀ (by positivity)).2
  exact le_mul_of_one_le_right ha.le (by nlinarith)
lemma localHistoryReach_lt {a : ℝ} (ha : 0 < a) (n : ℕ) : localHistoryReach a n < 4*a := by
  unfold localHistoryReach
  have : 0 < 1/((n:ℝ)+1) := by positivity
  nlinarith
lemma localHistoryReach_step (a : ℝ) (n : ℕ) :
    localHistoryReach a (n+1) = localHistoryReach a n+4*localHistoryRadius a n := by
  unfold localHistoryReach localHistoryRadius
  push_cast
  field_simp
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterWidth
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

def masterExponent : ℝ := 1/100000

def masterBaseDistance (r₀ : ℝ) (x : Space) : ℝ := max ‖x‖ r₀

def masterWidth (c₁ r₀ s : ℝ) (x : Space) : ℝ :=
  c₁*masterBaseDistance r₀ x*(min (masterBaseDistance r₀ x) s)^masterExponent

open Set Metric
open scoped NNReal

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_SelectedScreenedProfileBarrier
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

def tfDensityCoefficient : ℝ := (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹
end CoulombAnalysis

end

end OAI
end


