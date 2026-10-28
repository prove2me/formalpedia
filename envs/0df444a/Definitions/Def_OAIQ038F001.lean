-- Prove2me | Definitions.Def_OAIQ038F001
-- name    : OAIQ038F001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:51:24.30805+00:00
-- url     : https://prove2.me/theorems/7cae79c7-3869-48bc-aae4-4c6ddf873936
-- title:
--   Definitions bundle OAIQ038F001 of the split of OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 94 declarations of OpenAI's Lean: 55 definitions, 6 instances and 33 theorems. The definitions and types are `OAI.PlanarFalconer.complexSchwartz`, `OAI.PlanarFalconer.compositionDerivativeCost`, `OAI.PlanarFalconer.contentOuter`, `OAI.PlanarFalconer.cosineOscillator`, `OAI.PlanarFalconer.distanceDifferenceMeasure`, `OAI.PlanarFalconer.distanceFrequencyBox`, `OAI.PlanarFalconer.distanceSincKernel`, `OAI.PlanarFalconer.distanceWeight`, `OAI.PlanarFalconer.energyScale`, `OAI.PlanarFalconer.finiteRampProfile`, `OAI.PlanarFalconer.fourierDerivativeL1`, `OAI.PlanarFalconer.frechetCompositionCost`, `OAI.PlanarFalconer.gaussianQuadraticOn`, `OAI.PlanarFalconer.graphBinCountConstant`, `OAI.PlanarFalconer.graphNonedgeDerivativeScale`, `OAI.PlanarFalconer.graphPolarRectangle`, `OAI.PlanarFalconer.graphProfileCoefficient`, `OAI.PlanarFalconer.graphSourceChartAxis`, `OAI.PlanarFalconer.hausdorffContent`, `OAI.PlanarFalconer.imaginaryExponential`, `OAI.PlanarFalconer.imaginaryTaylor`, `OAI.PlanarFalconer.intervalRamp`, `OAI.PlanarFalconer.inverseStationaryWeight`, `OAI.PlanarFalconer.kernelMeasureConvolution`, `OAI.PlanarFalconer.leafBinEndpoint`, `OAI.PlanarFalconer.outerEntry`, `OAI.PlanarFalconer.quadraticExpansion`, `OAI.PlanarFalconer.quadraticFourierKernel`, `OAI.PlanarFalconer.radialEnergyPrefactor`, `OAI.PlanarFalconer.radialPhaseIntegral`, `OAI.PlanarFalconer.radialStationaryProfile`, `OAI.PlanarFalconer.restorationArcBound`, `OAI.PlanarFalconer.restorationDiscardBound`, `OAI.PlanarFalconer.rieszEnergyOn`, `OAI.PlanarFalconer.scaledAngularTransportCost`, `OAI.PlanarFalconer.schwartzLpTest`, `OAI.PlanarFalconer.sineZeroCutoff`, `OAI.PlanarFalconer.smoothInverseSine`, `OAI.PlanarFalconer.sourceDistanceSlot`, `OAI.PlanarFalconer.sourceEnergyConstant` and 15 more.
--
--   **Sources.** They come from these modules of lean/OAI/MeasureTheory/Falconer, in whole or in part: `Falconer_Angular_AngularIntegrationByParts`, `Falconer_Angular_CircleStationaryPartition`, `Falconer_Angular_GraphRotatedWeights`, `Falconer_Angular_InverseStationaryWeighted`, `Falconer_Angular_QuadraticStationaryExpansion`, `Falconer_Angular_RadialStationaryProfile`, `Falconer_Angular_ScaledAngularTransport`, `Falconer_Angular_SignedStationaryExpansion`, `Falconer_Angular_SmoothInverseSine`, `Falconer_Angular_StationaryProductIntegral`, `Falconer_Estimates_ActualOuterMasks`, `Falconer_Estimates_FrechetCompositionScale`, `Falconer_Estimates_MaskLoss`, `Falconer_Estimates_ProfileInterpolation`, `Falconer_Estimates_SignedConvolution`, `Falconer_Estimates_SmoothCompositionScale`, `Falconer_Estimates_SpatialPlancherel`, `Falconer_Fourier_DistanceFourierDifference`, `Falconer_Fourier_DistanceFrequencyBox`, `Falconer_Fourier_DistanceSincKernel`, `Falconer_Fourier_FourierEnergy`, `Falconer_Fourier_KernelFourierIdentity`, `Falconer_Fourier_LowFrequencyKernel`, `Falconer_Fourier_MeasureKernelConvolution`, `Falconer_Fourier_OscillatoryTaylor`, `Falconer_Fourier_QuadraticGaussianPairing`, `Falconer_Fourier_SchwartzFourierMomentBounds`, `Falconer_Fourier_SchwartzLpTests`, `Falconer_Fourier_UniformSymbolScale`, `Falconer_Frostman_Content`, `Falconer_Frostman_GeometricCapacity`, `Falconer_Graphs_ActualDistanceGraphAssembly`, `Falconer_Graphs_ActualProductGraphAssembly`, `Falconer_Graphs_Energy`, `Falconer_Graphs_FiberTrace`, `Falconer_Graphs_GraphAmplitudeScale`, `Falconer_Graphs_GraphNonedgeIndexCount`, `Falconer_Graphs_GraphPolarAnnulus`, `Falconer_Graphs_GraphProfileCoefficient`, `Falconer_Graphs_SourceSpatialEnergy`, `Falconer_Measures_DistanceMeasure`, `Falconer_Measures_TotalVariation`, `Falconer_Radial_LinearRadialDecay`, `Falconer_Radial_RadialTestEnergy`, `Falconer_Recursion_LeafMassBins`, `Falconer_Shells_ActualRestorationBound`, `Falconer_Shells_ShellFrequencyEnergy`, `Falconer_Shells_ShellKernels`, `Falconer_Shells_SmoothShellPartition`.
--
--   **Imports.** It imports the published bundle `Def_PlanarFalconer`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ038F002`; the statements `OAI.PlanarFalconer.full_circle_stationary_expansion`, `OAI.PlanarFalconer.uniform_actual_single_stationary_kernel` and `OAI.PlanarFalconer.uniform_independent_class_equation27`.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/MeasureTheory/Falconer at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer

section
-- module Solutions.OAIQ038_FA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_QuadraticGaussianPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

noncomputable def quadraticFourierKernel (a : ℂ) (ξ : ℝ) : ℂ :=
  ((Real.pi:ℂ)/a)^(1/2:ℂ) * Complex.exp (-((2*Real.pi*ξ:ℝ):ℂ)^2/(4*a))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Frostman_Content
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal NNReal

noncomputable def hausdorffContent {X : Type*} [EMetricSpace X] (s : ℝ) (E : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : E ⊆ ⋃ n, U n), ∑' n, (Metric.ediam (U n))^s

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Frostman_GeometricCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable def contentOuter {X : Type*} [EMetricSpace X]
    (s : ℝ) (hs : 0 < s) : OuterMeasure X :=
  OuterMeasure.ofFunction (fun U => (ediam U)^s)
    (by simp [ENNReal.zero_rpow_of_pos hs])

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable def energyScale (n : ℕ) : ℝ := (1/2 : ℝ)^n

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_FourierEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def rieszEnergyOn (μ : Measure V) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : V × V, (edist z.1 z.2)^(-u) ∂μ.prod μ

noncomputable def gaussianQuadraticOn (μ : Measure V) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : V × V, ENNReal.ofReal (Real.exp (-(Real.pi*a*‖z.1-z.2‖^2))) ∂μ.prod μ

noncomputable def sourceEnergyConstant (n u : ℝ) : ℝ :=
  (Real.pi^(u/2)/Real.Gamma (u/2)) *
    ((1/Real.pi)^((n-u)/2) * Real.Gamma ((n-u)/2))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_FiberTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal FourierTransform SchwartzMap

noncomputable def complexSchwartz (f : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM f

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_LeafMassBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal

noncomputable def leafBinEndpoint (N k : ℕ) : ℝ := (2:ℝ)^k / (2:ℝ)^(4*N)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProfileInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def intervalRamp (a b u : ℝ) : ℝ := min u b - min u a

noncomputable def finiteRampProfile (d c : ℕ → ℝ) (K : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range K, c i * intervalRamp (d (i+1)) (d i) u

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_UniformSymbolScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

noncomputable def sourceSymbolScale (N : ℕ) (sig : ℝ) (L : ℕ) : ℝ :=
  ((2:ℝ)^N)^sig * max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*sig))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_OscillatoryTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

noncomputable def imaginaryExponential (t : ℝ) : ℂ := Complex.exp (Complex.I*(t:ℂ))

noncomputable def imaginaryTaylor (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), ((k.factorial:ℝ)⁻¹*t^k) • (Complex.I^k)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_QuadraticStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable def quadraticExpansion (φ : 𝓢(ℝ,ℂ)) (n : ℕ) (b : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1),
    ((((k.factorial:ℝ)⁻¹*(Real.pi^2/b)^k):ℝ):ℂ)*Complex.I^k *
      (((-2*(Real.pi:ℂ)*Complex.I)^(2*k))⁻¹ * iteratedDeriv (2*k) (φ : ℝ → ℂ) 0)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SchwartzFourierMomentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap RealInnerProductSpace

noncomputable def fourierDerivativeL1 (φ : 𝓢(ℝ,ℂ)) (n : ℕ) : ℝ :=
  (∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖)/(2*Real.pi)^n

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SmoothCompositionScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

noncomputable def compositionDerivativeCost (g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ c : OrderedFinpartition n, ∏ j, ‖iteratedDeriv (c.partSize j) g x‖

noncomputable def weightedCompositionCost (w : ℝ → ℂ) (g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), (n.choose k:ℝ) * ‖iteratedDeriv k w x‖ * compositionDerivativeCost g (n-k) x

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularIntegrationByParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def cosineOscillator (Λ x : ℝ) : ℂ :=
  Complex.exp (Complex.I*(Λ:ℂ)*(Real.cos x:ℂ))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleStationaryPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

noncomputable def stationaryCosineChart (θ : ℝ) : ℝ := 2*Real.cos (θ/2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SmoothInverseSine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

noncomputable def sineZeroCutoff (η : ℝ) (hη : 0 < η) : ContDiffBump (0:ℝ) :=
  ⟨η/2,η,half_pos hη,half_lt_self hη⟩
noncomputable def smoothInverseSine (η : ℝ) (hη : 0 < η) (θ : ℝ) : ℝ :=
  (1-sineZeroCutoff η hη (Real.sin θ))*(Real.sin θ)⁻¹

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseStationaryWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

noncomputable def inverseStationaryWeight (Λ : ℝ) (j : ℕ) : ℝ :=
  Λ^(1/2:ℝ)*(Λ⁻¹)^j

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ScaledAngularTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

noncomputable def scaledAngularTransportCost (Q : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n+1, m => ∑ k ∈ Finset.range (m+2),
      ((m+1).choose k : ℝ) * Q k * scaledAngularTransportCost Q n (m+1-k)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphPolarAnnulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

def graphPolarRectangle (a b : ℝ) : Set (ℝ × ℝ) :=
  (Ioo a b) ×ˢ (Ioo (-Real.pi) Real.pi)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_GraphRotatedWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def graphSourceChartAxis (distance plus : Bool) : ℝ :=
  if distance then 0 else if plus then 0 else Real.pi

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_LinearRadialDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

noncomputable def radialPhaseIntegral (f : ℝ → ℂ) (xi : ℝ) : ℂ :=
  ∫ s : ℝ, Complex.exp (Complex.I*(xi:ℂ)*(s:ℂ))*f s

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RadialStationaryProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

noncomputable def radialStationaryProfile (Ψ : ℝ → ℝ) (p : ℝ) (s : ℝ) : ℂ :=
  (Ψ s * s^p : ℝ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SignedStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff ComplexConjugate

noncomputable def stationarySign (plus : Bool) : ℝ := if plus then 1 else -1

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryProductIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def stationarySignedIndices (n : ℕ) : Finset (Bool × ℕ) :=
  Finset.univ ×ˢ Finset.range (n+1)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualOuterMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

noncomputable def outerEntry (m₁ m₂ : ℝ → ℝ) (N : ℕ) (β : ℝ) : ℕ := by
  classical
  exact ((Finset.range (N+1)).filter fun (n : ℕ) =>
    min (m₁ n-(n:ℝ)/(N:ℝ)) (m₂ n-(n:ℝ)/(N:ℝ)) ≤ β).sup id

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_FrechetCompositionScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def frechetCompositionCost (g : E → ℝ) (n : ℕ) (x : E) : ℝ :=
  ∑ c : OrderedFinpartition n, ∏ j, ‖iteratedFDeriv ℝ (c.partSize j) g x‖

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_MaskLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem masked_pushforward_decomposition {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (f : α → β) (hf : Measurable f) (w m : α → ℝ≥0∞)
    (hw : Measurable w) (hm : Measurable m) (hm1 : ∀ x, m x ≤ 1) :
    (μ.withDensity w).map f =
      (μ.withDensity (fun x => w x*m x)).map f +
      (μ.withDensity (fun x => w x*(1-m x))).map f := by
  have hd : μ.withDensity w =
      μ.withDensity (fun x => w x*m x) + μ.withDensity (fun x => w x*(1-m x)) := by
    rw [← withDensity_add_left (μ := μ)
      (show Measurable (fun x => w x*m x) from hw.mul hm)
      (fun x => w x*(1-m x))]
    congr 1
    funext x
    dsimp
    rw [← mul_add, add_tsub_cancel_of_le (hm1 x), mul_one]
  rw [hd, Measure.map_add _ _ hf]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_TotalVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem finite_summands {α : Type*} [MeasurableSpace α]
    (τ σ ρ : Measure α) [IsFiniteMeasure τ] (h : τ = σ+ρ) :
    IsFiniteMeasure σ ∧ IsFiniteMeasure ρ := by
  have hσ : σ ≤ τ := by
    rw [h]
    apply Measure.le_iff.mpr
    intro s _
    simp only [Measure.add_apply]
    exact le_add_right le_rfl
  have hρ : ρ ≤ τ := by
    rw [h]
    apply Measure.le_iff.mpr
    intro s _
    simp only [Measure.add_apply]
    exact le_add_left le_rfl
  exact ⟨isFiniteMeasure_of_le τ hσ,isFiniteMeasure_of_le τ hρ⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_SmoothShellPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable def sourceShellBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

noncomputable def sourceShellLowpass (n : ℕ) (r : ℝ) : ℝ := sourceShellBump (r/(2:ℝ)^n)
noncomputable def sourceShellBand (n : ℕ) (r : ℝ) : ℝ := sourceShellLowpass (n+1) r - sourceShellLowpass n r

theorem sourceShellLowpass_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (sourceShellLowpass n) :=
  sourceShellBump.contDiff.comp (contDiff_id.div_const _)

theorem sourceShellBand_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (sourceShellBand n) :=
  (sourceShellLowpass_smooth (n+1)).sub (sourceShellLowpass_smooth n)

theorem sourceShellLowpass_one (n : ℕ) {r : ℝ} (hr : |r| ≤ (2:ℝ)^n) :
    sourceShellLowpass n r = 1 := by
  apply sourceShellBump.one_of_mem_closedBall
  change dist (r/(2:ℝ)^n) 0 ≤ 1
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2^n)]
  exact (div_le_one (by positivity)).mpr hr

theorem sourceShellLowpass_zero (n : ℕ) {r : ℝ} (hr : (2:ℝ)^(n+1) ≤ |r|) :
    sourceShellLowpass n r = 0 := by
  apply sourceShellBump.zero_of_le_dist
  change 2 ≤ dist (r/(2:ℝ)^n) 0
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2^n)]
  apply (le_div_iff₀ (by positivity)).mpr
  simpa [pow_succ, mul_comm] using hr

theorem sourceShellBand_abs_le (n : ℕ) (r : ℝ) : |sourceShellBand n r| ≤ 1 := by
  have ha : 0 ≤ sourceShellLowpass (n+1) r := sourceShellBump.nonneg
  have hb : sourceShellLowpass (n+1) r ≤ 1 := sourceShellBump.le_one
  have hc : 0 ≤ sourceShellLowpass n r := sourceShellBump.nonneg
  have hd : sourceShellLowpass n r ≤ 1 := sourceShellBump.le_one
  rw [sourceShellBand, abs_le]
  constructor <;> linarith

theorem sourceShellBand_support_bounds (n : ℕ) {r : ℝ} (hr : sourceShellBand n r ≠ 0) :
    (2:ℝ)^n ≤ |r| ∧ |r| ≤ (2:ℝ)^(n+2) := by
  have hpow : (2:ℝ)^n ≤ 2^(n+1) := by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]
  constructor
  · by_contra h
    have hle : |r| ≤ (2:ℝ)^n := (not_le.mp h).le
    exact hr (by rw [sourceShellBand, sourceShellLowpass_one (n+1) (hle.trans hpow),
      sourceShellLowpass_one n hle, sub_self])
  · by_contra h
    have hle : (2:ℝ)^(n+2) ≤ |r| := (not_le.mp h).le
    have hpow' : (2:ℝ)^(n+1) ≤ 2^(n+2) := by
      exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
    exact hr (by rw [sourceShellBand, sourceShellLowpass_zero (n+1) hle,
      sourceShellLowpass_zero n (hpow'.trans hle), sub_self])

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped SchwartzMap FourierTransform

theorem fourier_real_dilate (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    𝓕 (fun r => f (r/a)) x = |a| • 𝓕 f (a*x) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have h := Measure.integral_comp_div
    (fun r : ℝ => Complex.exp (↑(-2 * Real.pi * r * (a*x)) * Complex.I) • f r) a
  rw [← h]
  apply integral_congr_ae
  filter_upwards with r
  have he : -2 * Real.pi * (r/a) * (a*x) = -2 * Real.pi * r * x := by field_simp
  rw [he]

noncomputable def sourceInverseKernel (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (2*Real.pi)⁻¹ • 𝓕 f (x/(2*Real.pi))

theorem sourceInverseKernel_formula (f : ℝ → ℂ) (x : ℝ) :
    sourceInverseKernel f x = (2*Real.pi)⁻¹ •
      ∫ r, Complex.exp (↑(-x*r) * Complex.I) * f r := by
  rw [sourceInverseKernel, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  have he : -2 * Real.pi * r * (x/(2*Real.pi)) = -x*r := by
    field_simp
  rw [he, smul_eq_mul]

theorem sourceInverseKernel_dilate (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    sourceInverseKernel (fun r => f (r/a)) x = |a| • sourceInverseKernel f (a*x) := by
  rw [sourceInverseKernel, fourier_real_dilate f ha]
  have he : a*(x/(2*Real.pi)) = (a*x)/(2*Real.pi) := by ring
  rw [he, smul_comm]
  rfl

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_MeasureKernelConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform

noncomputable def kernelMeasureConvolution (K : ℝ → ℂ) (τ : Measure ℝ) (x : ℝ) : ℂ :=
  ∫ y, K (x-y) ∂τ

theorem kernelMeasureConvolution_prod_integrable (K : ℝ → ℂ)
    (hK : Continuous K) (hi : Integrable K) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    Integrable (fun z : ℝ × ℝ => K (z.1-z.2)) (volume.prod τ) := by
  apply (integrable_prod_iff' (hK.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mpr
  constructor
  · filter_upwards with y
    exact hi.comp_sub_right y
  · have he : (fun y : ℝ => ∫ x : ℝ, ‖K (x-y)‖) = fun _ => ∫ x, ‖K x‖ := by
      funext y
      exact integral_sub_right_eq_self (fun x => ‖K x‖) y
    change Integrable (fun y : ℝ => ∫ x : ℝ, ‖K (x-y)‖) τ
    rw [he]
    exact integrable_const _

theorem kernelMeasureConvolution_L1 (K : ℝ → ℂ)
    (hK : Continuous K) (hi : Integrable K) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    Integrable (kernelMeasureConvolution K τ) ∧
      (∫ x, ‖kernelMeasureConvolution K τ x‖) ≤ τ.real univ * ∫ x, ‖K x‖ := by
  have hp := kernelMeasureConvolution_prod_integrable K hK hi τ
  have hc : Integrable (kernelMeasureConvolution K τ) := hp.integral_prod_left
  refine ⟨hc, ?_⟩
  calc
    _ ≤ ∫ x, ∫ y, ‖K (x-y)‖ ∂τ := integral_mono hc.norm hp.integral_norm_prod_left
      (fun x => norm_integral_le_integral_norm _)
    _ = ∫ y, ∫ x, ‖K (x-y)‖ ∂volume ∂τ := integral_integral_swap hp.norm
    _ = _ := by
      simp_rw [integral_sub_right_eq_self (fun x => ‖K x‖)]
      rw [integral_const, smul_eq_mul]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SignedConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter

 theorem signed_difference_balance (τ σ : Measure ℝ)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] :
    τ + (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.negPart =
    σ + (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.posPart := by
  apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
  rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
  have h := SignedMeasure.toSignedMeasure_toJordanDecomposition
    (τ.toSignedMeasure-σ.toSignedMeasure)
  unfold JordanDecomposition.toSignedMeasure at h
  exact (sub_eq_sub_iff_add_eq_add.mp h).symm.trans (add_comm _ _)

 theorem kernelMeasureConvolution_sub_jordan (K : ℝ → ℂ)
    (hK : Continuous K) (hi : Integrable K) (τ σ : Measure ℝ)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] :
    (fun x => kernelMeasureConvolution K τ x-kernelMeasureConvolution K σ x) =ᵐ[volume]
    (fun x => kernelMeasureConvolution K
      (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.posPart x -
      kernelMeasureConvolution K
      (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.negPart x) := by
  let P := (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.posPart
  let N := (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.negPart
  have hτ := (kernelMeasureConvolution_prod_integrable K hK hi τ).prod_right_ae
  have hσ := (kernelMeasureConvolution_prod_integrable K hK hi σ).prod_right_ae
  have hP := (kernelMeasureConvolution_prod_integrable K hK hi P).prod_right_ae
  have hN := (kernelMeasureConvolution_prod_integrable K hK hi N).prod_right_ae
  filter_upwards [hτ,hσ,hP,hN] with x hxτ hxσ hxP hxN
  have he := congrArg (fun μ : Measure ℝ => ∫ y, K (x-y) ∂μ)
    (signed_difference_balance τ σ)
  rw [integral_add_measure hxτ hxN, integral_add_measure hxσ hxP] at he
  exact sub_eq_sub_iff_add_eq_add.mpr (he.trans (add_comm _ _))

 theorem kernelMeasureConvolution_sub_L1 (K : ℝ → ℂ)
    (hK : Continuous K) (hi : Integrable K) (τ σ : Measure ℝ)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] :
    Integrable (fun x => kernelMeasureConvolution K τ x-kernelMeasureConvolution K σ x) ∧
    (∫ x, ‖kernelMeasureConvolution K τ x-kernelMeasureConvolution K σ x‖) ≤
      (τ.toSignedMeasure-σ.toSignedMeasure).totalVariation.real univ * ∫ x, ‖K x‖ := by
  let P := (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.posPart
  let N := (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.negPart
  obtain ⟨hP,bP⟩ := kernelMeasureConvolution_L1 K hK hi P
  obtain ⟨hN,bN⟩ := kernelMeasureConvolution_L1 K hK hi N
  have he := kernelMeasureConvolution_sub_jordan K hK hi τ σ
  refine ⟨(hP.sub hN).congr he.symm, ?_⟩
  calc
    _ = ∫ x, ‖kernelMeasureConvolution K P x-kernelMeasureConvolution K N x‖ :=
      integral_congr_ae (he.mono (fun x hx => congrArg norm hx))
    _ ≤ ∫ x, ‖kernelMeasureConvolution K P x‖+‖kernelMeasureConvolution K N x‖ :=
      integral_mono (hP.sub hN).norm (hP.norm.add hN.norm) (fun x => norm_sub_le _ _)
    _ = (∫ x, ‖kernelMeasureConvolution K P x‖)+(∫ x, ‖kernelMeasureConvolution K N x‖) :=
      integral_add hP.norm hN.norm
    _ ≤ P.real univ * (∫ x, ‖K x‖)+N.real univ * (∫ x, ‖K x‖) := add_le_add bP bN
    _ = _ := by rw [← add_mul, SignedMeasure.totalVariation, measureReal_add_apply]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellFrequencyEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

noncomputable def sourceShellMultiplier (τ : Measure ℝ) (n : ℕ) (r : ℝ) : ℂ :=
  (sourceShellBand n r : ℂ) * charFun τ r

theorem sourceShellMultiplier_continuous (τ : Measure ℝ) [IsFiniteMeasure τ] (n : ℕ) :
    Continuous (sourceShellMultiplier τ n) :=
  (Complex.continuous_ofReal.comp (sourceShellBand_smooth n).continuous).mul continuous_charFun

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_KernelFourierIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter

theorem sourceInverseKernel_measure (f : ℝ → ℂ) (hf : Continuous f) (hi : Integrable f)
    (τ : Measure ℝ) [IsFiniteMeasure τ] (x : ℝ) :
    kernelMeasureConvolution (sourceInverseKernel f) τ x =
      sourceInverseKernel (fun r => f r * charFun τ r) x := by
  let g : ℝ × ℝ → ℂ := fun z =>
    Complex.exp (↑(-x*z.1)*Complex.I) * f z.1 * Complex.exp (↑(z.1*z.2)*Complex.I)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hb : Integrable (fun z : ℝ × ℝ => ‖f z.1‖ * (1:ℝ)) (volume.prod τ) :=
    hi.norm.mul_prod (integrable_const 1)
  have hp : Integrable g (volume.prod τ) := hb.mono' hg.aestronglyMeasurable (by
    filter_upwards with z
    simp [g, Complex.norm_exp, Complex.mul_re])
  have he (r y : ℝ) : Complex.exp (↑(-(x-y)*r)*Complex.I) * f r = g (r,y) := by
    have ha : (↑(-(x-y)*r) : ℂ)*Complex.I =
        ↑(-x*r)*Complex.I + ↑(r*y)*Complex.I := by push_cast; ring
    rw [ha, Complex.exp_add]
    dsimp [g]
    ring
  unfold kernelMeasureConvolution
  simp_rw [sourceInverseKernel_formula, he]
  rw [integral_smul, ← integral_integral_swap hp]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  dsimp [g]
  rw [integral_const_mul, charFun_apply_real]
  simp only [Complex.ofReal_mul]
  rw [mul_assoc]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SpatialPlancherel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap

 theorem integrable_fourier_pairing (f : ℝ → ℂ) (hf : Integrable f)
    (g : 𝓢(ℝ, ℂ)) :
    (∫ x, g x * 𝓕 f x) = ∫ x, 𝓕 g x * f x := by
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (μ := volume) (ν := volume)
    (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar
    (by fun_prop : Continuous (fun p : ℝ × ℝ => innerₗ ℝ p.1 p.2)) hf g.integrable
  simpa only [ContinuousLinearMap.mul_apply', Real.fourier_eq,
    VectorFourier.fourierIntegral, LinearMap.flip_apply,
    innerₗ_apply_apply, real_inner_comm, SchwartzMap.fourier_coe, mul_comm] using h

 theorem fourier_L2_ae (f : ℝ → ℂ) (h1 : Integrable f) (h2 : MemLp f 2 volume) :
    (⇑(𝓕 (h2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (h2.toLp f))).locallyIntegrable (by norm_num))
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h1).locallyIntegrable
  intro g hg hc
  let φ : 𝓢(ℝ, ℂ) := (hc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hg)
  have he := congrArg (fun T : 𝓢'(ℝ, ℂ) => T φ)
    (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at he
  have hf : (∫ x, 𝓕 φ x * (h2.toLp f) x) = ∫ x, 𝓕 φ x * f x :=
    integral_congr_ae (h2.coeFn_toLp.mono (fun x hx => by dsimp only; rw [hx]))
  have hh := integrable_fourier_pairing f h1 φ
  change (∫ x, (g x : ℂ) * (𝓕 (h2.toLp f) : Lp ℂ 2 volume) x) =
    ∫ x, (g x : ℂ) * 𝓕 f x
  exact (he.symm.trans hf).trans hh.symm

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceFourierDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory ComplexConjugate

noncomputable def distanceDifferenceMeasure (μ : Measure ℝ) : Measure ℝ :=
  (μ.prod μ).map (fun z : ℝ × ℝ => z.1-z.2)

instance distanceDifferenceMeasure_finite (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (distanceDifferenceMeasure μ) := by
  unfold distanceDifferenceMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceSincKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def distanceSincKernel (u s : ℝ) : ℝ := (Real.sinc (u*s))^2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceFrequencyBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def distanceFrequencyBox (u : ℝ) : Measure ℝ := volume.restrict (Ioc (-u) u)

instance distanceFrequencyBox_finite (u : ℝ) : IsFiniteMeasure (distanceFrequencyBox u) := by
  unfold distanceFrequencyBox
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_SourceSpatialEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace

 theorem integral_sq_norm_toLp (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    (∫ x, ‖f x‖^2) = ‖hf.toLp f‖^2 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hf.toLp f)
  rw [L2.inner_def] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  calc
    _ = ∫ x, ‖(hf.toLp f) x‖^2 := integral_congr_ae
      (hf.coeFn_toLp.symm.mono (fun x hx => by dsimp only; rw [hx]))
    _ = _ := h

 theorem integrable_fourier_memLp_two (f : ℝ → ℂ) (h1 : Integrable f)
    (h2 : MemLp f 2 volume) : MemLp (𝓕 f) 2 volume :=
  MemLp.ae_eq (fourier_L2_ae f h1 h2) (Lp.memLp (𝓕 (h2.toLp f) : Lp ℂ 2 volume))

 theorem integrable_fourier_plancherel (f : ℝ → ℂ) (h1 : Integrable f)
    (h2 : MemLp f 2 volume) : (∫ x, ‖𝓕 f x‖^2) = ∫ x, ‖f x‖^2 := by
  have he := fourier_L2_ae f h1 h2
  calc
    _ = ∫ x, ‖(𝓕 (h2.toLp f) : Lp ℂ 2 volume) x‖^2 :=
      integral_congr_ae (he.symm.mono (fun x hx => by dsimp only; rw [hx]))
    _ = ‖𝓕 (h2.toLp f)‖^2 := by
      have h := integral_sq_norm_toLp _ (Lp.memLp (𝓕 (h2.toLp f)))
      simpa only [Lp.toLp_coeFn] using h
    _ = _ := by rw [Lp.norm_fourier_eq, integral_sq_norm_toLp f h2]

 theorem sourceInverseKernel_continuous (f : ℝ → ℂ) (hf : Integrable f) :
    Continuous (sourceInverseKernel f) := by
  exact (continuous_const (y := (2*Real.pi)⁻¹)).smul ((VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf).comp
      (continuous_id.div_const (2*Real.pi)))

 theorem sourceInverseKernel_memLp_two (f : ℝ → ℂ) (h1 : Integrable f)
    (h2 : MemLp f 2 volume) : MemLp (sourceInverseKernel f) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (sourceInverseKernel_continuous f h1).aestronglyMeasurable).mpr
  have hi := ((integrable_fourier_memLp_two f h1 h2).integrable_norm_pow
    (by norm_num : (2:ℕ) ≠ 0)).comp_div (by positivity : 2*Real.pi ≠ 0)
  simpa only [sourceInverseKernel, norm_smul, Real.norm_eq_abs, mul_pow] using
    hi.const_mul (|(2*Real.pi)⁻¹|^2)

 theorem sourceInverseKernel_plancherel (f : ℝ → ℂ) (h1 : Integrable f)
    (h2 : MemLp f 2 volume) :
    (∫ x, ‖sourceInverseKernel f x‖^2) = (2*Real.pi)⁻¹ * ∫ r, ‖f r‖^2 := by
  simp_rw [sourceInverseKernel, norm_smul, Real.norm_eq_abs, mul_pow]
  rw [integral_const_mul, Measure.integral_comp_div (fun x => ‖𝓕 f x‖^2),
    smul_eq_mul, abs_of_pos (by positivity : (0:ℝ)<2*Real.pi),
    abs_of_pos (by positivity : (0:ℝ)<(2*Real.pi)⁻¹),
    integrable_fourier_plancherel f h1 h2]
  field_simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_LowFrequencyKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem sourceInverseSchwartz_integrable (f : 𝓢(ℝ, ℂ)) : Integrable (sourceInverseKernel f) := by
  have h := (𝓕 f).integrable.comp_div (by positivity : 2*Real.pi ≠ 0)
  change Integrable (fun x => (2*Real.pi)⁻¹ • 𝓕 (⇑f) (x/(2*Real.pi)))
  convert h.smul ((2*Real.pi)⁻¹) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  rw [Pi.smul_apply, SchwartzMap.fourier_coe]

noncomputable def sourceLowpassSchwartz : 𝓢(ℝ, ℂ) :=
  (sourceShellBump.hasCompactSupport.toSchwartzMap sourceShellBump.contDiff).postcompCLM Complex.ofRealCLM

@[simp] theorem sourceLowpassSchwartz_apply (r : ℝ) :
    sourceLowpassSchwartz r = (sourceShellLowpass 0 r : ℂ) := by
  simp [sourceLowpassSchwartz, sourceShellLowpass]

noncomputable def sourceLowKernel : ℝ → ℂ := sourceInverseKernel sourceLowpassSchwartz

 theorem sourceLowKernel_integrable : Integrable sourceLowKernel :=
  sourceInverseSchwartz_integrable sourceLowpassSchwartz

noncomputable def sourceLowTerm (τ : FiniteMeasure ℝ) : Lp (α := ℝ) ℂ 1 volume :=
  (memLp_one_iff_integrable.mpr (kernelMeasureConvolution_L1 sourceLowKernel
    (sourceInverseKernel_continuous _ sourceLowpassSchwartz.integrable)
    sourceLowKernel_integrable τ).1).toLp (kernelMeasureConvolution sourceLowKernel τ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SchwartzLpTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

noncomputable def schwartzLpTest (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ)) :
    Lp (α := ℝ) ℂ p volume →L[ℂ] ℂ :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp
    (Lp.toTemperedDistributionCLM ℂ volume p)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphAmplitudeScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def graphNonedgeDerivativeScale (N : ℕ) (sig u : ℝ) : ℝ :=
  (2:ℝ)^u * ((2:ℝ)^N)^(4*sig)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphNonedgeIndexCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

noncomputable def graphBinCountConstant (c₀ : ℝ) : ℝ := 4*Real.pi*max 1 c₀⁻¹

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphProfileCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

noncomputable def graphProfileCoefficient (N : ℕ) (mass : Fin 4 → ℝ → ℝ) (a p : ℝ) : ℝ :=
  ∏ l : Fin 4, ((2:ℝ)^N)^(-mass l p) / ((2:ℝ)^N)^(-mass l a)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualDistanceGraphAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

def sourceDistanceSlot (l : Fin 4) : Fin 2 := ![0,1,1,0] l

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualProductGraphAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

def sourceProductSlot (l : Fin 4) : Fin 2 := ![0,0,1,1] l

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DistanceMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

noncomputable def distanceWeight (z : Plane × Plane) : ℝ≥0∞ :=
  ENNReal.ofReal ((dist z.1 z.2) ^ (-1/2 : ℝ))

noncomputable def weightedDistance (π : Measure (Plane × Plane)) : Measure ℝ :=
  Measure.map (fun z => dist z.1 z.2) (π.withDensity distanceWeight)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialTestEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable def radialEnergyPrefactor (s p : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2) *
    (ENNReal.ofReal (sourceEnergyConstant 1 (2-s)))^(p/2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ActualRestorationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def restorationArcBound (N H : ℕ) (lam sig : ℝ) : ENNReal :=
  (((4*N+1)^(2*H+1):ℕ):ENNReal)*((N+1:ℕ):ENNReal)*(((N+1)^3+1:ℕ):ENNReal)*
    ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig)))

noncomputable def restorationDiscardBound (N H : ℕ) (lam : ℝ) : ENNReal :=
  ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
    (((4*N+1)^(2*H+1):ℕ):ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-lam))

end PlanarFalconer

end OAI
end


