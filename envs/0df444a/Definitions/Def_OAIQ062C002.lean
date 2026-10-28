-- Prove2me | Definitions.Def_OAIQ062C002
-- name    : OAIQ062C002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T23:51:39.58166+00:00
-- url     : https://prove2.me/theorems/4dfe8632-7e1b-47c7-8a70-c128c1074442
-- title:
--   Definitions bundle OAIQ062C002 of the split of OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 269 declarations of OpenAI's Lean: 151 definitions, 2 inductive types or structures, 6 instances and 110 theorems. The definitions and types are `OAI.Coulomb.centeredSpinCube`, `OAI.Coulomb.coefficientPermEquiv`, `OAI.Coulomb.cutL2`, `OAI.Coulomb.fermionicNearConstant`, `OAI.Coulomb.firstCoordinateBlock`, `OAI.Coulomb.firstFiber`, `OAI.Coulomb.firstParticleDensity`, `OAI.Coulomb.firstUnfiber`, `OAI.Coulomb.fourierPlane`, `OAI.Coulomb.fourierPlaneL2`, `OAI.Coulomb.lowOrbital`, `OAI.Coulomb.outLabelCount`, `OAI.Coulomb.scalarCoefficient`, `OAI.Coulomb.spinDelta`, `OAI.Coulomb.spinShift`, `OAI.Coulomb.weakCut`, `OAI.Coulomb.weakCutBump`, `OAI.NeutralAtom.Admissible`, `OAI.NeutralAtom.ExpectedExteriorAsymptotic`, `OAI.NeutralAtom.FormRegular`, `OAI.NeutralAtom.InsertionSupport`, `OAI.NeutralAtom.IsRadial`, `OAI.NeutralAtom.ObservationNoise`, `OAI.NeutralAtom.ObservationSample`, `OAI.NeutralAtom.PropagationConstants`, `OAI.NeutralAtom.PuncturedPosition`, `OAI.NeutralAtom.RetainedScales`, `OAI.NeutralAtom.SmoothMultiplier`, `OAI.NeutralAtom.UniformGroundStateCountControl`, `OAI.NeutralAtom.UnorderedArray`, `OAI.NeutralAtom.WeakDirectionalDerivative`, `OAI.NeutralAtom.allObservationNoiseLaw`, `OAI.NeutralAtom.antisymmetrize`, `OAI.NeutralAtom.arrayEventLikelihood`, `OAI.NeutralAtom.bindingBump`, `OAI.NeutralAtom.bindingCutoff`, `OAI.NeutralAtom.bindingScale`, `OAI.NeutralAtom.boolSign`, `OAI.NeutralAtom.closedNormAnnulus`, `OAI.NeutralAtom.conditionalPacketDensity` and 113 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv`, `CoulombRadii_FieldAnalysis_FermionicCoefficients`, `CoulombRadii_FieldAnalysis_FermionicNear`, `CoulombRadii_FieldAnalysis_GridIndex`, `CoulombRadii_FieldAnalysis_HighProjection`, `CoulombRadii_FieldAnalysis_SpinMode`, `CoulombRadii_FieldAnalysis_TsumFixed`, `CoulombRadii_FieldAnalysis_Weighted`, `CoulombRadii_FormDomain_ExplicitMultiplyGradient`, `CoulombRadii_FormDomain_L1L2Fourier`, `CoulombRadii_FormDomain_OrbitalHilbertBasis`, `CoulombRadii_FormDomain_ParticleGradientNorm`, `CoulombRadii_FormDomain_RegularizedKinetic`, `CoulombRadii_FormDomain_Translate`, `CoulombRadii_FormDomain_WeakFourierDerivative`, `CoulombRadii_FormDomain_WeakSchwartzDerivative`, `CoulombRadii_LimitTheory_UniformGroundStateCountControl`, `CoulombRadii_Localization_HarmonicInterior`, `CoulombRadii_Localization_SmoothMultiplier`, `CoulombRadii_Packets_InverseErrorScale`, `CoulombRadii_Packets_KernelScale`, `CoulombRadii_Packets_RetainedInverseOffset`, `CoulombRadii_Propagation_InitialMesh`, `CoulombRadii_Propagation_InitializationBranch`, `CoulombRadii_Propagation_MaximumMollifier`, `CoulombRadii_Propagation_NearActiveMaximum`, `CoulombRadii_Propagation_PhysicalInitialPoint`, `CoulombRadii_Propagation_PropagationAverage`, `CoulombRadii_Propagation_PropagationBarrierBounds`, `CoulombRadii_Propagation_PropagationBarrierOffset`, `CoulombRadii_Propagation_PropagationConstants`, `CoulombRadii_Propagation_PropagationMaximum`, `CoulombRadii_Propagation_PropagationRegularity`, `CoulombRadii_Propagation_RadialMaxSplice`, `CoulombRadii_Propagation_SmoothMaximum`, `CoulombRadii_Propagation_WeakLocality`, `CoulombRadii_Propagation_WeakReactionMax`, `CoulombRadii_RadialBounds_Radial`, `CoulombRadii_RadialBounds_SpatialAnnulus`, `CoulombRadii_RandomFields_ConditionalDensity`, `CoulombRadii_RandomFields_ConditionalMatching`, `CoulombRadii_RandomFields_EventTiltWavefunction`, `CoulombRadii_RandomFields_ObservationPatchScale`, `CoulombRadii_RandomFields_ObservationProductDensity`, `CoulombRadii_RandomFields_ObservationSmallScale`, `CoulombRadii_RandomFields_ObservationWidthSquareSum`, `CoulombRadii_RandomFields_ObservedUnordered`, `CoulombRadii_RandomFields_PhysicalLikelihoodBridge`, `CoulombRadii_RandomFields_PhysicalRetainedLikelihood`, `CoulombRadii_RandomFields_PosteriorDensityContinuity`, `CoulombRadii_Screening_CountMoments`, `CoulombRadii_SpectralTheory_BindingBump`, `CoulombRadii_ThomasFermi_FirstFiber`, `CoulombRadii_ThomasFermi_QuantumProfileDatum`, `CoulombRadii_ThomasFermi_Rescaling`, `CoulombRadii_ThomasFermi_ScaledProfile`, `CoulombRadii_Variational_Axis`, `CoulombRadii_Variational_ConfigurationDensity`, `CoulombRadii_Variational_ConfigurationSplit`, `CoulombRadii_Variational_CorrectionDensity`, `CoulombRadii_Variational_PhysicalBridge`, `CoulombRadii_Variational_PuncturedPosition`, `CoulombRadii_Variational_SignAverage`, `CoulombRadii_Variational_WeakLaplacian`, `CoulombRadii_Variational_WedgeInsert`.
--
--   **Imports.** It imports the published bundle `Def_CoulombRadii`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ062C005`; the statements `OAI.Coulomb.strictly_bound_sequence_tight` and `OAI.NeutralAtom.physical_observed_small_annular_count_tail`.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombRadii

section
-- module Solutions.OAIQ062_CR.Compat
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
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FermionicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

noncomputable def coefficientPermEquiv {n : ℕ} {α : Type*} (p : Equiv.Perm (Fin n)) :
    (Fin n → α) ≃ (Fin n → α) where
  toFun b := b ∘ p
  invFun b := b ∘ p.symm
  left_inv b := by ext i; simp
  right_inv b := by ext i; simp

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

open scoped Classical

theorem measurePreserving_uncurry {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Type*} [MeasurableSpace A] (μ : ι → κ → Measure A)
    [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A).symm
      (Measure.pi fun i => Measure.pi (μ i))
      (Measure.pi fun ij : ι × κ => μ ij.1 ij.2) := by
  refine ⟨(MeasurableEquiv.curry ι κ A).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have he : (MeasurableEquiv.curry ι κ A).symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s (i,j))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      MeasurableEquiv.coe_curry_symm, Function.uncurry_apply_pair, Prod.forall]
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  simpa only [Finset.univ_product_univ] using
    (Finset.prod_product Finset.univ Finset.univ (fun ij : ι × κ => μ ij.1 ij.2 (s ij))).symm

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_OrbitalHilbertBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical

section GeneralFermionSpace
variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

noncomputable def scalarCoefficient {n : ℕ} (f : (Fin n → A) → ℂ)
    (v : ι → A → ℂ) (b : Fin n → ι) : ℂ :=
  ∫ x, star (∏ i, v (b i) (x i)) * f x ∂(Measure.pi fun _ => μ)

end GeneralFermionSpace

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SpinMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

noncomputable def spinDelta (s t : Fin 2) : ℂ := if t = s then 1 else 0

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_TsumFixed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)

include hv in
lemma orbital_sum_memLp (s : Finset ι) (c : ι → ℂ) :
    MemLp (fun x => ∑ i ∈ s, c i * v i x) 2 μ :=
  memLp_finsetSum s (fun i _ => (hv i).const_mul (c i))

noncomputable def lowOrbital (s : Finset ι) (x : A) (y : A) : ℂ :=
  ∑ i ∈ s, star (v i x) * v i y

end Coulomb

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_FirstFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

noncomputable def firstFiber {A : Type*} {n : ℕ} (f : (Fin (n+1) → A) → ℂ)
    (z : (Fin n → A) × A) : ℂ := f (Fin.cons z.2 z.1)

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_HighProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

noncomputable def firstUnfiber {A : Type*} {n : ℕ} (f : (Fin n → A) × A → ℂ)
    (x : Fin (n+1) → A) : ℂ := f (Fin.tail x, x 0)

end Coulomb
open MeasureTheory Set Filter
open scoped ENNReal NNReal

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Weighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

noncomputable def firstParticleDensity {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {n : ℕ} (f : (Fin (n+1) → A) → ℂ) (x : A) : ℝ :=
  ((n+1:ℕ):ℝ)*(∫ y : Fin n → A, ‖firstFiber f (y,x)‖^2 ∂(Measure.pi fun _ => μ))

end Coulomb

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Translate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

def centeredSpinCube (R : ℝ) : Set (Fin 2 × (Fin 3 → ℝ)) :=
  univ ×ˢ (univ.pi fun _ : Fin 3 => Ioc (-R) R)

noncomputable def spinShift (t : Fin 3 → ℝ) :
    (Fin 2 × (Fin 3 → ℝ)) ≃ᵐ (Fin 2 × (Fin 3 → ℝ)) :=
  (MeasurableEquiv.refl (Fin 2)).prodCongr (MeasurableEquiv.addRight t)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_GridIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

lemma sum_indicator_rpow_disjoint {I X : Type*} [Fintype I]
    (s : I → Set X) (hs : Pairwise (fun i j => Disjoint (s i) (s j)))
    (w : I → ℝ) {p : ℝ} (hp : p ≠ 0) (x : X) :
    (∑ i, (s i).indicator (fun _ => w i) x)^p =
      ∑ i, (s i).indicator (fun _ => (w i)^p) x := by
  classical
  by_cases hx : ∃ i, x ∈ s i
  · obtain ⟨i,hi⟩ := hx
    have he (u : I → ℝ) : ∑ j, (s j).indicator (fun _ => u j) x = u i := by
      rw [Finset.sum_eq_single i]
      · exact Set.indicator_of_mem hi _
      · intro j _ hji
        exact Set.indicator_of_notMem (Set.disjoint_left.mp (hs hji.symm) hi) _
      · simp
    rw [he w, he (fun i => (w i)^p)]
  · have hn (i : I) : x ∉ s i := fun hi => hx ⟨i,hi⟩
    simp only [Set.indicator_of_notMem (hn _), Finset.sum_const_zero, Real.zero_rpow hp]

lemma cell_power_scaling {b : ℝ} (hb : 0 < b) {m : ℝ} (hm : 0 ≤ m) :
    b^3 * ((b⁻¹)^3*m)^(5/3 : ℝ) = (b⁻¹)^2*m^(5/3 : ℝ) := by
  have he : ((b⁻¹)^3)^(5/3 : ℝ) = (b⁻¹)^5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hb.le)]
    norm_num
  rw [Real.mul_rpow (by positivity) hm, he]
  field_simp

lemma sum_fiber_weight {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (g : I → J) (w : J → ℝ) :
    (∑ j, (Fintype.card {i : I // g i = j} : ℝ) * w j) = ∑ i, w (g i) := by
  calc
    _ = ∑ j, ∑ i : {i : I // g i = j}, w (g i) := by
      apply Finset.sum_congr rfl
      intro j _
      have he : (fun i : {i : I // g i = j} => w (g i)) = fun _ => w j := by
        funext i
        rw [i.property]
      rw [he]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := Fintype.sum_fiberwise g (fun i => w (g i))

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CountMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def outLabelCount {n : ℕ} (p : Fin n → Fin 2) : ℝ :=
  ∑ i : Fin n, if p i=0 then 1 else 0

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_Axis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom

def radialPower (p : ℝ) (x : Position) : ℝ := (‖x‖^2)^p

open scoped Convolution
open ContinuousLinearMap

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_WeakLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def punctured : Set Position := {x | x ≠ 0}

theorem isOpen_punctured : IsOpen punctured := isClosed_singleton.isOpen_compl

theorem contDiffOn_radialPower (p : ℝ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (radialPower p) punctured := by
  exact (contDiff_id.norm_sq ℝ).contDiffOn.rpow_const_of_ne
    (fun _ hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

def radialBarrier (a d : ℝ) (x : Position) : ℝ :=
  a*radialPower (-2) x + d*(radialPower (-1) x+radialPower (-3) x)

def radialPenalty (x : Position) : ℝ := ‖x‖^2+(‖x‖^2)⁻¹

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_ScaledProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def scaledProfile (F : Position → ℝ) (x : Position) : ℝ := (‖x‖^2)^2*F x

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_CorrectionDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

def correctionDensity (q a S : ℝ) (x : Position) : ℝ :=
  {y : Position | a ≤ ‖y‖ ∧ ‖y‖ ≤ S}.indicator (fun y => (q^8)⁻¹*(‖y‖^6)⁻¹) x

theorem integrable_mul_test_on {q φ : Position → ℝ} {Ω : Set Position}
    (hq : LocallyIntegrableOn q Ω) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (ht : tsupport φ ⊆ Ω) : Integrable (fun x => q x*φ x) := by
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right q φ).trans (subset_tsupport φ))).mp
    ((hq.integrableOn_compact_subset ht hc).mul_continuousOn hφ.continuousOn hc)

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_ConfigurationDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace NeutralAtom

def configurationDensity {n : ℕ} (ψ : Wavefunction n) (x : Configuration n) : ℝ :=
  ∑ σ : Spins n, ‖ψ σ x‖ ^ 2

def rawExpectation {n : ℕ} (ψ : Wavefunction n) (F : Configuration n → ℝ) : ℝ :=
  ∫ x : Configuration n, F x * configurationDensity ψ x

def rawCount {n : ℕ} (S : Set Position) (x : Configuration n) : ℝ :=
  ∑ i : Fin n, S.indicator (fun _ => (1 : ℝ)) (x i)

theorem configurationDensity_nonneg {n : ℕ} (ψ : Wavefunction n) (x : Configuration n) :
    0 ≤ configurationDensity ψ x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem integrable_configurationDensity {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) : Integrable (configurationDensity ψ) :=
  integrable_finsetSum _ fun σ _ => (hψ σ).norm.integrable_sq

theorem integral_configurationDensity {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) :
    (∫ x, configurationDensity ψ x) = normSquared ψ := by
  exact integral_finsetSum _ fun σ _ => (hψ σ).norm.integrable_sq

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_LimitTheory_UniformGroundStateCountControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

def UniformGroundStateCountControl : Prop :=
  ∃ (D : ℝ) (Z₀ : ℕ), 0 ≤ D ∧
    (∀ α β : ℝ, 0 < α → α < β → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (ψ : Wavefunction (N + 1)), Z₀ ≤ N + 1 →
        IsNormalizedGroundState (N + 1) ψ → ∀ u : ℝ, 0 < u →
        Real.sqrt (rawExpectation ψ (fun x =>
          (rawCount {y : Position | α * u < ‖y‖ ∧ ‖y‖ < β * u} x) ^ 2)) ≤
          C * (max (u ^ 3)⁻¹ 1 + Real.sqrt (D * u))) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (ψ : Wavefunction (N + 1)), Z₀ ≤ N + 1 →
      IsNormalizedGroundState (N + 1) ψ → exteriorMass ψ 1 ≤ C * (1 + Real.sqrt D))

def rawLaw {n : ℕ} (ψ : Wavefunction n) : Measure (Configuration n) :=
  volume.withDensity (fun x => ENNReal.ofReal (configurationDensity ψ x))

theorem integral_rawLaw {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (F : Configuration n → ℝ) :
    (∫ x, F x ∂rawLaw ψ) = rawExpectation ψ F := by
  have hq := (integrable_configurationDensity hψ).aemeasurable.ennreal_ofReal
  have hqtop : ∀ᵐ x : Configuration n ∂volume,
      ENNReal.ofReal (configurationDensity ψ x) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hi := integral_withDensity_eq_integral_toReal_smul₀ hq hqtop F
  simpa only [rawLaw, rawExpectation, ENNReal.toReal_ofReal (configurationDensity_nonneg ψ _),
    smul_eq_mul, mul_comm] using hi

theorem rawLaw_isProbability {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ = 1) :
    IsProbabilityMeasure (rawLaw ψ) := by
  apply isProbabilityMeasure_iff_real.mpr
  have h := integral_rawLaw hψ (fun _ => 1)
  simpa [integral_const, rawExpectation, integral_configurationDensity hψ, hn] using h

def packetExponent : ℝ := 1 / 100000

def packetWidth (c₁ r₀ s : ℝ) (z : Position) : ℝ :=
  c₁ * max ‖z‖ r₀ * (min (max ‖z‖ r₀) s) ^ packetExponent

def packetKernel (g : Position → ℝ) (c₁ r₀ s : ℝ) (z y : Position) : ℝ :=
  (packetWidth c₁ r₀ s z ^ 3)⁻¹ *
    (g ((packetWidth c₁ r₀ s z)⁻¹ • (y - z))) ^ 2

def packetMass {n : ℕ} (g : Position → ℝ) (c₁ r₀ s : ℝ)
    (S : Set Position) (x : Configuration n) : ℝ :=
  ∑ i, ∫ y in S, packetKernel g c₁ r₀ s (x i) y

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PhysicalBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom

lemma weakDirectional_pullback {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace F] [BorelSpace F]
    (L : E ≃L[ℝ] F) (hp : MeasurePreserving L.toHomeomorph.toMeasurableEquiv)
    {u g : F → ℂ} {v : F}
    (hw : ∀ (φ : F → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, u x * (fderiv ℝ φ x v : ℂ)) = -(∫ x, g x * (φ x : ℂ)))
    {w : E} (hL : L w = v) (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    (∫ x, u (L x) * (fderiv ℝ φ x w : ℂ)) = -(∫ x, g (L x) * (φ x : ℂ)) := by
  have H := hw (φ ∘ L.symm) (hφ.comp L.symm.contDiff)
    (hc.comp_homeomorph L.symm.toHomeomorph)
  have hd (x : F) : fderiv ℝ (φ ∘ L.symm) x v = fderiv ℝ φ (L.symm x) w := by
    rw [fderiv_comp x (hφ.differentiable (by simp) _) L.symm.differentiableAt]
    rw [L.symm.fderiv]
    change fderiv ℝ φ (L.symm x) (L.symm v) = _
    rw [← hL, L.symm_apply_apply]
  simp_rw [hd] at H
  rw [← hp.integral_comp' (fun x => u x * (fderiv ℝ φ (L.symm x) w : ℂ)),
      ← hp.integral_comp' (fun x => g x * ((φ ∘ L.symm) x : ℂ))] at H
  change (∫ x, u (L x) * (fderiv ℝ φ (L.symm (L x)) w : ℂ)) =
    -(∫ x, g (L x) * (φ (L.symm (L x)) : ℂ)) at H
  simpa only [L.symm_apply_apply] using H

end NeutralAtom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_HarmonicInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom

def coulombPartial (a : Fin 3) (x : Position) : ℝ :=
  -(x a)*(‖x‖^2)^(-3/2 : ℝ)

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FermionicNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace Coulomb

def fermionicNearConstant : ℝ := (32768/(3*Real.pi^2))^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)
end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_SmoothMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

structure SmoothMultiplier {n : ℕ} (θ : Configuration n → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ θ
  symmetric : ∀ (p : Equiv.Perm (Fin n)) x, θ (x ∘ p) = θ x
  bounded : ∃ C : ℝ, ∀ x, |θ x| ≤ C
  derivative_bounded : ∀ i a, ∃ C : ℝ,
    ∀ x, |fderiv ℝ θ x (coordinateDirection i a)| ≤ C

def multiplyWavefunction {n : ℕ} (θ : Configuration n → ℝ)
    (ψ : Wavefunction n) : Wavefunction n := fun σ x => θ x • ψ σ x

def multiplyGradient {n : ℕ} (θ : Configuration n → ℝ)
    (ψ : Wavefunction n) (g : Gradient n) : Gradient n :=
  fun σ i a x => (fderiv ℝ θ x (coordinateDirection i a)) • ψ σ x + θ x • g σ i a x

def scaleWavefunction {n : ℕ} (c : ℝ) (ψ : Wavefunction n) : Wavefunction n :=
  fun σ x => c • ψ σ x

def scaleGradient {n : ℕ} (c : ℝ) (g : Gradient n) : Gradient n :=
  fun σ i a x => c • g σ i a x

def stateWeightedIntegral {n : ℕ} (ψ : Wavefunction n) (θ : Configuration n → ℝ) : ℝ :=
  ∑ σ : Spins n, ∫ x : Configuration n, θ x*‖ψ σ x‖^2

def formMultiplierPairing {n : ℕ} (Z : ℕ) (ψ : Wavefunction n) (g : Gradient n)
    (θ : Configuration n → ℝ) : ℝ :=
  (1/2:ℝ)*(∑ σ : Spins n, ∑ i : Fin n, ∑ a : Fin 3,
    ∫ x : Configuration n, inner ℝ (g σ i a x) (multiplyGradient θ ψ g σ i a x)) +
  ∑ σ : Spins n, ∫ x : Configuration n, θ x*(coulombPotential Z x*‖ψ σ x‖^2)

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_ExplicitMultiplyGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

def explicitMultiplyGradient {n : ℕ} (θ : Configuration n → ℝ)
    (Dθ : Fin n → Fin 3 → Configuration n → ℝ)
    (ψ : Wavefunction n) (g : Gradient n) : Gradient n :=
  fun σ i a x => Dθ i a x • ψ σ x + θ x • g σ i a x

def explicitLocalizationError {n : ℕ} (ψ : Wavefunction n)
    (Dθ : Fin n → Fin 3 → Configuration n → ℝ) : ℝ :=
  (1/2:ℝ)*(∑ σ : Spins n, ∑ i : Fin n, ∑ a : Fin 3,
    ∫ x : Configuration n, (Dθ i a x)^2*‖ψ σ x‖^2)

open scoped ENNReal Convolution

def observationNoiseBase (u : ℝ) : ℝ := expNegInvGlue (1-u^2)

theorem observationNoiseBase_contDiff : ContDiff ℝ ∞ observationNoiseBase :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

theorem observationNoiseBase_nonneg (u : ℝ) : 0 ≤ observationNoiseBase u :=
  expNegInvGlue.nonneg _

theorem observationNoiseBase_formula (u : ℝ) :
    observationNoiseBase u = if |u| < 1 then Real.exp (-(1-u^2)⁻¹) else 0 := by
  have he : 0 < 1-u^2 ↔ |u| < 1 := by
    rw [abs_lt]
    constructor
    · intro hh
      constructor <;> nlinarith [sq_nonneg (u+1), sq_nonneg (u-1)]
    · rintro ⟨hl,hu⟩
      nlinarith [mul_pos (by linarith : 0 < u+1) (by linarith : 0 < 1-u)]
  unfold observationNoiseBase expNegInvGlue
  by_cases hu : |u| < 1
  · simp [hu, not_le.mpr (he.mpr hu)]
  · simp [hu, le_of_not_gt (he.not.mpr hu)]

def observationNoiseNormalizer : ℝ := (∫ u, observationNoiseBase u)⁻¹

def observationNoiseDensity (u : ℝ) : ℝ := observationNoiseNormalizer*observationNoiseBase u

def observationNoiseLaw : Measure ℝ := volume.withDensity
  (fun u => ENNReal.ofReal (observationNoiseDensity u))

def observationTranslationScore (u : ℝ) : ℝ := 2 * u / (1-u^2)^2

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_WeakSchwartzDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology SchwartzMap LineDeriv FourierTransform ComplexConjugate ContDiff
noncomputable section
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section
omit [MeasurableSpace E] [BorelSpace E]

def weakCutBump : ContDiffBump (0:E) := ⟨1,2,by norm_num,by norm_num⟩
def weakCut (k:ℕ) (x:E) : ℝ := (weakCutBump (E:=E)) (((k:ℝ)+1)⁻¹ • x)

end

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_WeakFourierDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal Topology ComplexConjugate
noncomputable section
namespace Coulomb
variable {X:Type*} [MeasurableSpace X] {μ:Measure X}
def cutL2 (s:Set X) (hs:MeasurableSet s) (u:Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp u).indicator hs).toLp (s.indicator u)
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_L1L2Fourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform ComplexConjugate
noncomputable section
namespace Coulomb
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def fourierPlane (s:Set E) (ξ:E) : E → ℂ :=
  s.indicator (fun x => conj (Real.fourierChar (-inner ℝ x ξ):ℂ))
lemma fourierPlane_memLp (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞) (ξ:E) :
    MemLp (fourierPlane s ξ) 2 volume := by
  apply (memLp_indicator_const 2 hs (1:ℂ) (Or.inr hμ)).mono
  · apply AEStronglyMeasurable.indicator _ hs
    exact (Complex.continuous_conj.comp (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg))).aestronglyMeasurable
  · filter_upwards [] with x
    by_cases hx:x∈s <;> simp [fourierPlane,hx,Circle.norm_coe]
def fourierPlaneL2 (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞) (ξ:E) :
    Lp ℂ 2 (volume:Measure E) := (fourierPlane_memLp s hs hμ ξ).toLp (fourierPlane s ξ)
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_BindingBump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

def bindingBump : ContDiffBump (0 : Position) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def bindingCutoff (n : ℕ) (x : Configuration n) : ℝ :=
  ∏ i : Fin n, bindingBump (x i)

def bindingScale (k : ℕ) : ℝ := ((k : ℝ)+1)⁻¹

def expandingCutoff (n k : ℕ) (x : Configuration n) : ℝ :=
  bindingCutoff n (bindingScale k • x)

section ProductWeakDerivative
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def WeakDirectionalDerivative (ψ g : F → ℂ) (v : F) : Prop :=
  ∀ φ : F → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, fderiv ℝ φ x v • ψ x) = -(∫ x, φ x • g x)

end ProductWeakDerivative

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_ConfigurationSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

def configurationSplit (n : ℕ) : Configuration (n+1) ≃L[ℝ] Position × Configuration n :=
  (Fin.consEquivL ℝ (fun _ : Fin (n+1) => Position)).symm

@[simp] theorem configurationSplit_apply (n : ℕ) (x : Configuration (n+1)) :
    configurationSplit n x = (x 0, fun i => x i.succ) := rfl

def configurationPerm {n : ℕ} (p : Equiv.Perm (Fin n)) : Configuration n ≃L[ℝ] Configuration n :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => Position) p).symm

@[simp] theorem configurationPerm_apply {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    configurationPerm p x = x ∘ p := rfl

@[simp] theorem configurationPerm_direction {n : ℕ} (p : Equiv.Perm (Fin n))
    (i : Fin n) (a : Fin 3) :
    configurationPerm p (coordinateDirection i a) = coordinateDirection (p.symm i) a := by
  ext j b
  by_cases hj : j = p.symm i
  · subst j; simp [coordinateDirection]
  · have hp : p j ≠ i := fun h => hj (p.injective (by simpa using h))
    simp [coordinateDirection, hj, hp]

 def permuteWavefunction {n : ℕ} (p : Equiv.Perm (Fin n)) (ψ : Wavefunction n) : Wavefunction n :=
  fun σ x => ψ (σ ∘ p) (x ∘ p)

 def permuteGradient {n : ℕ} (p : Equiv.Perm (Fin n)) (g : Gradient n) : Gradient n :=
  fun σ i a x => g (σ ∘ p) (p.symm i) a (x ∘ p)

@[simp] theorem configurationSplit_direction_zero {n : ℕ} (a : Fin 3) :
    configurationSplit n (coordinateDirection 0 a) = (EuclideanSpace.single a 1, 0) := by
  ext j <;> simp [coordinateDirection]

@[simp] theorem configurationSplit_direction_succ {n : ℕ} (i : Fin n) (a : Fin 3) :
    configurationSplit n (coordinateDirection i.succ a) = (0, coordinateDirection i a) := by
  ext j <;> simp [coordinateDirection, Pi.single_apply]

def insertWavefunction {n : ℕ} (f : Position → ℝ) (ψ : Wavefunction n) : Wavefunction (n+1) :=
  fun σ x => if σ 0 = 0 then f (x 0) • ψ (fun i => σ i.succ) (fun i => x i.succ) else 0

def insertGradient {n : ℕ} (f : Position → ℝ) (ψ : Wavefunction n) (g : Gradient n) :
    Gradient (n+1) :=
  fun σ i a x => if σ 0 = 0 then
    Fin.cases (fderiv ℝ f (x 0) (EuclideanSpace.single a 1) •
      ψ (fun j => σ j.succ) (fun j => x j.succ))
      (fun j => f (x 0) • g (fun k => σ k.succ) j a (fun k => x k.succ)) i else 0

def FormRegular {n : ℕ} (ψ : Wavefunction n) (g : Gradient n) : Prop :=
  HasWeakGradient ψ g ∧
  (∀ σ, MemLp (ψ σ) 2 volume) ∧
  (∀ σ i a, MemLp (g σ i a) 2 volume) ∧
  (∀ σ i, Integrable (fun x : Configuration n => ‖x i‖⁻¹ * ‖ψ σ x‖ ^ 2)) ∧
  (∀ σ i j, i < j →
    Integrable (fun x : Configuration n => ‖x i - x j‖⁻¹ * ‖ψ σ x‖ ^ 2))

 def sumWavefunction {n : ℕ} {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (ψ : ι → Wavefunction n) : Wavefunction n := fun σ x => ∑ i, c i • ψ i σ x

 def sumGradient {n : ℕ} {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (g : ι → Gradient n) : Gradient n := fun σ i a x => ∑ j, c j • g j σ i a x

 def permutationSign {n : ℕ} (p : Equiv.Perm (Fin n)) : ℝ := ((Equiv.Perm.sign p : ℤ) : ℝ)

@[simp] theorem permutationSign_mul {n : ℕ} (p q : Equiv.Perm (Fin n)) :
    permutationSign (p*q) = permutationSign p * permutationSign q := by
  simp [permutationSign, Equiv.Perm.sign_mul]

@[simp] theorem permutationSign_sq {n : ℕ} (p : Equiv.Perm (Fin n)) :
    permutationSign p * permutationSign p = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simp [permutationSign, h]

def antisymmetrize {n : ℕ} (ψ : Wavefunction n) : Wavefunction n :=
  sumWavefunction permutationSign (fun p => permuteWavefunction p ψ)

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_WedgeInsert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

def wedgeInsert {n : ℕ} (f : Position → ℝ) (ψ : Wavefunction n) : Wavefunction (n+1) :=
  sumWavefunction (fun i : Fin (n+1) => permutationSign (Equiv.swap 0 i))
    (fun i => permuteWavefunction (Equiv.swap 0 i) (insertWavefunction f ψ))

 def wedgeInsertGradient {n : ℕ} (f : Position → ℝ) (ψ : Wavefunction n) (g : Gradient n) :
    Gradient (n+1) :=
  sumGradient (fun i : Fin (n+1) => permutationSign (Equiv.swap 0 i))
    (fun i => permuteGradient (Equiv.swap 0 i) (insertGradient f ψ g))

def InsertionSupport {n : ℕ} (R : ℝ) (F : Wavefunction (n+1)) : Prop :=
  ∀ σ x, F σ x ≠ 0 → R < ‖x 0‖ ∧ ∀ i : Fin n, ‖x i.succ‖ ≤ R

 def spinsPerm {n : ℕ} (p : Equiv.Perm (Fin n)) : Spins n ≃ Spins n :=
  (Equiv.piCongrLeft (fun _ : Fin n => Fin 2) p).symm

@[simp] theorem spinsPerm_apply {n : ℕ} (p : Equiv.Perm (Fin n)) (σ : Spins n) :
    spinsPerm p σ = σ ∘ p := rfl

def gradientNormSquared {n : ℕ} (g : Gradient n) : ℝ :=
  ∑ i : Fin n, ∑ a : Fin 3, normSquared (fun σ x => g σ i a x)

 def potentialForm {n : ℕ} (Z : ℕ) (ψ : Wavefunction n) : ℝ :=
  ∑ σ : Spins n, ∫ x, coulombPotential Z x * ‖ψ σ x‖^2

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_ParticleGradientNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

 def oneParticleGradientNorm (f : Position → ℝ) : ℝ :=
  ∑ a : Fin 3, ∫ y : Position, (fderiv ℝ f y (EuclideanSpace.single a 1))^2

def distantCenter : Position := (4 : ℝ) • EuclideanSpace.single 0 1

def distantMass : ℝ := ∫ y : Position, (bindingBump y)^2

def distantPacket (t : ℝ) (y : Position) : ℝ :=
  (Real.sqrt (t^3 * distantMass))⁻¹ * bindingBump (t⁻¹ • y - distantCenter)

def sectorEnergy (Z n : ℕ) : EReal :=
  sInf {e : EReal | ∃ (ψ : Wavefunction n) (g : Gradient n),
    FormDomain ψ g ∧ normSquared ψ = 1 ∧ e = (energy Z ψ g : EReal)}

def vacuumWavefunction : Wavefunction 0 := fun _ _ => 1

def vacuumGradient : Gradient 0 := fun _ i => Fin.elim0 i

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_RegularizedKinetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb

def firstCoordinateBlock (k:ℕ):Finset (Fin (1+k) × Fin 3):=
  Finset.univ.map ⟨fun a => (0,a),fun _ _ h => Prod.mk.inj h |>.2⟩
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_SignAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution

open scoped BigOperators

def signAverage {ι : Type*} [Fintype ι] (f : (ι → Bool) → ℝ) : ℝ :=
  by classical exact (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ ε, f ε

def boolSign (b : Bool) : ℝ := if b then 1 else -1

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationProductDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution
open scoped BigOperators

open scoped Convolution

def observationProductDensity {ι : Type*} [Fintype ι] (u : ι → ℝ) : ℝ :=
  ∏ i, observationNoiseDensity (u i)

def observationEventLikelihood {ι : Type*} [Fintype ι]
    (s : Set (ι → ℝ)) (z : ι → ℝ) : ℝ :=
  (s.indicator (fun _ => (1:ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ] observationProductDensity) z

def observationScoreConstant : ℝ :=
  32 * Real.exp 2 * (2048 * Real.exp 1 * (max 1 (2*observationNoiseNormalizer))^2)

def coordinateLinear {n : ℕ} (i : Fin n) (a : Fin 3) : Configuration n →L[ℝ] ℝ :=
  (EuclideanSpace.proj a).comp (ContinuousLinearMap.proj i)

@[simp] theorem coordinateLinear_apply {n : ℕ} (i : Fin n) (a : Fin 3) (x : Configuration n) :
    coordinateLinear i a x = x i a := rfl

def observationArrayCenter {H : Type*} [Fintype H] {n : ℕ} (ℓ : H → ℝ) :
    Configuration n →L[ℝ] ((H × (Fin n × Fin 3)) → ℝ) :=
  ContinuousLinearMap.pi (fun hia => (ℓ hia.1)⁻¹ • coordinateLinear hia.2.1 hia.2.2)

def observationArrayRescale {H : Type*} {n : ℕ} (ℓ : H → ℝ)
    (y : (H × (Fin n × Fin 3)) → ℝ) : (H × (Fin n × Fin 3)) → ℝ :=
  fun hia => ℓ hia.1 * y hia

def arrayEventLikelihood {H : Type*} [Fintype H] {n : ℕ} (ℓ : H → ℝ)
    (s : Set ((H × (Fin n × Fin 3)) → ℝ)) (x : Configuration n) : ℝ :=
  observationEventLikelihood (observationArrayRescale ℓ ⁻¹' s) (observationArrayCenter ℓ x)

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationWidthSquareSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution
open scoped BigOperators
open scoped Convolution

def observationWidthSquareSum {H : Type*} [Fintype H] (ℓ : H → ℝ) : ℝ :=
  ∑ h, ((ℓ h)⁻¹)^2

def permuteObservationArray {H : Type*} {n : ℕ} (p : Equiv.Perm (Fin n))
    (y : (H × (Fin n × Fin 3)) → ℝ) : (H × (Fin n × Fin 3)) → ℝ :=
  fun hia => y (hia.1, p hia.2.1, hia.2.2)

def eventRootDerivative {n : ℕ} (F : Configuration n → ℝ)
    (i : Fin n) (a : Fin 3) (x : Configuration n) : ℝ :=
  fderiv ℝ F x (coordinateDirection i a) / (2 * Real.sqrt (F x))

def regularizedEventRoot {n : ℕ} (F : Configuration n → ℝ)
    (k : ℕ) (x : Configuration n) : ℝ := Real.sqrt (1/((k:ℝ)+1) + F x)

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_EventTiltWavefunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution
open scoped BigOperators
open scoped Convolution

def eventTiltWavefunction {n : ℕ} (ψ : Wavefunction n) (F : Configuration n → ℝ) :
    Wavefunction n :=
  scaleWavefunction (Real.sqrt (stateWeightedIntegral ψ F))⁻¹
    (multiplyWavefunction (fun x => Real.sqrt (F x)) ψ)

def eventTiltGradient {n : ℕ} (ψ : Wavefunction n) (g : Gradient n)
    (F : Configuration n → ℝ) : Gradient n :=
  scaleGradient (Real.sqrt (stateWeightedIntegral ψ F))⁻¹
    (explicitMultiplyGradient (fun x => Real.sqrt (F x)) (eventRootDerivative F) ψ g)

def observationEventEnergyConstant : ℝ :=
  observationScoreConstant/8*(1+120*Real.exp 1)

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationSmallScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

def singleObservationOffset (D r : ℝ) : ℝ :=
  D+observationEventEnergyConstant*((r^(101/100:ℝ))⁻¹)^2*(1-Real.log (r^40))^5

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_InverseErrorScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

def inverseResponseError (D F K κ L M a : ℝ) : ℝ :=
  Real.sqrt (D/(κ*a^(1+packetExponent))^5*a^(-699/100:ℝ))+
    (F/(κ*a^(1+packetExponent))^4*(2*a^(6/5:ℝ))+
      K/(κ*a^(1+packetExponent))^4*(Real.sqrt 3*(L*a^(101/100:ℝ))))*(M*a^(-3:ℝ))

def inverseHighMeanError (H B γ κ N a v : ℝ) : ℝ :=
  2*H*a^(1/100:ℝ)+(4*B/(γ*κ^3))*a^(1/50-3*packetExponent)+4*N*(v/a)

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_KernelScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set
namespace NeutralAtom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def scaledCenterKernel (φ : E → ℝ) (t : E → ℝ) (z y : E) :=
  ((t z)^3)⁻¹ * φ ((t z)⁻¹ • (y-z))

end NeutralAtom

end
open Set

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace NeutralAtom

def rawPacketDensity {n : ℕ} (g : Position → ℝ) (c₁ r₀ s : ℝ)
    (x : Configuration n) (y : Position) : ℝ :=
  ∑ i : Fin n, packetKernel g c₁ r₀ s (x i) y

def mixturePacketDensity {n : ℕ} (ν : Measure (Configuration n))
    (g : Position → ℝ) (c₁ r₀ s : ℝ) (y : Position) : ℝ :=
  ∫ x, rawPacketDensity g c₁ r₀ s x y ∂ν

def conditionalPacketDensity {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (raw : Ω → Configuration n) (obs : Ω → B)
    (g : Position → ℝ) (c₁ r₀ s : ℝ) (datum : B) (y : Position) : ℝ :=
  mixturePacketDensity (ProbabilityTheory.condDistrib raw obs P datum) g c₁ r₀ s y

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff
namespace NeutralAtom

def configurationOrderSetoid (n : ℕ) : Setoid (Configuration n) where
  r x y := ∃ p : Equiv.Perm (Fin n), y = x ∘ p
  iseqv := {
    refl := fun _ => ⟨Equiv.refl _, rfl⟩
    symm := by
      rintro x y ⟨p,rfl⟩
      refine ⟨p.symm, ?_⟩
      funext i
      simp
    trans := by
      rintro x y z ⟨p,rfl⟩ ⟨q,rfl⟩
      exact ⟨q.trans p,rfl⟩ }

def UnorderedArray (n : ℕ) := Quotient (configurationOrderSetoid n)

def forgetOrder {n : ℕ} (x : Configuration n) : UnorderedArray n := Quotient.mk _ x

instance unorderedArrayMeasurable (n : ℕ) : MeasurableSpace (UnorderedArray n) :=
  MeasurableSpace.map forgetOrder inferInstance

abbrev ObservationNoise (n J : ℕ) := Fin J → Fin n → Fin 3 → ℝ
abbrev ObservationSample (n J : ℕ) := Configuration n × ObservationNoise n J

def allObservationNoiseLaw (n J : ℕ) : Measure (ObservationNoise n J) :=
  Measure.pi (fun _ : Fin J => Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin 3 => observationNoiseLaw)))

def observationLaw {n : ℕ} (J : ℕ) (ν : Measure (Configuration n)) :
    Measure (ObservationSample n J) := ν.prod (allObservationNoiseLaw n J)

def observationNoiseVector (v : Fin 3 → ℝ) : Position :=
  ∑ a : Fin 3, v a • EuclideanSpace.single a 1

def observedOrdered {n J : ℕ} (r : Fin J → ℝ) (j : Fin J)
    (sample : ObservationSample n J) : Configuration n :=
  fun i => sample.1 i + (r j)^(101/100 : ℝ) • observationNoiseVector (sample.2 j i)

def observedArray {n J : ℕ} (r : Fin J → ℝ) (j : Fin J)
    (sample : ObservationSample n J) : UnorderedArray n :=
  forgetOrder (observedOrdered r j sample)

def tailObservation {n J : ℕ} (r : Fin J → ℝ) (j : ℕ)
    (sample : ObservationSample n J) : Fin J → UnorderedArray n :=
  fun k => if j ≤ k.val then observedArray r k sample else forgetOrder 0

@[instance_reducible] def observationSigma {n J : ℕ} (r : Fin J → ℝ) (j : ℕ) :
    MeasurableSpace (ObservationSample n J) :=
  MeasurableSpace.comap (tailObservation r j) inferInstance

def eraseEarlierArrays {n J : ℕ} (j : ℕ) (v : Fin J → UnorderedArray n) :
    Fin J → UnorderedArray n := fun k => if j ≤ k.val then v k else forgetOrder 0

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalLikelihoodBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace NeutralAtom

def flattenObservationNoise (n J : ℕ) :
    ObservationNoise n J ≃ᵐ ((Fin J × (Fin n × Fin 3)) → ℝ) where
  toEquiv := {
    toFun := fun u ia => u ia.1 ia.2.1 ia.2.2
    invFun := fun v j i a => v (j,i,a)
    left_inv := by intro u; rfl
    right_inv := by intro v; rfl }
  measurable_toFun := by change Measurable (fun (u : ObservationNoise n J) (ia : Fin J × (Fin n × Fin 3)) => u ia.1 ia.2.1 ia.2.2); fun_prop
  measurable_invFun := by change Measurable (fun (v : (Fin J × (Fin n × Fin 3)) → ℝ) (j : Fin J) (i : Fin n) (a : Fin 3) => v (j,i,a)); fun_prop

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalRetainedLikelihood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

def flattenIndexedNoise (n : ℕ) (H : Type*) [Fintype H] :
    (H → Fin n → Fin 3 → ℝ) ≃ᵐ ((H × (Fin n × Fin 3)) → ℝ) where
  toEquiv := {
    toFun := fun u ia => u ia.1 ia.2.1 ia.2.2
    invFun := fun v h i a => v (h,i,a)
    left_inv := by intro u; rfl
    right_inv := by intro v; rfl }
  measurable_toFun := by change Measurable (fun (u : H → Fin n → Fin 3 → ℝ) (ia : H × (Fin n × Fin 3)) => u ia.1 ia.2.1 ia.2.2); fun_prop
  measurable_invFun := by change Measurable (fun (v : (H × (Fin n × Fin 3)) → ℝ) (h : H) (i : Fin n) (a : Fin 3) => v (h,i,a)); fun_prop

abbrev RetainedScales (J j : ℕ) := {k : Fin J // j≤k.val}

def retainedNoise {n J : ℕ} (j : ℕ) (u : ObservationNoise n J) :
    (RetainedScales J j × (Fin n × Fin 3)) → ℝ :=
  fun ia => u ia.1.val ia.2.1 ia.2.2

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationPatchScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
namespace NeutralAtom

def inverseObservationOffset (D r : ℝ) : ℝ :=
  D+observationEventEnergyConstant*((r^(101/100:ℝ))⁻¹)^2*(1-Real.log (r^42))^5

end NeutralAtom

end
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_RetainedInverseOffset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

def retainedInverseOffset (D r : ℝ) : ℝ :=
  D+(4/3:ℝ)*inverseObservationOffset 0 r

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservedUnordered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace NeutralAtom

def unorderedSum {n : ℕ} (f : Position → ℝ) : UnorderedArray n → ℝ :=
  Quotient.lift (fun x : Configuration n => ∑ i, f (x i)) (by
    rintro x y ⟨p,rfl⟩
    exact (Equiv.sum_comp p (fun i => f (x i))).symm)

@[simp] theorem unorderedSum_forgetOrder {n : ℕ} (f : Position → ℝ) (x : Configuration n) :
    unorderedSum f (forgetOrder x)=∑ i, f (x i) := rfl

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_SmoothMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

def softAbs (e x : ℝ) := Real.sqrt (x^2+e^2)
def softSlope (e x : ℝ) := x/softAbs e x
def softWeight (e x : ℝ) := (1+softSlope e x)/2
def softPlus (e x : ℝ) := (x+softAbs e x)/2
def softMax (e a b : ℝ) := b+softPlus e (a-b)

lemma softAbs_pos {e : ℝ} (he : 0<e) (x : ℝ) : 0 < softAbs e x := by
  unfold softAbs
  exact Real.sqrt_pos.2 (by nlinarith [sq_nonneg x])

lemma softAbs_sq (e x : ℝ) : (softAbs e x)^2=x^2+e^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma abs_le_softAbs (e x : ℝ) : |x|≤ softAbs e x := by
  have hp : 0≤ softAbs e x := Real.sqrt_nonneg _
  nlinarith [softAbs_sq e x,sq_abs x,sq_nonneg e,abs_nonneg x]

lemma softWeight_bounds {e : ℝ} (he : 0<e) (x : ℝ) : 0≤ softWeight e x ∧ softWeight e x≤1 := by
  have ha := abs_le_softAbs e x
  have hl : -1≤ softSlope e x := (le_div_iff₀ (softAbs_pos he x)).mpr (by linarith [neg_abs_le x])
  have hu : softSlope e x≤1 := (div_le_iff₀ (softAbs_pos he x)).mpr (by linarith [le_abs_self x])
  unfold softWeight
  constructor <;> linarith

lemma softAbs_hasDerivAt {e : ℝ} (he : 0<e) (x : ℝ) :
    HasDerivAt (softAbs e) (softSlope e x) x := by
  have h := (((hasDerivAt_id x).pow 2).add_const (e^2)).sqrt
    (show x^2+e^2≠0 by nlinarith [sq_nonneg x])
  convert h using 1
  · rfl
  · dsimp [softSlope,softAbs]
    field_simp

lemma softSlope_hasDerivAt {e : ℝ} (he : 0<e) (x : ℝ) :
    HasDerivAt (softSlope e) (e^2/(softAbs e x)^3) x := by
  have hp := ne_of_gt (softAbs_pos he x)
  have H := (hasDerivAt_id x).div (softAbs_hasDerivAt he x) hp
  have heq : (1*softAbs e x-x*softSlope e x)/(softAbs e x)^2=e^2/(softAbs e x)^3 := by
    dsimp only [softSlope]
    field_simp [hp]
    nlinarith [softAbs_sq e x]
  change HasDerivAt (softSlope e) ((1*softAbs e x-x*softSlope e x)/(softAbs e x)^2) x at H
  rw [heq] at H
  exact H

lemma softPlus_hasDerivAt {e : ℝ} (he : 0<e) (x : ℝ) :
    HasDerivAt (softPlus e) (softWeight e x) x := by
  exact ((hasDerivAt_id x).add (softAbs_hasDerivAt he x)).div_const 2

lemma softWeight_hasDerivAt {e : ℝ} (he : 0<e) (x : ℝ) :
    HasDerivAt (softWeight e) (e^2/(2*(softAbs e x)^3)) x := by
  have H := ((softSlope_hasDerivAt he x).const_add 1).div_const 2
  have heq : (e^2/(softAbs e x)^3)/2=e^2/(2*(softAbs e x)^3) := by ring
  rw [heq] at H
  exact H

lemma contDiff_softAbs {e : ℝ} (he : 0<e) : ContDiff ℝ ∞ (softAbs e) := by
  apply (contDiff_id.pow 2 |>.add contDiff_const).sqrt
  intro x
  nlinarith [sq_nonneg x]

lemma contDiff_softPlus {e : ℝ} (he : 0<e) : ContDiff ℝ ∞ (softPlus e) :=
  (contDiff_id.add (contDiff_softAbs he)).div_const 2

lemma contDiff_softMax {e : ℝ} (he : 0<e) {f g : Position → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => softMax e (f x) (g x)) :=
  hg.add ((contDiff_softPlus he).comp (hf.sub hg))

lemma second_deriv_comp_scalar {f h : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hh : ContDiff ℝ 2 h) (x : ℝ) :
    deriv (deriv (fun t => h (f t))) x=
      deriv (deriv h) (f x)*(deriv f x)^2+deriv h (f x)*deriv (deriv f) x := by
  have hd : deriv (fun t => h (f t))=fun t => deriv h (f t)*deriv f t := by
    funext t
    exact ((hh.differentiable (by norm_num) (f t)).hasDerivAt.comp t
      (hf.differentiable (by norm_num) t).hasDerivAt).deriv
  rw [hd]
  have hh' : Differentiable ℝ (deriv h) := hh.differentiable_deriv_two
  have hf' : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have H := ((hh' (f x)).hasDerivAt.comp x (hf.differentiable (by norm_num) x).hasDerivAt).mul
    (hf' x).hasDerivAt
  change deriv ((deriv h ∘ f)*deriv f) x=_
  rw [H.deriv]
  simp only [Function.comp_def]
  ring

lemma second_deriv_softPlus {e : ℝ} (he : 0<e) (x : ℝ) :
    deriv (deriv (softPlus e)) x=e^2/(2*(softAbs e x)^3) := by
  have h : deriv (softPlus e)=softWeight e := funext (fun x => (softPlus_hasDerivAt he x).deriv)
  rw [h]
  exact (softWeight_hasDerivAt he x).deriv

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma softAbs_le {e : ℝ} (he : 0≤ e) (x : ℝ) : softAbs e x≤ |x|+e := by
  have h := softAbs_sq e x
  have h0 : 0≤ softAbs e x := Real.sqrt_nonneg _
  nlinarith [abs_nonneg x,sq_abs x,mul_nonneg (abs_nonneg x) he]

lemma softMax_zero (a b : ℝ) : softMax 0 a b=max a b := by
  unfold softMax softPlus softAbs
  simp only [zero_pow (by decide : 2≠0),add_zero,Real.sqrt_sq_eq_abs]
  by_cases h : b≤ a
  · rw [abs_of_nonneg (sub_nonneg.mpr h),max_eq_left h]
    ring
  · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h)),max_eq_right (le_of_not_ge h)]
    ring

lemma softMax_bounds {e : ℝ} (he : 0≤ e) (a b : ℝ) :
    max a b≤ softMax e a b ∧ softMax e a b≤ max a b+e/2 := by
  have h1 := abs_le_softAbs e (a-b)
  have h2 := softAbs_le he (a-b)
  have hz := softMax_zero a b
  unfold softMax softPlus softAbs at hz
  simp only [zero_pow (by decide : 2≠0),add_zero,Real.sqrt_sq_eq_abs] at hz
  unfold softMax softPlus
  constructor <;> linarith

lemma softMax_abs_le {e a b A B : ℝ} (he : 0≤ e) (ha : |a|≤ A) (hb : |b|≤ B) :
    |softMax e a b|≤ A+B+e := by
  have h := softMax_bounds he a b
  have hA := (abs_nonneg a).trans ha
  have hB := (abs_nonneg b).trans hb
  have hu : max a b≤ A+B := max_le (by linarith [(le_abs_self a).trans ha]) (by linarith [(le_abs_self b).trans hb])
  have hl : -(A+B)≤ max a b := by linarith [(abs_le.mp ha).1,le_max_left a b]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma softMax_tendsto {e a b : ℕ → ℝ} {A B : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) :
    Tendsto (fun n => softMax (e n) (a n) (b n)) atTop (𝓝 (max A B)) := by
  have h := hb.add (((ha.sub hb).add (((ha.sub hb).pow 2).add (he.pow 2)).sqrt).div_const 2)
  simpa only [softMax,softPlus,softAbs,←softMax_zero] using h

lemma softWeight_tendsto_of_lt {e a b : ℕ → ℝ} {A B : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (hAB : B<A) : Tendsto (fun n => softWeight (e n) (a n-b n)) atTop (𝓝 1) := by
  have hs : Tendsto (fun n => softAbs (e n) (a n-b n)) atTop (𝓝 (A-B)) := by
    have H := (((ha.sub hb).pow 2).add (he.pow 2)).sqrt
    simpa only [softAbs,zero_pow (by decide : 2≠0),add_zero,Real.sqrt_sq_eq_abs,
      abs_of_pos (sub_pos.mpr hAB)] using H
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have H := (h1.add ((ha.sub hb).div hs (ne_of_gt (sub_pos.mpr hAB)))).div_const 2
  simpa only [softWeight,softSlope,Pi.div_apply,div_self (ne_of_gt (sub_pos.mpr hAB)),one_add_one_eq_two,div_self (by norm_num : (2:ℝ)≠0)] using H

lemma softWeight_tendsto_of_gt {e a b : ℕ → ℝ} {A B : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (hAB : A<B) : Tendsto (fun n => softWeight (e n) (a n-b n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => softAbs (e n) (a n-b n)) atTop (𝓝 (B-A)) := by
    have H := (((ha.sub hb).pow 2).add (he.pow 2)).sqrt
    simpa only [softAbs,zero_pow (by decide : 2≠0),add_zero,Real.sqrt_sq_eq_abs,
      abs_of_neg (sub_neg.mpr hAB),neg_sub] using H
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have H := (h1.add ((ha.sub hb).div hs (ne_of_gt (sub_pos.mpr hAB)))).div_const 2
  have hr : (A-B)/(B-A)= -1 := by rw [show A-B= -(B-A) by ring,neg_div,div_self (ne_of_gt (sub_pos.mpr hAB))]
  simpa only [softWeight,softSlope,Pi.div_apply,hr,add_neg_cancel,zero_div] using H

lemma convex_pair_bounds {p u v : ℝ} (hp : 0≤ p) (hp1 : p≤ 1) :
    min u v≤ p*u+(1-p)*v ∧ p*u+(1-p)*v≤ max u v := by
  by_cases h : u≤ v
  · rw [min_eq_left h,max_eq_right h]
    constructor <;> nlinarith [mul_nonneg hp (sub_nonneg.mpr h),mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr h)]
  · have h := le_of_not_ge h
    rw [min_eq_right h,max_eq_left h]
    constructor <;> nlinarith [mul_nonneg hp (sub_nonneg.mpr h),mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr h)]

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_MaximumMollifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped BigOperators Topology ContDiff Convolution
namespace NeutralAtom

def maximumBump (n : ℕ) : ContDiffBump (0:Position) :=
  ⟨(1/((n:ℝ)+1))/2, 1/((n:ℝ)+1), by positivity, by
    have H : 0<1/((n:ℝ)+1) := by positivity
    linarith⟩

def maximumMollify (n : ℕ) (f : Position → ℝ) : Position → ℝ :=
  f ⋆[lsmul ℝ ℝ,volume] (maximumBump n).normed volume

lemma maximumBump_rOut_le_one (n : ℕ) : (maximumBump n).rOut≤1 := by
  dsimp [maximumBump]
  exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)

lemma maximumBump_rOut_tendsto : Tendsto (fun n => (maximumBump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma maximumMollify_contDiff {f : Position → ℝ} (hf : LocallyIntegrable f volume) (n : ℕ) :
    ContDiff ℝ ∞ (maximumMollify n f) :=
  (maximumBump n).hasCompactSupport_normed.contDiff_convolution_right (lsmul ℝ ℝ) hf
    (maximumBump n).contDiff_normed

end NeutralAtom

end
open MeasureTheory Set Filter ContinuousLinearMap
open scoped BigOperators Topology ContDiff Convolution
namespace NeutralAtom

lemma continuous_softWeight {e : ℝ} (he : 0 < e) : Continuous (softWeight e) :=
  (continuous_const.add (continuous_id.div (contDiff_softAbs he).continuous
    (fun x => ne_of_gt (softAbs_pos he x)))).div_const 2

lemma convex_pair_abs_le {p u v A B : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hu : |u| ≤ A) (hv : |v| ≤ B) : |p*u+(1-p)*v| ≤ A+B := by
  calc
    _ ≤ |p*u|+|(1-p)*v| := abs_add_le _ _
    _ ≤ |u|+|v| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hp,abs_of_nonneg (sub_nonneg.mpr hp1)]
      apply add_le_add
      · simpa using mul_le_mul_of_nonneg_right hp1 (abs_nonneg u)
      · simpa using mul_le_mul_of_nonneg_right (show 1-p ≤ 1 by linarith) (abs_nonneg v)
    _ ≤ A+B := add_le_add hu hv

lemma tendsto_integral_compact_mul {F : ℕ → Position → ℝ} {f φ : Position → ℝ}
    (hF : ∀ n, Continuous (F n)) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {C : ℝ} (hb : ∀ n x, x ∈ tsupport φ → |F n x| ≤ C)
    (ht : ∀ᵐ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, F n x*φ x) atTop (𝓝 (∫ x, f x*φ x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => C*‖φ x‖)
    (fun n => ((hF n).mul hφ).aestronglyMeasurable)
    ((hφ.integrable_of_hasCompactSupport hc).norm.const_mul C)
  · intro n
    filter_upwards [] with x
    change ‖F n x*φ x‖ ≤ C*‖φ x‖
    rw [norm_mul,Real.norm_eq_abs (F n x)]
    by_cases hx : x ∈ tsupport φ
    · exact mul_le_mul_of_nonneg_right (hb n x hx) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · filter_upwards [ht] with x hx
    exact hx.mul_const _

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_WeakReactionMax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma joint_compact_test_integrable {F : Ω → Position → ℝ}
    (hm : Measurable (Function.uncurry F))
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |F o x| ≤ C)
    {φ : Position → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun z : Ω × Position => F z.1 z.2*φ z.2) (μ.prod volume) := by
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:Position)
  obtain ⟨C,hC⟩ := hb R
  have hi : Integrable (fun z : Ω × Position => C*‖φ z.2‖) (μ.prod volume) :=
    ((hφ.integrable_of_hasCompactSupport hc).norm.const_mul C).comp_snd μ
  apply hi.mono' (hm.mul (hφ.measurable.comp measurable_snd)).aestronglyMeasurable
  filter_upwards [] with z
  change ‖F z.1 z.2*φ z.2‖ ≤ C*‖φ z.2‖
  rw [norm_mul,Real.norm_eq_abs (F z.1 z.2)]
  by_cases hz : z.2 ∈ tsupport φ
  · exact mul_le_mul_of_nonneg_right (hC z.1 z.2 (hR hz)) (norm_nonneg _)
  · simp [image_eq_zero_of_notMem_tsupport hz]

lemma integral_average_test {F : Ω → Position → ℝ}
    (hm : Measurable (Function.uncurry F))
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |F o x| ≤ C)
    {φ : Position → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    (∫ x, (∫ o, F o x ∂μ)*φ x)=(∫ o, (∫ x, F o x*φ x) ∂μ) := by
  simp_rw [←integral_mul_const]
  exact (integral_integral_swap (joint_compact_test_integrable hm hb hφ hc)).symm

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_WeakLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma locallyIntegrable_of_ball_bounds {q : Position → ℝ} (hm : Measurable q)
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |q x| ≤ C) :
    LocallyIntegrable q volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0:Position)
  obtain ⟨C,hC⟩ := hb R
  have hfin : volume K < ⊤ := hK.measure_lt_top
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hfin⟩
  apply (integrable_const C).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  simpa only [Real.norm_eq_abs] using hC x (hR hx)

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_NearActiveMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

def propagationBarrier (B r : ℝ) (x : Position) : ℝ :=
  B*(radialPower (-2) x-r/8*radialPower (-(5/2:ℝ)) x)

lemma radialPower_half_nat (n : ℕ) (x : Position) :
    radialPower (-((n:ℝ)/2)) x=(‖x‖^n)⁻¹ := by
  unfold radialPower
  rw [←Real.rpow_natCast ‖x‖ 2,←Real.rpow_mul (norm_nonneg x)]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*-((n:ℝ)/2)=-(n:ℝ) by ring]
  rw [Real.rpow_neg (norm_nonneg x),Real.rpow_natCast]

lemma propagationBarrier_eq (B r : ℝ) (x : Position) :
    propagationBarrier B r x=B/‖x‖^4*(1-r/(8*‖x‖)) := by
  unfold propagationBarrier
  rw [show (-2:ℝ)=-(((4:ℕ):ℝ)/2) by norm_num,
    show (-(5/2:ℝ))=-(((5:ℕ):ℝ)/2) by norm_num]
  rw [radialPower_half_nat,radialPower_half_nat]
  by_cases hn : ‖x‖=0
  · simp [hn]
  · field_simp

lemma contDiffOn_propagationBarrier (B r : ℝ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (propagationBarrier B r) punctured :=
  contDiffOn_const.mul ((contDiffOn_radialPower (-2) n).sub
    (contDiffOn_const.mul (contDiffOn_radialPower (-(5/2:ℝ)) n)))

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationBarrierBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

def propagationGamma (B : ℝ) : ℝ := B/(16*(11/10:ℝ)^5)

lemma propagationBarrier_two_sided {B r : ℝ} (hB : 0≤B) (hr : 0 < r)
    {x : Position} (hx : r≤‖x‖) :
    (7/8:ℝ)*B/‖x‖^4≤propagationBarrier B r x ∧ propagationBarrier B r x≤B/‖x‖^4 := by
  have hd := hr.trans_le hx
  have ht : 0 ≤ r/(8*‖x‖) := by positivity
  have ht' : r/(8*‖x‖)≤1/8 := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hx])
  rw [propagationBarrier_eq]
  constructor
  · have H := mul_le_mul_of_nonneg_left (show (7/8:ℝ)≤1-r/(8*‖x‖) by linarith only [ht'])
      (div_nonneg hB (pow_pos hd 4).le)
    calc
      _=(B/‖x‖^4)*(7/8:ℝ) := by ring
      _≤_ := H
  · have H := mul_le_mul_of_nonneg_left (show 1-r/(8*‖x‖)≤1 by linarith only [ht])
      (div_nonneg hB (pow_pos hd 4).le)
    simpa only [mul_one] using H

lemma propagationBarrier_positive {B r : ℝ} (hB : 0<B) (hr : 0 < r)
    {x : Position} (hx : r≤‖x‖) : 0<propagationBarrier B r x := by
  have hd := hr.trans_le hx
  exact (by positivity : (0:ℝ)<(7/8:ℝ)*B/‖x‖^4).trans_le (propagationBarrier_two_sided hB.le hr hx).1

lemma propagationBarrier_gap {B r : ℝ} (hB : 0<B) (hr : 0 < r)
    {x : Position} (hx : 2*r≤‖x‖) (hx' : ‖x‖≤(11/10)*(2*r)) :
    propagationGamma B/(2*r)^4≤propagationBarrier B r x-propagationBarrier B (2*r) x := by
  have hd : 0<‖x‖ := (by positivity : (0:ℝ)<2*r).trans_le hx
  have he : (propagationBarrier B r x-propagationBarrier B (2*r) x)*(2*r)^4=
      B*(2*r)^5/(16*‖x‖^5) := by
    rw [propagationBarrier_eq,propagationBarrier_eq]
    field_simp
    ring
  apply (div_le_iff₀ (pow_pos (mul_pos (by norm_num) hr) 4)).mpr
  rw [he]
  apply (le_div_iff₀ (by positivity : 0<16*‖x‖^5)).mpr
  have hp := pow_le_pow_left₀ hd.le hx' 5
  have hmul := mul_le_mul_of_nonneg_left hp hB.le
  unfold propagationGamma
  norm_num
  nlinarith only [hmul]

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

structure PropagationConstants (B C : ℝ) where
  L : ℝ
  l1 : ℝ
  l2 : ℝ
  e : ℝ
  ξ : ℝ
  L_large : 2<L
  l2_pos : 0<l2
  l2_le_l1 : l2≤l1
  l1_le_gamma : l1≤propagationGamma B
  upper_overlap : C≤l2*L^4
  e_pos : 0<e
  xi_pos : 0<ξ
  xi_lt_l2 : ξ<l2
  xi_lt_height : ξ<B/2
  gain_gap : 16*ξ+2*e<l1-l2
  height_lower : B/2≤(7/8:ℝ)*B-2*e*(2*L)^4

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationBarrierOffset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

def propagationBarrierOffset (B R Z : ℝ) (x : Position) : ℝ :=
  B/(max R ‖x‖)^4*(1-R/(8*max R ‖x‖))-Z/(max R ‖x‖)

lemma propagationBarrierOffset_continuous (B Z : ℝ) {R : ℝ} (hR : 0<R) :
    Continuous (propagationBarrierOffset B R Z) := by
  have hD : Continuous (fun x : Position => max R ‖x‖) := continuous_const.max continuous_norm
  have hne (x : Position) : max R ‖x‖≠0 := ne_of_gt (hR.trans_le (le_max_left _ _))
  exact ((continuous_const.div (hD.pow 4) (fun x => pow_ne_zero 4 (hne x))).mul
    (continuous_const.sub (continuous_const.div (continuous_const.mul hD)
      (fun x => mul_ne_zero (by norm_num) (hne x))))).sub (continuous_const.div hD hne)

end NeutralAtom

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
namespace NeutralAtom

def propagationCoreSource (r d μ p : ℝ) : ℝ := 4*Real.pi*((if d < r then μ else 0)-p)
def propagationStepError (bad : Prop) (r R d μ p : ℝ) : ℝ :=
  p+if bad ∧ r≤d ∧ d<R then μ else 0

lemma propagationStepError_nonneg {bad : Prop} {r R d μ p : ℝ}
    (hμ : 0≤μ) (hp : 0≤p) : 0≤propagationStepError bad r R d μ p := by
  unfold propagationStepError
  split_ifs <;> positivity

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma normalized_cap {d C v : ℝ} (hd : 0<d) (hcap : v≤C/d^4) : d^4*v≤C := by
  have H := (le_div_iff₀ (pow_pos hd 4)).mp hcap
  nlinarith only [H]

lemma normalized_barrier_lower {B r u : ℝ} (hB : 0≤B) (hr : 0 < r)
    {x : Position} (hx : r≤‖x‖) (hu : propagationBarrier B r x≤u) : (7/8:ℝ)*B≤‖x‖^4*u := by
  have hd := hr.trans_le hx
  have H := (propagationBarrier_two_sided hB hr hx).1.trans hu
  exact le_trans (by rw [div_mul_cancel₀ _ (ne_of_gt (pow_pos hd 4))])
    (mul_le_mul_of_nonneg_right H (pow_pos hd 4).le) |>.trans_eq (mul_comm _ _)

lemma normalized_near_barrier_lower {B R L e v : ℝ} (hB : 0≤B) (hR : 0<R)
    (_ : 0≤L) (he : 0≤e) {x : Position} (hx : R≤‖x‖) (hx' : ‖x‖≤2*L*R)
    (hv : propagationBarrier B R x-2*e/R^4≤v) :
    (7/8:ℝ)*B-2*e*(2*L)^4≤‖x‖^4*v := by
  have hd := hR.trans_le hx
  have hl := (propagationBarrier_two_sided hB hR hx).1
  have H := mul_le_mul_of_nonneg_left hv (pow_pos hd 4).le
  have H' := mul_le_mul_of_nonneg_left hl (pow_pos hd 4).le
  have hh : ‖x‖^4*((7/8:ℝ)*B/‖x‖^4)=(7/8:ℝ)*B := by field_simp
  rw [hh] at H'
  have hp := pow_le_pow_left₀ hd.le hx' 4
  have he' : ‖x‖^4*(2*e/R^4)≤2*e*(2*L)^4 := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (pow_pos hR 4)).mpr
    calc
      _≤(2*L*R)^4*(2*e) := mul_le_mul_of_nonneg_right hp (by positivity)
      _=2*e*(2*L)^4*R^4 := by ring
  nlinarith only [H,H',he']

lemma near_active_old_field {u H M R l1 l2 e : ℝ} (_ : 0<R)
    (hcandidate : H-l2/R^4≤M) (hnear : M-(u-l1/R^4)<2*e/R^4) :
    H≤u-(l1-l2-2*e)/R^4 := by
  have he : (l1-l2-2*e)/R^4=l1/R^4-l2/R^4-2*e/R^4 := by ring
  rw [he]
  linarith only [hcandidate,hnear]

lemma near_active_physical_lower {v M B R e : ℝ} {x : Position}
    (hlower : propagationBarrier B R x≤M) (hnear : M-v<2*e/R^4) :
    propagationBarrier B R x-2*e/R^4≤v := by linarith only [hlower,hnear]

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_RadialMaxSplice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology Classical
noncomputable section
namespace NeutralAtom

def radialMaxSplice (α β : ℝ) (f g : Position → ℝ) (x : Position) : ℝ :=
  if ‖x‖<α then f x else if ‖x‖<β then max (f x) (g x) else g x

lemma radialMaxSplice_inner {α β a b : ℝ} {f g : Position → ℝ}
    (hbα : b≤α) (haβ : a≤β)
    (hlow : ∀ x,b≤‖x‖ → ‖x‖≤a → g x≤f x)
    {x : Position} (hx : ‖x‖<a) : radialMaxSplice α β f g x=f x := by
  unfold radialMaxSplice
  split_ifs with hα hβ
  · rfl
  · exact max_eq_left (hlow x (hbα.trans (le_of_not_gt hα)) hx.le)
  · exact False.elim (hβ (hx.trans_le haβ))

lemma radialMaxSplice_middle {α β a b c e : ℝ} {f g : Position → ℝ}
    (hαa : α≤a) (heβ : e≤β)
    (hlow : ∀ x,b≤‖x‖ → ‖x‖≤a → g x≤f x)
    (hupp : ∀ x,e≤‖x‖ → ‖x‖ ≤ c → f x≤g x)
    {x : Position} (hx : b<‖x‖ ∧ ‖x‖ < c) : radialMaxSplice α β f g x=max (f x) (g x) := by
  unfold radialMaxSplice
  split_ifs with hα hβ
  · exact (max_eq_left (hlow x hx.1.le (hα.le.trans hαa))).symm
  · rfl
  · exact (max_eq_right (hupp x (heβ.trans (le_of_not_gt hβ)) hx.2.le)).symm

lemma radialMaxSplice_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {f g : Ω → Position → ℝ} (α β : ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : Ω×Position => radialMaxSplice α β (f z.1) (g z.1) z.2) := by
  exact hf.ite (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const)
    ((hf.max hg).ite (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const) hg)

lemma radialMaxSplice_abs_bound {α β A B : ℝ} {f g : Position → ℝ} {x : Position}
    (hf : |f x|≤A) (hg : |g x|≤B) : |radialMaxSplice α β f g x| ≤ max A B := by
  unfold radialMaxSplice
  split_ifs
  · exact hf.trans (le_max_left _ _)
  · have hAf : -(max A B)≤f x := (neg_le_neg (le_max_left A B)).trans ((abs_le.mp hf).1)
    have hBf : f x ≤ max A B := (abs_le.mp hf).2.trans (le_max_left _ _)
    have hAg : g x ≤ max A B := (abs_le.mp hg).2.trans (le_max_right _ _)
    exact abs_le.mpr ⟨hAf.trans (le_max_left _ _),max_le hBf hAg⟩
  · exact hg.trans (le_max_right _ _)

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

def propagationPairOffset (bad : Prop) (R l1 l2 : ℝ) (u H : Position → ℝ) (x : Position) : ℝ :=
  if bad then u x-l1/R^4 else max (u x-l1/R^4) (H x-l2/R^4)

def propagationNextOffset (bad : Prop) (B R Z L l1 l2 : ℝ) (u H : Position → ℝ) : Position → ℝ :=
  radialMaxSplice ((53/50)*R) ((3/2)*L*R)
    (propagationPairOffset bad R l1 l2 u H) (propagationBarrierOffset B R Z)

lemma le_propagationPairOffset (bad : Prop) (R l1 l2 : ℝ) (u H : Position → ℝ) (x : Position) :
    u x-l1/R^4 ≤ propagationPairOffset bad R l1 l2 u H x := by
  unfold propagationPairOffset
  split_ifs
  · rfl
  · exact le_max_left _ _

lemma propagation_shift_cap_nonpos {C d R L l v : ℝ} (hR : 0<R) (hL : 0<L)
    (hl : 0≤l) (hd : L*R≤d) (hC : C≤l*L^4) (hv : v≤C/d^4) : v-l/R^4≤0 := by
  have hd' := (mul_pos hL hR).trans_le hd
  have hp := pow_le_pow_left₀ (mul_pos hL hR).le hd 4
  have h1 := mul_le_mul_of_nonneg_right hC (pow_pos hR 4).le
  have h2 := mul_le_mul_of_nonneg_left hp hl
  have hh : C/d^4≤l/R^4 := (div_le_div_iff₀ (pow_pos hd' 4) (pow_pos hR 4)).mpr (by
    nlinarith only [h1,h2])
  linarith only [hv,hh]

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

def propagationCandidates (B R Z l1 l2 : ℝ) (u H : Position → ℝ) : Fin 3 → Position → ℝ :=
  ![fun x => u x-l1/R^4,fun x => H x-l2/R^4,propagationBarrierOffset B R Z]

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

def propagationInnerIndices (bad : Prop) : Finset (Fin 3) := if bad then {0} else {0,1}
def propagationMiddleIndices (bad : Prop) : Finset (Fin 3) := insert 2 (propagationInnerIndices bad)

lemma zero_mem_propagationInnerIndices (bad : Prop) : (0:Fin 3)∈propagationInnerIndices bad := by
  by_cases h : bad <;> simp [propagationInnerIndices,h]
lemma one_mem_propagationInnerIndices (bad : Prop) : (1:Fin 3)∈propagationInnerIndices bad ↔ ¬bad := by
  by_cases h : bad <;> simp [propagationInnerIndices,h]
lemma two_not_mem_propagationInnerIndices (bad : Prop) : (2:Fin 3)∉propagationInnerIndices bad := by
  by_cases h : bad <;> simp [propagationInnerIndices,h]
lemma zero_mem_propagationMiddleIndices (bad : Prop) : (0:Fin 3)∈propagationMiddleIndices bad :=
  Finset.mem_insert_of_mem (zero_mem_propagationInnerIndices bad)
lemma one_mem_propagationMiddleIndices (bad : Prop) : (1:Fin 3)∈propagationMiddleIndices bad ↔ ¬bad := by
  simp [propagationMiddleIndices,one_mem_propagationInnerIndices]

lemma propagationInner_sup (bad : Prop) (B R Z l1 l2 : ℝ) (u H : Position → ℝ) (x : Position) :
    (propagationInnerIndices bad).sup' ⟨0,zero_mem_propagationInnerIndices bad⟩
      (fun i => propagationCandidates B R Z l1 l2 u H i x)=propagationPairOffset bad R l1 l2 u H x := by
  by_cases h : bad <;> simp [propagationInnerIndices,propagationCandidates,propagationPairOffset,h]

lemma propagationMiddle_sup (bad : Prop) (B R Z l1 l2 : ℝ) (u H : Position → ℝ) (x : Position) :
    (propagationMiddleIndices bad).sup' ⟨0,zero_mem_propagationMiddleIndices bad⟩
      (fun i => propagationCandidates B R Z l1 l2 u H i x)=
      max (propagationPairOffset bad R l1 l2 u H x) (propagationBarrierOffset B R Z x) := by
  change (insert 2 (propagationInnerIndices bad)).sup' _ _=_
  rw [Finset.sup'_insert ⟨0,zero_mem_propagationInnerIndices bad⟩,propagationInner_sup]
  exact max_comm _ _

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma propagationCoreSource_measurable {r : ℝ} {μ p : Position → ℝ}
    (hμ : Measurable μ) (hp : Measurable p) :
    Measurable (fun x => propagationCoreSource r ‖x‖ (μ x) (p x)) := by
  exact measurable_const.mul ((hμ.ite (isOpen_lt continuous_norm continuous_const).measurableSet measurable_const).sub hp)

lemma propagationStepError_measurable (bad : Prop) (r R : ℝ) {μ p : Position → ℝ}
    (hμ : Measurable μ) (hp : Measurable p) :
    Measurable (fun x => propagationStepError bad r R ‖x‖ (μ x) (p x)) := by
  unfold propagationStepError
  by_cases hb : bad
  · simp only [hb,true_and]
    exact hp.add (hμ.ite ((isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet) measurable_const)
  · simpa only [hb,false_and,ite_false,add_zero] using hp

lemma propagationCoreSource_abs_bound {r d μ p M P : ℝ} (hμ : |μ|≤M) (hp : |p|≤P) :
    |propagationCoreSource r d μ p|≤4*Real.pi*(M+P) := by
  have hm : |if d < r then μ else 0|≤M := by
    split_ifs
    · exact hμ
    · simpa only [abs_zero] using (abs_nonneg μ).trans hμ
  unfold propagationCoreSource
  rw [abs_mul,abs_of_pos (by positivity : 0<4*Real.pi)]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hm hp)) (by positivity)

lemma propagationStepError_abs_bound {bad : Prop} {r R d μ p M P : ℝ}
    (hμ : |μ|≤M) (hp : |p|≤P) : |propagationStepError bad r R d μ p|≤P+M := by
  unfold propagationStepError
  split_ifs
  · exact (abs_add_le _ _).trans (add_le_add hp hμ)
  · simp only [add_zero]
    have : 0≤M := (abs_nonneg μ).trans hμ
    linarith only [hp,this]

lemma propagationCoreSource_ball_bounds {r : ℝ} {μ p : Position → ℝ}
    (hμ : ∀ D : ℝ,∃ M : ℝ,∀ x∈Metric.closedBall 0 D,|μ x|≤M)
    (hp : ∀ D : ℝ,∃ P : ℝ,∀ x∈Metric.closedBall 0 D,|p x|≤P) :
    ∀ D : ℝ,∃ K : ℝ,∀ x∈Metric.closedBall 0 D,|propagationCoreSource r ‖x‖ (μ x) (p x)|≤K := by
  intro D
  obtain ⟨M,hM⟩ := hμ D
  obtain ⟨P,hP⟩ := hp D
  exact ⟨4*Real.pi*(M+P),fun x hx => propagationCoreSource_abs_bound (hM x hx) (hP x hx)⟩

lemma propagationStepError_ball_bounds {bad : Prop} {r R : ℝ} {μ p : Position → ℝ}
    (hμ : ∀ D : ℝ,∃ M : ℝ,∀ x∈Metric.closedBall 0 D,|μ x|≤M)
    (hp : ∀ D : ℝ,∃ P : ℝ,∀ x∈Metric.closedBall 0 D,|p x|≤P) :
    ∀ D : ℝ,∃ K : ℝ,∀ x∈Metric.closedBall 0 D,|propagationStepError bad r R ‖x‖ (μ x) (p x)|≤K := by
  intro D
  obtain ⟨M,hM⟩ := hμ D
  obtain ⟨P,hP⟩ := hp D
  exact ⟨P+M,fun x hx => propagationStepError_abs_bound (hM x hx) (hP x hx)⟩

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_InitializationBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

def initialPropagationOffset (bad : Prop) (Z r a : ℝ) (H : Position → ℝ) (x : Position) : ℝ :=
  (if bad then 0 else H x)-(7/10:ℝ)*Z/r+a*‖x‖^2

def initialPropagationError (bad : Prop) (r : ℝ) (μ : Position → ℝ) (x : Position) : ℝ :=
  if bad ∧ ‖x‖ < r then μ x else 0

lemma initialPropagationError_nonneg {bad : Prop} {r : ℝ} {μ : Position → ℝ}
    (hμ : ∀ x,0≤μ x) (x : Position) : 0 ≤ initialPropagationError bad r μ x := by
  unfold initialPropagationError
  split_ifs
  · exact hμ x
  · rfl

lemma initialPropagationError_support (bad : Prop) (r : ℝ) (μ : Position → ℝ)
    {x : Position} (hx : r≤‖x‖) : initialPropagationError bad r μ x=0 := by
  simp [initialPropagationError,not_lt_of_ge hx]

lemma initialPropagationError_measurable (bad : Prop) (r : ℝ) {μ : Position → ℝ}
    (hμ : Measurable μ) : Measurable (initialPropagationError bad r μ) := by
  unfold initialPropagationError
  by_cases hb : bad
  · simp only [hb,true_and]
    exact hμ.ite (isOpen_lt continuous_norm (continuous_const (y:=r))).measurableSet measurable_const
  · simp only [hb,false_and,ite_false]
    exact measurable_const

lemma initialPropagationError_ball_bounds {bad : Prop} {r : ℝ} {μ : Position → ℝ}
    (hμ : ∀ D : ℝ,∃ C : ℝ,∀ x∈Metric.closedBall 0 D,|μ x|≤C) :
    ∀ D : ℝ,∃ C : ℝ,∀ x∈Metric.closedBall 0 D,|initialPropagationError bad r μ x|≤C := by
  intro D
  obtain ⟨C,hC⟩ := hμ D
  refine ⟨max C 0,fun x hx => ?_⟩
  unfold initialPropagationError
  split_ifs
  · exact (hC x hx).trans (le_max_left _ _)
  · simpa only [abs_zero] using le_max_right C 0

lemma initial_core_source (bad : Prop) (r : ℝ) (μ : Position → ℝ) (x : Position)
    (hμ : 0≤μ x) : propagationCoreSource r ‖x‖ (μ x) (initialPropagationError bad r μ x)≤
      4*Real.pi*(if bad then 0 else μ x) := by
  by_cases hb : bad <;> by_cases hd : ‖x‖ < r
  all_goals simp [propagationCoreSource,initialPropagationError,hb,hd]
  positivity

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

def initialNextOffset (bad : Prop) (B Z r a : ℝ) (H : Position → ℝ) : Position → ℝ :=
  radialMaxSplice ((103/100)*r) ((39/20)*r) (initialPropagationOffset bad Z r a H)
    (propagationBarrierOffset B r Z)

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom
section Average
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integrable_section_of_ball_bounds {f : Ω → Position → ℝ}
    (hm : Measurable (Function.uncurry f))
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C)
    (x : Position) : Integrable (fun o => f o x) μ := by
  obtain ⟨C,hC⟩ := hb ‖x‖
  apply (integrable_const C).mono' (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [] with o
  change ‖f o x‖ ≤ C
  simpa only [Real.norm_eq_abs] using hC o x (by simp)

lemma average_ball_bounds {f : Ω → Position → ℝ}
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C) :
    ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |∫ o, f o x ∂μ| ≤ C := by
  intro R
  obtain ⟨C,hC⟩ := hb R
  refine ⟨C,fun x hx => ?_⟩
  calc
    |∫ o, f o x ∂μ| ≤ ∫ o, |f o x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Ω, C ∂μ := integral_mono_of_nonneg
      (Eventually.of_forall (fun o => abs_nonneg (f o x))) (integrable_const C)
      (Eventually.of_forall (fun o => hC o x hx))
    _ = C := by simp

end Average
end NeutralAtom

end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorDensityContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Posterior
variable {Ω A : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace A]
variable (P : Measure Ω) [IsProbabilityMeasure P] (obs : Ω → A)

lemma posterior_ae {q : Ω → Prop} (ho : Measurable obs) (hq : ∀ᵐ o ∂P,q o) :
    ∀ᵐ o ∂P,∀ᵐ v ∂ProbabilityTheory.condDistrib id obs P (obs o),q v := by
  have H : ∀ᵐ v ∂(ProbabilityTheory.condDistrib id obs P ∘ₘ P.map obs),q v := by
    simpa only [ProbabilityTheory.condDistrib_comp_map ho.aemeasurable aemeasurable_id,Measure.map_id] using hq
  exact ae_of_ae_map ho.aemeasurable (Measure.ae_ae_of_ae_comp H)
end Posterior
end NeutralAtom
end

end
section
open MeasureTheory
noncomputable section
namespace NeutralAtom
instance observationNoise_standardBorel (n J : ℕ) : StandardBorelSpace (ObservationNoise n J) := by
  let : StandardBorelSpace (Fin 3 → ℝ) := StandardBorelSpace.pi_countable
  let : StandardBorelSpace (Fin n → Fin 3 → ℝ) := StandardBorelSpace.pi_countable
  exact StandardBorelSpace.pi_countable
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PhysicalInitialPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology Classical SchwartzMap
noncomputable section
namespace NeutralAtom

def initialPacketModulus (A c r : ℝ) : ℝ :=
  3*(A*(c^3)⁻¹*r^(1-3*packetExponent)+r^4)

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_InitialMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace NeutralAtom

def initialAtomicRadius (ε Z : ℝ) : ℝ := ε*Z^(-(1/3:ℝ))

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RadialBounds_Radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

def IsRadial (w : Position → ℝ) : Prop := ∀ x y, ‖x‖ = ‖y‖ → w x = w y

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RadialBounds_SpatialAnnulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

def spatialAnnulus (a b : ℝ) : Set Position := {x | a < ‖x‖ ∧ ‖x‖ < b}

def Admissible (Zbar : ℝ → ℕ) (s : ℕ → ℝ) (N : ℕ → ℕ) : Prop :=
  (∀ᶠ n in atTop, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
  (∀ᶠ n in atTop, Zbar (s n) ≤ N n + 1) ∧
  Tendsto (fun n => (N n + 1 : ℝ) * s n ^ (3 : ℕ)) atTop atTop

def ExpectedExteriorAsymptotic (Zbar : ℝ → ℕ) : Prop :=
  ∀ (s : ℕ → ℝ) (N : ℕ → ℕ), Admissible Zbar s N →
    ∀ ψ : ∀ n, Wavefunction (N n + 1),
      (∀ n, IsNormalizedGroundState (N n + 1) (ψ n)) →
      ∀ a : ℝ, 0 < a →
        Tendsto (fun n => s n ^ (3 : ℕ) * exteriorMass (ψ n) (a*s n))
          atTop (𝓝 (bTF^ (3 : ℕ) / a^ (3 : ℕ)))

def radiusChargeThreshold (Zbar : ℝ → ℕ) (m : ℕ) : ℕ :=
  max (Zbar ((m : ℝ)^(-(1/3 : ℝ)))) ((m+1)^2)

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PuncturedPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

abbrev PuncturedPosition := {x : Position // x ≠ 0}

def extendPunctured (f : PuncturedPosition → ℝ) (x : Position) : ℝ :=
  if hx : x ≠ 0 then f ⟨x, hx⟩ else 0

@[simp] theorem extendPunctured_val (f : PuncturedPosition → ℝ) (x : PuncturedPosition) :
    extendPunctured f x = f x := by simp [extendPunctured, x.property]

def closedNormAnnulus (a b : ℝ) : Set Position := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_Rescaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

def scaledDensity (D : ℝ) (σ : Position → ℝ) (x : Position) : ℝ := D^6*σ (D • x)

theorem scaledDensity_integrable {D : ℝ} (hD : 0 < D) {σ : Position → ℝ}
    (hi : Integrable σ) : Integrable (scaledDensity D σ) :=
  (hi.comp_smul hD.ne').const_mul _

theorem integral_scaledDensity {D : ℝ} (hD : 0 < D) (σ : Position → ℝ) :
    (∫ x, scaledDensity D σ x) = D^3*(∫ x, σ x) := by
  unfold scaledDensity
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume σ D (hR := hD.le)]
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul]
  field_simp

theorem scaledDensity_nonneg {D : ℝ} {σ : Position → ℝ}
    (hσ : ∀ x, 0 ≤ σ x) (x : Position) : 0 ≤ scaledDensity D σ x :=
  mul_nonneg (by positivity) (hσ _)

theorem scaledDensity_bound {D A : ℝ} {σ : Position → ℝ}
    (hσ : ∀ x, σ x ≤ A) (x : Position) : scaledDensity D σ x ≤ D^6*A :=
  mul_le_mul_of_nonneg_left (hσ _) (by positivity)

theorem scaledDensity_support {D r : ℝ} (hD : 0 < D) {p : Position → ℝ}
    (hp : ∀ x, r < ‖x‖ → p x = 0) (x : Position) (hx : r/D < ‖x‖) :
    scaledDensity D p x = 0 := by
  have hh : r < ‖D • x‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_comm] using
      (div_lt_iff₀ hD).mp hx
  simp only [scaledDensity, hp _ hh, mul_zero]

theorem barrier_bounds_dilate {D r B C : ℝ} (hD : 0 < D) {U : Position → ℝ}
    (hbound : ∀ y, r ≤ ‖y‖ →
      B/‖y‖^4*(1-r/(8*‖y‖)) ≤ U y ∧ U y ≤ C/‖y‖^4)
    (x : Position) (hx : r/D ≤ ‖x‖) :
    B/‖x‖^4*(1-(r/D)/(8*‖x‖)) ≤ D^4*U (D • x) ∧
      D^4*U (D • x) ≤ C/‖x‖^4 := by
  have hh : r ≤ ‖D • x‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_comm] using
      (div_le_iff₀ hD).mp hx
  have hb := hbound _ hh
  have hnorm : ‖D • x‖ = D*‖x‖ := by simp [norm_smul, abs_of_pos hD]
  have hlo : D^4*(B/‖D • x‖^4*(1-r/(8*‖D • x‖))) =
      B/‖x‖^4*(1-(r/D)/(8*‖x‖)) := by
    rw [hnorm]
    by_cases hz : ‖x‖ = 0
    · simp [hz]
    · field_simp
  have hup : D^4*(C/‖D • x‖^4) = C/‖x‖^4 := by
    rw [hnorm, mul_pow]
    field_simp
  constructor
  · rw [← hlo]
    exact mul_le_mul_of_nonneg_left hb.1 (by positivity)
  · rw [← hup]
    exact mul_le_mul_of_nonneg_left hb.2 (by positivity)

theorem mul_inverse_power_dilate {D : ℝ} (hD : 0 < D) (C : ℝ) (n : ℕ) (x : Position) :
    D^n*(C/‖D • x‖^n) = C/‖x‖^n := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hD, mul_pow]
  field_simp

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_QuantumProfileDatum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

def profileRadius (ε : ℝ) (N j : ℕ) : ℝ := initialAtomicRadius ε ((N+1:ℕ):ℝ)*2^j

end NeutralAtom
end

end

end OAI
end


