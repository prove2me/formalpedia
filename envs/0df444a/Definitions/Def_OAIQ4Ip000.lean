-- Prove2me | Definitions.Def_OAIQ4Ip000
-- name    : OAIQ4Ip000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T07:12:49.669088+00:00
-- url     : https://prove2.me/theorems/c5d1ed6a-2ed5-47ff-a89f-ba697cdd0df3
-- title:
--   Definitions bundle OAIQ4Ip000 of the split of OpenAI, The free energy of the Ising random perceptron
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.IsingPerceptron.variationalValue_real_of_continuous`, carved from OpenAI's openai/math development (OpenAI, *The free energy of the Ising random perceptron*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 373 declarations of OpenAI's Lean: 250 definitions, 1 inductive type or structure, 58 instances and 64 theorems. The definitions and types are `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.ChildLabel`, `OAI.IsingPerceptron.EnrichedBlock`, `OAI.IsingPerceptron.EnrichedCylinderBase`, `OAI.IsingPerceptron.EnrichedCylinderData`, `OAI.IsingPerceptron.EnrichedLabeledData`, `OAI.IsingPerceptron.EnrichedPoissonRoot`, `OAI.IsingPerceptron.EnrichedRootData`, `OAI.IsingPerceptron.EnrichedRootSize`, `OAI.IsingPerceptron.ExponentialNormMoments`, `OAI.IsingPerceptron.ForestVertex`, `OAI.IsingPerceptron.GibbsReference`, `OAI.IsingPerceptron.GoodNoiseTree`, `OAI.IsingPerceptron.GramDiagonal`, `OAI.IsingPerceptron.HasEntryGhirlandaGuerra`, `OAI.IsingPerceptron.HasGhirlandaGuerra`, `OAI.IsingPerceptron.HasLinearGrowth`, `OAI.IsingPerceptron.HasStableTotal`, `OAI.IsingPerceptron.InfiniteRootData`, `OAI.IsingPerceptron.IsUltrametricArray`, `OAI.IsingPerceptron.JointArray`, `OAI.IsingPerceptron.JointBlock`, `OAI.IsingPerceptron.JointEntry`, `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.MarkForest`, `OAI.IsingPerceptron.Marked.PoissonGood`, `OAI.IsingPerceptron.NoiseGibbsRegular`, `OAI.IsingPerceptron.NoiseLeaf`, `OAI.IsingPerceptron.NoiseTree`, `OAI.IsingPerceptron.OtherNamespaces`, `OAI.IsingPerceptron.PositiveCovariance`, `OAI.IsingPerceptron.PrefixPattern`, `OAI.IsingPerceptron.RawLeaf`, `OAI.IsingPerceptron.RawTree`, `OAI.IsingPerceptron.RawTreeSpace`, `OAI.IsingPerceptron.RealArray`, `OAI.IsingPerceptron.Spin`, `OAI.IsingPerceptron.WeightCloud`, `OAI.IsingPerceptron.arrayBlock` and 211 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/IsingPerceptron, in whole or in part: `IsingPerceptron_ArrayGeometry`, `IsingPerceptron_ArraySynchronization`, `IsingPerceptron_CascadeFreshMoments`, `IsingPerceptron_CascadePair`, `IsingPerceptron_ChildLabel`, `IsingPerceptron_ContactFaces`, `IsingPerceptron_ConvexDerivativeFluctuation`, `IsingPerceptron_CountableMonomialGG`, `IsingPerceptron_EnergyShift`, `IsingPerceptron_EnrichedCGF`, `IsingPerceptron_EnrichedFieldCap`, `IsingPerceptron_EnrichedGGFinite`, `IsingPerceptron_FieldChain`, `IsingPerceptron_GaussianIntegration`, `IsingPerceptron_GaussianMomentTest`, `IsingPerceptron_JointGGClosure`, `IsingPerceptron_JointShapes`, `IsingPerceptron_LabeledSampling`, `IsingPerceptron_LintegralGammaKernel`, `IsingPerceptron_MapWithDensityEquiv`, `IsingPerceptron_MarkedPartitionNumerator`, `IsingPerceptron_MemLpOfAbsBound`, `IsingPerceptron_MonomialGgAtMinimum`, `IsingPerceptron_NamespaceSplit`, `IsingPerceptron_NoiseGibbsRegular`, `IsingPerceptron_NoiseTreeKeep`, `IsingPerceptron_NormalizedRestrictionPi`, `IsingPerceptron_PartitionPowLe`, `IsingPerceptron_PoissonCloud`, `IsingPerceptron_ReplicaEnergyCovarianceBound`, `IsingPerceptron_RetainedDisplacement`, `IsingPerceptron_SamplingIndependent`, `IsingPerceptron_TiltedLabelLaw`, `IsingPerceptron_VarianceDerivative`, `IsingPerceptron_VarianceOfConditionalCenterBound`, `IsingPerceptron_VariationalDefs`, `IsingPerceptron_VariationalFiniteness`, `IsingPerceptron_WeightedPartitionNumeratorIncrement`.
--
--   **Imports.** It imports the published bundle `Def_IsingFiniteness`.
--
--   **Imported by** (directly, in this split): the proof of `OAI.IsingPerceptron.variationalValue_real_of_continuous`.
-- source:
--   OpenAI, The free energy of the Ising random perceptron, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-free-energy-of-the-Ising-random-perceptron-September-24-2026/The-free-energy-of-the-Ising-random-perceptron-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/IsingPerceptron at commit adc7f12

import Mathlib
import Definitions.Def_IsingFiniteness

section
-- module Solutions.OAIQ4_Ip.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_PoissonCloud
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson Cloud. -/

noncomputable section



 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

 
namespace IsingPerceptron

variable {E : Type*} [MeasurableSpace E]

def finitePoissonCloud (r : ℝ≥0) (μ : Measure E) : Measure (ℕ × (ℕ → E)) :=
  (poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ => μ))

instance finitePoissonCloud_probability (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (finitePoissonCloud r μ) := by
  unfold finitePoissonCloud
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def cloudSum (ψ : E → ℝ) (p : ℕ × (ℕ → E)) : ℝ :=
  ∑ i : Fin p.1, ψ (p.2 i)

def enegExp (x : ℝ≥0∞) : ℝ≥0∞ := EReal.exp (-(x : EReal))
def negExp (x : ℝ≥0∞) : ℝ := (enegExp x).toReal

lemma enegExp_le_one (x : ℝ≥0∞) : enegExp x ≤ 1 := by
  exact EReal.exp_le_one_iff.mpr (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg x))
lemma enegExp_ne_top (x : ℝ≥0∞) : enegExp x ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (enegExp_le_one x)
lemma continuous_enegExp : Continuous enegExp :=
  ENNReal.continuous_exp.comp continuous_coe_ennreal_ereal.neg
lemma continuous_negExp : Continuous negExp :=
  continuous_iff_continuousAt.mpr fun x =>
    (ENNReal.continuousAt_toReal (enegExp_ne_top x)).comp continuous_enegExp.continuousAt
lemma negExp_nonneg (x : ℝ≥0∞) : 0 ≤ negExp x := ENNReal.toReal_nonneg
lemma negExp_le_one (x : ℝ≥0∞) : negExp x ≤ 1 := by
  exact (ENNReal.toReal_le_toReal (enegExp_ne_top x) ENNReal.one_ne_top).mpr
    (enegExp_le_one x)
@[simp] lemma enegExp_zero : enegExp 0 = 1 := by simp [enegExp]
@[simp] lemma enegExp_top : enegExp ∞ = 0 := by simp [enegExp]
@[simp] lemma negExp_zero : negExp 0 = 1 := by simp [negExp]
@[simp] lemma negExp_top : negExp ∞ = 0 := by simp [negExp]


def finiteCloudMeasure (p : ℕ × (ℕ → E)) : Measure E :=
  ∑ i : Fin p.1, Measure.dirac (p.2 i)

lemma measurable_finiteCloudMeasure : Measurable (finiteCloudMeasure (E := E)) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun ω : ℕ → E => ∑ i : Fin n, Measure.dirac (ω i))
  exact Finset.measurable_sum _ (fun i _ => Measure.measurable_dirac.comp
    (measurable_pi_apply (i : ℕ)))

variable [Nonempty E]

 
def finitePoissonLaw (μ : FiniteMeasure E) : Measure (Measure E) :=
  (finitePoissonCloud μ.mass (μ.normalize : Measure E)).map finiteCloudMeasure

instance finitePoissonLaw_probability (μ : FiniteMeasure E) :
    IsProbabilityMeasure (finitePoissonLaw μ) := by
  unfold finitePoissonLaw
  exact Measure.isProbabilityMeasure_map measurable_finiteCloudMeasure.aemeasurable


def poissonComponentLaw (μ : Measure E) [SFinite μ] (n : ℕ) : Measure (Measure E) :=
  finitePoissonLaw ⟨sfiniteSeq μ n, by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩

instance poissonComponentLaw_probability (μ : Measure E) [SFinite μ] (n : ℕ) :
    IsProbabilityMeasure (poissonComponentLaw μ n) := by
  exact finitePoissonLaw_probability ⟨sfiniteSeq μ n, by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩

def poissonProductLaw (μ : Measure E) [SFinite μ] : Measure (ℕ → Measure E) :=
  Measure.infinitePi (poissonComponentLaw μ)

instance poissonProductLaw_probability (μ : Measure E) [SFinite μ] :
    IsProbabilityMeasure (poissonProductLaw μ) := by unfold poissonProductLaw; infer_instance

omit [Nonempty E] in
lemma measurable_measureSum : Measurable (Measure.sum : (ℕ → Measure E) → Measure E) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.sum_apply _ hs]
  exact Measurable.tsum fun n => (Measure.measurable_coe hs).comp (measurable_pi_apply n)

 
def poissonLaw (μ : Measure E) [SFinite μ] : Measure (Measure E) :=
  (poissonProductLaw μ).map Measure.sum

instance poissonLaw_probability (μ : Measure E) [SFinite μ] : IsProbabilityMeasure (poissonLaw μ) := by
  unfold poissonLaw
  exact Measure.isProbabilityMeasure_map measurable_measureSum.aemeasurable


def negExpBCF : ℝ≥0∞ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup negExp continuous_negExp 1
    (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg x)]; exact negExp_le_one x)

def measureCoordinates (ν : Measure E) (s : {s : Set E // MeasurableSet s}) : ℝ≥0∞ := ν s.1

end IsingPerceptron


end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_LabeledSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labeled Sampling. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
open Function


def finitePartKernel {E : Type*} [MeasurableSpace E] : Kernel (Measure E) E where
  toFun ν := if ν univ < ∞ then ν else 0
  measurable' := measurable_id.ite
    (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const)
    measurable_const

variable {E : Type*} [MeasurableSpace E]
def atomCloud {n : ℕ} (ω : Fin n → E) : Measure E :=
  ∑ i, Measure.dirac (ω i)

def poissonWeight (r : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ))

variable [Nonempty E]



def sigmaPart (μ : Measure E) [SigmaFinite μ] (ν : Measure E) : Measure E :=
  Measure.sum (fun n => finitePartKernel (ν.restrict (disjointed (spanningSets μ) n)))

end IsingPerceptron


end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_MapWithDensityEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Map With Density Equiv. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

def powerIntensityDensity (b : ℝ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (if 0 < x then b * x ^ (-1-b) else 0)

def powerIntensity (b : ℝ) : Measure ℝ := volume.withDensity (powerIntensityDensity b)

instance powerIntensity_sigmaFinite (b : ℝ) : SigmaFinite (powerIntensity b) := by
  unfold powerIntensity powerIntensityDensity
  infer_instance

open Set

def stableLaplaceCost (x : ℝ) : ℝ := 1 - Real.exp (-max x 0)

def stableLaplaceConstant (b : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (stableLaplaceCost x) ∂powerIntensity b

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_LintegralGammaKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lintegral Gamma Kernel. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

instance powerIntensity_nullSingleton (b : ℝ) : NullSingletonClass (powerIntensity b) := by
  unfold powerIntensity
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

end IsingPerceptron

namespace IsingPerceptron.Marked

variable {E : Type} [MeasurableSpace E] [Nonempty E]

def PoissonGood (μ : Measure E) [SigmaFinite μ] (ν : Measure E) : Prop :=
  ∀ n, ν (disjointed (spanningSets μ) n) < ∞

end IsingPerceptron.Marked

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_MarkedPartitionNumerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked Partition Numerator. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron
variable {E : Type*} [MeasurableSpace E] [Nonempty E]

def weightedPoissonTotal (a : E → ℝ≥0∞) (ν : Measure (ℝ × E)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (max p.1 0) * a p.2 ∂ν

end IsingPerceptron

namespace IsingPerceptron

structure RawTreeSpace where
  carrier : Type
  space : MeasurableSpace carrier

attribute [instance] RawTreeSpace.space

@[reducible] def rawTreeSpace : ℕ → RawTreeSpace
  | 0 => ⟨PUnit, by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  | n+1 => ⟨Measure (ℝ × (rawTreeSpace n).carrier), by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩

abbrev RawTree (n : ℕ) := (rawTreeSpace n).carrier

instance rawTreeMeasurableSpace (n : ℕ) : MeasurableSpace (RawTree n) :=
  (rawTreeSpace n).space

instance rawTreeNonempty : (n : ℕ) → Nonempty (RawTree n)
  | 0 => ⟨PUnit.unit⟩
  | n+1 => ⟨(0 : Measure (ℝ × RawTree n))⟩

def rawTreeTotal : (n : ℕ) → RawTree n → ℝ≥0∞
  | 0, _ => 1
  | n+1, ν => ∫⁻ p : ℝ × RawTree n, ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2 ∂ν

lemma measurable_rawTreeTotal (n : ℕ) : Measurable (rawTreeTotal n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measure.measurable_lintegral
      ((by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
        (ih.comp measurable_snd))

end IsingPerceptron

namespace IsingPerceptron

def rawCascadeLaw : (n : ℕ) → (ℕ → ℝ) → ProbabilityMeasure (RawTree n)
  | 0, _ => ⟨Measure.dirac PUnit.unit, by
      change IsProbabilityMeasure (Measure.dirac (PUnit.unit : PUnit)); infer_instance⟩
  | n+1, b => ⟨poissonLaw ((powerIntensity (b 0)).prod
      (rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n))), by
        change IsProbabilityMeasure (poissonLaw ((powerIntensity (b 0)).prod
          (rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n))))
        exact poissonLaw_probability _⟩

def HasStableTotal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ≥0∞) (b : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
    (∫ ω, negExp (ENNReal.ofReal t * X ω) ∂P) = Real.exp (-C*t^b)

def CascadeExponents (n : ℕ) (b : ℕ → ℝ) : Prop :=
  (∀ i < n, 0 < b i ∧ b i < 1) ∧ ∀ i j, i < j → j < n → b i < b j

open scoped ProbabilityTheory

lemma measurable_withDensity_fixed {E : Type*} [MeasurableSpace E]
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun ν : Measure E => ν.withDensity f) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [withDensity_apply _ hs, ← lintegral_indicator hs]
  exact Measure.measurable_lintegral (hf.indicator hs)

def normalizeMass {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) : Measure E :=
  if 0 < ν univ ∧ ν univ < ∞ then (ν univ)⁻¹ • ν
  else Measure.dirac (Classical.choice (inferInstance : Nonempty E))

lemma measurable_normalizeMass {E : Type*} [MeasurableSpace E] [Nonempty E] :
    Measurable (normalizeMass : Measure E → Measure E) := by
  have hm : Measurable (fun ν : Measure E => ν univ) := Measure.measurable_coe MeasurableSet.univ
  apply Measurable.ite ((measurableSet_lt measurable_const hm).inter (measurableSet_lt hm measurable_const))
  · apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    exact hm.inv.mul (Measure.measurable_coe hs)
  · exact measurable_const

instance normalizeMass_probability {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) : IsProbabilityMeasure (normalizeMass ν) := by
  unfold normalizeMass
  split_ifs with h
  · constructor
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h.1.ne' h.2.ne
  · infer_instance

@[reducible] def RawLeaf : ℕ → Type
  | 0 => PUnit
  | n+1 => ℝ × RawLeaf n

instance rawLeafMeasurableSpace : (n : ℕ) → MeasurableSpace (RawLeaf n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => letI := rawLeafMeasurableSpace n
    inferInstanceAs (MeasurableSpace (ℝ × RawLeaf n))

instance rawLeafNonempty : (n : ℕ) → Nonempty (RawLeaf n)
  | 0 => ⟨PUnit.unit⟩
  | n+1 => letI := rawLeafNonempty n
    inferInstanceAs (Nonempty (ℝ × RawLeaf n))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_WeightedPartitionNumeratorIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Partition Numerator Increment. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron
variable (A : Type) [MeasurableSpace A]

@[reducible] def noiseTreeSpace : ℕ → RawTreeSpace
  | 0 => ⟨PUnit, by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  | n+1 => let T := noiseTreeSpace n
    letI := T.space
    ⟨Measure (ℝ × (A × T.carrier)), by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩

abbrev NoiseTree (n : ℕ) := (noiseTreeSpace A n).carrier
instance noiseTreeMeasurableSpace (n : ℕ) : MeasurableSpace (NoiseTree A n) := (noiseTreeSpace A n).space
instance noiseTreeNonempty : (n : ℕ) → Nonempty (NoiseTree A n)
  | 0 => ⟨PUnit.unit⟩
  | _+1 => ⟨0⟩

variable [Nonempty A]

def noiseCascadeLaw : (n : ℕ) → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) → ProbabilityMeasure (NoiseTree A n)
  | 0, _, _ => ⟨Measure.dirac PUnit.unit, by
      change IsProbabilityMeasure (Measure.dirac (PUnit.unit : PUnit))
      infer_instance⟩
  | n+1, b, μ => ⟨poissonLaw ((powerIntensity (b 0)).prod
      ((μ 0 : Measure A).prod (noiseCascadeLaw n (fun j => b (j+1)) (fun j => μ (j+1))))), by
        change IsProbabilityMeasure (poissonLaw _)
        infer_instance⟩

def noiseTreeForget : (n : ℕ) → NoiseTree A n → RawTree n
  | 0, _ => PUnit.unit
  | n+1, ν => ν.map (fun p => (p.1, noiseTreeForget n p.2.2))

omit [Nonempty A] in
lemma measurable_noiseTreeForget (n : ℕ) : Measurable (noiseTreeForget A n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measure.measurable_map _ (measurable_fst.prodMk (ih.comp (measurable_snd.comp measurable_snd)))

def noiseTreeTotal (n : ℕ) (ν : NoiseTree A n) : ℝ≥0∞ := rawTreeTotal n (noiseTreeForget A n ν)

omit [Nonempty A] in
lemma measurable_noiseTreeTotal (n : ℕ) : Measurable (noiseTreeTotal A n) :=
  (measurable_rawTreeTotal n).comp (measurable_noiseTreeForget A n)

end IsingPerceptron

namespace IsingPerceptron

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def noiseTreeDisplace : (n : ℕ) → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) →
    (ℕ → S × A → ℝ) → (ℕ → S × A → S) → S → NoiseTree A n → RawTree n
  | 0, _, _, _, _, _, _ => PUnit.unit
  | n+1, b, μ, c, u, s, ν =>
    (sigmaPart ((powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))) ν).map
      (fun p => (c 0 (s,p.2.1) * p.1,
        noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2))

end IsingPerceptron

namespace IsingPerceptron

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def noiseTreeFactor : (n : ℕ) → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) →
    (ℕ → S → ℝ) → (ℕ → S × A → S) → S → NoiseTree A n → ℝ≥0∞
  | 0, _, _, X, _, s, _ => ENNReal.ofReal (Real.exp (X 0 s))
  | n+1, b, μ, X, u, s, ν =>
    ∫⁻ p, ENNReal.ofReal (max p.1 0) *
      noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2
      ∂sigmaPart ((powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
        (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))) ν

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_NoiseTreeKeep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noise Tree Keep. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def noiseTreeKeep : (n : ℕ) → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) →
    (ℕ → S × A → ℝ) → (ℕ → S × A → S) → S → NoiseTree A n → NoiseTree A n
  | 0, _, _, _, _, _, _ => PUnit.unit
  | n+1, b, μ, c, u, s, ν =>
    (sigmaPart ((powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))) ν).map
      (fun p => (c 0 (s,p.2.1)*p.1, (p.2.1,
        noiseTreeKeep n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2)))

end IsingPerceptron

namespace IsingPerceptron

variable (A : Type) [MeasurableSpace A] [Nonempty A]

def GoodNoiseTree : (n : ℕ) → NoiseTree A n → Prop
  | 0, _ => True
  | n+1, ν => (0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞) ∧
      ∀ᵐ p ∂ν, GoodNoiseTree n p.2.2

def noiseChildMass (n : ℕ) (ν : NoiseTree A (n+1)) : Measure (ℝ × (A × NoiseTree A n)) :=
  ν.withDensity (fun p => ENNReal.ofReal (max p.1 0)*noiseTreeTotal A n p.2.2)

omit [Nonempty A] in
lemma measurable_noiseChildMass (n : ℕ) : Measurable (noiseChildMass A n) :=
  measurable_withDensity_fixed ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
    ENNReal.ofReal (max p.1 0))).mul ((measurable_noiseTreeTotal A n).comp (by fun_prop)))

def noiseChildKernel (n : ℕ) : Kernel (NoiseTree A (n+1)) (ℝ × (A × NoiseTree A n)) :=
  ⟨fun ν => normalizeMass (noiseChildMass A n ν),
    measurable_normalizeMass.comp (measurable_noiseChildMass A n)⟩

instance noiseChildKernel_markov (n : ℕ) : IsMarkovKernel (noiseChildKernel A n) :=
  ⟨fun _ => normalizeMass_probability _⟩

@[reducible] def NoiseLeaf : ℕ → Type
  | 0 => PUnit
  | n+1 => ℝ × (A × NoiseLeaf n)

instance noiseLeafMeasurableSpace : (n : ℕ) → MeasurableSpace (NoiseLeaf A n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => letI := noiseLeafMeasurableSpace n
    inferInstanceAs (MeasurableSpace (ℝ × (A × NoiseLeaf A n)))

instance noiseLeafNonempty : (n : ℕ) → Nonempty (NoiseLeaf A n)
  | 0 => ⟨PUnit.unit⟩
  | n+1 => letI := noiseLeafNonempty n
    inferInstanceAs (Nonempty (ℝ × (A × NoiseLeaf A n)))

def noiseLeafKernelData : (n : ℕ) → {κ : Kernel (NoiseTree A n) (NoiseLeaf A n) // IsMarkovKernel κ}
  | 0 => ⟨Kernel.const _ (Measure.dirac PUnit.unit), by
      change IsMarkovKernel (Kernel.const PUnit (Measure.dirac (PUnit.unit : PUnit)))
      infer_instance⟩
  | n+1 =>
    let κ := (noiseLeafKernelData n).val
    letI : IsMarkovKernel κ := (noiseLeafKernelData n).property
    ⟨((Kernel.id : Kernel ℝ ℝ) ∥ₖ ((Kernel.id : Kernel A A) ∥ₖ κ)) ∘ₖ noiseChildKernel A n, by
      change IsMarkovKernel (((Kernel.id : Kernel ℝ ℝ) ∥ₖ ((Kernel.id : Kernel A A) ∥ₖ κ)) ∘ₖ noiseChildKernel A n)
      infer_instance⟩

def noiseLeafKernel (n : ℕ) : Kernel (NoiseTree A n) (NoiseLeaf A n) := (noiseLeafKernelData A n).val

instance noiseLeafKernel_markov (n : ℕ) : IsMarkovKernel (noiseLeafKernel A n) :=
  (noiseLeafKernelData A n).property

end IsingPerceptron

namespace IsingPerceptron
open scoped ProbabilityTheory
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def noiseLeafTerminal : (n : ℕ) → (ℕ → S → ℝ) → (ℕ → S × A → S) →
    S → NoiseLeaf A n → ℝ
  | 0, X, _, s, _ => X 0 s
  | n+1, X, u, s, v => noiseLeafTerminal n (fun i => X (i+1))
      (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2

end IsingPerceptron

namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def noiseLeafProduct : (n : ℕ) → (ℕ → S × A → ℝ) → (ℕ → S × A → S) →
    S → NoiseLeaf A n → ℝ≥0∞
  | 0, _, _, _, _ => 1
  | n+1, c, u, s, v => ENNReal.ofReal (c 0 (s,v.2.1)) *
      noiseLeafProduct n (fun i => c (i+1)) (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2

def noiseLeafKeep : (n : ℕ) → (ℕ → S × A → ℝ) → (ℕ → S × A → S) →
    S → NoiseLeaf A n → NoiseLeaf A n
  | 0, _, _, _, _ => PUnit.unit
  | n+1, c, u, s, v => (c 0 (s,v.2.1)*v.1, (v.2.1,
      noiseLeafKeep n (fun i => c (i+1)) (fun i => u (i+1)) (u 0 (s,v.2.1)) v.2.2))

omit [Nonempty A] in
lemma measurable_noiseLeafProduct (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseLeaf A n => noiseLeafProduct n c u p.1 p.2) := by
  induction n generalizing c u with
  | zero => exact measurable_const
  | succ n ih =>
    exact ((hc 0).comp (by fun_prop)).ennreal_ofReal.mul
      ((ih (fun i => hc (i+1)) (fun i => hu (i+1))).comp
        (((hu 0).comp (by fun_prop)).prodMk (by fun_prop)))

def noiseWeightedLeafMeasure (n : ℕ) (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (s : S) (ν : NoiseTree A n) : Measure (NoiseLeaf A n) :=
  ((noiseLeafKernel A n ν).withDensity
    (fun v => noiseTreeTotal A n ν * noiseLeafProduct n c u s v)).map (noiseLeafKeep n c u s)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_NoiseGibbsRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noise Gibbs Regular. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def NoiseGibbsRegular : (n : ℕ) → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) →
    (ℕ → S × A → ℝ) → (ℕ → S × A → S) → S → NoiseTree A n → Prop
  | 0, _, _, _, _, _, _ => True
  | n+1, b, μ, c, u, s, ν =>
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))
    (0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞) ∧
    (0 < noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u s ν) ∧
      noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u s ν) < ∞) ∧
    Marked.PoissonGood I ν ∧ ∀ᵐ p ∂sigmaPart I ν,
      NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2

end IsingPerceptron

namespace IsingPerceptron

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def noiseTiltedLeafLaw (n : ℕ) (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (s : S) (ν : NoiseTree A n) : Measure (NoiseLeaf A n) :=
  normalizeMass ((noiseLeafKernel A n ν).withDensity (noiseLeafProduct n c u s))

instance noiseTiltedLeafLaw_probability (n : ℕ) (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (s : S) (ν : NoiseTree A n) : IsProbabilityMeasure (noiseTiltedLeafLaw n c u s ν) :=
  normalizeMass_probability _

end IsingPerceptron

namespace IsingPerceptron

def labeledPoissonLaw {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) : Measure (ℕ → ℕ × (ℕ → E)) :=
  Measure.infinitePi (fun n => finitePoissonCloud (μ n).mass (μ n).normalize)

instance labeledPoissonLaw_probability {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) : IsProbabilityMeasure (labeledPoissonLaw μ) := by
  unfold labeledPoissonLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def labeledMarkedMeasure {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ω : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F)) : Measure (E × F) :=
  Measure.sum (fun n => finiteCloudMeasure ((ω.1 n).1,fun i => ((ω.1 n).2 i,ω.2 n i)))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_ChildLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Child Label. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

abbrev ChildLabel := ℕ × ℕ
abbrev WeightCloud := ℕ → ℕ × (ℕ → ℝ)

@[reducible] def labeledTreeSpace : ℕ → RawTreeSpace
  | 0 => ⟨PUnit, by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  | n+1 => let T := labeledTreeSpace n
    letI := T.space
    ⟨WeightCloud × (ℕ → ℕ → T.carrier), by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩

abbrev LabeledTree (n : ℕ) := (labeledTreeSpace n).carrier
instance labeledTreeMeasurableSpace (n : ℕ) : MeasurableSpace (LabeledTree n) :=
  (labeledTreeSpace n).space
instance labeledTreeNonempty : (n : ℕ) → Nonempty (LabeledTree n)
  | 0 => ⟨PUnit.unit⟩
  | n+1 => letI := labeledTreeNonempty n
    inferInstanceAs (Nonempty (WeightCloud × (ℕ → ℕ → LabeledTree n)))

def intensityComponents {E : Type*} [MeasurableSpace E] (μ : Measure E) [SFinite μ] :
    ℕ → FiniteMeasure E := fun n => ⟨sfiniteSeq μ n,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩

def labeledCascadeLaw : (n : ℕ) → (ℕ → ℝ) → ProbabilityMeasure (LabeledTree n)
  | 0, _ => ⟨Measure.dirac PUnit.unit, by
      change IsProbabilityMeasure (Measure.dirac (PUnit.unit : PUnit)); infer_instance⟩
  | n+1, b => ⟨(labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
        (labeledCascadeLaw n (fun j => b (j+1)) : Measure (LabeledTree n))))), by
      change IsProbabilityMeasure ((labeledPoissonLaw _).prod
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
          (labeledCascadeLaw n (fun j => b (j+1)) : Measure (LabeledTree n))))))
      infer_instance⟩

@[reducible] def LabeledLeaf : ℕ → Type
  | 0 => PUnit
  | n+1 => ChildLabel × LabeledLeaf n
instance labeledLeafMeasurableSpace : (n : ℕ) → MeasurableSpace (LabeledLeaf n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => letI := labeledLeafMeasurableSpace n
    inferInstanceAs (MeasurableSpace (ChildLabel × LabeledLeaf n))
instance labeledLeafCountable : (n : ℕ) → Countable (LabeledLeaf n)
  | 0 => inferInstanceAs (Countable PUnit)
  | n+1 => letI := labeledLeafCountable n
    inferInstanceAs (Countable (ChildLabel × LabeledLeaf n))
instance labeledLeafSingleton : (n : ℕ) → MeasurableSingletonClass (LabeledLeaf n)
  | 0 => inferInstanceAs (MeasurableSingletonClass PUnit)
  | n+1 => letI := labeledLeafSingleton n
    inferInstanceAs (MeasurableSingletonClass (ChildLabel × LabeledLeaf n))
instance labeledLeafNonempty : (n : ℕ) → Nonempty (LabeledLeaf n)
  | 0 => inferInstanceAs (Nonempty PUnit)
  | n+1 => letI := labeledLeafNonempty n
    inferInstanceAs (Nonempty (ChildLabel × LabeledLeaf n))

def childLabelWeight (ω : WeightCloud) (a : ChildLabel) : ℝ≥0∞ :=
  if a.2 < (ω a.1).1 then ENNReal.ofReal (max ((ω a.1).2 a.2) 0) else 0

def labeledLeafWeight : (n : ℕ) → LabeledTree n → LabeledLeaf n → ℝ≥0∞
  | 0, _, _ => 1
  | n+1, ω, v => childLabelWeight ω.1 v.1 * labeledLeafWeight n (ω.2 v.1.1 v.1.2) v.2

lemma measurable_childLabelWeight (a : ChildLabel) : Measurable (fun ω => childLabelWeight ω a) := by
  unfold childLabelWeight
  apply Measurable.ite
  · exact measurableSet_lt measurable_const (by fun_prop)
  · fun_prop
  · fun_prop

lemma measurable_labeledLeafWeight (n : ℕ) (v : LabeledLeaf n) :
    Measurable (fun ω => labeledLeafWeight n ω v) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ((measurable_childLabelWeight v.1).comp measurable_fst).mul
      ((ih v.2).comp ((measurable_pi_apply v.1.2).comp
        ((measurable_pi_apply v.1.1).comp measurable_snd)))

def labeledLeafMass (n : ℕ) (ω : LabeledTree n) : Measure (LabeledLeaf n) :=
  Measure.count.withDensity (labeledLeafWeight n ω)

lemma measurable_labeledLeafMass (n : ℕ) : Measurable (labeledLeafMass n) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [labeledLeafMass,withDensity_apply _ hs,← lintegral_indicator hs,lintegral_count]
  exact Measurable.tsum (fun v => by
    by_cases hv : v ∈ s
    · simpa only [Set.indicator_of_mem hv] using measurable_labeledLeafWeight n v
    · simp only [Set.indicator_of_notMem hv]; exact measurable_const)

def labeledLeafLaw (n : ℕ) (ω : LabeledTree n) : Measure (LabeledLeaf n) :=
  normalizeMass (labeledLeafMass n ω)
instance labeledLeafLaw_probability (n : ℕ) (ω : LabeledTree n) :
    IsProbabilityMeasure (labeledLeafLaw n ω) := normalizeMass_probability _
lemma measurable_labeledLeafLaw (n : ℕ) : Measurable (labeledLeafLaw n) :=
  measurable_normalizeMass.comp (measurable_labeledLeafMass n)

variable (A : Type) [MeasurableSpace A]

@[reducible] def markForestSpace : ℕ → RawTreeSpace
  | 0 => ⟨PUnit,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  | n+1 => let T := markForestSpace n
    letI := T.space
    ⟨ℕ → ℕ → A × T.carrier,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩

abbrev MarkForest (n : ℕ) := (markForestSpace A n).carrier
instance markForestMeasurableSpace (n : ℕ) : MeasurableSpace (MarkForest A n) :=
  (markForestSpace A n).space
instance markForestNonempty [Nonempty A] : (n : ℕ) → Nonempty (MarkForest A n)
  | 0 => inferInstanceAs (Nonempty PUnit)
  | n+1 => letI := markForestNonempty n
    inferInstanceAs (Nonempty (ℕ → ℕ → A × MarkForest A n))

def markForestLaw : (n : ℕ) → (ℕ → ProbabilityMeasure A) → ProbabilityMeasure (MarkForest A n)
  | 0, _ => ⟨Measure.dirac PUnit.unit,by
      change IsProbabilityMeasure (Measure.dirac (PUnit.unit : PUnit)); infer_instance⟩
  | n+1, μ => ⟨Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      (μ 0 : Measure A).prod (markForestLaw n (fun j => μ (j+1)) : Measure (MarkForest A n)))),by
        change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi
          (fun _ : ℕ => (μ 0 : Measure A).prod (markForestLaw n (fun j => μ (j+1)) : Measure (MarkForest A n)))))
        infer_instance⟩

def labeledNoiseJoin : (n : ℕ) → LabeledTree n × MarkForest A n → NoiseTree A n
  | 0, _ => PUnit.unit
  | n+1, p => labeledMarkedMeasure (p.1.1,fun m i =>
      ((p.2 m i).1,labeledNoiseJoin n (p.1.2 m i,(p.2 m i).2)))

end IsingPerceptron

namespace IsingPerceptron

@[reducible] def ForestVertex : ℕ → Type
  | 0 => PEmpty
  | n+1 => ℕ × (ℕ × Option (ForestVertex n))

instance forestVertexCountable : (n : ℕ) → Countable (ForestVertex n)
  | 0 => inferInstanceAs (Countable PEmpty)
  | n+1 => letI := forestVertexCountable n
    inferInstanceAs (Countable (ℕ × (ℕ × Option (ForestVertex n))))

def forestVertexDepth : (n : ℕ) → ForestVertex n → ℕ
  | 0, v => v.elim
  | _+1, (_,_,none) => 0
  | n+1, (_,_,some v) => forestVertexDepth n v+1

variable (A : Type) [MeasurableSpace A]

def markForestOfCoords : (n : ℕ) → (ForestVertex n → A) → MarkForest A n
  | 0, _ => PUnit.unit
  | n+1, g => fun m i => (g (m,i,none),markForestOfCoords n (fun v => g (m,i,some v)))

@[fun_prop] lemma measurable_markForestOfCoords (n : ℕ) :
    Measurable (markForestOfCoords A n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply Measurable.of_eval
    intro m
    apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply (m,i,none)).prodMk (ih.comp (by fun_prop))

end IsingPerceptron

namespace IsingPerceptron

variable (A : Type) [MeasurableSpace A] [Nonempty A]

def labeledNoiseLeaf : (n : ℕ) → LabeledTree n × MarkForest A n → LabeledLeaf n → NoiseLeaf A n
  | 0, _, _ => PUnit.unit
  | n+1, p, v => ((p.1.1 v.1.1).2 v.1.2,
      ((p.2 v.1.1 v.1.2).1,labeledNoiseLeaf n (p.1.2 v.1.1 v.1.2,(p.2 v.1.1 v.1.2).2) v.2))

omit [Nonempty A] in
@[fun_prop] lemma measurable_labeledNoiseLeaf (n : ℕ) (v : LabeledLeaf n) :
    Measurable (fun p => labeledNoiseLeaf A n p v) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun p : (WeightCloud × (ℕ → ℕ → LabeledTree n)) ×
        (ℕ → ℕ → A × MarkForest A n) =>
      ((p.1.1 v.1.1).2 v.1.2,
        ((p.2 v.1.1 v.1.2).1,labeledNoiseLeaf A n (p.1.2 v.1.1 v.1.2,(p.2 v.1.1 v.1.2).2) v.2)))
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    exact (ih v.2).comp (by fun_prop)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_GaussianIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Integration. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

section FiniteGibbs
variable {S : Type*} [Fintype S]

def finitePartition (w H : S → ℝ) : ℝ := ∑ x, w x * Real.exp (H x)
def finiteGibbs (w H : S → ℝ) (x : S) : ℝ :=
  w x * Real.exp (H x) / finitePartition w H

def GibbsReference (w : S → ℝ) : Prop := (∀ x, 0 ≤ w x) ∧ ∃ x, 0 < w x

end FiniteGibbs

section GaussianGibbs
variable {S : Type*} [Fintype S]

def linearGaussian {n : ℕ} (C : S → Fin n → ℝ) (g : Fin n → ℝ) (x : S) : ℝ :=
  ∑ j, C x j * g j

def gaussianGibbs {n : ℕ} (w B : S → ℝ) (C : S → Fin n → ℝ)
    (g : Fin n → ℝ) (x : S) : ℝ :=
  finiteGibbs w (fun y => B y + linearGaussian C g y) x

end GaussianGibbs

section Replicas
variable {S : Type*} [Fintype S]

def replicaGibbs {n r : ℕ} (w B : S → ℝ) (C : S → Fin n → ℝ)
    (g : Fin n → ℝ) (σ : Fin r → S) : ℝ :=
  ∏ l, gaussianGibbs w B C g (σ l)

omit [Fintype S] in
def gaussianCross {n : ℕ} (A C : S → Fin n → ℝ) (x y : S) : ℝ :=
  ∑ i, A x i * C y i

end Replicas

abbrev Spin (N : ℕ) := Fin N → Fin 2

def spinValue (x : Fin 2) : ℝ := if x = 0 then -1 else 1

def spinOverlap {N : ℕ} (x y : Spin N) : ℝ :=
  (∑ i, spinValue (x i)*spinValue (y i))/(N : ℝ)

variable {S : Type*} [Fintype S]

def replicaMean {n r : ℕ} (w B : S → ℝ) (C : S → Fin n → ℝ)
    (D : (Fin r → S) → ℝ) (g : Fin n → ℝ) : ℝ :=
  ∑ σ, replicaGibbs w B C g σ*D σ

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_CountableMonomialGG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable Monomial G G. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

section
variable {S : Type*} [Fintype S]

def freshCovarianceMean {n r : ℕ} (w B : S → ℝ) (C : S → Fin n → ℝ)
    (κ : S → S → ℝ) (D : (Fin (r+1) → S) → ℝ) (g : Fin n → ℝ) : ℝ :=
  ∑ σ, replicaGibbs w B C g σ*D σ*(∑ z, gaussianGibbs w B C g z*κ (σ 0) z)

end

def referencePartition {X : Type*} [MeasurableSpace X] (ν : Measure X) (H : X → ℝ) : ℝ :=
  ∫ x, Real.exp (H x) ∂ν

def referenceReplicaMean {X : Type*} [MeasurableSpace X] {r : ℕ}
    (ν : Measure X) (H : X → ℝ) (D : (Fin r → X) → ℝ) : ℝ :=
  (∫ σ, Real.exp (∑ i, H (σ i))*D σ ∂Measure.pi (fun _ : Fin r => ν)) /
    (referencePartition ν H)^r

def gaussianCoordinates : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance gaussianCoordinates_probability : IsProbabilityMeasure gaussianCoordinates :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)))

def cylinderField (a : ℕ →₀ ℝ) (g : ℕ → ℝ) : ℝ :=
  a.sum (fun i c => c*g i)

lemma measurable_cylinderField (a : ℕ →₀ ℝ) : Measurable (cylinderField a) := by
  classical
  change Measurable (fun g : ℕ → ℝ => ∑ i ∈ a.support, a i*g i)
  fun_prop

lemma measurable_cylinderFields {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (a : X → ℕ →₀ ℝ) :
    Measurable (fun z : (ℕ → ℝ) × X => cylinderField (a z.2) z.1) :=
  measurable_from_prod_countable_left (fun x => measurable_cylinderField (a x))

def cylinderCross (a b : ℕ →₀ ℝ) : ℝ := a.sum (fun i c => c*b i)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_PartitionPowLe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition Pow Le. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron



def normalizedRestriction {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (A : Set X) : Measure X := (ν A)⁻¹ • ν.restrict A

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_NormalizedRestrictionPi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Restriction Pi. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

def subtypeReference {X : Type*} [MeasurableSpace X] (ν : Measure X) (A : Set X) : Measure A :=
  (ν A)⁻¹ • ν.comap Subtype.val

lemma measurable_random_referencePartition {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H) :
    Measurable (fun ω => referencePartition (ν ω) (fun x => H (ω,x))) := by
  let κ : Kernel Ω X := ⟨ν,hν⟩
  have : IsMarkovKernel κ := ⟨fun ω => by
    change IsProbabilityMeasure (ν ω)
    infer_instance⟩
  exact (hH.exp.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

lemma integrable_of_measurable_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {F : Ω → ℝ} (hF : Measurable F)
    {c : ℝ} (hbound : ∀ ω, |F ω| ≤ c) : Integrable F μ := by
  exact (integrable_const c).mono' hF.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hbound ω)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_ConvexDerivativeFluctuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex Derivative Fluctuation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma tilted_singleton {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) (x : X) :
    (ν.tilted H) {x} = ENNReal.ofReal (Real.exp (H x)/referencePartition ν H)*ν {x} := by
  rw [tilted_apply,lintegral_singleton]; rfl

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_ReplicaEnergyCovarianceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica Energy Covariance Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

def randomReplicaAverage (P : Measure Ω) (ν : Ω → Measure X) (A : X → ℕ →₀ ℝ)
    (t : ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) : ℝ :=
  ∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
    (fun x => t*cylinderField (A x) z.2) D ∂P.prod gaussianCoordinates

def randomReplicaEnergy (P : Measure Ω) (ν : Ω → Measure X) (A : X → ℕ →₀ ℝ)
    (t : ℝ) {r : ℕ} (D : (Fin (r+1) → X) → ℝ) : ℝ :=
  ∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1)
    (fun x => t*cylinderField (A x) z.2) (fun σ => cylinderField (A (σ 0)) z.2*D σ)
    ∂P.prod gaussianCoordinates

end IsingPerceptron

namespace IsingPerceptron

def featureCoefficients {I : Type*} [Fintype I] (tag : I → ℕ) (c : I → ℝ) : ℕ →₀ ℝ :=
  ∑ i, Finsupp.single (tag i) (c i)

def labeledAddress : (n : ℕ) → LabeledLeaf n → List ChildLabel
  | 0, _ => []
  | n+1, v => v.1 :: labeledAddress n v.2

def labeledCommonDepth : (n : ℕ) → LabeledLeaf n → LabeledLeaf n → ℕ
  | 0, _, _ => 0
  | n+1, v, w => if v.1 = w.1 then labeledCommonDepth n v.2 w.2+1 else 0

instance labeledLeafEncodable (n : ℕ) : Encodable (LabeledLeaf n) := Encodable.ofCountable _

def treeFeatureTag {J : Type*} [Encodable J] (n : ℕ) (v : LabeledLeaf n)
    (i : Fin (n+1) × J) : ℕ :=
  Encodable.encode (i.1.1, (labeledAddress n v).take i.1, i.2)

def treeFieldCoefficients {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v : LabeledLeaf n) (a : Fin (n+1) → ℝ) (c : J → ℝ) : ℕ →₀ ℝ :=
  featureCoefficients (treeFeatureTag n v) (fun i => a i.1*c i.2)

def pathIncrement (q : ℕ → ℝ) : ℕ → ℝ
  | 0 => q 0
  | i+1 => q (i+1)-q i

def pathAmplitude (q : ℕ → ℝ) (i : ℕ) : ℝ := Real.sqrt (pathIncrement q i)

def tensorFeature {J : Type*} [Fintype J] (p : ℕ) (x : J → ℝ) (i : Fin p → J) : ℝ :=
  ∏ d, x (i d)

def spinCoordinate {N : ℕ} (x : Spin N) (i : Fin N) : ℝ :=
  spinValue (x i) / Real.sqrt (N : ℝ)

def treeOverlap (n : ℕ) (v w : LabeledLeaf n) : ℝ :=
  (labeledCommonDepth n v w : ℝ) / (n+1 : ℕ)

def monomialPath (n d : ℕ) (i : ℕ) : ℝ := ((i : ℝ) / (n+1 : ℕ)) ^ d

def monomialCoefficients {N : ℕ} (n p d : ℕ) (s : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  treeFieldCoefficients n s.2 (fun i => pathAmplitude (monomialPath n d) i)
    (tensorFeature p (spinCoordinate s.1))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_MonomialGgAtMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monomial Gg At Minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {A : Type*} [MeasurableSpace A]

def logMean (b : ℝ) (μ : Measure A) (F : A → ℝ) : ℝ :=
  Real.log (∫ a, Real.exp (b*F a) ∂μ) / b

end IsingPerceptron

namespace IsingPerceptron
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]

def cascadeRecursion : ℕ → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) →
    (ℕ → S × A → S) → (S → ℝ) → S → ℝ
  | 0, _, _, _, F => F
  | n+1, b, μ, u, F => fun s => logMean (b 0) (μ 0 : Measure A)
      (fun a => cascadeRecursion n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => u (j+1)) F (u 0 (s,a)))

def stoppedUpdate (n : ℕ) (u : ℕ → S × A → S) (i : ℕ) (p : S × A) : S :=
  if i < n then u i p else p.1

def backwardValue (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (u : ℕ → S × A → S) (F : S → ℝ) (i : ℕ) : S → ℝ :=
  cascadeRecursion (n-i) (fun j => b (i+j)) (fun j => μ (i+j))
    (fun j => u (i+j)) F

end IsingPerceptron

namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def terminalTreeFactor : (n : ℕ) → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) →
    (ℕ → S × A → S) → (S → ℝ) → S → NoiseTree A n → ℝ≥0∞
  | 0, _, _, _, F, s, _ => ENNReal.ofReal (Real.exp (F s))
  | n+1, b, μ, u, F, s, ν => ∫⁻ p, ENNReal.ofReal (max p.1 0) *
      terminalTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => u (j+1)) F (u 0 (s,p.2.1)) p.2.2
        ∂sigmaPart ((powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
          (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))) ν

end IsingPerceptron

namespace IsingPerceptron
variable {S : Type*} [SeminormedAddCommGroup S] [MeasurableSpace S] [MeasurableAdd₂ S]

def ExponentialNormMoments (μ : Measure S) : Prop :=
  ∀ a : ℝ, Integrable (fun s => Real.exp (a*‖s‖)) μ

def HasLinearGrowth (F : S → ℝ) : Prop :=
  ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ ∀ s, |F s| ≤ C+L*‖s‖

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_EnrichedFieldCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched Field Cap. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

def finiteLogIntegral (ν : Measure I) (H : I → ℝ) : ℝ := Real.log (∫ x, Real.exp (H x) ∂ν)

def energyRecursion (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) (H : I → ℝ) : ℝ :=
  cascadeRecursion n b μ (fun _ p => p.1+p.2) (finiteLogIntegral ν) H

end IsingPerceptron

namespace IsingPerceptron

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

def cascadeEnergyLog (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) (H : I → ℝ) (T : NoiseTree (I → ℝ) n) : ℝ :=
  Real.log ((terminalTreeFactor n b μ (fun _ p => p.1+p.2) (finiteLogIntegral ν) H T).toReal /
    (noiseTreeTotal (I → ℝ) n T).toReal)

end IsingPerceptron

namespace IsingPerceptron

def tagCoefficients (j : ℕ) (a : ℕ →₀ ℝ) : ℕ →₀ ℝ := Finsupp.mapDomain (Nat.pair j) a

def monomialIndex (j : ℕ) : ℕ × ℕ := Nat.unpair (j+1)

def perturbationScale (N : ℕ) : ℝ := (N : ℝ)^(-1/16 : ℝ)
def perturbationWeight (j : ℕ) : ℝ := (1/2 : ℝ)^(j+1)

def externalFieldCoefficients {N : ℕ} (n : ℕ) (h : ℕ → ℝ)
    (s : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  treeFieldCoefficients n s.2 (fun i => pathAmplitude h i) (fun i => spinValue (s.1 i))

def enrichedCoefficients {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (s : Spin N × LabeledLeaf n) : ℕ →₀ ℝ :=
  ∑ i : Fin (N+1), tagCoefficients i
    (Fin.cases (externalFieldCoefficients n h s)
      (fun j => (Real.sqrt N*perturbationScale N*perturbationWeight j*u j) •
        monomialCoefficients n (monomialIndex j).1 (monomialIndex j).2 s) i)

abbrev EnrichedBlock (N : ℕ) := Fin N ⊕ (Σ j : Fin N, Fin (monomialIndex j).1 → Fin N)

def enrichedLevelCoefficient {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (i : ℕ) (x : Spin N) : EnrichedBlock N → ℝ
  | .inl a => pathAmplitude h i * spinValue (x a)
  | .inr ⟨j,t⟩ => (Real.sqrt N*perturbationScale N*perturbationWeight j*u j) *
      pathAmplitude (monomialPath n (monomialIndex j).2) i *
      tensorFeature (monomialIndex j).1 (spinCoordinate x) t

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_MemLpOfAbsBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mem Lp Of Abs Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

def rootEnergy (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) (g : Fin m → ℝ) : ℝ :=
  energyRecursion n b μ ν (fun x => H x+∑ j, a x j*g j)

variable {A : Type*} [MeasurableSpace A]

def patternBase {M : ℕ} (φ : A → I → ℝ) (y : Fin M → A) (x : I) : ℝ := ∑ r, φ (y r) x

end IsingPerceptron

namespace IsingPerceptron

def enrichedCoefficientsFin (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ)
    (x : Spin N) (j : Fin (Fintype.card (EnrichedBlock N))) : ℝ :=
  enrichedLevelCoefficient n h u i x ((Fintype.equivFin (EnrichedBlock N)).symm j)

def enrichedIncrement (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ)
    (g : Fin (Fintype.card (EnrichedBlock N)) → ℝ) (x : Spin N) : ℝ :=
  ∑ j, enrichedCoefficientsFin N n h u i x j*g j

lemma measurable_enrichedIncrement (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ) :
    Measurable (enrichedIncrement N n h u i) := by
  unfold enrichedIncrement
  fun_prop

def enrichedIncrementLaw (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ) :
    ProbabilityMeasure (Spin N → ℝ) :=
  ⟨(Measure.pi (fun _ : Fin (Fintype.card (EnrichedBlock N)) => gaussianReal 0 1)).map
    (enrichedIncrement N n h u i), Measure.isProbabilityMeasure_map (measurable_enrichedIncrement N n h u i).aemeasurable⟩

end IsingPerceptron

namespace IsingPerceptron

abbrev EnrichedRootSize (N : ℕ) := Fintype.card (EnrichedBlock N)
abbrev EnrichedRootData (N M : ℕ) (A : Type*) := (Fin (EnrichedRootSize N) → ℝ) × (Fin M → A)

def enrichedBaseEnergy {N M : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (φ : A → Spin N → ℝ) (p : EnrichedRootData N M A) (x : Spin N) : ℝ :=
  patternBase φ p.2 x + enrichedIncrement N n h u 0 p.1 x

def poissonMass (r : ℝ≥0) (n : ℕ) : ℝ := Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_VarianceOfConditionalCenterBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Of Conditional Center Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

abbrev InfiniteRootData (m : ℕ) (A : Type*) := (Fin m → ℝ) × (ℕ → A)

def rootPrefix {m : ℕ} {A : Type*} (M : ℕ) (p : InfiniteRootData m A) :
    (Fin m → ℝ) × (Fin M → A) := (p.1,fun i => p.2 i)

variable {I A : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable [MeasurableSpace A]

def infinitePatternRoot (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) {m : ℕ} (a : I → Fin m → ℝ) (φ : A → I → ℝ)
    (p : ℕ × InfiniteRootData m A) : ℝ :=
  rootEnergy n b μ ν (patternBase φ (fun i : Fin p.1 => p.2.2 i)) a p.2.1

end IsingPerceptron

namespace IsingPerceptron

abbrev EnrichedPoissonRoot (N : ℕ) (A : Type*) := ℕ × InfiniteRootData (EnrichedRootSize N) A

def enrichedPoissonBase {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (φ : A → Spin N → ℝ) (p : EnrichedPoissonRoot N A) : Spin N → ℝ :=
  enrichedBaseEnergy n h u φ (rootPrefix p.1 p.2)

def enrichedPoissonLog {N : ℕ} {A : Type*} (n : ℕ) (b h : ℕ → ℝ) (u : Fin N → ℝ)
    (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (p : EnrichedPoissonRoot N A × NoiseTree (Spin N → ℝ) n) : ℝ :=
  cascadeEnergyLog n b (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (enrichedPoissonBase n h u φ p.1) p.2 - N*h n/2

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def labeledEnergy : (n : ℕ) → MarkForest (I → ℝ) n → LabeledLeaf n → (I → ℝ) → (I → ℝ)
  | 0, _, _, H => H
  | n+1, z, γ, H => labeledEnergy n (z γ.1.1 γ.1.2).2 γ.2 (H + (z γ.1.1 γ.1.2).1)

def labeledSpinReference (n : ℕ) (ν : Measure I) (ω : LabeledTree n) :
    Measure (I × LabeledLeaf n) := ν.prod (labeledLeafLaw n ω)

instance labeledSpinReference_probability (n : ℕ) (ν : Measure I) [IsProbabilityMeasure ν]
    (ω : LabeledTree n) : IsProbabilityMeasure (labeledSpinReference n ν ω) := by
  unfold labeledSpinReference
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def labeledEnergyLog (n : ℕ) (ν : Measure I) (H : I → ℝ)
    (p : LabeledTree n × MarkForest (I → ℝ) n) : ℝ :=
  Real.log (∫ s, Real.exp (labeledEnergy n p.2 s.2 H s.1)
    ∂labeledSpinReference n ν p.1)

end IsingPerceptron

namespace IsingPerceptron

def enrichedForestCoordinates (N n : ℕ) : Measure (ForestVertex n → Fin (EnrichedRootSize N) → ℝ) :=
  Measure.infinitePi (fun _ : ForestVertex n =>
    Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))

instance enrichedForestCoordinates_probability (N n : ℕ) :
    IsProbabilityMeasure (enrichedForestCoordinates N n) := by
  unfold enrichedForestCoordinates
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def enrichedForest (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (g : ForestVertex n → Fin (EnrichedRootSize N) → ℝ) : MarkForest (Spin N → ℝ) n :=
  markForestOfCoords (Spin N → ℝ) n
    (fun v => enrichedIncrement N n h u (forestVertexDepth n v+1) (g v))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_EnergyShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy Shift. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

abbrev EnrichedLabeledData (N n : ℕ) (A : Type*) :=
  EnrichedPoissonRoot N A × (LabeledTree n × (ForestVertex n → Fin (EnrichedRootSize N) → ℝ))

 
def enrichedCoordinateLaw {A : Type*} [MeasurableSpace A] (P : Measure A)
    (r : ℝ≥0) (N n : ℕ) (b : ℕ → ℝ) : Measure (EnrichedLabeledData N n A) :=
  ((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
    (Measure.infinitePi (fun _ : ℕ => P)))).prod
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (enrichedForestCoordinates N n))

instance enrichedCoordinateLaw_probability {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (N n : ℕ) (b : ℕ → ℝ) :
    IsProbabilityMeasure (enrichedCoordinateLaw P r N n b) := by
  unfold enrichedCoordinateLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

 

def enrichedCoordinatePressure {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (p : EnrichedLabeledData N n A) : ℝ :=
  (labeledEnergyLog n ν (enrichedPoissonBase n h u φ p.1)
    (p.2.1,enrichedForest N n h u p.2.2) - N*h n/2) / N

 

def enrichedToNoise {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (p : EnrichedLabeledData N n A) : EnrichedPoissonRoot N A × NoiseTree (Spin N → ℝ) n :=
  (p.1,labeledNoiseJoin (Spin N → ℝ) n (p.2.1,enrichedForest N n h u p.2.2))

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 
def nodeAddress : (n : ℕ) → Option (ForestVertex n) → List ChildLabel
  | _, none => []
  | 0, some v => v.elim
  | n+1, some (m,i,v) => (m,i) :: nodeAddress n v


def nodeAt : (n : ℕ) → LabeledLeaf n → Fin (n+1) → Option (ForestVertex n)
  | 0, _, _ => none
  | n+1, γ, i => Fin.cases none (fun j => some (γ.1.1,γ.1.2,nodeAt n γ.2 j)) i


def enrichedNodeTag {N n : ℕ} (v : Option (ForestVertex n)) : EnrichedBlock N → ℕ
  | .inl a => Nat.pair 0 (Encodable.encode ((nodeAddress n v).length,nodeAddress n v,a))
  | .inr ⟨j,t⟩ => Nat.pair (j+1) (Encodable.encode ((nodeAddress n v).length,nodeAddress n v,t))



def enrichedGaussianNodes (N n : ℕ) (g : ℕ → ℝ)
    (v : Option (ForestVertex n)) (j : Fin (EnrichedRootSize N)) : ℝ :=
  g (enrichedNodeTag v ((Fintype.equivFin (EnrichedBlock N)).symm j))

def edgeAt : (n : ℕ) → LabeledLeaf n → Fin n → ForestVertex n
  | 0, _, i => i.elim0
  | n+1, γ, i => (γ.1.1,γ.1.2,nodeAt n γ.2 i)

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

abbrev EnrichedCylinderBase (n : ℕ) (A : Type*) := (ℕ × (ℕ → A)) × LabeledTree n
abbrev EnrichedCylinderData (n : ℕ) (A : Type*) := EnrichedCylinderBase n A × (ℕ → ℝ)

def enrichedCylinderBaseLaw {A : Type*} [MeasurableSpace A] (P : Measure A)
    (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ) : Measure (EnrichedCylinderBase n A) :=
  ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ => P))).prod (labeledCascadeLaw n b)

def enrichedCylinderLaw {A : Type*} [MeasurableSpace A] (P : Measure A)
    (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ) : Measure (EnrichedCylinderData n A) :=
  (enrichedCylinderBaseLaw P r n b).prod gaussianCoordinates

instance enrichedCylinderBaseLaw_probability {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ) :
    IsProbabilityMeasure (enrichedCylinderBaseLaw P r n b) := by
  unfold enrichedCylinderBaseLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

instance enrichedCylinderLaw_probability {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ) :
    IsProbabilityMeasure (enrichedCylinderLaw P r n b) := by
  unfold enrichedCylinderLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def enrichedCylinderToCoordinates (N n : ℕ) {A : Type*}
    (p : EnrichedCylinderData n A) : EnrichedLabeledData N n A :=
  ((p.1.1.1,(enrichedGaussianNodes N n p.2 none,p.1.1.2)),
    (p.1.2,fun v => enrichedGaussianNodes N n p.2 (some v)))



def enrichedCylinderPressure {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (p : EnrichedCylinderData n A) : ℝ :=
  (Real.log (∫ s, Real.exp (patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i) s.1 +
      cylinderField (enrichedCoefficients n h u s) p.2) ∂labeledSpinReference n ν p.1.2) - N*h n/2)/N

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_NamespaceSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Namespace Split. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

abbrev OtherNamespaces (j : ℕ) := {k : ℕ // k ≠ j} → ℕ → ℝ

def otherNamespacesLaw (j : ℕ) : Measure (OtherNamespaces j) :=
  Measure.infinitePi (fun _ : {k : ℕ // k ≠ j} => gaussianCoordinates)

instance otherNamespacesLaw_probability (j : ℕ) : IsProbabilityMeasure (otherNamespacesLaw j) := by
  unfold otherNamespacesLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def gaussianNamespaceSplit (j : ℕ) (g : ℕ → ℝ) : (ℕ → ℝ) × OtherNamespaces j :=
  ((fun i => g (Nat.pair j i)),fun k i => g (Nat.pair k i))

end IsingPerceptron

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace IsingPerceptron

def gibbsProbability {X : Type*} [MeasurableSpace X] (ν : Measure X) (H : X → ℝ) : Measure X :=
  if referencePartition ν H = 0 then ν else ν.tilted H

instance gibbsProbability_probability {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) :
    IsProbabilityMeasure (gibbsProbability ν H) := by
  unfold gibbsProbability
  split_ifs with h
  · infer_instance
  · apply isProbabilityMeasure_tilted
    by_contra he
    exact h (integral_undef he)

lemma measurable_random_tilted_measure {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H) :
    Measurable (fun ω => (ν ω).tilted (fun x => H (ω,x))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he (ω : Ω) : (ν ω).tilted (fun x => H (ω,x)) s =
      ∑' x, s.indicator (fun x => (ν ω).tilted (fun x => H (ω,x)) {x}) x :=
    (Measure.tsum_indicator_apply_singleton _ s hs).symm
  simp_rw [he]
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx,tilted_singleton]
    exact (((hH.comp (measurable_id.prodMk measurable_const)).exp.div
      (measurable_random_referencePartition hν hH)).ennreal_ofReal).mul
      ((Measure.measurable_coe (measurableSet_singleton x)).comp hν)
  · simp only [Set.indicator_of_notMem hx]
    exact measurable_const

lemma measurable_gibbsProbability {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H) :
    Measurable (fun ω => gibbsProbability (ν ω) (fun x => H (ω,x))) := by
  exact Measurable.ite (measurableSet_eq_fun (measurable_random_referencePartition hν hH) measurable_const)
    hν (measurable_random_tilted_measure hν hH)

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_EnrichedCGF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched C G F. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def enrichedMeanPressure {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ) : ℝ :=
  ∫ p, enrichedCylinderPressure n h u ν φ p ∂enrichedCylinderLaw P r n b

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def gaussianPair (g : ℕ → ℝ) : (ℕ → ℝ) × (ℕ → ℝ) :=
  ((fun i => g (Nat.pair 0 i)),fun i => g (Nat.pair 1 i))

def gaussianSumCoefficients {X : Type*} (a b : X → ℕ →₀ ℝ) (t : ℝ) (x : X) : ℕ →₀ ℝ :=
  ∑ i : Fin 2, tagCoefficients i (Fin.cases (a x) (fun _ => t • b x) i)

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_VarianceDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Derivative. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

def edgeGaussianTag (n : ℕ) (v : ForestVertex n) : ℕ :=
  Encodable.encode (nodeAddress n (some v))

def edgeGaussianCoordinates (n : ℕ) (g : ℕ → ℝ) : ForestVertex n → ℝ :=
  fun v => g (edgeGaussianTag n v)

def labelLevelCoefficients (n : ℕ) (d : Fin n) (s : I × LabeledLeaf n) : ℕ →₀ ℝ :=
  Finsupp.single (edgeGaussianTag n (edgeAt n s.2 d)) 1

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def enrichedHamiltonian {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (φ : A → Spin N → ℝ) (p : EnrichedCylinderData n A)
    (s : Spin N × LabeledLeaf n) : ℝ :=
  patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i) s.1 +
    cylinderField (enrichedCoefficients n h u s) p.2

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def enrichedFieldFunctional {N : ℕ} {A : Type*} (n : ℕ) (d : ℝ)
    (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (p : EnrichedCylinderBase n A × ((Spin N × LabeledLeaf n) → ℝ)) : ℝ :=
  (Real.log (∫ s, Real.exp (patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i) s.1+p.2 s)
    ∂labeledSpinReference n ν p.1.2)-N*d/2)/N

def enrichedGibbsReference {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ)
    (p : EnrichedCylinderData n A) : Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability (labeledSpinReference n ν p.1.2) (enrichedHamiltonian n h u φ p)

instance enrichedGibbsReference_probability {N : ℕ} {A : Type*} (n : ℕ) (h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν] (φ : A → Spin N → ℝ)
    (p : EnrichedCylinderData n A) : IsProbabilityMeasure (enrichedGibbsReference n h u ν φ p) := by
  unfold enrichedGibbsReference
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def enrichedFieldInsertedPressure {N : ℕ} {A : Type*} (n : ℕ) (h l : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) (φ : A → Spin N → ℝ) (a : ℝ)
    (p : EnrichedCylinderData n A × (ℕ → ℝ)) : ℝ :=
  enrichedFieldFunctional n (h n+a*l n) ν φ (p.1.1,fun s =>
    cylinderField (enrichedCoefficients n h u s) p.1.2 +
      Real.sqrt a*cylinderField (externalFieldCoefficients n l s) p.2)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_TiltedLabelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tilted Label Law. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma measurable_countable_pi {Ω I X : Type*} [MeasurableSpace Ω]
    [Fintype I] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] :
    Measurable (fun ω => Measure.pi (fun _ : I => ν ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he (ω : Ω) : (Measure.pi (fun _ : I => ν ω)) s =
      ∑' x, s.indicator (fun x => (Measure.pi (fun _ : I => ν ω)) {x}) x :=
    (Measure.tsum_indicator_apply_singleton _ s hs).symm
  simp_rw [he]
  apply Measurable.tsum
  intro x
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx,Measure.pi_singleton]
    exact Finset.measurable_prod _ (fun i _ =>
      (Measure.measurable_coe (measurableSet_singleton (x i))).comp hν)
  · simp only [Set.indicator_of_notMem hx]
    exact measurable_const

lemma measurable_countable_infinitePi {Ω I X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] :
    Measurable (fun ω => Measure.infinitePi (fun _ : I => ν ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => Measurable (fun ω => (Measure.infinitePi (fun _ : I => ν ω)) s))
    (s := measurableCylinders (fun _ : I => X))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_ ?_ ?_ s hs
  · simpa only [measure_empty] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ≥0∞)))
  · intro s hs
    obtain ⟨J,S,hS,rfl⟩ := (mem_measurableCylinders s).mp hs
    have he (ω : Ω) : (Measure.infinitePi (fun _ : I => ν ω)) (cylinder J S) =
        (Measure.pi (fun _ : J => ν ω)) S := by
      exact Measure.infinitePi_cylinder _ hS
    simp_rw [he]
    exact (Measure.measurable_coe hS).comp (measurable_countable_pi hν)
  · intro s hs ih
    have he (ω : Ω) : (Measure.infinitePi (fun _ : I => ν ω)) sᶜ =
        1-(Measure.infinitePi (fun _ : I => ν ω)) s := by rw [measure_compl hs (measure_ne_top _ _),measure_univ]
    simp_rw [he]
    exact measurable_const.sub ih
  · intro s hd hs ih
    have he (ω : Ω) : (Measure.infinitePi (fun _ : I => ν ω)) (⋃ n,s n) =
        ∑' n, (Measure.infinitePi (fun _ : I => ν ω)) (s n) := measure_iUnion hd hs
    simp_rw [he]
    exact Measurable.tsum ih

def replicaKernel {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Ω → Measure X)
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] : Kernel Ω (ℕ → X) :=
  ⟨fun ω => Measure.infinitePi (fun _ : ℕ => ν ω),measurable_countable_infinitePi hν⟩

instance replicaKernel_markov {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Ω → Measure X)
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] :
    IsMarkovKernel (replicaKernel ν hν) := by
  constructor
  intro ω
  change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => ν ω))
  infer_instance

def replicaLaw {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) (ν : Ω → Measure X)
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] : Measure (ℕ → X) :=
  (replicaKernel ν hν) ∘ₘ P

instance replicaLaw_probability {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] :
    IsProbabilityMeasure (replicaLaw P ν hν) := inferInstanceAs (IsProbabilityMeasure (_ ∘ₘ P))

abbrev JointEntry := Set.Icc (-1 : ℝ) 1 × Set.Icc (0 : ℝ) 1
abbrev JointArray := ℕ × ℕ → JointEntry

abbrev JointBlock (n : ℕ) := Fin n → Fin n → JointEntry

def entryCoordinate (b : Bool) (x : JointEntry) : ℝ := if b then x.2.1 else x.1.1

def blockPairCoordinate (n : ℕ) (i : ((Fin n × Fin n) × Bool) ⊕ Bool)
    (x : JointBlock n × JointEntry) : ℝ :=
  match i with
  | .inl ijb => entryCoordinate ijb.2 (x.1 ijb.1.1 ijb.1.2)
  | .inr b => entryCoordinate b x.2

def jointBlockView (n : ℕ) (x : JointArray) : JointBlock n := fun i j => x (i,j)

def jointBlockLink (n i j : ℕ) (x : JointArray) : JointBlock n × JointEntry :=
  (jointBlockView n x,x (i,j))

def HasEntryGhirlandaGuerra {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (B : Ω → ℕ → ℕ → E) (μ : Measure Ω) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (i : Fin n)
    (A : Set (Fin n → Fin n → E)), MeasurableSet A →
    ∀ (t : Set E), MeasurableSet t →
    μ.real ({ω | (fun j k : Fin n => B ω j k) ∈ A} ∩ {ω | B ω i n ∈ t}) =
      (μ.real {ω | (fun j k : Fin n => B ω j k) ∈ A} * μ.real {ω | B ω 0 1 ∈ t}) / n +
      (∑ j ∈ Finset.univ.erase i,
        μ.real ({ω | (fun j k : Fin n => B ω j k) ∈ A} ∩ {ω | B ω i j ∈ t})) / n

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_ArraySynchronization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Synchronization. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix

namespace IsingPerceptron

 
def arrayBlock {Ω : Type*} (B : Ω → ℕ → ℕ → ℝ) (n : ℕ) (ω : Ω) :
    Fin n → Fin n → ℝ := fun i j => B ω i j

 

def HasGhirlandaGuerra {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → ℕ → ℕ → ℝ) (μ : Measure Ω) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (i : Fin n)
    (A : Set (Fin n → Fin n → ℝ)), MeasurableSet A →
    ∀ (t : Set ℝ), MeasurableSet t →
    μ.real ((arrayBlock B n ⁻¹' A) ∩ {ω | B ω i n ∈ t}) =
      (μ.real (arrayBlock B n ⁻¹' A) * μ.real {ω | B ω 0 1 ∈ t}) / n +
      (∑ j ∈ Finset.univ.erase i,
        μ.real ((arrayBlock B n ⁻¹' A) ∩ {ω | B ω i j ∈ t})) / n


abbrev RealArray := ℕ → ℕ → ℝ


def blockLaw {Ω : Type*} [MeasurableSpace Ω] (B : Ω → RealArray)
    (μ : Measure Ω) (n : ℕ) : Measure (Fin n → Fin n → ℝ) :=
  Measure.map (arrayBlock B n) μ


def IsUltrametricArray (b : RealArray) : Prop :=
  ∀ i j k, min (b i k) (b j k) ≤ b i j

def augmentArrayBlock (D : ℝ) (n : ℕ)
    (p : (Fin n → Fin n → ℝ) × (Fin n → ℝ)) : Fin (n+1) → Fin (n+1) → ℝ :=
  fun i j => if hi : i.val < n then
    if hj : j.val < n then p.1 ⟨i.val, hi⟩ ⟨j.val, hj⟩ else p.2 ⟨i.val, hi⟩
    else if hj : j.val < n then p.2 ⟨j.val, hj⟩ else D

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_JointGGClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint G G Closure. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

 
def jointMonomialResidual (μ : Measure JointArray) (n : ℕ) (i : Fin n)
    (D : JointBlock n → ℝ) (p d : ℕ) : ℝ :=
  (n : ℝ)*(∫ x, D (jointBlockView n x)*(x (i,n)).1.1^p*(x (i,n)).2.1^d ∂μ) -
    (∫ x, D (jointBlockView n x) ∂μ)*(∫ x, (x (0,1)).1.1^p*(x (0,1)).2.1^d ∂μ) -
    ∑ j ∈ Finset.univ.erase i,
      ∫ x, D (jointBlockView n x)*(x (i,j)).1.1^p*(x (i,j)).2.1^d ∂μ

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_EnrichedGGFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched G G Finite. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

def newReplicaEmbedding (k : ℕ) (e : Equiv.Perm (Fin k)) : Fin (k+1) → ℕ :=
  Fin.cases k (fun j => (e j).val)

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_ArrayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Geometry. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix
namespace IsingPerceptron

def GramDiagonal (D : ℝ) (B : RealArray) : Prop :=
  (∀ n, Matrix.PosSemidef (fun i j : Fin n => B i j)) ∧ ∀ i, B i i = D

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

def spinArray (x : JointArray) : RealArray := fun i j => (x (i,j)).1.1

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

def unitUniform : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1)

instance unitUniform_probability : IsProbabilityMeasure unitUniform := by
  constructor
  simp [unitUniform,Real.volume_Ioo]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_VariationalDefs
attribute [-instance] _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variational Defs. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def unitMonotoneExtension (q : ℝ → ℝ) (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else if 1 ≤ u then 1 else q u

def overlapPathOfMonotone (p : ℝ → ℝ) (hp : Monotone p) (hb : ∀ u, p u ∈ Icc (0:ℝ) 1) : OverlapPath where
  val := AEEqFun.mk p hp.measurable.aestronglyMeasurable
  admissible := ⟨p,(AEEqFun.coeFn_mk p _).symm,hp.monotoneOn _,fun u _ => hb u⟩

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 
def spinLaw (N : ℕ) : Measure (Spin N) :=
  Measure.pi (fun _ : Fin N => (PMF.uniformOfFintype (Fin 2)).toMeasure)
instance spinLaw_probability (N : ℕ) : IsProbabilityMeasure (spinLaw N) := by
  unfold spinLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

def magneticEnergy {N : ℕ} (z : Fin N → ℝ) (x : Spin N) : ℝ :=
  ∑ i, z i*spinValue (x i)

lemma measurable_magneticEnergy (N : ℕ) : Measurable (magneticEnergy (N := N)) := by
  unfold magneticEnergy
  fun_prop

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def magneticIncrementLaw (N : ℕ) (a : ℝ) : ProbabilityMeasure (Spin N → ℝ) :=
  ⟨(Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map
    (fun z => magneticEnergy (fun i => a*z i)),
    Measure.isProbabilityMeasure_map ((measurable_magneticEnergy N).comp (by fun_prop)).aemeasurable⟩

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def magneticRecursion : ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℝ → ℝ
  | 0, _, _ => fun x => Real.log (Real.cosh x)
  | n+1, a, b => gaussianTransform ((a 0)^2) (b 0)
      (magneticRecursion n (fun i => a (i+1)) (fun i => b (i+1)))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 

def magneticFieldValue (n : ℕ) (b h : ℕ → ℝ) : ℝ :=
  (∫ z, magneticRecursion n (fun i => pathAmplitude h (i+1)) b (pathAmplitude h 0*z)
    ∂gaussianReal 0 1) - h n/2

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_RetainedDisplacement
attribute [-instance] _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained Displacement. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_probability_pi {Ω I X : Type*} [MeasurableSpace Ω] [Fintype I]
    [MeasurableSpace X] {ν : Ω → Measure X} (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] : Measurable (fun ω => Measure.pi (fun _ : I => ν ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => Measurable (fun ω => (Measure.pi (fun _ : I => ν ω)) s))
    _root_.generateFrom_pi.symm isPiSystem_pi ?_ ?_ ?_ ?_ s hs
  · simp only [measure_empty]; exact measurable_const
  · rintro s ⟨t,ht,rfl⟩
    simp only [Measure.pi_pi]
    exact Finset.measurable_prod _ (fun i _ => (Measure.measurable_coe (ht i (mem_univ _))).comp hν)
  · intro s hs ih
    have he (ω : Ω) : (Measure.pi (fun _ : I => ν ω)) sᶜ = 1-(Measure.pi (fun _ : I => ν ω)) s := by
      rw [measure_compl hs (measure_ne_top _ _),measure_univ]
    simp_rw [he]; exact measurable_const.sub ih
  · intro s hd hs ih
    have he (ω : Ω) : (Measure.pi (fun _ : I => ν ω)) (⋃ n,s n) =
        ∑' n, (Measure.pi (fun _ : I => ν ω)) (s n) := measure_iUnion hd hs
    simp_rw [he]; exact Measurable.tsum ih

lemma measurable_probability_infinitePi {Ω I X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {ν : Ω → Measure X} (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] : Measurable (fun ω => Measure.infinitePi (fun _ : I => ν ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => Measurable (fun ω => (Measure.infinitePi (fun _ : I => ν ω)) s))
    (s := measurableCylinders (fun _ : I => X))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_ ?_ ?_ s hs
  · simp only [measure_empty]; exact measurable_const
  · intro s hs
    obtain ⟨J,S,hS,rfl⟩ := (mem_measurableCylinders s).mp hs
    have he (ω : Ω) : (Measure.infinitePi (fun _ : I => ν ω)) (cylinder J S) =
        (Measure.pi (fun _ : J => ν ω)) S := Measure.infinitePi_cylinder _ hS
    simp_rw [he]
    exact (Measure.measurable_coe hS).comp (measurable_probability_pi hν)
  · intro s hs ih
    have he (ω : Ω) : (Measure.infinitePi (fun _ : I => ν ω)) sᶜ =
        1-(Measure.infinitePi (fun _ : I => ν ω)) s := by rw [measure_compl hs (measure_ne_top _ _),measure_univ]
    simp_rw [he]; exact measurable_const.sub ih
  · intro s hd hs ih
    have he (ω : Ω) : (Measure.infinitePi (fun _ : I => ν ω)) (⋃ n,s n) =
        ∑' n, (Measure.infinitePi (fun _ : I => ν ω)) (s n) := measure_iUnion hd hs
    simp_rw [he]; exact Measurable.tsum ih

def probabilityReplicaKernel {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] : Kernel Ω (ℕ → X) :=
  ⟨fun ω => Measure.infinitePi (fun _ : ℕ => ν ω),measurable_probability_infinitePi hν⟩

instance probabilityReplicaKernel_markov {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] :
    IsMarkovKernel (probabilityReplicaKernel ν hν) := by
  constructor
  intro ω
  change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => ν ω))
  infer_instance

def markedReplicaLaw {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) : Measure (ℕ → NoiseLeaf A n) :=
  probabilityReplicaKernel (noiseLeafKernel A n) (noiseLeafKernel A n).measurable ∘ₘ
    (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))

instance markedReplicaLaw_probability {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) : IsProbabilityMeasure (markedReplicaLaw n b μ) :=
  inferInstanceAs (IsProbabilityMeasure (_ ∘ₘ _))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

variable {A : Type} [MeasurableSpace A]

def noiseLeafMark : (n : ℕ) → NoiseLeaf A n → Fin n → A
  | 0, _, i => i.elim0
  | n+1, v, i => Fin.cases v.2.1 (noiseLeafMark n v.2.2) i

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_noiseTiltedLeafLaw {A S : Type} [MeasurableSpace A] [MeasurableSpace S]
    [Nonempty A] (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    Measurable (noiseTiltedLeafLaw n c u s) :=
  measurable_normalizeMass.comp ((measurable_withDensity_fixed
    ((measurable_noiseLeafProduct n hc hu).comp (measurable_const.prodMk measurable_id))).comp
    (noiseLeafKernel A n).measurable)



end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_random_withDensity {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {W : Ω × X → ℝ≥0∞} (hW : Measurable W) :
    Measurable (fun ω => (ν ω).withDensity (fun x => W (ω,x))) := by
  let K : Kernel Ω X := ⟨ν,hν⟩
  have : IsMarkovKernel K := ⟨fun _ => inferInstance⟩
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [withDensity_apply _ hs,← lintegral_indicator hs]
  exact (hW.indicator (hs.preimage measurable_snd)).lintegral_kernel_prod_right' (κ := K)

def labeledWeight {A S : Type} [MeasurableSpace A] (n : ℕ)
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S) (s : S)
    (p : (LabeledTree n × (ForestVertex n → A)) × LabeledLeaf n) : ℝ≥0∞ :=
  noiseLeafProduct n c u s (labeledNoiseLeaf A n (p.1.1,markForestOfCoords A n p.1.2) p.2)

def labeledWeightedMass {A S : Type} [MeasurableSpace A] (n : ℕ)
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S) (s : S)
    (p : LabeledTree n × (ForestVertex n → A)) : Measure (LabeledLeaf n) :=
  (labeledLeafLaw n p.1).withDensity (fun v => labeledWeight n c u s (p,v))

def labeledWeightedLeafLaw {A S : Type} [MeasurableSpace A] (n : ℕ)
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S) (s : S)
    (p : LabeledTree n × (ForestVertex n → A)) : Measure (LabeledLeaf n) :=
  normalizeMass (labeledWeightedMass n c u s p)

instance labeledWeightedLeafLaw_probability {A S : Type} [MeasurableSpace A] (n : ℕ)
    (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S) (s : S)
    (p : LabeledTree n × (ForestVertex n → A)) : IsProbabilityMeasure (labeledWeightedLeafLaw n c u s p) :=
  normalizeMass_probability _

lemma measurable_labeledWeight {A S : Type} [MeasurableSpace A] [MeasurableSpace S]
    (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    Measurable (labeledWeight (A := A) n c u s) := by
  apply measurable_from_prod_countable_left
  intro v
  exact (measurable_noiseLeafProduct n hc hu).comp (measurable_const.prodMk
    ((measurable_labeledNoiseLeaf A n v).comp (by fun_prop)))

lemma measurable_labeledWeightedMass {A S : Type} [MeasurableSpace A] [MeasurableSpace S]
    (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    Measurable (labeledWeightedMass (A := A) n c u s) := by
  have hν : Measurable (fun p : LabeledTree n × (ForestVertex n → A) => labeledLeafLaw n p.1) :=
    (measurable_labeledLeafLaw n).comp measurable_fst
  exact measurable_random_withDensity hν (measurable_labeledWeight n hc hu s)

lemma measurable_labeledWeightedLeafLaw {A S : Type} [MeasurableSpace A] [MeasurableSpace S]
    (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    Measurable (labeledWeightedLeafLaw (A := A) n c u s) :=
  measurable_normalizeMass.comp (measurable_labeledWeightedMass n hc hu s)



end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def retainedGaussianScale (b a x : ℝ) : ℝ := Real.exp (a*x-b*a^2/2)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_SamplingIndependent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sampling Independent. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

abbrev PrefixPattern (n r : ℕ) := Fin r → Fin r → Fin n → Bool

def labelPrefixPattern (n r : ℕ) (σ : Fin r → LabeledLeaf n) : PrefixPattern n r :=
  fun i j d => if (labeledAddress n (σ i)).take (d+1) = (labeledAddress n (σ j)).take (d+1) then true else false

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def cascadeReplicaLaw (n : ℕ) (b : ℕ → ℝ) : Measure (ℕ → LabeledLeaf n) :=
  probabilityReplicaKernel (labeledLeafLaw n) (measurable_labeledLeafLaw n) ∘ₘ
    (labeledCascadeLaw n b : Measure (LabeledTree n))

instance cascadeReplicaLaw_probability (n : ℕ) (b : ℕ → ℝ) : IsProbabilityMeasure (cascadeReplicaLaw n b) :=
  inferInstanceAs (IsProbabilityMeasure (_ ∘ₘ _))

def replicaMarkPath {A : Type} (n : ℕ) (σ : ℕ → NoiseLeaf A n) : ℕ → Fin n → A :=
  fun i => noiseLeafMark n (σ i)

def coordinateMarkPath {A : Type} (n : ℕ) (p : (ℕ → LabeledLeaf n) × (ForestVertex n → A)) : ℕ → Fin n → A :=
  fun i d => p.2 (edgeAt n (p.1 i) d)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def retainedLabelLeafLaw (n : ℕ) (b a : ℕ → ℝ) :
    LabeledTree n × (ForestVertex n → ℝ) → Measure (LabeledLeaf n) :=
  labeledWeightedLeafLaw n (fun i (p : PUnit × ℝ) => retainedGaussianScale (b i) (a i) p.2)
    (fun _ _ => PUnit.unit) PUnit.unit

instance retainedLabelLeafLaw_probability (n : ℕ) (b a : ℕ → ℝ)
    (p : LabeledTree n × (ForestVertex n → ℝ)) : IsProbabilityMeasure (retainedLabelLeafLaw n b a p) :=
  labeledWeightedLeafLaw_probability _ _ _ _ _

lemma measurable_retainedLabelLeafLaw (n : ℕ) (b a : ℕ → ℝ) :
    Measurable (retainedLabelLeafLaw n b a) :=
  measurable_labeledWeightedLeafLaw n (fun i => by unfold retainedGaussianScale; fun_prop)
    (fun _ => measurable_const) PUnit.unit

def retainedLabelBase (n : ℕ) (b : ℕ → ℝ) : Measure (LabeledTree n × (ForestVertex n → ℝ)) :=
  (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
    (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1))

instance retainedLabelBase_probability (n : ℕ) (b : ℕ → ℝ) : IsProbabilityMeasure (retainedLabelBase n b) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.prod _ _))

def retainedLabelJoint (n : ℕ) (b a : ℕ → ℝ) :
    Measure ((LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n)) :=
  retainedLabelBase n b ⊗ₘ probabilityReplicaKernel (retainedLabelLeafLaw n b a)
    (measurable_retainedLabelLeafLaw n b a)

instance retainedLabelJoint_probability (n : ℕ) (b a : ℕ → ℝ) : IsProbabilityMeasure (retainedLabelJoint n b a) :=
  inferInstanceAs (IsProbabilityMeasure (_ ⊗ₘ _))

def sampledMarkPath (n : ℕ) (p : (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n)) :
    ℕ → Fin n → ℝ := coordinateMarkPath n (p.2,p.1.2)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def leafLevelCoefficients (n : ℕ) (d : Fin n) (v : LabeledLeaf n) : ℕ →₀ ℝ :=
  Finsupp.single (edgeGaussianTag n (edgeAt n v d)) 1

def rawLeafGibbs (n : ℕ) (d : Fin n) (t : ℝ)
    (p : LabeledTree n × (ℕ → ℝ)) : Measure (LabeledLeaf n) :=
  gibbsProbability (labeledLeafLaw n p.1) (fun v => t*cylinderField (leafLevelCoefficients n d v) p.2)

instance rawLeafGibbs_probability (n : ℕ) (d : Fin n) (t : ℝ) (p : LabeledTree n × (ℕ → ℝ)) :
    IsProbabilityMeasure (rawLeafGibbs n d t p) := gibbsProbability_probability _ _

lemma measurable_rawLeafGibbs (n : ℕ) (d : Fin n) (t : ℝ) : Measurable (rawLeafGibbs n d t) := by
  have hH : Measurable (fun p : (LabeledTree n × (ℕ → ℝ)) × LabeledLeaf n =>
      t*cylinderField (leafLevelCoefficients n d p.2) p.1.2) :=
    ((measurable_cylinderFields (leafLevelCoefficients n d)).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).const_mul t
  have hν : Measurable (fun p : LabeledTree n × (ℕ → ℝ) => labeledLeafLaw n p.1) :=
    (measurable_labeledLeafLaw n).comp measurable_fst
  exact measurable_gibbsProbability hν hH

def rawLabelBase (n : ℕ) (b : ℕ → ℝ) : Measure (LabeledTree n × (ℕ → ℝ)) :=
  (labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates

instance rawLabelBase_probability (n : ℕ) (b : ℕ → ℝ) : IsProbabilityMeasure (rawLabelBase n b) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.prod _ _))

def rawLabelJoint (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ) :
    Measure ((LabeledTree n × (ℕ → ℝ)) × (ℕ → LabeledLeaf n)) :=
  rawLabelBase n b ⊗ₘ probabilityReplicaKernel (rawLeafGibbs n d t) (measurable_rawLeafGibbs n d t)

instance rawLabelJoint_probability (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ) :
    IsProbabilityMeasure (rawLabelJoint n b d t) := inferInstanceAs (IsProbabilityMeasure (_ ⊗ₘ _))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def rawLabelToRetained (n : ℕ) (p : (LabeledTree n × (ℕ → ℝ)) × (ℕ → LabeledLeaf n)) :
    (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n) :=
  ((p.1.1,edgeGaussianCoordinates n p.1.2),p.2)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def pathPrefixPattern (n r : ℕ) (z : ℕ → Fin n → ℝ) : PrefixPattern n r :=
  fun i j d => if z i d = z j d then true else false

lemma measurable_labelPrefixPattern (n r : ℕ) : Measurable (labelPrefixPattern n r) :=
  measurable_of_countable _

lemma measurable_infiniteLabelPattern (n r : ℕ) :
    Measurable (fun σ : ℕ → LabeledLeaf n => labelPrefixPattern n r (fun i => σ i)) :=
  (measurable_labelPrefixPattern n r).comp (by fun_prop)

def gaussianMarkedPathLaw (n : ℕ) (b m : ℕ → ℝ) : Measure (ℕ → Fin n → ℝ) :=
  (markedReplicaLaw n b (fun i => ⟨gaussianReal (m i) 1,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩)).map (replicaMarkPath n)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_JointShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint Shapes. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma prefixPattern_bound (n r : ℕ) (D : PrefixPattern n r → ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x, |D x| ≤ c := by
  refine ⟨∑ x, |D x|,Finset.sum_nonneg (fun _ _ => abs_nonneg _),?_⟩
  intro x
  exact Finset.single_le_sum (f := fun x => |D x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ x)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def prefixPatternMean (n r : ℕ) (b : ℕ → ℝ) (D : PrefixPattern n r → ℝ) : ℝ :=
  ∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b

def patternReindex {n r s : ℕ} (Q : PrefixPattern n r) (e : Fin s → Fin r) : PrefixPattern n s :=
  fun i j d => Q (e i) (e j) d

def boolReal (b : Bool) : ℝ := if b then 1 else 0

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma prefixPatternMean_integrable (n r : ℕ) (b : ℕ → ℝ) (D : PrefixPattern n r → ℝ) :
    Integrable (fun σ => D (labelPrefixPattern n r (fun i => σ i))) (cascadeReplicaLaw n b) := by
  obtain ⟨c,hc,hD⟩ := prefixPattern_bound n r D
  exact integrable_of_measurable_abs_le
    ((measurable_of_countable D).comp (measurable_infiniteLabelPattern n r)) (fun σ => hD _)

lemma prefixPatternMean_add (n r : ℕ) (b : ℕ → ℝ) (D E : PrefixPattern n r → ℝ) :
    prefixPatternMean n r b (fun Q => D Q+E Q) = prefixPatternMean n r b D+prefixPatternMean n r b E :=
  integral_add (prefixPatternMean_integrable n r b D) (prefixPatternMean_integrable n r b E)

lemma prefixPatternMean_mul (n r : ℕ) (b : ℕ → ℝ) (c : ℝ) (D : PrefixPattern n r → ℝ) :
    prefixPatternMean n r b (fun Q => c*D Q) = c*prefixPatternMean n r b D := integral_const_mul _ _

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def prefixVectorValue (n : ℕ) (a : ℕ → ℝ) (v : Fin n → Bool) : ℝ :=
  a 0+∑ d : Fin n, (a (d+1)-a d)*boolReal (v d)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def prefixGGResidual (n r : ℕ) (b : ℕ → ℝ) (i : Fin (r+1)) (D : PrefixPattern n (r+1) → ℝ) :
    ((Fin n → Bool) → ℝ) →ₗ[ℝ] ℝ where
  toFun V := (r+1 : ℕ)*prefixPatternMean n (r+1+1) b
      (fun Q => D (patternReindex Q Fin.castSucc)*V (Q i.castSucc (Fin.last (r+1)))) -
    prefixPatternMean n (r+1) b D*prefixPatternMean n 2 b (fun Q => V (Q 0 1)) -
    ∑ j ∈ Finset.univ.erase i, prefixPatternMean n (r+1) b (fun Q => D Q*V (Q i j))
  map_add' V W := by
    simp only [Pi.add_apply,mul_add,prefixPatternMean_add,Finset.sum_add_distrib]
    ring
  map_smul' c V := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,show ∀ x y : ℝ, x*(c*y) = c*(x*y) from fun x y => by ring,
      prefixPatternMean_mul,← Finset.mul_sum]
    ring

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

def cascadeScalarArray (n : ℕ) (a : ℕ → ℝ) (σ : ℕ → LabeledLeaf n) : RealArray :=
  fun i j => a (labeledCommonDepth n (σ i) (σ j))

lemma measurable_cascadeScalarArray (n : ℕ) (a : ℕ → ℝ) : Measurable (cascadeScalarArray n a) := by
  unfold cascadeScalarArray
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro j
  have h : Measurable (fun p : LabeledLeaf n × LabeledLeaf n => a (labeledCommonDepth n p.1 p.2)) := measurable_of_countable _
  exact h.comp (show Measurable (fun σ : ℕ → LabeledLeaf n => (σ i,σ j)) by fun_prop)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_CascadePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cascade Pair. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def uniformCellIndex (n : ℕ) (u : ℝ) : ℕ := min n ⌊((n+1:ℕ):ℝ)*u⌋₊
def uniformExponent (n : ℕ) (d : ℕ) : ℝ := ((d:ℝ)+1)/(n+1:ℕ)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def uniformCellAverage (q : ℝ → ℝ) (n i : ℕ) : ℝ :=
  ((n+1:ℕ):ℝ)*∫ u in Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ)), q u

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def scalarNodeTag (n : ℕ) (v : Option (ForestVertex n)) : ℕ :=
  Encodable.encode ((nodeAddress n v).length,nodeAddress n v,(Unit.unit : Unit))

def scalarGaussianNodes (n : ℕ) (g : ℕ → ℝ) (v : Option (ForestVertex n)) : ℝ :=
  g (scalarNodeTag n v)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

abbrev PositiveCovariance (m : ℕ) := {S : Matrix (Fin m) (Fin m) ℝ // S.PosSemidef}

def covarianceGaussian (m : ℕ) (S : PositiveCovariance m) : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)) :=
  ⟨multivariateGaussian 0 S.1,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_GaussianMomentTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Moment Test. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix InnerProductSpace
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix BoundedContinuousFunction
namespace IsingPerceptron

def gaussianMoment (m : ℕ) (f : ℝ → ℝ) (S : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∫ z : EuclideanSpace ℝ (Fin m), Real.exp (∑ i, f (z i)) ∂multivariateGaussian 0 S

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

def freshPatternFactor {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (A : X → ℕ →₀ ℝ) (f : ℝ → ℝ) (g : ℕ → ℝ) : ℝ :=
  ∫ x, Real.exp (f (cylinderField (A x) g)) ∂ν

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def labeledScalarFactor (n : ℕ) (s : ℕ → ℝ) (F : ℝ → ℝ) (x : ℝ)
    (p : LabeledTree n × (ForestVertex n → ℝ)) : ℝ :=
  ∫ v, Real.exp (F (x+∑ i : Fin n, s i*p.2 (edgeAt n v i))) ∂labeledLeafLaw n p.1

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 

def rowFactor (c : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ z, Real.exp (f (y+Real.sqrt c*z)) ∂gaussianReal 0 1

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Classical
namespace IsingPerceptron

def diagonalPatch {I : Type*} [DecidableEq I] (D : ℝ) (B : I → I → ℝ) : I → I → ℝ :=
  fun i j => if i=j then D else B i j

lemma measurable_diagonalPatch {I : Type*} [DecidableEq I] (D : ℝ) : Measurable (diagonalPatch (I := I) D) := by
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro j
  unfold diagonalPatch
  split_ifs <;> fun_prop

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_CascadeFreshMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cascade Fresh Moments. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron



def cascadeFreshFactor (n : ℕ) (a : ℕ → ℝ) (f : ℝ → ℝ)
    (p : LabeledTree n × (ℕ → ℝ)) : ℝ :=
  freshPatternFactor (labeledLeafLaw n p.1)
    (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1))
    (gaussianTransform (1-a n) 1 f) p.2

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

def unitClip (x : ℝ) : ℝ := max 0 (min 1 x)
lemma unitClip_mem (x : ℝ) : unitClip x ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩
lemma continuous_unitClip : Continuous unitClip := by unfold unitClip; fun_prop

def scalarJointEntry (x : ℝ) : JointEntry :=
  (⟨unitClip x,⟨(by norm_num : (-1:ℝ) ≤ 0).trans (unitClip_mem x).1,(unitClip_mem x).2⟩⟩,⟨0,by norm_num⟩)
lemma continuous_scalarJointEntry : Continuous scalarJointEntry := by
  unfold scalarJointEntry
  exact continuous_unitClip.subtype_mk _ |>.prodMk continuous_const

def compactScalarArray (B : RealArray) : JointArray := fun ij => scalarJointEntry (B ij.1 ij.2)
lemma continuous_compactScalarArray : Continuous compactScalarArray := by
  apply continuous_pi; intro ij
  exact continuous_scalarJointEntry.comp (by fun_prop)

def cascadeCompactLaw (n : ℕ) (b a : ℕ → ℝ) : ProbabilityMeasure JointArray :=
  ⟨(cascadeReplicaLaw n b).map (fun σ => compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))),
    Measure.isProbabilityMeasure_map (continuous_compactScalarArray.measurable.comp ((measurable_diagonalPatch 1).comp (measurable_cascadeScalarArray n a))).aemeasurable⟩

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix BoundedContinuousFunction





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_FieldChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Field Chain. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def chainPartition (n : ℕ) (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ)
    (hfirst : ζ 0=0) (hlast : ζ (Fin.last (n+1))=1) : Partition :=
  ⟨n+1,by omega,ζ,hz,hfirst,hlast⟩

def chainFieldStep (n : ℕ) (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ)
    (hfirst : ζ 0=0) (hlast : ζ (Fin.last (n+1))=1)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) : FieldStep where
  partition := chainPartition n ζ hz hfirst hlast
  value i := h i
  nonneg _ := h0.trans (hh (Nat.zero_le _))
  ordered := fun _ _ hi => hh hi

def chainExponent {n : ℕ} (ζ : Fin (n+2) → ℝ) (i : ℕ) : ℝ :=
  ζ ⟨min (i+1) (n+1),by omega⟩

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open scoped BigOperators





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_ContactFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contact Faces. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def uniformCut (n : ℕ) (i : Fin (n+2)) : ℝ := (i.val:ℝ)/(n+1:ℕ)

lemma uniformCut_strict (n : ℕ) : StrictMono (uniformCut n) := by
  intro i j hij
  apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
  exact_mod_cast hij

lemma uniformCut_zero (n : ℕ) : uniformCut n 0=0 := by simp [uniformCut]
lemma uniformCut_last (n : ℕ) : uniformCut n (Fin.last (n+1))=1 := by
  change ((n+1:ℕ):ℝ)/((n+1:ℕ):ℝ)=1
  exact div_self (by positivity)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_VariationalFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variational Finiteness. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


def zeroFieldStep : FieldStep :=
  chainFieldStep 0 (uniformCut 0) (uniformCut_strict 0) (uniformCut_zero 0)
    (uniformCut_last 0) (fun _ => 0) monotone_const le_rfl


def zeroOverlapPath : OverlapPath :=
  overlapPathOfMonotone (fun _ => 0) monotone_const (by intro u; constructor <;> norm_num)

end IsingPerceptron

end

end OAI
end


