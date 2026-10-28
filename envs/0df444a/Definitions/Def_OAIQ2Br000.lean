-- Prove2me | Definitions.Def_OAIQ2Br000
-- name    : OAIQ2Br000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T22:24:31.925353+00:00
-- url     : https://prove2.me/theorems/f903e0b9-35be-4b1e-96fc-559b1f0cabaa
-- title:
--   Definitions bundle OAIQ2Br000 of the split of OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FiniteFactor.productBrown`, carved from OpenAI's openai/math development (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 86 declarations of OpenAI's Lean: 39 definitions, 1 inductive type or structure, 6 instances and 40 theorems. The definitions and types are `OAI.BrownLog.mercator`, `OAI.FiniteFactor.CouplingParameters.blockPrefix`, `OAI.FiniteFactor.SourceBaseFunction`, `OAI.FiniteFactor.SourceCStar`, `OAI.FiniteFactor.WeightInterval`, `OAI.FiniteFactor.finiteFloorSupport`, `OAI.FiniteFactor.instModuleRealProductOp_1`, `OAI.FiniteFactor.instModuleRealProductOp_2`, `OAI.FiniteFactor.resolventRealModule`, `OAI.FiniteFactor.sourceAlgebra`, `OAI.FiniteFactor.sourceAlgebraUltraweakTopology`, `OAI.FiniteFactor.sourceBaseIndicator`, `OAI.FiniteFactor.sourceBaseMeasure`, `OAI.FiniteFactor.sourceBaseStar`, `OAI.FiniteFactor.sourceBasis`, `OAI.FiniteFactor.sourceCStarOperator`, `OAI.FiniteFactor.sourceCircleRepresentative`, `OAI.FiniteFactor.sourceCommutantRotation`, `OAI.FiniteFactor.sourceConjugation`, `OAI.FiniteFactor.sourceContinuousWeight`, `OAI.FiniteFactor.sourceContinuousWeightBase`, `OAI.FiniteFactor.sourceContinuousWeightHom`, `OAI.FiniteFactor.sourceFiberIndicator`, `OAI.FiniteFactor.sourceGeneratedVonNeumann`, `OAI.FiniteFactor.sourceMatrixEntry`, `OAI.FiniteFactor.sourcePi`, `OAI.FiniteFactor.sourcePiSymbol`, `OAI.FiniteFactor.sourceRealTrace`, `OAI.FiniteFactor.sourceReflectionIndex`, `OAI.FiniteFactor.sourceReflectionLinear`, `OAI.FiniteFactor.sourceSamplingHaar`, `OAI.FiniteFactor.sourceScalar`, `OAI.FiniteFactor.sourceShiftNIndex`, `OAI.FiniteFactor.sourceTransport`, `OAI.FiniteFactor.sourceTransportIndex`, `OAI.FiniteFactor.sourceWeightBase`, `OAI.FiniteFactor.sourceWeightPoint`, `OAI.FiniteFactor.sourceWeightSqrtBase`, `OAI.FiniteFactor.ultraweakTopology`, `OAI.FiniteFactor.unitDeterminantRealModule`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/BrownMeasure, in whole or in part: `BrownMeasure_ConcreteTrace`, `BrownMeasure_Determinant`, `BrownMeasure_FunctionalCalculus`, `BrownMeasure_Mercator`, `BrownMeasure_Modulus`, `BrownMeasure_Resolvent`, `BrownMeasure_UnitDeterminant`, `FiniteFactor_Coupling_BlockLimit`, `FiniteFactor_CrossedProduct_FiberIndicators`, `FiniteFactor_CrossedProduct_FloorSupport`, `FiniteFactor_CrossedProduct_GeneratedAlgebra`, `FiniteFactor_CrossedProduct_MultiplicationAdjoint`, `FiniteFactor_CrossedProduct_Powers`, `FiniteFactor_CrossedProduct_Reflection`, `FiniteFactor_CrossedProduct_Rotation`, `FiniteFactor_CrossedProduct_RotationCommutant`, `FiniteFactor_CrossedProduct_ScalarCommutant`, `FiniteFactor_CrossedProduct_Transport`, `FiniteFactor_CrossedProduct_VacuumFunctional`, `FiniteFactor_Matrix_Entries`, `FiniteFactor_OperatorUltraweak`, `FiniteFactor_OrbitSampling_Measures`.
--
--   **Imports.** It imports the published bundle `Def_ProductBrown`.
--
--   **Imported by** (directly, in this split): the proof of `OAI.FiniteFactor.productBrown`.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/BrownMeasure at commit adc7f12

import Mathlib
import Definitions.Def_ProductBrown

section
-- module Solutions.OAIQ2_Brown.Compat
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
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_FloorSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def finiteFloorSupport {ι : Type*} (θ : ι → ℝ) (x : ι → ℝ) : Prop :=
  ∀ k : ℤ, (Function.support (coordinateFloor θ k x)).Finite

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_Rotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceCircleRepresentative (x : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIco 1 0 x).val

theorem sourceCircleRepresentative_measurable : Measurable sourceCircleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

theorem sourceCircleRepresentative_coe (x : ℝ) :
    sourceCircleRepresentative (x : AddCircle (1 : ℝ)) = Int.fract x := by
  have hx : Int.fract x ∈ Set.Ico (0 : ℝ) (0+1) :=
    ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one x⟩
  have he := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := 0) hx
  rw [AddCircle.coe_fract] at he
  exact congrArg Subtype.val he

theorem sourceCircle_mk_preserving :
    MeasurePreserving ((↑) : ℝ → AddCircle (1 : ℝ)) unitIntervalMeasure volume := by
  simpa [unitIntervalMeasure, restrict_Ico_eq_restrict_Ioc] using
    AddCircle.measurePreserving_mk 1 0

theorem sourceCircleRepresentative_preserving :
    MeasurePreserving sourceCircleRepresentative volume unitIntervalMeasure := by
  refine ⟨sourceCircleRepresentative_measurable, ?_⟩
  rw [← sourceCircle_mk_preserving.map_eq,
    Measure.map_map sourceCircleRepresentative_measurable sourceCircle_mk_preserving.measurable]
  have he : (sourceCircleRepresentative ∘ ((↑) : ℝ → AddCircle (1 : ℝ))) =ᵐ[unitIntervalMeasure] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    rw [Function.comp_apply, sourceCircleRepresentative_coe]
    exact Int.fract_eq_self.mpr hx
  rw [Measure.map_congr he, Measure.map_id]

/-- Translation modulo one preserves the exact real representative measure. -/
theorem unitInterval_rotate_preserving (a : ℝ) :
    MeasurePreserving (fun x : ℝ => Int.fract (x+a)) unitIntervalMeasure unitIntervalMeasure := by
  have hh := sourceCircleRepresentative_preserving.comp
    ((measurePreserving_add_right (volume : Measure (AddCircle (1 : ℝ))) (a : AddCircle (1 : ℝ))).comp
      sourceCircle_mk_preserving)
  convert hh using 1
  funext x
  simpa only [Function.comp_apply, ← AddCircle.coe_add] using (sourceCircleRepresentative_coe (x+a)).symm

/-- All integer iterates of the countable source rotation preserve its actual
infinite product measure. This is not an assumed action property. -/
theorem coordinateRotate_preserving {ι : Type*} (θ : ι → ℝ) (k : ℤ) :
    MeasurePreserving (coordinateRotate θ k)
      (Measure.infinitePi (fun _ : ι => unitIntervalMeasure))
      (Measure.infinitePi (fun _ : ι => unitIntervalMeasure)) := by
  have hm (i : ι) : Measurable (fun x : ℝ => Int.fract (x+(k : ℝ)*θ i)) :=
    (unitInterval_rotate_preserving _).measurable
  refine ⟨Measurable.of_eval (fun i => (hm i).comp (measurable_pi_apply i)), ?_⟩
  unfold coordinateRotate
  rw [Measure.infinitePi_map_pi _ hm]
  simp_rw [(unitInterval_rotate_preserving _).map_eq]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_Coupling_BlockLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section
namespace CouplingParameters

def blockPrefix (m : ℕ → ℕ) (n : ℕ) : Finset (BlockCoordinate m) :=
  (Finset.range n).sigma (fun _ => Finset.univ)

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_Powers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

def sourceShiftNIndex {ι : Type*} (n : ℕ) (z : (ι → ℝ) × ℤ) : (ι → ℝ) × ℤ :=
  (z.1, z.2-(n : ℤ))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_GeneratedAlgebra
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Pointwise
noncomputable section

/-- A bounded Borel function on the source cube. Values outside the cube
are irrelevant because the representation evaluates rotation representatives. -/
structure SourceBaseFunction where
  toFun : (SourceCoordinate → ℝ) → ℂ
  measurable : Measurable toFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ x, (∀ i, x i ∈ Set.Ico 0 1) → ‖toFun x‖ ≤ bound

def sourcePiSymbol (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction)
    (z : (SourceCoordinate → ℝ) × ℤ) : ℂ := g.toFun (coordinateRotate θ z.2 z.1)

theorem sourcePiSymbol_measurable (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    Measurable (sourcePiSymbol θ g) := by
  apply g.measurable.comp
  apply Measurable.of_eval
  intro i
  unfold coordinateRotate
  fun_prop

theorem sourcePiSymbol_bound (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) (z) :
    ‖sourcePiSymbol θ g z‖ ≤ g.bound :=
  g.norm_le _ (fun _ => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)

theorem sourcePiSymbol_memLp (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    MemLp (sourcePiSymbol θ g) ∞ (sourceMeasure SourceCoordinate) :=
  memLp_top_of_bound (sourcePiSymbol_measurable θ g).aestronglyMeasurable g.bound
    (Eventually.of_forall (sourcePiSymbol_bound θ g))

def sourcePi (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (sourceMeasure SourceCoordinate) ∞ 2 2
    ((sourcePiSymbol_memLp θ g).toLp (sourcePiSymbol θ g))

theorem sourcePi_apply_ae (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction)
    (f : SourceHilbert SourceCoordinate) :
    sourcePi θ g f =ᵐ[sourceMeasure SourceCoordinate] fun z => sourcePiSymbol θ g z * f z := by
  have hh := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    ((sourcePiSymbol_memLp θ g).toLp (sourcePiSymbol θ g)) f (r := 2)
  filter_upwards [hh, (sourcePiSymbol_memLp θ g).coeFn_toLp] with z hz hg
  simpa [sourcePi, hg] using hz

theorem sourcePi_norm_le (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    ‖sourcePi θ g‖ ≤ g.bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ g.bound_nonneg
  intro f
  have hh : ‖sourcePi θ g f‖ ≤ ‖g.bound • f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [sourcePi_apply_ae θ g f, Lp.coeFn_smul g.bound f] with z hz hs
    rw [hz, hs, Pi.smul_apply, norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg g.bound_nonneg]
    exact mul_le_mul_of_nonneg_right (sourcePiSymbol_bound θ g z) (norm_nonneg _)
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg g.bound_nonneg] using hh

/-- Double commutant of a concrete family, including its adjoints. -/
def sourceGeneratedVonNeumann {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)
  centralizer_centralizer' := by
    have he : (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier =
        Set.centralizer (Set.centralizer (S ∪ star S)) :=
      StarSubalgebra.coe_centralizer_centralizer ℂ S
    rw [he]
    simp

theorem mem_sourceGeneratedVonNeumann {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Set (H →L[ℂ] H)) {T : H →L[ℂ] H} (hT : T ∈ S) :
    T ∈ sourceGeneratedVonNeumann S := by
  have he : (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier =
      Set.centralizer (Set.centralizer (S ∪ star S)) :=
    StarSubalgebra.coe_centralizer_centralizer ℂ S
  change T ∈ (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier
  rw [he]
  exact Set.subset_centralizer_centralizer (Or.inl hT)

/-- The actual generated algebra of the source regular representation.
Factor, trace, finiteness and predual properties are separate obligations. -/
def sourceAlgebra (θ : SourceCoordinate → ℝ) : VonNeumannAlgebra (SourceHilbert SourceCoordinate) :=
  sourceGeneratedVonNeumann ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ))

theorem sourcePi_mem (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    sourcePi θ g ∈ sourceAlgebra θ :=
  mem_sourceGeneratedVonNeumann _ (Or.inr ⟨g,rfl⟩)

theorem sourceShift_mem (θ : SourceCoordinate → ℝ) :
    sourceShift SourceCoordinate ∈ sourceAlgebra θ :=
  mem_sourceGeneratedVonNeumann _ (Or.inl rfl)

def sourceWeightBase (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) : SourceBaseFunction where
  toFun := fun x => (sourceCocycle θ sourceLogWeight 1 x : ℂ)
  measurable := Complex.measurable_ofReal.comp (sourceCocycle_measurable θ sourceLogWeight 1)
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := by
    intro x hx
    rw [Complex.norm_real, Real.norm_of_nonneg (sourceCocycle_pos _ _ _ _).le]
    exact sourceWeight_le_one θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hx

theorem sourceMultiplication_eq_pi (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceMultiplication θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg =
      sourcePi θ (sourceWeightBase θ hθ) := rfl

/-- Actual membership of the already verified staged operator in its generated
von Neumann algebra, without an assumed operator-membership hypothesis. -/
theorem staged_sourceOperator_mem (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ∈ sourceAlgebra θ := by
  change sourceShift SourceCoordinate * sourceMultiplication θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ∈ _
  rw [sourceMultiplication_eq_pi θ hθ]
  exact mul_mem (sourceShift_mem θ) (sourcePi_mem θ (sourceWeightBase θ hθ))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_OperatorUltraweak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteFactor
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual ultraweak topology, generated by absolutely summable vector
functionals. No continuity of a chosen trace is built into this definition. -/
@[instance_reducible] def ultraweakTopology : TopologicalSpace (H →L[ℂ] H) :=
  ⨅ (ξ : ℕ → H) (η : ℕ → H) (_ : Summable (fun n => ‖ξ n‖ * ‖η n‖)),
    TopologicalSpace.induced (fun T : H →L[ℂ] H => ∑' n, inner ℂ (ξ n) (T (η n)))
      inferInstance

end FiniteFactor

end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_VacuumFunctional
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceVacuumFunctional_add (S T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    sourceVacuumFunctional (S+T) = sourceVacuumFunctional S + sourceVacuumFunctional T := by
  simp [sourceVacuumFunctional,inner_add_right]

theorem sourceVacuumFunctional_smul (c : ℂ)
    (T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    sourceVacuumFunctional (c • T) = c * sourceVacuumFunctional T := by
  simp [sourceVacuumFunctional,inner_smul_right]

theorem sourceVacuumFunctional_bound
    (T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    ‖sourceVacuumFunctional T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖sourceVacuum‖ * ‖T sourceVacuum‖ := norm_inner_le_norm _ _
    _ ≤ ‖sourceVacuum‖ * (‖T‖ * ‖sourceVacuum‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [sourceVacuum_norm]; ring

@[instance_reducible] def sourceAlgebraUltraweakTopology (θ : SourceCoordinate → ℝ) :
    TopologicalSpace (sourceAlgebra θ).toStarSubalgebra :=
  TopologicalSpace.induced (fun T : (sourceAlgebra θ).toStarSubalgebra =>
    (T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate))
    (ultraweakTopology (SourceHilbert SourceCoordinate))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_Mercator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace BrownLog
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

def mercator (a : A) : A := -∑' n : ℕ, ((n+1 : ℝ)⁻¹) • a^(n+1)

end BrownLog
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_MultiplicationAdjoint
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

/-- Conjugate of a bounded source base function, with the same bound. -/
def sourceBaseStar (g : SourceBaseFunction) : SourceBaseFunction where
  toFun := fun x => star (g.toFun x)
  measurable := Complex.continuous_conj.measurable.comp g.measurable
  bound := g.bound
  bound_nonneg := g.bound_nonneg
  norm_le := by intro x hx; simpa using g.norm_le x hx

/-- The multiplication representation has the actual Hilbert adjoint. -/
theorem sourcePi_star (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    star (sourcePi θ g) = sourcePi θ (sourceBaseStar g) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  change (∫ z, inner ℂ ((sourcePi θ (sourceBaseStar g) f) z) (h z) ∂sourceMeasure SourceCoordinate) =
    ∫ z, inner ℂ (f z) ((sourcePi θ g h) z) ∂sourceMeasure SourceCoordinate
  apply integral_congr_ae
  filter_upwards [sourcePi_apply_ae θ (sourceBaseStar g) f,
    sourcePi_apply_ae θ g h] with z hf hh
  rw [hf, hh]
  simp [sourcePiSymbol, sourceBaseStar, RCLike.inner_apply, mul_comm, mul_left_comm, mul_assoc]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_Transport
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Combined integer base rotation and fiber translation. -/
def sourceTransportIndex (θ : SourceCoordinate → ℝ) (n m : ℤ)
    (z : (SourceCoordinate → ℝ) × ℤ) : (SourceCoordinate → ℝ) × ℤ :=
  (coordinateRotate θ n z.1, z.2 - m)

theorem sourceTransportIndex_preserving (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    MeasurePreserving (sourceTransportIndex θ n m)
      (sourceMeasure SourceCoordinate) (sourceMeasure SourceCoordinate) := by
  have hm : Measurable (fun k : ℤ => k-m) := measurable_of_countable _
  have hi : Function.Injective (fun k : ℤ => k-m) := by intro a b h; dsimp at h; omega
  have hs : Function.Surjective (fun k : ℤ => k-m) := by intro k; exact ⟨k+m, by dsimp; omega⟩
  have hp : MeasurePreserving (fun k : ℤ => k-m) Measure.count Measure.count := by
    refine ⟨hm, ?_⟩
    ext S hS
    rw [Measure.map_apply hm hS, Measure.count_apply (hS.preimage hm), Measure.count_apply hS,
      ← hi.encard_image, Set.image_preimage_eq S hs]
  exact (coordinateRotate_preserving θ n).prod hp

def sourceTransport (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate :=
  (Lp.compMeasurePreservingₗᵢ ℂ (sourceTransportIndex θ n m)
    (sourceTransportIndex_preserving θ n m)).toContinuousLinearMap

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_Reflection
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

/-- The reflection for the source regular representation. -/
def sourceReflectionIndex (θ : SourceCoordinate → ℝ)
    (z : (SourceCoordinate → ℝ) × ℤ) : (SourceCoordinate → ℝ) × ℤ :=
  (coordinateRotate θ z.2 z.1, -z.2)

theorem sourceReflectionIndex_preserving (θ : SourceCoordinate → ℝ) :
    MeasurePreserving (sourceReflectionIndex θ)
      (sourceMeasure SourceCoordinate) (sourceMeasure SourceCoordinate) := by
  have hn : MeasurePreserving (fun n : ℤ => -n) Measure.count Measure.count := by
    refine ⟨measurable_of_countable _, ?_⟩
    ext S hS
    rw [Measure.map_apply (measurable_of_countable _) hS,
      Measure.count_apply (hS.preimage (measurable_of_countable _)), Measure.count_apply hS,
      ← neg_injective.encard_image, Set.image_preimage_eq S neg_surjective]
  have hm : Measurable (Function.uncurry (fun (n : ℤ) (x : SourceCoordinate → ℝ) => coordinateRotate θ n x)) := by
    apply Measurable.of_eval
    intro i
    unfold coordinateRotate
    fun_prop
  have hp := hn.skew_product hm (Eventually.of_forall (fun n => (coordinateRotate_preserving θ n).map_eq))
  exact Measure.measurePreserving_swap.comp (hp.comp Measure.measurePreserving_swap)

def sourceReflectionLinear (θ : SourceCoordinate → ℝ) :
    SourceHilbert SourceCoordinate →ₗᵢ[ℂ] SourceHilbert SourceCoordinate :=
  Lp.compMeasurePreservingₗᵢ ℂ (sourceReflectionIndex θ) (sourceReflectionIndex_preserving θ)

/-- Explicit conjugate-linear isometry; no modular or tracial property assumed. -/
def sourceConjugation (θ : SourceCoordinate → ℝ) (f : SourceHilbert SourceCoordinate) :
    SourceHilbert SourceCoordinate := star (sourceReflectionLinear θ f)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_ScalarCommutant
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Scalar base multiplication, independent of the fiber coordinate. -/
def sourceScalar (g : SourceBaseFunction) :
    SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate :=
  sourcePi (fun _ => 0) g

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_RotationCommutant
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

def sourceCommutantRotation (θ : SourceCoordinate → ℝ) (n : ℤ) := sourceTransport θ n n

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_CrossedProduct_FiberIndicators
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Bounded measurable indicator on the base. -/
def sourceBaseIndicator (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) :
    SourceBaseFunction where
  toFun := A.indicator (fun _ => (1 : ℂ))
  measurable := measurable_const.indicator hA
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := by intro x _; by_cases hx : x ∈ A <;> simp [hx]

theorem sourceFiberMeasure_ne_top (A : Set (SourceCoordinate → ℝ)) (n : ℤ) :
    sourceMeasure SourceCoordinate (A ×ˢ {n}) ≠ ∞ := by
  rw [Measure.prod_prod]
  simp

def sourceFiberIndicator (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
    SourceHilbert SourceCoordinate :=
  indicatorConstLp 2 (hA.prod (measurableSet_singleton n)) (sourceFiberMeasure_ne_top A n) (1 : ℂ)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_Matrix_Entries
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

abbrev sourceBaseMeasure : Measure (SourceCoordinate → ℝ) :=
  Measure.infinitePi (fun _ => unitIntervalMeasure)

/-- Constant coordinate vector, realized in the original source L2 space. -/
def sourceBasis (n : ℤ) : SourceHilbert SourceCoordinate :=
  sourceFiberIndicator Set.univ MeasurableSet.univ n

/-- Actual matrix coefficients obtained by applying H to constant e_n. -/
def sourceMatrixEntry (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (k n : ℤ) (x : SourceCoordinate → ℝ) : ℂ := (H (sourceBasis n)) (x,k)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_ConcreteTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology Ring
namespace FiniteFactor
abbrev SourceCStar (θ : SourceCoordinate → ℝ) := (sourceAlgebra θ).toStarSubalgebra
instance sourceCStar_closed (θ : SourceCoordinate → ℝ) : IsClosed (SourceCStar θ:Set ProductOp) := by
  change IsClosed (sourceAlgebra θ:Set ProductOp)
  rw [← (sourceAlgebra θ).centralizer_centralizer]
  exact Set.isClosed_centralizer _
instance sourceCStar_nontrivial (θ : SourceCoordinate → ℝ) : Nontrivial (SourceCStar θ) := by
  exact nontrivial_of_ne (0 : SourceCStar θ) 1
    (fun equality => zero_ne_one (congrArg Subtype.val equality))

def sourceRealTrace (θ : SourceCoordinate → ℝ) : SourceCStar θ →L[ℝ] ℝ :=
  (show SourceCStar θ →ₗ[ℝ] ℝ from {
    toFun := fun a=>(sourceVacuumFunctional a).re
    map_add' := fun a b=>by simp [sourceVacuumFunctional_add]
    map_smul' := fun a b=>by
      change (sourceVacuumFunctional (((a:ℂ) • (b:ProductOp)))).re=a*(sourceVacuumFunctional b).re
      rw [sourceVacuumFunctional_smul]
      simp
  }).mkContinuous 1 (fun a=>by
    change |(sourceVacuumFunctional a).re|≤1*‖(a:ProductOp)‖
    simpa only [one_mul] using (Complex.abs_re_le_norm (sourceVacuumFunctional a)).trans (sourceVacuumFunctional_bound a))

def sourceCStarOperator (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) : SourceCStar θ :=
  ⟨sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg,staged_sourceOperator_mem θ hθ⟩

end FiniteFactor
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.FiniteFactor_OrbitSampling_Measures
attribute [-instance] _root_.OAI.FiniteFactor.productHilbertNontrivial _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal
noncomputable section

abbrev sourceSamplingHaar : Measure (SourceCoordinate → ℝ) :=
  Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_Modulus
attribute [-instance] _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal CStarAlgebra
namespace FiniteFactor
local instance instModuleRealProductOp_1 : Module ℝ ProductOp := Module.complexToReal ProductOp

def sourceWeightSqrtBase (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) : SourceBaseFunction where
  toFun := fun x=>(Real.sqrt (sourceCocycle θ sourceLogWeight 1 x):ℂ)
  measurable := Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
    (sourceCocycle_measurable θ sourceLogWeight 1))
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := by
    intro x hx
    rw [Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_one).mpr (sourceWeight_le_one θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hx)

lemma sourceWeight_positive (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    0 ≤ sourcePi θ (sourceWeightBase θ hθ) := by
  let B := sourcePi θ (sourceWeightSqrtBase θ hθ)
  have he : star B*B=sourcePi θ (sourceWeightBase θ hθ) := by
    dsimp [B]
    rw [sourcePi_star]
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [sourcePi_apply_ae θ (sourceBaseStar (sourceWeightSqrtBase θ hθ))
      (sourcePi θ (sourceWeightSqrtBase θ hθ) u),sourcePi_apply_ae θ (sourceWeightSqrtBase θ hθ) u,
      sourcePi_apply_ae θ (sourceWeightBase θ hθ) u] with z h1 h2 h3
    change (sourcePi θ (sourceBaseStar (sourceWeightSqrtBase θ hθ))
      (sourcePi θ (sourceWeightSqrtBase θ hθ) u)) z=(sourcePi θ (sourceWeightBase θ hθ) u) z
    rw [h1,h2,h3]
    simp only [sourcePiSymbol,sourceBaseStar,sourceWeightSqrtBase,sourceWeightBase,
      Complex.star_def,Complex.conj_ofReal,← mul_assoc,← Complex.ofReal_mul,
      Real.mul_self_sqrt (sourceCocycle_pos _ _ _ _).le]
  rw [← he]
  exact star_mul_self_nonneg B

end FiniteFactor
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_FunctionalCalculus
attribute [-instance] _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology
namespace FiniteFactor
local instance instIsometricContinuousFunctionalCalculusRealProductOpIsSelfAdjoint_2 : IsometricContinuousFunctionalCalculus ℝ ProductOp IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
abbrev WeightInterval := Set.Icc (0:ℝ) 1

def sourceWeightPoint (θ : SourceCoordinate → ℝ) (x : SourceCoordinate → ℝ) : WeightInterval :=
  ⟨min 1 (sourceCocycle θ sourceLogWeight 1 x),le_min zero_le_one (sourceCocycle_pos _ _ _ _).le,min_le_left _ _⟩
lemma sourceWeightPoint_measurable (θ : SourceCoordinate → ℝ) : Measurable (sourceWeightPoint θ) := by
  apply Measurable.subtype_mk
  exact measurable_const.min (sourceCocycle_measurable θ sourceLogWeight 1)

def sourceContinuousWeightBase (θ : SourceCoordinate → ℝ) (φ : C(WeightInterval,ℝ)) : SourceBaseFunction where
  toFun x := (φ (sourceWeightPoint θ x):ℂ)
  measurable := Complex.measurable_ofReal.comp (φ.continuous.measurable.comp (sourceWeightPoint_measurable θ))
  bound := ‖φ‖
  bound_nonneg := norm_nonneg _
  norm_le x _ := by simpa only [Complex.norm_real] using φ.norm_coe_le_norm (sourceWeightPoint θ x)

def sourceContinuousWeight (θ : SourceCoordinate → ℝ) (φ : C(WeightInterval,ℝ)) : ProductOp :=
  sourcePi θ (sourceContinuousWeightBase θ φ)

lemma sourceContinuousWeight_apply_ae (θ : SourceCoordinate → ℝ) (φ : C(WeightInterval,ℝ))
    (u : SourceHilbert SourceCoordinate) :
    sourceContinuousWeight θ φ u=ᵐ[sourceMeasure SourceCoordinate] fun z=>
      (φ (sourceWeightPoint θ (coordinateRotate θ z.2 z.1)):ℂ)*u z :=
  sourcePi_apply_ae θ (sourceContinuousWeightBase θ φ) u

lemma sourceContinuousWeight_one (θ : SourceCoordinate → ℝ) : sourceContinuousWeight θ 1=1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceContinuousWeight_apply_ae θ 1 u] with z hz
  change (sourceContinuousWeight θ 1 u) z=u z
  simpa using hz
lemma sourceContinuousWeight_zero (θ : SourceCoordinate → ℝ) : sourceContinuousWeight θ 0=0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceContinuousWeight_apply_ae θ 0 u,Lp.coeFn_zero ℂ 2 (sourceMeasure SourceCoordinate)] with z hz h0
  change (sourceContinuousWeight θ 0 u) z=(0:SourceHilbert SourceCoordinate) z
  rw [h0]
  simpa using hz
lemma sourceContinuousWeight_add (θ : SourceCoordinate → ℝ) (φ ψ : C(WeightInterval,ℝ)) :
    sourceContinuousWeight θ (φ+ψ)=sourceContinuousWeight θ φ+sourceContinuousWeight θ ψ := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceContinuousWeight_apply_ae θ (φ+ψ) u,sourceContinuousWeight_apply_ae θ φ u,
    sourceContinuousWeight_apply_ae θ ψ u,Lp.coeFn_add (sourceContinuousWeight θ φ u) (sourceContinuousWeight θ ψ u)] with z ha hf hg hs
  change (sourceContinuousWeight θ (φ+ψ) u) z=(sourceContinuousWeight θ φ u+sourceContinuousWeight θ ψ u) z
  rw [ha,hs,Pi.add_apply,hf,hg]
  simp [add_mul]
lemma sourceContinuousWeight_mul (θ : SourceCoordinate → ℝ) (φ ψ : C(WeightInterval,ℝ)) :
    sourceContinuousWeight θ (φ*ψ)=sourceContinuousWeight θ φ*sourceContinuousWeight θ ψ := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceContinuousWeight_apply_ae θ (φ*ψ) u,
    sourceContinuousWeight_apply_ae θ φ (sourceContinuousWeight θ ψ u),sourceContinuousWeight_apply_ae θ ψ u] with z ha hf hg
  change (sourceContinuousWeight θ (φ*ψ) u) z=(sourceContinuousWeight θ φ (sourceContinuousWeight θ ψ u)) z
  rw [ha,hf,hg]
  simp [mul_assoc]
lemma sourceContinuousWeight_smul (θ : SourceCoordinate → ℝ) (r : ℝ) (φ : C(WeightInterval,ℝ)) :
    sourceContinuousWeight θ (r • φ)=r • sourceContinuousWeight θ φ := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourceContinuousWeight_apply_ae θ (r • φ) u,sourceContinuousWeight_apply_ae θ φ u,
    Lp.coeFn_smul r (sourceContinuousWeight θ φ u)] with z ha hf hs
  change (sourceContinuousWeight θ (r • φ) u) z=(r • sourceContinuousWeight θ φ u) z
  rw [ha,hs,Pi.smul_apply,hf]
  simp [Complex.real_smul,mul_assoc]
lemma sourceContinuousWeight_star (θ : SourceCoordinate → ℝ) (φ : C(WeightInterval,ℝ)) :
    sourceContinuousWeight θ (star φ)=star (sourceContinuousWeight θ φ) := by
  change sourcePi θ (sourceContinuousWeightBase θ (star φ))=star (sourcePi θ (sourceContinuousWeightBase θ φ))
  rw [sourcePi_star]
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [sourcePi_apply_ae θ (sourceContinuousWeightBase θ (star φ)) u,
    sourcePi_apply_ae θ (sourceBaseStar (sourceContinuousWeightBase θ φ)) u] with z h1 h2
  rw [h1,h2]
  simp [sourcePiSymbol,sourceContinuousWeightBase,sourceBaseStar]

def sourceContinuousWeightHom (θ : SourceCoordinate → ℝ) : C(WeightInterval,ℝ) →⋆ₐ[ℝ] ProductOp where
  toFun := sourceContinuousWeight θ
  map_one' := sourceContinuousWeight_one θ
  map_zero' := sourceContinuousWeight_zero θ
  map_add' := sourceContinuousWeight_add θ
  map_mul' := sourceContinuousWeight_mul θ
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one,sourceContinuousWeight_smul,sourceContinuousWeight_one,Algebra.algebraMap_eq_smul_one]
  map_star' := sourceContinuousWeight_star θ

lemma sourceWeight_spectrum_subset (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    spectrum ℝ (sourcePi θ (sourceWeightBase θ hθ))⊆WeightInterval := by
  intro t ht
  exact ⟨spectrum_nonneg_of_nonneg (sourceWeight_positive θ hθ) ht,
    (Real.le_norm_self t).trans ((spectrum.norm_le_norm_of_mem ht).trans (sourcePi_norm_le θ (sourceWeightBase θ hθ)))⟩

end FiniteFactor
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_Determinant
attribute [-instance] _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal
namespace FiniteFactor
local instance instModuleRealProductOp_2 : Module ℝ ProductOp := Module.complexToReal ProductOp
local instance instIsometricContinuousFunctionalCalculusRealProductOpIsSelfAdjoint_3 : IsometricContinuousFunctionalCalculus ℝ ProductOp IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

end FiniteFactor
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_UnitDeterminant
attribute [-instance] _root_.OAI.FiniteFactor.sourceCStar_closed _root_.OAI.FiniteFactor.sourceCStar_nontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal Ring
namespace FiniteFactor
local instance unitDeterminantRealModule : Module ℝ ProductOp := Module.complexToReal ProductOp
local instance unitDeterminantFunctionalCalculus :
    IsometricContinuousFunctionalCalculus ℝ ProductOp IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

end FiniteFactor
end

end OAI
end

section
-- module Solutions.OAIQ2_Brown.BrownMeasure_Resolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology Ring ENNReal
namespace FiniteFactor
local instance resolventRealModule : Module ℝ ProductOp := Module.complexToReal ProductOp
end FiniteFactor
end

end OAI
end


