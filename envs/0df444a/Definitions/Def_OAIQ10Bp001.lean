-- Prove2me | Definitions.Def_OAIQ10Bp001
-- name    : OAIQ10Bp001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:17:05.949704+00:00
-- url     : https://prove2.me/theorems/13954a83-664d-4fca-b4c4-166c6fb1958b
-- title:
--   Definitions bundle OAIQ10Bp001 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 40 definitions, 4 instances and 16 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.CompatibleWith`, `OAI.HigherDimensionalBallPacking.Rigidity.FramedCR.HasFrame`, `OAI.HigherDimensionalBallPacking.Rigidity.FramedCR.centeredFrame`, `OAI.HigherDimensionalBallPacking.Rigidity.FramedCR.curlLinear`, `OAI.HigherDimensionalBallPacking.Rigidity.FramedCR.frameConjugation`, `OAI.HigherDimensionalBallPacking.Rigidity.FramedCR.frozenCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.FramedCR.shearEquiv`, `OAI.HigherDimensionalBallPacking.Rigidity.FramedCR.standardCurl`, `OAI.HigherDimensionalBallPacking.Rigidity.FramedCR.tangentCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.FramedCR.tangentCurveDir`, `OAI.HigherDimensionalBallPacking.Rigidity.FramedCR.tangentField`, `OAI.HigherDimensionalBallPacking.Rigidity.FramedCR.tangentMap`, `OAI.HigherDimensionalBallPacking.Rigidity.blowupCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.blowupMoment`, `OAI.HigherDimensionalBallPacking.Rigidity.blowupSize`, `OAI.HigherDimensionalBallPacking.Rigidity.blowupSlope`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoffCRRemainder`, `OAI.HigherDimensionalBallPacking.Rigidity.lineMean`, `OAI.HigherDimensionalBallPacking.Rigidity.oneForm`, `OAI.HigherDimensionalBallPacking.Rigidity.outerProfile`, `OAI.HigherDimensionalBallPacking.Rigidity.radialCoefficient`, `OAI.HigherDimensionalBallPacking.Rigidity.radialMoment`, `OAI.HigherDimensionalBallPacking.Rigidity.radialOffset`, `OAI.HigherDimensionalBallPacking.Rigidity.radialShift`, `OAI.HigherDimensionalBallPacking.Rigidity.radialSlope`, `OAI.HigherDimensionalBallPacking.Rigidity.radialSwitch`, `OAI.HigherDimensionalBallPacking.Rigidity.realAffineProfile`, `OAI.HigherDimensionalBallPacking.Rigidity.relativeTransition`, `OAI.HigherDimensionalBallPacking.Rigidity.rescaleMap`, `OAI.HigherDimensionalBallPacking.Rigidity.scalarDirection`, `OAI.TwoPointContinuation.LocallyPrecompact`, `OAI.TwoPointContinuation.approxBump`, `OAI.TwoPointContinuation.coordinateForm`, `OAI.TwoPointContinuation.cubeLower`, `OAI.TwoPointContinuation.cubeUpper`, `OAI.TwoPointContinuation.cylinderLower`, `OAI.TwoPointContinuation.cylinderUpper`, `OAI.TwoPointContinuation.formFlux`, `OAI.TwoPointContinuation.mollify`, `OAI.TwoPointContinuation.pulledCoordinateForm`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/BallPacking, in whole or in part: `BallPacking_Necessity_C1Energy`, `BallPacking_Necessity_CompactContinuation`, `BallPacking_Necessity_DensityLimits`, `BallPacking_Necessity_FiniteContinuation`, `BallPacking_Necessity_FrameFredholm`, `BallPacking_Necessity_FramedCompactness`, `BallPacking_Necessity_FrozenInverse`, `BallPacking_Necessity_GradientLimits`, `BallPacking_Necessity_NonlinearCR`, `BallPacking_Necessity_SchauderBounds`, `BallPacking_Necessity_SquareBounds`, `BallPacking_Necessity_TangentLimits`, `BallPacking_Rigidity_Adapted`, `BallPacking_Rigidity_Correction`, `BallPacking_Rigidity_CurveArea`, `BallPacking_Rigidity_RadialForm`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ10Bp002` and `OAIQ10Bp003`; the statement `OAI.TwoPointContinuation.local_degree_continuation`; the proof of `OAI.TwoPointContinuation.local_degree_continuation`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/BallPacking at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ10_BP.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Adapted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def radialSwitch (σ τ t : ℝ) : ℝ := Real.smoothTransition ((t-σ)/(τ-σ))

def radialOffset (σ τ t : ℝ) : ℝ := ∫ s in σ..t, radialSwitch σ τ s

def radialShift (σ τ : ℝ) : ℝ := 1 + radialOffset σ τ τ - τ

def radialCoefficient (σ τ t : ℝ) : ℝ := (1 + radialOffset σ τ t)⁻¹

def radialMoment (σ τ t : ℝ) : ℝ := t * radialCoefficient σ τ t

@[simp] theorem radialMoment_zero {σ τ : ℝ} : radialMoment σ τ 0 = 0 := by
  simp [radialMoment]



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_RadialForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def radialSlope (σ τ t : ℝ) : ℝ :=
  -radialSwitch σ τ t / (1 + radialOffset σ τ t)^2

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CurveArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def oneForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : E → E →L[ℝ] ℝ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ 0 (α x)


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def blowupSize (σ τ : ℝ) : ℝ := τ - radialOffset σ τ τ

def blowupMoment (σ τ t : ℝ) : ℝ := blowupSize σ τ + radialOffset σ τ t

def blowupCoefficient (σ τ t : ℝ) : ℝ := blowupMoment σ τ t / t

def blowupSlope (σ τ t : ℝ) : ℝ :=
  (t * radialSwitch σ τ t - blowupMoment σ τ t) / t^2


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Correction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def outerProfile (A t : ℝ) : ℝ :=
  Real.smoothTransition (t+2) * (1 - Real.smoothTransition ((t-A)/A))



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_C1Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
namespace TwoPointContinuation

variable {G E : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 def approxBump (j : ℕ) : ContDiffBump (0:G) :=
  ⟨(1/((j:ℝ)+1))/2,1/((j:ℝ)+1),by positivity,by apply half_lt_self; positivity⟩

 def mollify (μ : Measure G) (j : ℕ) (f : G → E) : G → E :=
  (approxBump j).normed μ ⋆[lsmul ℝ ℝ,μ] f

end TwoPointContinuation

 

 

open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap







open scoped ContDiff Topology
open Set Filter Function MeasureTheory





open scoped ContDiff Topology
open Set Filter Function MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FiniteContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function MeasureTheory
namespace TwoPointContinuation

def coordinateForm (n : ℕ) : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ :=
  { (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ) with
    cont := by
      change Continuous (fun v : Matrix (Fin n) (Fin n) ℝ => Matrix.det v)
      exact continuous_id.matrix_det }

@[simp] theorem coordinateForm_apply (n : ℕ) (v : Fin n → Fin n → ℝ) :
    coordinateForm n v=Matrix.det v := rfl

 def formFlux {n : ℕ} (W : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (i : Fin (n+1)) (x : Fin (n+1) → ℝ) : ℝ :=
  (-1:ℝ)^i.val • W x (i.removeNth (fun j : Fin (n+1) => (Pi.single j (1:ℝ) : Fin (n+1) → ℝ)))

 def pulledCoordinateForm {n : ℕ} (F : (Fin (n+1) → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (x : Fin (n+1) → ℝ) :
    (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ :=
  (φ (F x) • coordinateForm n).compContinuousLinearMap (fderiv ℝ F x)






open scoped ContDiff Topology
open Set Filter Function MeasureTheory

def cubeLower (n : ℕ) (R : ℝ) : Fin n → ℝ := fun _ => -R
def cubeUpper (n : ℕ) (R : ℝ) : Fin n → ℝ := fun _ => R

def cylinderLower (n : ℕ) (R : ℝ) : Fin (n+1) → ℝ := Fin.cons (0:ℝ) (cubeLower n R)
def cylinderUpper (n : ℕ) (R : ℝ) : Fin (n+1) → ℝ := Fin.cons (1:ℝ) (cubeUpper n R)






open scoped ContDiff Topology Manifold
open Set Filter Function






open scoped ContDiff Topology
open Set Filter Function






open scoped ContDiff Topology
open Set Filter Function

end TwoPointContinuation

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_CompactContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function
namespace TwoPointContinuation






open scoped ContDiff Topology
open Set Filter Function






open scoped ContDiff Topology
open Set Filter Function






open scoped ContDiff Topology
open Set Filter Function






open scoped Topology
open Set Filter Function

 def LocallyPrecompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (x : X) : Prop := ∃ V∈𝓝 x, ∃ K : Set Y, IsCompact K ∧ f '' V⊆K

end TwoPointContinuation

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_SquareBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
namespace HigherDimensionalBallPacking.Rigidity








open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def lineMean (f : ℝ → ℝ) (a b : ℝ) : ℝ := (∫ x in a..b, f x)/(b-a)








open scoped ContDiff Topology
open Set Function Filter MeasureTheory








open scoped ContDiff Topology
open Set Function Filter MeasureTheory

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrameFredholm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter





open Set Function Filter Topology

 

 

open Set Function Filter Topology
open scoped NNReal

 

 

open scoped NNReal
open Set Function Filter Topology

 

 

open Set Function Filter Topology

 

 

open Set Function Filter Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped ContDiff Topology
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 
def CompatibleWith (η : E →L[ℝ] E →L[ℝ] ℝ) (J : E →L[ℝ] E) : Prop :=
  (∀ v, J (J v) = -v) ∧ (∀ u v, η (J u) (J v) = η u v) ∧
    (∀ v ≠ 0, 0 < η v (J v))


def relativeTransition (t : ℝ) (B J : E →L[ℝ] E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - t • J.comp B

@[simp] theorem relativeTransition_apply (t : ℝ) (B J : E →L[ℝ] E) (v : E) :
    relativeTransition t B J v = v - t • J (B v) := rfl

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_NonlinearCR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction



namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [CompleteSpace E]


def realAffineProfile (c : E) (A : ℂ →L[ℝ] E) : C(ℂ,E) :=
  ⟨fun z => c+A z,continuous_const.add A.continuous⟩

omit [CompleteSpace E] in
@[simp] theorem realAffineProfile_apply (c : E) (A : ℂ →L[ℝ] E) (z : ℂ) :
    realAffineProfile c A z = c+A z := rfl

omit [CompleteSpace E] in
theorem realAffineProfile_lipschitz (c : E) (A : ℂ →L[ℝ] E) :
    LipschitzWith ‖A‖₊ (realAffineProfile c A) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (c+A x) (c+A y) ≤ ‖A‖*dist x y
  rw [dist_add_left,dist_eq_norm,← map_sub,dist_eq_norm]
  exact A.le_opNorm (x-y)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_SchauderBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open MeasureTheory
open Set Filter Function
open MeasureTheory
open scoped Topology
open Finset
open scoped ContDiff Classical
open scoped BoundedContinuousFunction
open Topology
open scoped NNReal

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def cutoffCRRemainder (χ : ℂ → ℝ) (A : ℂ → E →L[ℝ] E) (u : ℂ → E) (z : ℂ) : E :=
  fderiv ℝ χ z Complex.I • u z - Complex.I • (fderiv ℝ χ z 1 • u z) -
    A z (fderiv ℝ χ z 1 • u z)

def scalarDirection (χ : ℂ → ℝ) (w : ℂ) (z : ℂ) : ℝ := fderiv ℝ χ z w

end

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_GradientLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity








open scoped Topology ContDiff
open Set Filter Function







open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function







open scoped Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function
section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def rescaleMap (u : ℂ → F) (x : ℂ) (r : ℝ) : ℂ → F := fun z => u (x+r • z)

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function
open HigherDimensionalBallPacking.Rigidity

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FramedCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open MeasureTheory
open Set Filter Function
open MeasureTheory
open scoped Topology
open Finset
open scoped ContDiff Classical
open scoped BoundedContinuousFunction
open Topology
open scoped NNReal

namespace HigherDimensionalBallPacking.Rigidity.FramedCR
open HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Filter Function
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

def HasFrame (J : E →L[ℝ] E) : Prop :=
  ∃ S : E ≃L[ℝ] E, ∀ v, S (J v)=Complex.I • S v

def centeredFrame  (S : E ≃L[ℝ] E) (p : E)
    (u : ℂ → E) : ℂ → E := fun z => S (u z-p)

def frozenCoefficient  (S : E ≃L[ℝ] E) (J : (E →L[ℝ] E))
    (B : ℂ → (E →L[ℝ] E)) : ℂ → (E →L[ℝ] E) := fun z =>
      S.toContinuousLinearMap.comp ((B z-J).comp S.symm.toContinuousLinearMap)

def frameConjugation  (S : E ≃L[ℝ] E) : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ (E) (E) (E) S.toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℝ (E) (E) (E)).flip S.symm.toContinuousLinearMap)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
@[simp] theorem frameConjugation_apply [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : E ≃L[ℝ] E) (B : (E →L[ℝ] E)) :
    frameConjugation S B=S.toContinuousLinearMap.comp (B.comp S.symm.toContinuousLinearMap) := rfl

end HigherDimensionalBallPacking.Rigidity.FramedCR
open scoped ContDiff Topology
open Set Filter Function

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_TangentLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

def tangentMap (J K : E →L[ℝ] E) : (E × E) →L[ℝ] (E × E) :=
  (J.comp (ContinuousLinearMap.fst ℝ E E)).prod
    (K.comp (ContinuousLinearMap.fst ℝ E E)+J.comp (ContinuousLinearMap.snd ℝ E E))

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
@[simp] theorem tangentMap_apply [FiniteDimensional ℂ E] [CompleteSpace E]
    (J K : E →L[ℝ] E) (a b : E) :
    tangentMap J K (a,b)=(J a,K a+J b) := rfl

def shearEquiv (C : E →L[ℝ] E) : (E × E) ≃L[ℝ] (E × E) where
  toFun v := (v.1,v.2+C v.1)
  invFun v := (v.1,v.2-C v.1)
  left_inv := by intro v; simp
  right_inv := by intro v; simp
  map_add' := by intro v w; simp only [Prod.fst_add,Prod.snd_add,map_add,Prod.mk_add_mk];congr 1;abel
  map_smul' := by intro r v; simp only [Prod.smul_fst,Prod.smul_snd,map_smul,smul_add,Prod.smul_mk,RingHom.id_apply]
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (C.continuous.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (C.continuous.comp continuous_fst))

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

def tangentField (H : ℝ × E → E →L[ℝ] E) : ℝ × (E × E) → (E × E) →L[ℝ] (E × E) :=
  fun y => tangentMap (H (y.1,y.2.1)) (fderiv ℝ H (y.1,y.2.1) (0,y.2.2))

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

def tangentCurve (u : ℂ → E) : ℂ → E × E := fun z => (u z,fderiv ℝ u z 1)

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function





open scoped ContDiff Topology
open Set Filter Function

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

def tangentCurveDir (a : ℂ) (u : ℂ → E) : ℂ → E × E := fun z => (u z,fderiv ℝ u z a)

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

def standardCurl (u : ℂ → E) (z : ℂ) : E :=
  fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1

def curlLinear : (ℂ →L[ℝ] E) →L[ℝ] E :=
  ContinuousLinearMap.apply ℝ E Complex.I-
    ((Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ).comp
      (ContinuousLinearMap.apply ℝ E 1)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
@[simp] theorem curlLinear_apply [FiniteDimensional ℂ E] [CompleteSpace E]
    (D : ℂ →L[ℝ] E) :
    curlLinear D=D Complex.I-Complex.I • D 1 := rfl

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem density_tsupport_subset [NormedSpace ℝ E] [CompleteSpace E]
    (R : ℝ) (f : ℂ → E)
    (hf : ∀ z, R < ‖z‖ → f z=0) : tsupport f ⊆ Metric.closedBall (0:ℂ) R := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  by_contra hn
  exact hz (hf z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hn))

theorem density_compact_support (R : ℝ) (f : ℂ → E)
    (hf : ∀ z, R < ‖z‖ → f z=0) : HasCompactSupport f :=
  (isCompact_closedBall (0:ℂ) R).of_isClosed_subset (isClosed_tsupport _) (density_tsupport_subset R f hf)

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function








open scoped ContDiff Topology
open Set Filter Function

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

 theorem inverseField_continuous {a : ℂ → E →L[ℝ] E} (ha : Continuous a)
    (hi : ∀ z, (a z).IsInvertible) : Continuous (fun z => (a z).inverse) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact ((hi z).contDiffAt_map_inverse (n := ∞)).continuousAt.comp ha.continuousAt

 theorem inverseField_bound (R : ℝ) {a : ℂ → E →L[ℝ] E} (ha : Continuous a)
    (hi : ∀ z, (a z).IsInvertible) (hout : ∀ z, R<‖z‖ → a z=ContinuousLinearMap.id ℝ E) :
    ∃ C : ℝ, 0<C ∧ ∀ z, ‖(a z).inverse‖≤C := by
  have hc := inverseField_continuous ha hi
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C ‖ContinuousLinearMap.id ℝ E‖+1,by positivity,?_⟩
  intro z
  by_cases hz : ‖z‖≤R
  · exact (hC z (by simpa using hz)).trans ((le_max_left _ _).trans (by linarith))
  · rw [hout z (lt_of_not_ge hz),ContinuousLinearMap.inverse_id]
    exact (le_max_right _ _).trans (by linarith)

 omit [CompleteSpace E] in
 theorem inverseField_sub {a b : E →L[ℝ] E} (ha : a.IsInvertible) (hb : b.IsInvertible) :
    a.inverse-b.inverse=a.inverse.comp ((b-a).comp b.inverse) := by
  ext v
  simp only [sub_apply,ContinuousLinearMap.comp_apply,map_sub,
    hb.self_apply_inverse,ha.inverse_apply_self]

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end


