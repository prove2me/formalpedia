-- Prove2me | Definitions.Def_OAIQ15Sf005
-- name    : OAIQ15Sf005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:21:08.273392+00:00
-- url     : https://prove2.me/theorems/2cd2d544-91fc-4a63-bd28-3f78b89ff46d
-- title:
--   Definitions bundle OAIQ15Sf005 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 6 definitions, 4 instances and 3 theorems. The definitions and types are `OAI.KaplanskyConsequences.ProperClosedIdeal`, `OAI.KaplanskyConsequences.commutatorSpan`, `OAI.KaplanskyConsequences.complexify`, `OAI.KaplanskyConsequences.positiveCone`, `OAI.KaplanskyConsequences.selfCommutator`, `OAI.KaplanskyConsequences.tracialStatePullback`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: [`Kaplansky_Quotient_Extraction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Quotient/Extraction.lean), [`Kaplansky_Quotient_MaximalClosedIdeal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Quotient/MaximalClosedIdeal.lean), [`Kaplansky_Quotient_TracePullback`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Quotient/TracePullback.lean).
--
--   **Imports.** It imports the published bundle `Def_KaplanskyStableFiniteness`.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.KaplanskyConsequences.Regular.polynomial_average_small`, `OAI.KaplanskyConsequences.separable_extraction`, `OAI.KaplanskyConsequences.simple_stable_tensor_counterexample_exists`, `OAI.KaplanskyConsequences.simple_stablyFinite_traceless_exists` and `OAI.KaplanskyConsequences.trace_free_stably_finite_exists`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness

section
-- module Solutions.OAIQ15_Sf.Compat
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
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_Extraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace KaplanskyConsequences
open scoped ComplexOrder BigOperators
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

def selfCommutator (x : A) : selfAdjoint A :=
  ⟨star x * x - x * star x, (IsSelfAdjoint.star_mul_self x).sub (IsSelfAdjoint.mul_star_self x)⟩

def commutatorSpan (A : Type*) [CStarAlgebra A] : Submodule ℝ (selfAdjoint A) :=
  Submodule.span ℝ (Set.range (selfCommutator (A := A)))

def positiveCone (A : Type*) [CStarAlgebra A] : Set (selfAdjoint A) :=
  {x | 0 ≤ (x : A)}

def complexify (g : (selfAdjoint A) →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ :=
  Module.Dual.extendRCLike (𝕜 := ℂ) (g.comp (selfAdjointPart ℝ))

end KaplanskyConsequences

end
end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_MaximalClosedIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences
open Topology
open scoped CStarAlgebra
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def ProperClosedIdeal (S : NonUnitalStarSubalgebra ℂ A) : Prop :=
  (∀ a b : A, b ∈ S → a*b ∈ S) ∧ (∀ a b : A, a ∈ S → a*b ∈ S) ∧
    IsClosed (S : Set A) ∧ (1:A) ∉ S

end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_TracePullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def tracialStatePullback (f : A →⋆ₐ[ℂ] B) (τ : TracialState B) : TracialState A where
  functional := PositiveLinearMap.mk₀
    (τ.functional.toLinearMap.comp f.toAlgHom.toLinearMap)
    (fun x hx => by
      change 0 ≤ τ.functional (f x)
      exact τ.functional.map_nonneg (by simpa only [map_zero] using (OrderHomClass.mono f hx)))
  normalized := by change τ.functional (f 1) = 1; rw [map_one,τ.normalized]
  tracial a b := by
    change τ.functional (f (a*b)) = τ.functional (f (b*a))
    simp only [map_mul f]
    exact τ.tracial (f a) (f b)


end KaplanskyConsequences

end

end OAI
end


