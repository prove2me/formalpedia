-- Prove2me | Definitions.Def_OAIQ7T1000
-- name    : OAIQ7T1000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T08:34:47.239224+00:00
-- url     : https://prove2.me/theorems/ac8159f1-ba5c-4289-8bcb-1accc880e937
-- title:
--   Definitions bundle OAIQ7T1000 of the split of OpenAI, Nagata's conjecture for plane curves
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Nagata.Workers.W30.exists_positive_degree_equation_of_homogeneous_cycle`, carved from OpenAI's openai/math development (OpenAI, *Nagata's conjecture for plane curves*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 3 definitions, 4 instances and 6 theorems. The definitions and types are `OAI.Nagata.Workers.W30.cycleEquation`, `OAI.Nagata.Workers.W30.principalIdealAssociate`, `OAI.Nagata.Workers.W30.supportAssociateDecidableEq`.
--
--   **Sources.** They come from these modules of lean/OAI/AlgebraicGeometry, in whole or in part: [`PlaneCurves_Factorization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/Factorization.lean), [`PlaneCurves_IdealCycles`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/IdealCycles.lean).
--
--   **Imports.** It imports the published bundle `Def_Nagata`.
--
--   **Imported by** (directly, in this split): the proof of `OAI.Nagata.Workers.W30.exists_positive_degree_equation_of_homogeneous_cycle`.
-- source:
--   OpenAI, Nagata's conjecture for plane curves, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nagatas-Conjecture-for-Plane-Curves-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/AlgebraicGeometry at commit adc7f12

import Mathlib
import Definitions.Def_Nagata

section
-- module Solutions.OAIQ7_T1.Compat
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
-- module Solutions.OAIQ7_T1.PlaneCurves_Factorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Homogeneous factorization and height-one prime generators
-/

section

namespace Nagata.Workers.W30

open UniqueFactorizationMonoid

noncomputable section

@[simp] theorem associatePrincipalIdeal_mk (F : TernaryPolynomial) :
    associatePrincipalIdeal (Associates.mk F) = Ideal.span {F} := rfl

end
end Nagata.Workers.W30

end

end OAI
end

section
-- module Solutions.OAIQ7_T1.PlaneCurves_IdealCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reconstruction of effective homogeneous prime ideal cycles
-/

section

/-! Reconstruct an equation from any finite effective cycle of prime associate classes. -/
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
noncomputable section

/-- Choose an actual polynomial representing the product of prime classes with weights. -/
def cycleEquation (D : Associates TernaryPolynomial →₀ ℕ) : TernaryPolynomial :=
  Classical.choose (Associates.mk_surjective (D.prod fun a n => a ^ n))

@[simp] theorem cycleEquation_mk (D : Associates TernaryPolynomial →₀ ℕ) :
    Associates.mk (cycleEquation D) = D.prod (fun a n => a ^ n) :=
  Classical.choose_spec (Associates.mk_surjective (D.prod fun a n => a ^ n))

end
end Nagata.Workers.W30

end

section

/-! Zero-cycle exclusion and multiplicities of nonreduced equations. -/
namespace Nagata.Workers.W30

@[simp] theorem equationIdealCycle_one : equationIdealCycle (1 : TernaryPolynomial) = 0 := by
  simp only [equationIdealCycle, equationMultiplicity, Associates.mk_one,
    factorization_one, Finsupp.mapDomain_zero]

end Nagata.Workers.W30

end

section

/-! Exact divisibility meaning of prime ideal cycle support. -/
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
noncomputable section
local instance supportAssociateDecidableEq : DecidableEq (Associates TernaryPolynomial) := Classical.decEq _

end
end Nagata.Workers.W30

end

section

/-! Reconstructing actual finite cycles of nonzero prime principal ideals. -/
namespace Nagata.Workers.W30
noncomputable section

/-- Associate class of a principal ideal; unsupported nonprincipal ideals map to zero. -/
def principalIdealAssociate (I : Ideal TernaryPolynomial) : Associates TernaryPolynomial := by
  classical
  exact if h : I.IsPrincipal then (Ideal.associatesEquivIsPrincipal TernaryPolynomial).symm ⟨I,h⟩
    else 0

end
end Nagata.Workers.W30

end

end OAI
end


