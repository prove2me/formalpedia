-- Prove2me | Definitions.Def_OAIQ4Cc001
-- name    : OAIQ4Cc001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T04:38:17.023492+00:00
-- url     : https://prove2.me/theorems/7d7a3528-5e02-4817-8698-d51f7b05b242
-- title:
--   Definitions bundle OAIQ4Cc001 of the split of OpenAI, The crossing number of complete graphs
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Paper170.complete_graph_crossing_number`, carved from OpenAI's openai/math development (OpenAI, *The crossing number of complete graphs*, OpenAI Math Release, September 23, 2026, result family 165, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 17 definitions, 4 instances and 7 theorems. The definitions and types are `OAI.Zarankiewicz.Bounded`, `OAI.Zarankiewicz.boundedSpace`, `OAI.Zarankiewicz.chordEndpointPairing`, `OAI.Zarankiewicz.cyclicIndex`, `OAI.Zarankiewicz.lowerTriangle`, `OAI.Zarankiewicz.mulRoot`, `OAI.Zarankiewicz.orderSign`, `OAI.Zarankiewicz.parameterNeighborhood`, `OAI.Zarankiewicz.positiveIndicator`, `OAI.Zarankiewicz.sideAfter`, `OAI.Zarankiewicz.sideBefore`, `OAI.Zarankiewicz.slopeSign`, `OAI.Zarankiewicz.stepAt`, `OAI.Zarankiewicz.stepEvent`, `OAI.Zarankiewicz.triangleRelabel`, `OAI.Zarankiewicz.twoTriangle`, `OAI.Zarankiewicz.upperTriangle`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/CompleteCrossing, in whole or in part: [`Crossing_AffineSideEvents`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/Crossing/AffineSideEvents.lean), [`Crossing_Bivariate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/Crossing/Bivariate.lean), [`Crossing_ChordPairing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/Crossing/ChordPairing.lean), [`Crossing_GraphWalkTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/Crossing/GraphWalkTrace.lean), [`Crossing_ParameterNeighborhoods`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/Crossing/ParameterNeighborhoods.lean), [`Crossing_PeriodicPolygon`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/Crossing/PeriodicPolygon.lean), [`Crossing_PolynomialKernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/Crossing/PolynomialKernel.lean), [`Crossing_StepEvents`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/Crossing/StepEvents.lean), [`Crossing_TwoTriangleIndices`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/Crossing/TwoTriangleIndices.lean), [`Crossing_UniqueWalkPassage`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/CompleteCrossing/Crossing/UniqueWalkPassage.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ4Cc002`.
-- source:
--   OpenAI, The crossing number of complete graphs, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 165; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-crossing-number-of-complete-graphs-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/CompleteCrossing at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ4_Cc.Compat
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
-- module Solutions.OAIQ4_Cc.Crossing_StepEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def stepAt (root before after t : ℝ) : ℝ := if t < root then before else after

def stepEvent {n : ℕ} (r lo hi : Fin n → ℝ) (i : Fin n) : ℝ :=
  if 0 < r i ∧ r i < 1 then
    (hi i-lo i) * ∏ j, if j=i then 1 else stepAt (r j) (lo j) (hi j) (r i)
  else 0

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_AffineSideEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def positiveIndicator (x : ℝ) : ℝ := if 0 < x then 1 else 0

def slopeSign (b : ℝ) : ℝ := if 0 < b then 1 else -1

def sideBefore (b : ℝ) : ℝ := if 0 < b then 0 else 1

def sideAfter (b : ℝ) : ℝ := if 0 < b then 1 else 0

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PolynomialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

def Bounded (k : ℕ) (p : PolynomialModule ℝ W) : Prop :=
  ∀ n, k ≤ n → p.coeff n = 0

theorem bounded_zero (k : ℕ) : Bounded k (0 : PolynomialModule ℝ W) := by
  intro n hn
  simp

theorem bounded_add {k : ℕ} {p q : PolynomialModule ℝ W}
    (hp : Bounded k p) (hq : Bounded k q) : Bounded k (p + q) := by
  intro n hn
  simp [hp n hn, hq n hn]

def mulRoot (t : ℝ) (p : PolynomialModule ℝ W) : PolynomialModule ℝ W :=
  (Polynomial.X - Polynomial.C t) • p

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_Bivariate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule

def boundedSpace (k : ℕ) : Submodule ℝ (PolynomialModule ℝ ℝ) where
  carrier := {p | Bounded k p}
  zero_mem' := bounded_zero k
  add_mem' := bounded_add
  smul_mem' := by
    intro c p hp n hn
    change c • p.coeff n = 0
    rw [hp n hn, smul_zero]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ChordPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def orderSign (a b : ℝ) : ℝ := if a < b then 1 else if b < a then -1 else 0

def chordEndpointPairing (a b c d : ℝ) : ℝ :=
  (orderSign a c-orderSign a d-orderSign b c+orderSign b d)/2

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_UniqueWalkPassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

theorem walk_dart_parameters {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (d : G.Dart) (hd : d ∈ p.darts) :
    ∃ i : ℕ, i < p.length ∧ d.fst=p.getVert i ∧ d.snd=p.getVert (i+1) := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hd
  have he := SimpleGraph.Walk.darts_getElem_eq_getVert (p:=p) i.val i.isLt
  have hd' := hi.symm.trans he
  refine ⟨i.val,by simpa only [p.length_darts] using i.isLt,?_,?_⟩
  · exact congrArg (fun r : G.Dart => r.fst) hd'
  · exact congrArg (fun r : G.Dart => r.snd) hd'

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_GraphWalkTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem walk_dart_at {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    (i : ℕ) (hi : i < p.length) :
    ∃ d : G.Dart, d ∈ p.darts ∧ d.fst=p.getVert i ∧ d.snd=p.getVert (i+1) := by
  have hi' : i < p.darts.length := by simpa only [p.length_darts] using hi
  refine ⟨p.darts[i],List.getElem_mem hi',?_,?_⟩
  · rw [SimpleGraph.Walk.darts_getElem_eq_getVert]
  · rw [SimpleGraph.Walk.darts_getElem_eq_getVert]

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_ParameterNeighborhoods
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz

def parameterNeighborhood (t : unitInterval) (δ : ℝ) : Set unitInterval :=
  {s | |s.val-t.val| < δ}

end Zarankiewicz

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_PeriodicPolygon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Zarankiewicz

def cyclicIndex (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n := ⟨i%n,Nat.mod_lt i hn⟩

end Zarankiewicz

end

end OAI
end

section
-- module Solutions.OAIQ4_Cc.Crossing_TwoTriangleIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Zarankiewicz
open Finset

def lowerTriangle (s : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (s+1)) ×ˢ (Icc 1 (s+1))).filter (fun z => z.2 < z.1)

def upperTriangle (s : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc (s+2) (2*s+1)) ×ˢ (Icc (s+2) (2*s+1))).filter (fun z => z.1 < z.2)

def twoTriangle (s : ℕ) : Finset (ℕ × ℕ) := lowerTriangle s ∪ upperTriangle s

def triangleRelabel (s k : ℕ) : ℕ := if k ≤ s then s+1+k else k-s+1

end Zarankiewicz

end OAI
end


