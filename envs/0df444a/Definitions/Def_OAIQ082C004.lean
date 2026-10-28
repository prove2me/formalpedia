-- Prove2me | Definitions.Def_OAIQ082C004
-- name    : OAIQ082C004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:22:40.262538+00:00
-- url     : https://prove2.me/theorems/05c7c01b-220f-4b94-918b-15a6bffe6fc6
-- title:
--   Definitions bundle OAIQ082C004 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 381 declarations of OpenAI's Lean: 165 definitions, 23 inductive types or structures, 25 instances and 168 theorems. The definitions and types are `OAI.BinPackingGap.GraphPackingPoolRuntime.tallyPolynomial`, `OAI.BinPackingGap.GraphPackingRegisters.Extra`, `OAI.BinPackingGap.GraphPreparationMachine.fieldIndices`, `OAI.BinPackingGap.GraphPreparationMachine.fieldSlots`, `OAI.BinPackingGap.GraphPreparationMachine.tokenIndices`, `OAI.BinPackingGap.GraphPreparationMachine.tokenSlots`, `OAI.BinPackingGap.IntervalCoverage.ShiftData`, `OAI.BinPackingGap.IntervalCoverage.ShiftData.activeTests`, `OAI.BinPackingGap.IntervalCoverage.ShiftData.instDecidableEq`, `OAI.BinPackingGap.IntervalCoverage.coverageCount`, `OAI.BinPackingGap.IntervalCoverage.coverageSet`, `OAI.BinPackingGap.IntervalCoverage.prefixCount`, `OAI.BinPackingGap.IntervalCoverage.prefixSet`, `OAI.BinPackingGap.InventoryData.templateFiberBoolEquiv`, `OAI.BinPackingGap.LabelConservation.exports`, `OAI.BinPackingGap.LabelConservation.prefixItems`, `OAI.BinPackingGap.LiteralSlotGraphMachine.Control`, `OAI.BinPackingGap.LiteralSlotGraphMachine.RawLiteral`, `OAI.BinPackingGap.LiteralSlotGraphMachine.Tape`, `OAI.BinPackingGap.LiteralSlotGraphMachine.Tape.enumList`, `OAI.BinPackingGap.LiteralSlotGraphMachine.bodyControl`, `OAI.BinPackingGap.LiteralSlotGraphMachine.bodyEdge`, `OAI.BinPackingGap.LiteralSlotGraphMachine.branchCost`, `OAI.BinPackingGap.LiteralSlotGraphMachine.comparedControl`, `OAI.BinPackingGap.LiteralSlotGraphMachine.comparisonResult`, `OAI.BinPackingGap.LiteralSlotGraphMachine.countHeaderResult`, `OAI.BinPackingGap.LiteralSlotGraphMachine.counterHead`, `OAI.BinPackingGap.LiteralSlotGraphMachine.initialControl`, `OAI.BinPackingGap.LiteralSlotGraphMachine.mainTapes`, `OAI.BinPackingGap.LiteralSlotGraphMachine.nextRemaining`, `OAI.BinPackingGap.LiteralSlotGraphMachine.nextSlot`, `OAI.BinPackingGap.LiteralSlotGraphMachine.outerBodyControl`, `OAI.BinPackingGap.LiteralSlotGraphMachine.outerControl`, `OAI.BinPackingGap.LiteralSlotGraphMachine.pairCost`, `OAI.BinPackingGap.LiteralSlotGraphMachine.rowControl`, `OAI.BinPackingGap.LiteralSlotGraphMachine.rowEdges`, `OAI.BinPackingGap.LiteralSlotGraphMachine.rowStartControl`, `OAI.BinPackingGap.LiteralSlotGraphMachine.startRow`, `OAI.BinPackingGap.LiteralSlotGraphMachine.suffixEdges`, `OAI.BinPackingGap.LiteralSlotGraphMachine.twoTapes` and 148 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Arithmetic_GraphPackingRegisters`, `BinPacking_Arithmetic_PackingRegisterFrame`, `BinPacking_Arithmetic_PackingRegisterUpdate`, `BinPacking_Hardness_LiteralSlotGraphEnumeration`, `BinPacking_Inventory_CurrentMatches`, `BinPacking_Inventory_LabelConservation`, `BinPacking_Inventory_LocalCompletionCoverage`, `BinPacking_Inventory_PackingConstantPool`, `BinPacking_Inventory_PackingExclusions`, `BinPacking_Inventory_SpeciesAllocation`, `BinPacking_Machines_GraphPackingGlobalExecution`, `BinPacking_Machines_GraphPackingJobList`, `BinPacking_Machines_GraphPackingMachine`, `BinPacking_Machines_GraphPackingPreparationFinish`, `BinPacking_Machines_GraphPackingVerticesBound`, `BinPacking_Machines_MachineBoundedIteration`, `BinPacking_Machines_MachineControlEmbedding`, `BinPacking_Machines_MachineKeepDecisionTyped`, `BinPacking_Machines_PackingCountedProgram`, `BinPacking_Machines_PackingJobLoop`, `BinPacking_Machines_PackingPoolMachine`, `BinPacking_Machines_PackingPowerProgram`, `BinPacking_Packing_K4Graph`, `BinPacking_Packing_LocalTemplateBases`, `BinPacking_Packing_PackingGapDefinitions`, `BinPacking_Packing_PackingScalar`, `BinPacking_Packing_PrimaryLoss`, `BinPacking_Search_SearchFinalizeMachine`, `BinPacking_Search_SearchFixedReplaceMachine`, `BinPacking_Search_SearchInitialItemsMachine`, `BinPacking_Search_SearchInitialShapeMachine`, `BinPacking_Search_SearchInitializeEncoding`, `BinPacking_Search_SearchPrepareMachine`, `BinPacking_Search_SearchStageMachines`, `BinPacking_Search_SearchUpdateMachine`, `BinPacking_Trees_CompletionGeometry`, `BinPacking_Trees_TestGeometry`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ082C009`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std

section
-- module Solutions.OAIQ082_BP.Compat
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
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_K4Graph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open scoped BigOperators

namespace BinPackingGap

variable {V : Type*} [Fintype V] [DecidableEq V]

def thresholdCover (d : ℕ) (xplus : V → ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => (d : ℝ) / 8 < (xplus v : ℝ)

def largePlus (d K : ℕ) (xplus : V → ℕ) : Finset V := by
  classical
  exact Finset.univ.filter fun v => (d : ℝ) - 6 * K ≤ (xplus v : ℝ)

end BinPackingGap

end

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PrimaryLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.PrimaryLoss

open scoped BigOperators

variable {ι : Type*} [Fintype ι] {N : ℕ}

def binItems (f : ι → Fin N) (b : Fin N) : Finset ι :=
  Finset.univ.filter fun i => f i = b

abbrev fiber (f : ι → Fin N) (b : Fin N) : Finset ι := binItems f b

def itemsIn (f : ι → Fin N) (s : Finset (Fin N)) : Finset ι :=
  Finset.univ.filter fun i => f i ∈ s

def binPrimary (f : ι → Fin N) (p : ι → ℤ) (b : Fin N) : ℤ :=
  ∑ i ∈ binItems f b, p i

def fullBins (f : ι → Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun b => (fiber f b).card = 5

def nonfullBins (f : ι → Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun b => (fiber f b).card < 5

def nonfullItems (f : ι → Fin N) : Finset ι := itemsIn f (nonfullBins f)

def negativeFullBins (f : ι → Fin N) (p : ι → ℤ) : Finset (Fin N) :=
  (fullBins f).filter fun b => binPrimary f p b < 0

def outsideZeroFullItems (f : ι → Fin N) (p : ι → ℤ) : Finset ι :=
  Finset.univ.filter fun i =>
    ¬ ((fiber f (f i)).card = 5 ∧ binPrimary f p (f i) = 0)

end BinPackingGap.PrimaryLoss

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

open scoped BigOperators

def coordinateTotal (w : Fin 5 → ℚ) : ℚ := ∑ i, w i

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_CompletionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

def completion (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ) : ℚ :=
  b - (if short then delta else 0) - globalLen - localLen

def completionInterval (b : ℚ) (short : Bool) (globalLen localLen delta : ℚ) :
    Set ℚ := Set.Ico (completion b short globalLen localLen delta) b

@[simp] theorem completion_false (b globalLen localLen delta : ℚ) :
    completion b false globalLen localLen delta = b - globalLen - localLen := by
  simp [completion]

@[simp] theorem completion_true (b globalLen localLen delta : ℚ) :
    completion b true globalLen localLen delta = b - delta - globalLen - localLen := by
  simp [completion]

@[simp] theorem mem_completionInterval (b : ℚ) (short : Bool)
    (globalLen localLen delta a : ℚ) :
    a ∈ completionInterval b short globalLen localLen delta ↔
      completion b short globalLen localLen delta ≤ a ∧ a < b := Iff.rfl

@[simp] theorem completion_long_zero_lengths (b delta : ℚ) :
    completion b false 0 0 delta = b := by simp

@[simp] theorem completion_short_zero_lengths (b delta : ℚ) :
    completion b true 0 0 delta = b - delta := by simp

@[simp] theorem completionInterval_long_zero_lengths (b delta : ℚ) :
    completionInterval b false 0 0 delta = ∅ := by
  simp [completionInterval]

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_CurrentMatches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.IntervalCoverage

variable {ι κ τ α : Type*} [LinearOrder α]

def prefixSet [Fintype ι] (f : ι → α) (a : α) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => f i ≤ a

def prefixCount [Fintype ι] (f : ι → α) (a : α) : ℕ := (prefixSet f a).card

def coverageSet [Fintype ι] (h b : ι → α) (a : α) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => h i ≤ a ∧ a < b i

def coverageCount [Fintype ι] (h b : ι → α) (a : α) : ℕ :=
  (coverageSet h b a).card

@[simp] theorem mem_prefixSet [Fintype ι] (f : ι → α) (a : α) (i : ι) :
    i ∈ prefixSet f a ↔ f i ≤ a := by
  classical
  simp [prefixSet]

@[simp] theorem mem_coverageSet [Fintype ι] (h b : ι → α) (a : α) (i : ι) :
    i ∈ coverageSet h b a ↔ h i ≤ a ∧ a < b i := by
  classical
  simp [coverageSet]

structure ShiftData (Copy Test : Type*) (d : ℕ) (Coordinate : Type*)
    [LinearOrder Coordinate] where
  baseline : Copy → Coordinate
  left : Test → Coordinate
  right : Test → Coordinate
  designated : (Test × Fin d) ↪ Copy
  baseline_designated : ∀ q, baseline (designated q) = right q.1
  left_le_right : ∀ t, left t ≤ right t

namespace ShiftData

variable {d : ℕ} (D : ShiftData ι τ d α)

local instance instDecidableEq : DecidableEq ι := Classical.decEq ι

def activeTests [Fintype τ] (a : α) : Finset τ := by
  classical
  exact Finset.univ.filter fun t => D.left t ≤ a ∧ a < D.right t

@[simp] theorem mem_activeTests [Fintype τ] (a : α) (t : τ) :
    t ∈ D.activeTests a ↔ D.left t ≤ a ∧ a < D.right t := by
  classical
  simp [activeTests]

theorem activeTests_card [Fintype τ]
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (Set.Ico (D.left s) (D.right s)) (Set.Ico (D.left t) (D.right t)))
    (a : α) :
    (D.activeTests a).card = if ∃ t, D.left t ≤ a ∧ a < D.right t then 1 else 0 := by
  classical
  have hle : (D.activeTests a).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro s hs t ht
    by_contra hst
    exact Set.disjoint_left.mp (hdisjoint s t hst)
      (D.mem_activeTests a s |>.mp hs) (D.mem_activeTests a t |>.mp ht)
  split_ifs with hex
  · obtain ⟨t, ht⟩ := hex
    have hpos := Finset.card_pos.mpr ⟨t, (D.mem_activeTests a t).mpr ht⟩
    omega
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact hex ⟨t, (D.mem_activeTests a t).mp ht⟩

end ShiftData

end BinPackingGap.IntervalCoverage

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_LabelConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

namespace LabelConservation

open scoped BigOperators

variable {n : ℕ}
variable {T A R D : Type*}
variable [Fintype T] [Fintype A] [Fintype R] [Fintype D]
variable [DecidableEq A] [DecidableEq R] [DecidableEq D]

def prefixItems (label : A → Fin n) (h : ℕ) : Finset A :=
  Finset.univ.filter fun x => (label x).val < h

def exports (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R) (h : ℕ) : Finset T :=
  Finset.univ.filter fun t =>
    (labelR (role t)).val < h ∧ ¬ (labelA (anchor t)).val < h

omit [DecidableEq A] in
@[simp] theorem prefixItems_zero (label : A → Fin n) : prefixItems label 0 = ∅ := by
  simp [prefixItems]

omit [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] in
@[simp] theorem exports_zero (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R) : exports labelA labelR anchor role 0 = ∅ := by
  simp [exports]

end LabelConservation
end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TestGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

theorem disjoint_of_endpoint_lt {a b c d : ℚ} (h : b < c) :
    Disjoint (Set.Icc a b) (Set.Icc c d) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (not_le_of_gt h) (hy.1.trans hx.2)

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_LocalCompletionCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PartialAllocation

theorem exists_equiv_extending_embeddings
    {I J S : Type*} [Fintype I] [Fintype J]
    (f : S ↪ I) (g : S ↪ J)
    (hcard : Fintype.card I = Fintype.card J) :
    ∃ e : I ≃ J, ∀ s, e (f s) = g s := by
  classical
  let assigned : Set.range f ≃ Set.range g :=
    (Equiv.ofInjective f f.injective).symm.trans (Equiv.ofInjective g g.injective)
  have hremaining : Fintype.card ↥((Set.range f)ᶜ) =
      Fintype.card ↥((Set.range g)ᶜ) := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set, hcard,
      Fintype.card_congr assigned]
  let remaining : ↥((Set.range f)ᶜ) ≃ ↥((Set.range g)ᶜ) :=
    Fintype.equivOfCardEq hremaining
  let e : I ≃ J := (Equiv.Set.sumCompl (Set.range f)).symm.trans
    ((Equiv.sumCongr assigned remaining).trans (Equiv.Set.sumCompl (Set.range g)))
  refine ⟨e, ?_⟩
  intro s
  have hfs : f s ∈ Set.range f := ⟨s, rfl⟩
  change ((Equiv.Set.sumCompl (Set.range g))
    ((Equiv.sumCongr assigned remaining)
      ((Equiv.Set.sumCompl (Set.range f)).symm (f s)))) = g s
  rw [Equiv.Set.sumCompl_symm_apply_of_mem hfs]
  simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumCompl_apply_inl]
  change ((Equiv.ofInjective g g.injective)
    ((Equiv.ofInjective f f.injective).symm ⟨f s, hfs⟩)).val = g s
  rw [Equiv.ofInjective_symm_apply]
  rfl

end BinPackingGap.PartialAllocation

namespace BinPackingGap.LocalCompletionCoverage

open InventoryData IntervalCoverage

theorem card_le_coverage {ι κ : Type*} [Fintype ι]
    (h baseline : ι → ℚ) (a : ℚ) (s : Finset κ) (f : κ → ι)
    (hf : Function.Injective f)
    (hc : ∀ x ∈ s, h (f x) ≤ a ∧ a < baseline (f x)) :
    s.card ≤ coverageCount h baseline a := by
  classical
  exact Finset.card_le_card_of_injOn f
    (fun x hx => (mem_coverageSet h baseline a (f x)).mpr (hc x hx))
    (fun _ _ _ _ hxy => hf hxy)

end BinPackingGap.LocalCompletionCoverage

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_PackingExclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

def excludedPositions {T Pos : Type*} [Fintype Pos]
    (selected : Finset T) (I : T → Pos → Prop) : Finset Pos := by
  classical
  exact Finset.univ.filter fun r => ∃ t ∈ selected, I t r

@[simp] theorem mem_excludedPositions {T Pos : Type*} [Fintype Pos]
    (selected : Finset T) (I : T → Pos → Prop) {r : Pos} :
    r ∈ excludedPositions selected I ↔ ∃ t ∈ selected, I t r := by
  classical
  simp [excludedPositions]

def excludedRepetitions {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) : Finset (Fin R) := by
  classical
  exact Finset.univ.filter fun j => (e, j) ∈ bad

def nonexcludedRepetitions {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) : Finset (Fin R) := by
  classical
  exact Finset.univ.filter fun j => (e, j) ∉ bad

@[simp] theorem mem_excludedRepetitions {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) {j : Fin R} :
    j ∈ excludedRepetitions bad e ↔ (e, j) ∈ bad := by
  classical
  simp [excludedRepetitions]

@[simp] theorem mem_nonexcludedRepetitions {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) {j : Fin R} :
    j ∈ nonexcludedRepetitions bad e ↔ (e, j) ∉ bad := by
  classical
  simp [nonexcludedRepetitions]

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_PackingRegisterFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingRegisterFrame

variable {Local Global K : Type}

def withScratch (register : Local ↪ Global) : (Local ⊕ Fin 6) ↪ (Global ⊕ Fin 6) where
  toFun
    | .inl r => .inl (register r)
    | .inr i => .inr i
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all only [Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl]
    exact register.injective h

def localSlots (slot : (Global ⊕ Fin 6) ↪ K) (register : Local ↪ Global) :
    (Local ⊕ Fin 6) ↪ K := (withScratch register).trans slot

end BinPackingGap.PackingRegisterFrame

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_MachineControlEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.MachineControlEmbedding

open Turing

structure Control (σ τ : Type) where
  put : σ → τ
  get : τ → σ
  get_put : ∀ s, get (put s) = s

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

def statement (control : Control σ τ) (labels : Λ → Λ') (exit : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' τ
  | .push k f next => .push k (fun s => f (control.get s))
      (statement control labels exit next)
  | .peek k f next => .peek k (fun s bit => control.put (f (control.get s) bit))
      (statement control labels exit next)
  | .pop k f next => .pop k (fun s bit => control.put (f (control.get s) bit))
      (statement control labels exit next)
  | .load f next => .load (fun s => control.put (f (control.get s)))
      (statement control labels exit next)
  | .branch f yes no => .branch (fun s => f (control.get s))
      (statement control labels exit yes) (statement control labels exit no)
  | .goto f => .goto (fun s => labels (f (control.get s)))
  | .halt => match exit with
      | none => .halt
      | some l => .goto (fun _ => l)

end BinPackingGap.MachineControlEmbedding

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingPoolMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.MachineFieldTemplate

open Turing

variable {q : Nat} {K Λ σ : Type}

abbrev State (σ : Type) := (σ × Unit) × Option Bool

end BinPackingGap.MachineFieldTemplate

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_MachineBoundedIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.MachineBoundedIteration

open Turing

noncomputable def timeBound (body growth : Polynomial Nat) : Polynomial Nat :=
  Polynomial.X + 1 +
    Polynomial.X * (body.comp growth + Polynomial.C 2 * growth + Polynomial.C 3) +
    Polynomial.C 2 * growth + Polynomial.C 3

theorem timeBound_eval (body growth : Polynomial Nat) (n : Nat) :
    (timeBound body growth).eval n =
      n + 1 + n * (body.eval (growth.eval n) + 2 * growth.eval n + 3) +
        2 * growth.eval n + 3 := by
  simp [timeBound, Polynomial.eval_comp]

end BinPackingGap.MachineBoundedIteration

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_MachineKeepDecisionTyped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.MachineKeepDecision

section

open Turing

def frame : List Bool → List Bool
  | [] => [false]
  | bit :: rest => true :: bit :: frame rest

@[simp] theorem frame_length (word : List Bool) :
    (frame word).length = 2 * word.length + 1 := by
  induction word with
  | nil => rfl
  | cons bit rest ih => simp only [frame, List.length_cons, ih]; omega

def inputBits (p : List Bool × List Bool) : List Bool := frame p.1 ++ p.2

def outputBits (p : List Bool × Bool) : List Bool := p.2 :: p.1

def keep (decide : List Bool → Bool) (p : List Bool × List Bool) : List Bool × Bool :=
  (p.1, decide p.2)

@[simp] theorem inputBits_length (p : List Bool × List Bool) :
    (inputBits p).length = 2 * p.1.length + 1 + p.2.length := by
  simp [inputBits]

inductive ExtraTape
  | saved | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.saved, .output]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Phase
  | parse | transfer | finish
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.parse, .transfer, .finish]

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance instFintypePhase : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape (M : FinTM2) := M.K ⊕ ExtraTape
abbrev Label (M : FinTM2) := M.Λ ⊕ Phase
abbrev State (M : FinTM2) := M.σ × Option (M.Γ M.k₀)

def extraTapes (M : FinTM2) (saved output : List (M.Γ M.k₀)) :
    ExtraTape → List (M.Γ M.k₀)
  | .saved => saved
  | .output => output

def oneStep {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := le_refl _

end

open Turing

def typedInputBits {α : Type} (encode : α → List Bool) (p : α × List Bool) : List Bool :=
  inputBits (encode p.1, p.2)

def typedOutputBits {α : Type} (encode : α → List Bool) (p : α × Bool) : List Bool :=
  p.2 :: encode p.1

def typedKeep {α : Type} (decide : List Bool → Bool) (p : α × List Bool) : α × Bool :=
  (p.1, decide p.2)

end BinPackingGap.MachineKeepDecision

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingGapDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.PairFirstProjection

open Turing

inductive Tape
  | input | counter | reversed | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .counter, .reversed, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | scan | copy | reverse
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .copy, .reverse]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State := Option Bool

def tapes (input counter reversed output : List Bool) : Tape → List Bool
  | .input => input
  | .counter => counter
  | .reversed => reversed
  | .output => output

@[simp] theorem tapes_input (a b c d : List Bool) : tapes a b c d .input = a := rfl
@[simp] theorem tapes_counter (a b c d : List Bool) : tapes a b c d .counter = b := rfl
@[simp] theorem tapes_reversed (a b c d : List Bool) : tapes a b c d .reversed = c := rfl
@[simp] theorem tapes_output (a b c d : List Bool) : tapes a b c d .output = d := rfl

@[simp] theorem update_input (a b c d e : List Bool) :
    Function.update (tapes a b c d) .input e = tapes e b c d := by
  funext k
  cases k <;> rfl

@[simp] theorem update_counter (a b c d e : List Bool) :
    Function.update (tapes a b c d) .counter e = tapes a e c d := by
  funext k
  cases k <;> rfl

@[simp] theorem update_reversed (a b c d e : List Bool) :
    Function.update (tapes a b c d) .reversed e = tapes a b e d := by
  funext k
  cases k <;> rfl

@[simp] theorem update_output (a b c d e : List Bool) :
    Function.update (tapes a b c d) .output e = tapes a b c e := by
  funext k
  cases k <;> rfl

def code : Label → TM2.Stmt (fun _ : Tape => Bool) Label State
  | .scan => .pop .input (fun _ head => head)
      (.branch (fun head => head.getD false)
        (.push .counter (fun _ => true) (.goto fun _ => .scan))
        (.goto fun _ => .copy))
  | .copy => .pop .counter (fun _ head => head)
      (.branch Option.isSome
        (.pop .input (fun _ head => head)
          (.push .reversed (fun head => head.getD false) (.goto fun _ => .copy)))
        (.goto fun _ => .reverse))
  | .reverse => .pop .reversed (fun _ head => head)
      (.branch Option.isSome
        (.push .output (fun head => head.getD false) (.goto fun _ => .reverse))
        .halt)

noncomputable def rawTime : Polynomial Nat := 3 * Polynomial.X + 3

def cleanupTapes : List Tape := [.input, .counter, .reversed]

end BinPackingGap.PairFirstProjection

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitializeEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchSemantics

theorem get_some_of_lt {α : Type*} (xs : List α) (i : Nat)
    (hi : i < xs.length) : ∃ x, xs[i]? = some x := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => exact ⟨x, rfl⟩
      | succ i => simpa using ih i (by simpa using hi)

theorem mem_of_get_some {α : Type*} {xs : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : x ∈ xs := by
  induction xs generalizing i with
  | nil => simp at h
  | cons y ys ih =>
      cases i with
      | zero =>
          have hyx : y = x := by simpa using h
          subst x
          simp
      | succ i => exact List.mem_cons_of_mem y (ih h)

theorem get_set_same {α : Type*} (xs : List α) (i : Nat) (x : α)
    (hi : i < xs.length) : (xs.set i x)[i]? = some x := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons y ys ih =>
      cases i with
      | zero => rfl
      | succ i => simpa using ih i (by simpa using hi)

theorem get_set_other {α : Type*} (xs : List α) (i j : Nat) (x : α)
    (hij : j ≠ i) : (xs.set i x)[j]? = xs[j]? := by
  induction xs generalizing i j with
  | nil => simp
  | cons y ys ih =>
      cases i <;> cases j <;> simp_all

def Prefix (i : Nat) (fixed : List (Option Nat)) : Prop :=
  (∀ t < i, ∃ j, fixed[t]? = some (some j)) ∧
  (∀ t, i ≤ t → t < fixed.length → fixed[t]? = some none)

theorem prefix_none (n : Nat) : Prefix 0 (List.replicate n none) := by
  constructor
  · intro t ht
    omega
  · intro t _ ht
    have ht' : t < n := by simpa using ht
    simp [ht']

theorem prefix_set {fixed : List (Option Nat)} {i : Nat}
    (hp : Prefix i fixed) (hi : i < fixed.length) (j : Nat) :
    Prefix (i + 1) (fixed.set i (some j)) := by
  constructor
  · intro t ht
    by_cases hti : t = i
    · subst t
      exact ⟨j, get_set_same fixed i (some j) hi⟩
    · obtain ⟨q, hq⟩ := hp.1 t (by omega)
      exact ⟨q, (get_set_other fixed i t (some j) hti).trans hq⟩
  · intro t ht hlen
    rw [get_set_other fixed i t (some j) (by omega)]
    exact hp.2 t (by omega) (by simpa using hlen)

theorem index_of_mem {α : Type*} {x : α} {xs : List α} (hx : x ∈ xs) :
    ∃ i : Nat, xs[i]? = some x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with h | h
      · subst y
        exact ⟨0, rfl⟩
      · obtain ⟨i, hi⟩ := ih h
        exact ⟨i + 1, hi⟩

end BinPackingGap.SearchSemantics

namespace BinPackingGap.SearchEncoding

open SearchSemantics

theorem size_le_self (n : Nat) : n.size ≤ n := by
  apply Nat.size_le.mpr
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

noncomputable def growthPolynomial : Polynomial Nat :=
  Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 6 * Polynomial.X + 1

end BinPackingGap.SearchEncoding

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitialItemsMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialItemsMachine

open Turing

inductive Number
  | numerator | denominator
  deriving DecidableEq

protected abbrev Number.enumList : List Number := [.numerator, .denominator]

protected theorem Number.enumList_nodup : Number.enumList.Nodup := by decide

instance instFintypeNumber : Fintype Number where
  elems := ⟨Number.enumList, Number.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Control
  | entry | malformedDrain | malformedFinish | copyOut | copyBack | seed
  | marker | positive | failed | clearNumerator | clearDenominator
  | countOut | countBack | finish
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.entry, .malformedDrain, .malformedFinish,
  .copyOut, .copyBack, .seed, .marker, .positive, .failed, .clearNumerator, .clearDenominator,
  .countOut, .countBack, .finish]

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance instFintypeControl : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 8
abbrev Alphabet (_ : Tape) := Bool

def scanTape (which : Number) : Fin 3 → Tape
  | 0 => 1
  | 1 => match which with | .numerator => 3 | .denominator => 4
  | _ => 2

def orderTape : Fin 5 → Tape
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 6
  | _ => 2

def tapes (raw stream scratch numerator denominator count : List Bool) : Tape → List Bool
  | 0 => raw
  | 1 => stream
  | 2 => scratch
  | 3 => numerator
  | 4 => denominator
  | 7 => count
  | _ => []

theorem update_raw (r i s n d c x : List Bool) :
    Function.update (tapes r i s n d c) 0 x = tapes x i s n d c := by
  funext k; fin_cases k <;> rfl

theorem update_stream (r i s n d c x : List Bool) :
    Function.update (tapes r i s n d c) 1 x = tapes r x s n d c := by
  funext k; fin_cases k <;> rfl

theorem update_scratch (r i s n d c x : List Bool) :
    Function.update (tapes r i s n d c) 2 x = tapes r i x n d c := by
  funext k; fin_cases k <;> rfl

theorem update_numerator (r i s n d c x : List Bool) :
    Function.update (tapes r i s n d c) 3 x = tapes r i s x d c := by
  funext k; fin_cases k <;> rfl

theorem update_denominator (r i s n d c x : List Bool) :
    Function.update (tapes r i s n d c) 4 x = tapes r i s n x c := by
  funext k; fin_cases k <;> rfl

theorem update_count (r i s n d c x : List Bool) :
    Function.update (tapes r i s n d c) 7 x = tapes r i s n d x := by
  funext k; fin_cases k <;> rfl

def rowTime (a d : Nat) : Nat := 6 * (a.size + d.size) + 14

end BinPackingGap.SearchInitialItemsMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingPowerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

open Turing

inductive Tape
  | input | output | accumulator | vertexCount | unary | scratch
  | outerIndex | innerIndex | outerVariable | innerVariable | comparison | innerSource
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .output, .accumulator, .vertexCount,
  .unary, .scratch, .outerIndex, .innerIndex, .outerVariable, .innerVariable, .comparison,
  .innerSource]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

structure Control where
  slot : Fin 3
  remaining : Fin 3
  outerSign : Bool
  innerSign : Bool
  otherHead : Option Bool
  equal : Bool
  deriving DecidableEq, Fintype

def initialControl : Control := ⟨0, 0, false, false, none, true⟩

def nextRemaining (a : Control) : Control :=
  {a with remaining := ⟨a.remaining.val - 1, by have := a.remaining.isLt; omega⟩}

def startRow (a : Control) : Control :=
  {a with remaining := ⟨2 - a.slot.val, by omega⟩}

def nextSlot (a : Control) : Control :=
  {a with slot := ⟨(a.slot.val + 1) % 3, Nat.mod_lt _ (by decide)⟩}

end BinPackingGap.LiteralSlotGraphMachine

namespace BinPackingGap.PackingFieldDecodeMachine

open Turing

variable {K A : Type} [DecidableEq K]

def decoderSlots (slots : Fin 3 ↪ K) : Fin 3 ↪ K where
  toFun i := slots ((Equiv.swap (1 : Fin 3) 2) i)
  inj' := fun _ _ h => (Equiv.swap (1 : Fin 3) 2).injective (slots.injective h)

omit [DecidableEq K] in
@[simp] theorem decoderSlots_zero (slots : Fin 3 ↪ K) :
    decoderSlots slots 0 = slots 0 := by
  change slots ((Equiv.swap (1 : Fin 3) 2) 0) = slots 0
  congr 1

omit [DecidableEq K] in
@[simp] theorem decoderSlots_one (slots : Fin 3 ↪ K) :
    decoderSlots slots 1 = slots 2 := by
  change slots ((Equiv.swap (1 : Fin 3) 2) 1) = slots 2
  rw [Equiv.swap_apply_left]

omit [DecidableEq K] in
@[simp] theorem decoderSlots_two (slots : Fin 3 ↪ K) :
    decoderSlots slots 2 = slots 1 := by
  change slots ((Equiv.swap (1 : Fin 3) 2) 2) = slots 1
  rw [Equiv.swap_apply_right]

def decodedTapes (slots : Fin 3 ↪ K) (base : K → List Bool)
    (payload suffix : List Bool) : K → List Bool :=
  Function.update (Function.update base (slots 0) suffix) (slots 2)
    (payload ++ base (slots 2))

end BinPackingGap.PackingFieldDecodeMachine

namespace BinPackingGap.PackingPowerProgram

open Turing

variable {K A : Type} [DecidableEq K]

def resultTapes (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat) : K → List Bool :=
  Function.update (Function.update base (slots 9) []) (slots 1) (a ^ n).bits

@[simp] theorem resultTapes_output (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat) :
    resultTapes slots base a n (slots 1) = (a ^ n).bits := by
  simp [resultTapes]

@[simp] theorem resultTapes_tally (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat) :
    resultTapes slots base a n (slots 9) = [] := by
  have h : slots 9 ≠ slots 1 := slots.injective.ne (by decide)
  simp [resultTapes, h]

end BinPackingGap.PackingPowerProgram

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingCountedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.GraphPreparationMachine

open Turing

def fieldIndices (edge : Bool) : Fin 4 ↪ Fin 7 where
  toFun := if edge then ![0, 1, 2, 4] else ![0, 1, 2, 3]
  inj' := by cases edge <;> decide

def tokenIndices (edge : Bool) : Fin 3 ↪ Fin 7 where
  toFun := if edge then ![0, 1, 6] else ![0, 1, 5]
  inj' := by cases edge <;> decide

variable {K Λ A : Type} [DecidableEq K]

def fieldSlots (slots : Fin 7 ↪ K) (edge : Bool) : Fin 4 ↪ K :=
  (fieldIndices edge).trans slots

def tokenSlots (slots : Fin 7 ↪ K) (edge : Bool) : Fin 3 ↪ K :=
  (tokenIndices edge).trans slots

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGap.GraphPreparationMachine

namespace BinPackingGap.PackingCountedProgram

open scoped BigOperators

variable {K : Type} [DecidableEq K]

def counterTapes (counter : K) (base : K → List Bool) (n : Nat) : K → List Bool :=
  Function.update base counter (List.replicate n true)

end BinPackingGap.PackingCountedProgram

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_PackingRegisterUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.PackingRegisterUpdate

open Turing

inductive Kind
  | add | multiply
  deriving DecidableEq

instance instFintypeKind : Fintype Kind where
  elems := {.add, .multiply}
  complete k := by cases k <;> simp

def operation (kind : Kind) : Nat → Nat → Nat :=
  match kind with
  | .add => Nat.add
  | .multiply => Nat.mul

def values (a b : Nat) : Fin 3 → Nat := ![a, b, 0]

end BinPackingGap.PackingRegisterUpdate

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingJobLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingItemBlockMachine

open Turing

variable {α K A : Type} [DecidableEq α] [DecidableEq K]

def outputTapes (output : K) (base : K → List Bool) (word : List Bool) : K → List Bool :=
  Function.update base output (word.reverse ++ base output)

end BinPackingGap.PackingItemBlockMachine

namespace BinPackingGap.PackingVertexLoop

variable {α δ : Type} [DecidableEq α]

def aggregateWidth (inputWidth start count : Nat) : Nat :=
  inputWidth + 2 * (start + count + 1) + 1

end BinPackingGap.PackingVertexLoop

namespace BinPackingGap.PackingJobBody

open PackingItemBlockMachine (outputTapes)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

def nextInput (input : α → Nat) (power repetition : α) (rightValue : Nat) : α → Nat :=
  Function.update (Function.update input power rightValue) repetition (input repetition + 1)

theorem update_size_le (input : α → Nat) (power : α) (value width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (hv : value.size ≤ width) :
    ∀ a, (Function.update input power value a).size ≤ width := by
  intro a
  by_cases ha : a = power
  · subst a
    simpa only [Function.update_self] using hv
  · simpa only [Function.update_of_ne ha] using hi a

end BinPackingGap.PackingJobBody

namespace BinPackingGap.PackingVertexRecords

theorem finRange_cons (n : Nat) :
    List.finRange (n + 1) = (0 : Fin (n + 1)) :: (List.finRange n).map Fin.succ := by
  rw [← List.ofFn_id, List.ofFn_succ, List.ofFn_eq_map]
  rfl

end BinPackingGap.PackingVertexRecords

namespace BinPackingGap.PackingJobLoop

section

variable {α δ : Type} [DecidableEq α]

def aggregateWidth (inputWidth otherWidth count : Nat) : Nat :=
  inputWidth + otherWidth + count + 2

end

open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes )
open PackingJobBody (nextInput )

end BinPackingGap.PackingJobLoop

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_GraphPackingRegisters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingRegisters

open PackingRegisterFrame

inductive Extra
  | input | scanScratch | scanTemporary | threshold | endpoints | vertices | edges
  | vertexCounter | edgeCounter | repetitionCounter | poolCounter | powerCounter
  | decodeScratch | reverseOutput | output
  deriving DecidableEq

instance instFintypeExtra : Fintype Extra where
  elems := {.input, .scanScratch, .scanTemporary, .threshold, .endpoints,
    .vertices, .edges, .vertexCounter, .edgeCounter, .repetitionCounter,
    .poolCounter, .powerCounter, .decodeScratch, .reverseOutput, .output}
  complete e := by cases e <;> simp

end BinPackingGap.GraphPackingRegisters

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Hardness_LiteralSlotGraphEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

section

def twoTapes (base : Tape → List Bool) (source destination : Tape)
    (input output : List Bool) : Tape → List Bool :=
  Function.update (Function.update base source input) destination output

@[simp] theorem twoTapes_source (base : Tape → List Bool) (source destination : Tape)
    (different : source ≠ destination) (input output : List Bool) :
    twoTapes base source destination input output source = input := by
  simp [twoTapes, different]

@[simp] theorem twoTapes_destination (base : Tape → List Bool) (source destination : Tape)
    (input output : List Bool) :
    twoTapes base source destination input output destination = output := by
  simp [twoTapes]

theorem twoTapes_update_source (base : Tape → List Bool) (source destination : Tape)
    (different : source ≠ destination) (input output next : List Bool) :
    Function.update (twoTapes base source destination input output) source next =
      twoTapes base source destination next output := by
  funext k
  by_cases hs : k = source
  · subst k; simp [twoTapes, different]
  · by_cases hd : k = destination
    · subst k; simp [twoTapes, different.symm]
    · simp [twoTapes, hs, hd]

@[simp] theorem twoTapes_update_destination (base : Tape → List Bool)
    (source destination : Tape) (input output next : List Bool) :
    Function.update (twoTapes base source destination input output) destination next =
      twoTapes base source destination input next := by
  simp [twoTapes]

abbrev RawLiteral := Nat × Bool

def counterHead (n : Nat) : Option Bool := if n = 0 then none else some true

def comparedControl (a : Control) (left right : Option Bool) : Control :=
  {a with otherHead := left, equal := a.equal && decide (left = right)}

def comparisonResult (a : Control) (n m : Nat) : Control :=
  {a with otherHead := none, equal := a.equal && decide (n = m)}

theorem counter_head_tail_eq (n m : Nat) :
    (decide (counterHead n = counterHead m) && decide (n - 1 = m - 1)) = decide (n = m) := by
  cases n <;> cases m <;> simp [counterHead]

theorem comparisonResult_step (a : Control) (n m : Nat) :
    comparisonResult (comparedControl a (counterHead n) (counterHead m)) (n - 1) (m - 1) =
      comparisonResult a n m := by
  simp [comparisonResult, comparedControl, Bool.and_assoc, counter_head_tail_eq]

theorem bits_length_le (n : Nat) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr n.lt_two_pow_self

def pairCost (u v : Nat) : Nat := 3 * u.bits.length + 3 * v.bits.length + 8

def bodyEdge (a : Control) (left right : RawLiteral) : Prop :=
  0 < a.remaining.val ∨ (left.1 = right.1 ∧ a.outerSign ≠ right.2)

instance instDecidableBodyEdge (a : Control) (left right : RawLiteral) : Decidable (bodyEdge a left right) := by
  unfold bodyEdge
  infer_instance

def bodyControl (a : Control) (left right : RawLiteral) : Control :=
  nextRemaining {a with innerSign := right.2, otherHead := none, equal := decide (left.1 = right.1)}

def branchCost (a : Control) (left right : RawLiteral) (u v : Nat) : Nat :=
  if bodyEdge a left right then pairCost u v + 1 else 2

theorem pairCost_le (u v : Nat) : pairCost u v ≤ 3 * u + 3 * v + 8 := by
  have hu := bits_length_le u
  have hv := bits_length_le v
  simp only [pairCost]
  omega

def rowEdges (u v : Nat) (left : RawLiteral) : List RawLiteral → List (Nat × Nat)
  | [] => []
  | right :: rest =>
      let tail := rowEdges u (v + 1) left rest
      if u / 3 = v / 3 ∨ (left.1 = right.1 ∧ left.2 ≠ right.2)
      then (u, v) :: tail else tail

def suffixEdges (u : Nat) : List RawLiteral → List (Nat × Nat)
  | [] => []
  | literal :: rest => rowEdges u (u + 1) literal rest ++ suffixEdges (u + 1) rest

theorem remaining_same_clause (u t : Nat) :
    0 < (2 - u % 3) - t ↔ u / 3 = (u + 1 + t) / 3 := by
  omega

def rowControl (a : Control) (left : RawLiteral) : List RawLiteral → Control
  | [] => a
  | right :: rest => rowControl (bodyControl a left right) left rest

theorem bodyControl_remaining (a : Control) (left right : RawLiteral) :
    (bodyControl a left right).remaining.val = a.remaining.val - 1 := rfl

@[simp] theorem bodyControl_slot (a : Control) (left right : RawLiteral) :
    (bodyControl a left right).slot = a.slot := rfl

@[simp] theorem bodyControl_outerSign (a : Control) (left right : RawLiteral) :
    (bodyControl a left right).outerSign = a.outerSign := rfl

@[simp] theorem rowControl_slot (a : Control) (left : RawLiteral) (rest : List RawLiteral) :
    (rowControl a left rest).slot = a.slot := by
  induction rest generalizing a with
  | nil => rfl
  | cons right rest ih => simp [rowControl, ih]

@[simp] theorem rowControl_outerSign (a : Control) (left : RawLiteral) (rest : List RawLiteral) :
    (rowControl a left rest).outerSign = a.outerSign := by
  induction rest generalizing a with
  | nil => rfl
  | cons right rest ih => simp [rowControl, ih]

def rowStartControl (a : Control) (left : RawLiteral) : Control :=
  startRow {a with outerSign := left.2}

def outerBodyControl (a : Control) (left : RawLiteral) (rest : List RawLiteral) : Control :=
  nextSlot (rowControl (rowStartControl a left) left rest)

theorem outerBodyControl_slot (a : Control) (left : RawLiteral) (rest : List RawLiteral) :
    (outerBodyControl a left rest).slot.val = (a.slot.val + 1) % 3 := by
  simp [outerBodyControl, nextSlot, rowStartControl, startRow]

def outerControl (a : Control) : List RawLiteral → Control
  | [] => a
  | left :: rest => outerControl (outerBodyControl a left rest) rest

def countHeaderResult (base : Tape → List Bool) (m : Nat) (suffix : List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .input suffix) .unary
    (List.replicate (2 * m) true ++ base .unary)) .vertexCount
      (List.replicate (3 * m) true ++ base .vertexCount)

def mainTapes (input accumulator index count unary output : List Bool) : Tape → List Bool
  | .input => input
  | .accumulator => accumulator
  | .outerIndex => index
  | .vertexCount => count
  | .unary => unary
  | .output => output
  | _ => []

@[simp] theorem mainTapes_input (i a x c u o next : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.input next = mainTapes next a x c u o := by
  funext tape; cases tape <;> rfl

@[simp] theorem mainTapes_accumulator (i a x c u o next : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.accumulator next = mainTapes i next x c u o := by
  funext tape; cases tape <;> rfl

@[simp] theorem mainTapes_outerIndex (i a x c u o next : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.outerIndex next = mainTapes i a next c u o := by
  funext tape; cases tape <;> rfl

@[simp] theorem mainTapes_vertexCount (i a x c u o next : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.vertexCount next = mainTapes i a x next u o := by
  funext tape; cases tape <;> rfl

@[simp] theorem mainTapes_unary (i a x c u o next : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.unary next = mainTapes i a x c next o := by
  funext tape; cases tape <;> rfl

@[simp] theorem mainTapes_output (i a x c u o next : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.output next = mainTapes i a x c u next := by
  funext tape; cases tape <;> rfl

@[simp] theorem mainTapes_scratch (i a x c u o : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.scratch [] = mainTapes i a x c u o := by
  funext tape; cases tape <;> rfl

end

end BinPackingGap.LiteralSlotGraphMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_PackingConstantPool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingConstantPool

open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes )

variable {α δ K : Type} [DecidableEq α] [DecidableEq K]

def repeatRecords (word : List Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => word ++ repeatRecords word n

end BinPackingGap.PackingConstantPool

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_SpeciesAllocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.SpeciesAllocation

variable {Slot Species : Type*} [Fintype Slot] [DecidableEq Species]

def allocation (request : Slot → Species) (stock : Species → ℕ)
    (hcount : ∀ s, Fintype.card {b : Slot // request b = s} = stock s) :
    Slot ≃ (Σ s : Species, Fin (stock s)) :=
  (Equiv.sigmaFiberEquiv request).symm.trans
    (Equiv.sigmaCongrRight fun s =>
      (Fintype.equivFin {b : Slot // request b = s}).trans (finCongr (hcount s)))

@[simp] theorem allocation_species (request : Slot → Species) (stock : Species → ℕ)
    (hcount : ∀ s, Fintype.card {b : Slot // request b = s} = stock s) (b : Slot) :
    (allocation request stock hcount b).1 = request b := rfl

end BinPackingGap.SpeciesAllocation

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingJobs

theorem finRange_add_map (m start : Nat) :
    (List.finRange m).map (fun i => start + i.val) = List.range' start m := by
  induction m generalizing start with
  | zero => rfl
  | succ m ih =>
      rw [List.finRange_succ, List.map_cons, List.map_map, List.range'_succ]
      simp only [Function.comp_def, Fin.val_zero, Nat.add_zero, Fin.val_succ]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_comm 1] using ih (start + 1)

theorem finRange_val_map (m : Nat) :
    (List.finRange m).map Fin.val = List.range' 0 m := by
  simpa only [Nat.zero_add] using finRange_add_map m 0

theorem contiguous_finRange (m : Nat) :
    (List.finRange m).map Fin.val = List.range' 0 m :=
  finRange_val_map m

theorem contiguous_cons {m : Nat} (e : Fin m) (es : List (Fin m)) (start : Nat)
    (h : (e :: es).map Fin.val = List.range' start (e :: es).length) :
    e.val = start ∧ es.map Fin.val = List.range' (start + 1) es.length := by
  have h' : e.val :: es.map Fin.val =
      start :: List.range' (start + 1) es.length := by
    simpa only [List.map_cons, List.length_cons, List.range'_succ] using h
  exact List.cons.inj h'

end BinPackingGap.GraphPackingJobs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingPreparationFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingEndpointPower

variable {K : Type} [DecidableEq K]

def values (v power : Nat) : Fin 7 → Nat := ![v, 3, power, 0, 0, 0, 0]

structure Ready (slots : (Fin 7 ⊕ Fin 6) ↪ K) (tally : K)
    (base : K → List Bool) (v : Nat) : Prop where
  registers : ∀ r, base (slots (.inl r)) = (values v 0 r).bits
  scratch : ∀ j, base (slots (.inr j)) = []
  tallyEmpty : base tally = []

def resultTapes (slots : (Fin 7 ⊕ Fin 6) ↪ K) (base : K → List Bool) (v : Nat) :
    K → List Bool := Function.update base (slots (.inl 2)) (3 ^ (v + 1)).bits

def timePolynomial : Polynomial Nat :=
  Polynomial.C 40 * (Polynomial.X + Polynomial.C 1) ^ 3 +
    Polynomial.C 100 * (Polynomial.X + Polynomial.C 4) ^ 5 +
    Polynomial.C 64 * (Polynomial.C 2 * Polynomial.X + Polynomial.C 4) ^ 2 +
    Polynomial.C 2

end BinPackingGap.PackingEndpointPower

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingGlobalExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingPoolRuntime

open GraphPackingRegisters

def tallyPolynomial (N : Polynomial Nat) : Polynomial Nat :=
  Polynomial.C 40 * (N + 1) ^ 3

@[simp] theorem tallyPolynomial_eval (N : Polynomial Nat) (s : Nat) :
    (tallyPolynomial N).eval s = 40 * (N.eval s + 1) ^ 3 := by
  simp only [tallyPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one]

end BinPackingGap.GraphPackingPoolRuntime

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingVerticesBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingVertices

section

open GraphPackingRegisters

variable (K : Nat)

theorem update_width {α : Type} [DecidableEq α]
    (input : α → Nat) (location : α) (value bound : Nat)
    (hi : ∀ a, (input a).size ≤ bound) (hv : value.size ≤ bound) :
    ∀ a, (Function.update input location value a).size ≤ bound := by
  intro a
  by_cases ha : a = location
  · subst a
    simpa only [Function.update_self] using hv
  · simpa only [Function.update_of_ne ha] using hi a

end

open GraphPackingRegisters
open PackingItemBlockMachine (outputTapes)

end BinPackingGap.GraphPackingVertices

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingJobs

section

open GraphPackingRegisters

variable (K : Nat)

theorem bounded_update {α : Type} [DecidableEq α]
    (values : α → Nat) (location : α) (value width : Nat)
    (h : ∀ a, (values a).size ≤ width) (hv : value.size ≤ width) :
    ∀ a, (Function.update values location value a).size ≤ width := by
  intro a
  by_cases ha : a = location
  · subst a
    simpa only [Function.update_self] using hv
  · simpa only [Function.update_of_ne ha] using h a

end

open GraphPackingRegisters
open PackingCountedProgram (counterTapes )

end BinPackingGap.GraphPackingJobs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_LocalTemplateBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

def templateFiberBoolEquiv {T C : Type*} (e : T ≃ Bool × C) (c : C) :
    {t : T // (e t).2 = c} ≃ Bool where
  toFun x := (e x.1).1
  invFun b := ⟨e.symm (b, c), by simp only [Equiv.apply_symm_apply]⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply e.injective
    change e (e.symm ((e x.1).1, c)) = e x.1
    rw [e.apply_symm_apply]
    exact Prod.ext rfl x.2.symm
  right_inv := by
    intro b
    simp only [Equiv.apply_symm_apply]

end BinPackingGap.InventoryData

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchFinalizeMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchFinalizeMachine

open Turing
open SearchSemantics SearchEncoding

inductive Tape
  | input | binary | scratch | reversed | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .binary, .scratch, .reversed, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Register := Unit × Option Bool

def tapes (input binary scratch reversed output : List Bool) : Tape → List Bool
  | .input => input
  | .binary => binary
  | .scratch => scratch
  | .reversed => reversed
  | .output => output

@[simp] theorem tapes_input (a b c d e : List Bool) : tapes a b c d e .input = a := rfl
@[simp] theorem tapes_binary (a b c d e : List Bool) : tapes a b c d e .binary = b := rfl
@[simp] theorem tapes_scratch (a b c d e : List Bool) : tapes a b c d e .scratch = c := rfl
@[simp] theorem tapes_reversed (a b c d e : List Bool) : tapes a b c d e .reversed = d := rfl
@[simp] theorem tapes_output (a b c d e : List Bool) : tapes a b c d e .output = e := rfl

@[simp] theorem update_input (a b c d e x : List Bool) :
    Function.update (tapes a b c d e) .input x = tapes x b c d e := by
  funext k; cases k <;> rfl

@[simp] theorem update_binary (a b c d e x : List Bool) :
    Function.update (tapes a b c d e) .binary x = tapes a x c d e := by
  funext k; cases k <;> rfl

@[simp] theorem update_scratch (a b c d e x : List Bool) :
    Function.update (tapes a b c d e) .scratch x = tapes a b x d e := by
  funext k; cases k <;> rfl

@[simp] theorem update_reversed (a b c d e x : List Bool) :
    Function.update (tapes a b c d e) .reversed x = tapes a b c x e := by
  funext k; cases k <;> rfl

@[simp] theorem update_output (a b c d e x : List Bool) :
    Function.update (tapes a b c d e) .output x = tapes a b c d x := by
  funext k; cases k <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

noncomputable def rawTime : Polynomial Nat := 10 * (Polynomial.X + 1) ^ 2

def cleanupTapes : List Tape := [.input, .binary, .scratch, .reversed]

end BinPackingGap.SearchFinalizeMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchFixedReplaceMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchFixedReplaceMachine

open Turing
open SearchEncoding

inductive Slot
  | source | index | payload | reversed
  deriving DecidableEq

inductive Action
  | before | after | discard
  deriving DecidableEq

protected abbrev Action.enumList : List Action := [.before, .after, .discard]

protected theorem Action.enumList_nodup : Action.enumList.Nodup := by decide

instance instFintypeAction : Fintype Action where
  elems := ⟨Action.enumList, Action.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | entry (searching : Bool)
  | index
  | option (action : Action)
  | name (action : Action)
  | digit (action : Action)
  | payload | payloadDigit
  | drainIndex | drainPayload | drainPayloadDigit
  deriving DecidableEq, Fintype

def Action.writes : Action → Bool
  | .before | .after => true
  | .discard => false

def Action.next : Action → Label
  | .before => .entry true
  | .after | .discard => .entry false

abbrev Words := Slot → List Bool
abbrev Register (A : Type) := A × Option Bool

def put (words : Words) (slot : Slot) (value : List Bool) : Words :=
  Function.update words slot value

def consume (words : Words) (slot : Slot) : Words := put words slot (words slot).tail

def emit (words : Words) (bit : Bool) : Words :=
  put words .reversed (bit :: words .reversed)

def saved (action : Action) (bits acc : List Bool) : List Bool :=
  if action.writes then bits.reverse ++ acc else acc

section Program

variable {K Λ A : Type} [DecidableEq K]

def finish (next : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ (Register A) :=
  .load (fun state => (state.1, none))
    (match next with | none => .halt | some label => .goto (fun _ => label))

def copyIf (action : Action) (output : K)
    (rest : TM2.Stmt (fun _ : K => Bool) Λ (Register A)) :
    TM2.Stmt (fun _ : K => Bool) Λ (Register A) :=
  if action.writes then .push output (fun state => state.2.getD false) rest else rest

def instruction (place : Slot → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (Register A)
  | .entry searching => .pop (place .source) (fun state head => (state.1, head))
      (.push (place .reversed) (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (finish (some (labels (if searching then .index else .option .after))))
          (finish (if searching then some (labels .drainIndex) else exit))))
  | .index => .pop (place .index) (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (finish (some (labels (.option .before))))
        (.push (place .reversed) (fun _ => true) (finish (some (labels .payload)))))
  | .option action => .pop (place .source) (fun state head => (state.1, head))
      (copyIf action (place .reversed)
        (.branch (fun state => state.2.getD false)
          (finish (some (labels (.name action)))) (finish (some (labels action.next)))))
  | .name action => .pop (place .source) (fun state head => (state.1, head))
      (copyIf action (place .reversed)
        (.branch (fun state => state.2.getD false)
          (finish (some (labels (.digit action)))) (finish (some (labels action.next)))))
  | .digit action => .pop (place .source) (fun state head => (state.1, head))
      (copyIf action (place .reversed) (finish (some (labels (.name action)))))
  | .payload => .pop (place .payload) (fun state head => (state.1, head))
      (.push (place .reversed) (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (finish (some (labels .payloadDigit)))
          (finish (some (labels (.option .discard))))))
  | .payloadDigit => .pop (place .payload) (fun state head => (state.1, head))
      (.push (place .reversed) (fun state => state.2.getD false)
        (finish (some (labels .payload))))
  | .drainIndex => .pop (place .index) (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (finish (some (labels .drainIndex))) (finish (some (labels .drainPayload))))
  | .drainPayload => .pop (place .payload) (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (finish (some (labels .drainPayloadDigit))) (finish exit))
  | .drainPayloadDigit => .pop (place .payload) (fun state head => (state.1, head))
      (finish (some (labels .drainPayload)))

def tapes (place : Slot → K) (base : K → List Bool) (words : Words) : K → List Bool :=
  fun k => if k = place .source then words .source
    else if k = place .index then words .index
    else if k = place .payload then words .payload
    else if k = place .reversed then words .reversed else base k

variable (place : Slot → K) (distinct : Function.Injective place)

include distinct in
@[simp] theorem tapes_at (base : K → List Bool) (words : Words) (slot : Slot) :
    tapes place base words (place slot) = words slot := by
  cases slot <;> simp [tapes, distinct.eq_iff]

include distinct in
theorem update_tapes (base : K → List Bool) (words : Words) (slot : Slot)
    (value : List Bool) :
    Function.update (tapes place base words) (place slot) value =
      tapes place base (put words slot value) := by
  funext k
  by_cases hs : k = place .source
  · subst k; cases slot <;> simp [tapes, put, distinct.eq_iff]
  by_cases hi : k = place .index
  · subst k; cases slot <;> simp [tapes, put, distinct.eq_iff]
  by_cases hp : k = place .payload
  · subst k; cases slot <;> simp [tapes, put, distinct.eq_iff]
  by_cases hr : k = place .reversed
  · subst k; cases slot <;> simp [tapes, put, distinct.eq_iff]
  cases slot <;> simp [tapes, hs, hi, hp, hr]

def configuration (labels : Label → Λ) (exit : Option Λ) (base : K → List Bool)
    (ambient : A) (label : Option Label) (words : Words) :
    TM2.Cfg (fun _ : K => Bool) Λ (Register A) :=
  ⟨match label with | none => exit | some label => some (labels label),
    (ambient, none), tapes place base words⟩

end Program

def next (label : Label) (words : Words) : Option Label × Words :=
  let input := (words .source).head?.getD false
  let payload := (words .payload).head?.getD false
  let index := (words .index).head?.getD false
  match label with
  | .entry searching =>
      (if input then some (if searching then .index else .option .after)
        else if searching then some .drainIndex else none,
       emit (consume words .source) input)
  | .index =>
      if index then (some (.option .before), consume words .index)
      else (some .payload, emit (consume words .index) true)
  | .option action | .name action =>
      let words := consume words .source
      let words := if action.writes then emit words input else words
      (some (if input then
          match label with | .option _ => .name action | _ => .digit action
        else action.next), words)
  | .digit action =>
      let words := consume words .source
      (some (.name action), if action.writes then emit words input else words)
  | .payload =>
      (some (if payload then .payloadDigit else .option .discard),
        emit (consume words .payload) payload)
  | .payloadDigit => (some .payload, emit (consume words .payload) payload)
  | .drainIndex =>
      (some (if index then .drainIndex else .drainPayload), consume words .index)
  | .drainPayload =>
      (if payload then some .drainPayloadDigit else none, consume words .payload)
  | .drainPayloadDigit => (some .drainPayload, consume words .payload)

variable {K Λ A : Type} [DecidableEq K]
variable (place : Slot → K) (distinct : Function.Injective place)
variable (labels : Label → Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (Register A))
variable (atLabels : ∀ l, program (labels l) = instruction place labels exit l)
variable (base : K → List Bool) (ambient : A)

local notation "C" => configuration place labels exit base ambient

include distinct atLabels in
theorem step_eq (label : Label) (words : Words) :
    TM2.step program (C (some label) words) =
      some (C (next label words).1 (next label words).2) := by
  change some (TM2.stepAux (program (labels label)) _ _) = _
  rw [atLabels label]
  cases exit <;> cases label with
  | entry searching =>
      cases searching <;> cases head : (words .source).head?.getD false <;>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put, *]
  | index =>
      cases head : (words .index).head?.getD false <;>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put, *]
  | option action =>
      cases action <;> cases head : (words .source).head?.getD false <;>
      simp [instruction, copyIf, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put,
        Action.writes, Action.next, *]
  | name action =>
      cases action <;> cases head : (words .source).head?.getD false <;>
      simp [instruction, copyIf, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put,
        Action.writes, Action.next, *]
  | digit action =>
      cases action <;>
      simp [instruction, copyIf, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put,
        Action.writes, *]
  | payload =>
      cases head : (words .payload).head?.getD false <;>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put, *]
  | payloadDigit =>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put, *]
  | drainIndex =>
      cases head : (words .index).head?.getD false <;>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, put, *]
  | drainPayload =>
      cases head : (words .payload).head?.getD false <;>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, put, *]
  | drainPayloadDigit =>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, put, *]

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def words (source index payload reversed : List Bool) : Words
  | .source => source
  | .index => index
  | .payload => payload
  | .reversed => reversed

theorem put_words (source index payload reversed value : List Bool) (slot : Slot) :
    put (words source index payload reversed) slot value =
      match slot with
      | .source => words value index payload reversed
      | .index => words source value payload reversed
      | .payload => words source index value reversed
      | .reversed => words source index payload value := by
  funext k; cases slot <;> cases k <;> rfl

end BinPackingGap.SearchFixedReplaceMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitialShapeMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialShapeMachine

inductive Continuation
  | numerator
  | denominator
  deriving DecidableEq

protected abbrev Continuation.enumList : List Continuation := [.numerator, .denominator]

protected theorem Continuation.enumList_nodup : Continuation.enumList.Nodup := by decide

instance instFintypeContinuation : Fintype Continuation where
  elems := ⟨Continuation.enumList, Continuation.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Mode
  | name (next : Continuation) (last : Bool)
  | digit (next : Continuation)
  | items
  | done
  | reject
  deriving DecidableEq, Fintype

def afterName : Continuation → Mode
  | .numerator => .name .denominator true
  | .denominator => .items

def nextMode : Mode → Bool → Mode
  | .name next _, true => .digit next
  | .name next last, false => if last then afterName next else .reject
  | .digit next, bit => .name next bit
  | .items, true => .name .numerator true
  | .items, false => .done
  | .done, _ => .reject
  | .reject, _ => .reject

def run : Mode → List Bool → Mode
  | mode, [] => mode
  | mode, bit :: rest => run (nextMode mode bit) rest

@[simp] theorem run_reject (input : List Bool) : run .reject input = .reject := by
  induction input with
  | nil => rfl
  | cons bit input ih => simpa only [run, nextMode] using ih

theorem run_done_iff (input : List Bool) : run .done input = .done ↔ input = [] := by
  cases input with
  | nil => simp [run]
  | cons bit rest => simp [run, nextMode]

def accepts (input : List Bool) : Bool := decide (run .items input = .done)

open Turing

inductive Label
  | scan
  | restore
  | finish
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .restore, .finish]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Fin 3) := Bool
abbrev State := Mode × Option Bool

def tapes (input output saved : List Bool) : Fin 3 → List Bool
  | 0 => input
  | 1 => output
  | _ => saved

@[simp] theorem tapes_input (input output saved : List Bool) :
    tapes input output saved 0 = input := rfl

@[simp] theorem tapes_output (input output saved : List Bool) :
    tapes input output saved 1 = output := rfl

@[simp] theorem tapes_saved (input output saved : List Bool) :
    tapes input output saved 2 = saved := rfl

theorem update_input (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 0 replacement =
      tapes replacement output saved := by
  funext k
  fin_cases k <;> rfl

theorem update_output (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 1 replacement =
      tapes input replacement saved := by
  funext k
  fin_cases k <;> rfl

theorem update_saved (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 2 replacement =
      tapes input output replacement := by
  funext k
  fin_cases k <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGap.SearchInitialShapeMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchPrepareMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchPrepareMachine

open Turing
open SearchSemantics SearchEncoding

inductive Tape
  | input | binary | scratch | index | payload | reversed | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .binary, .scratch, .index, .payload,
  .reversed, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Register := Bool × Option Bool

def tapes (input binary scratch index payload reversed output : List Bool) : Tape → List Bool
  | .input => input
  | .binary => binary
  | .scratch => scratch
  | .index => index
  | .payload => payload
  | .reversed => reversed
  | .output => output

@[simp] theorem tapes_input (a b c d e f g : List Bool) :
    tapes a b c d e f g .input = a := rfl

@[simp] theorem update_input (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .input x =
      tapes x b c d e f g := by
  funext k; cases k <;> rfl

@[simp] theorem tapes_binary (a b c d e f g : List Bool) :
    tapes a b c d e f g .binary = b := rfl

@[simp] theorem update_binary (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .binary x =
      tapes a x c d e f g := by
  funext k; cases k <;> rfl

@[simp] theorem tapes_scratch (a b c d e f g : List Bool) :
    tapes a b c d e f g .scratch = c := rfl

@[simp] theorem update_scratch (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .scratch x =
      tapes a b x d e f g := by
  funext k; cases k <;> rfl

@[simp] theorem tapes_index (a b c d e f g : List Bool) :
    tapes a b c d e f g .index = d := rfl

@[simp] theorem update_index (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .index x =
      tapes a b c x e f g := by
  funext k; cases k <;> rfl

@[simp] theorem tapes_payload (a b c d e f g : List Bool) :
    tapes a b c d e f g .payload = e := rfl

@[simp] theorem update_payload (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .payload x =
      tapes a b c d x f g := by
  funext k; cases k <;> rfl

@[simp] theorem tapes_reversed (a b c d e f g : List Bool) :
    tapes a b c d e f g .reversed = f := rfl

@[simp] theorem update_reversed (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .reversed x =
      tapes a b c d e x g := by
  funext k; cases k <;> rfl

@[simp] theorem tapes_output (a b c d e f g : List Bool) :
    tapes a b c d e f g .output = g := rfl

@[simp] theorem update_output (a b c d e f g x : List Bool) :
    Function.update (tapes a b c d e f g) .output x =
      tapes a b c d e f x := by
  funext k; cases k <;> rfl

def replacePlace : SearchFixedReplaceMachine.Slot → Tape
  | .source => .input
  | .index => .index
  | .payload => .payload
  | .reversed => .reversed

theorem replacePlace_injective : Function.Injective replacePlace := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem replaceTapes_eq (source index payload reversed : List Bool) :
    SearchFixedReplaceMachine.tapes replacePlace (tapes [] [] [] [] [] [] [])
      (SearchFixedReplaceMachine.words source index payload reversed) =
        tapes source [] [] index payload reversed [] := by
  funext k
  cases k <;> rfl

noncomputable def rawTime : Polynomial Nat := 100 * (Polynomial.X + 1) ^ 2

def cleanupTapes : List Tape := [.input, .binary, .scratch, .index, .payload, .reversed]

end BinPackingGap.SearchPrepareMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchUpdateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchUpdateMachine

open Turing
open SearchSemantics SearchEncoding

inductive Tape
  | input | index | compare | binary | scratch | payload | reversed | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .index, .compare, .binary, .scratch,
  .payload, .reversed, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

structure Ambient where
  phaseHigh : Bool
  phaseLow : Bool
  flag : Bool
  deriving DecidableEq, Fintype

abbrev Register := Ambient × Option Bool
abbrev Tapes := Tape → List Bool

def put (tapes : Tapes) (tape : Tape) (word : List Bool) : Tapes :=
  Function.update tapes tape word

def replacePlace : SearchFixedReplaceMachine.Slot → Tape
  | .source => .input
  | .index => .index
  | .payload => .payload
  | .reversed => .reversed

theorem replacePlace_injective : Function.Injective replacePlace := by
  intro a b h; cases a <;> cases b <;> simp_all [replacePlace]

def io (base : Tapes) (input reversed : List Bool) : Tapes :=
  put (put base .input input) .reversed reversed

@[simp] theorem io_input (base : Tapes) (input reversed : List Bool) :
    io base input reversed .input = input := by simp [io, put]

@[simp] theorem io_reversed (base : Tapes) (input reversed : List Bool) :
    io base input reversed .reversed = reversed := by simp [io, put]

theorem update_io_input (base : Tapes) (input reversed next : List Bool) :
    Function.update (io base input reversed) .input next = io base next reversed := by
  funext k; cases k <;> simp [io, put]

theorem update_io_reversed (base : Tapes) (input reversed next : List Bool) :
    Function.update (io base input reversed) .reversed next = io base input next := by
  simp [io, put]

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def decrement (counter : List Bool × Bool) : List Bool × Bool :=
  (counter.1.tail, counter.2 || !(counter.1.head?.getD false))

def counterAfter : Nat → (List Bool × Bool) → List Bool × Bool
  | 0, counter => counter
  | n + 1, counter => counterAfter n (decrement counter)

@[simp] theorem counterAfter_empty (n : Nat) :
    counterAfter n ([], true) = ([], true) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [counterAfter, decrement] using ih

def countIO (base : Tapes) (counter : List Bool × Bool)
    (input reversed : List Bool) : Tapes := io (put base .compare counter.1) input reversed

def work (input index compare binary scratch payload reversed output : List Bool) : Tapes
  | .input => input
  | .index => index
  | .compare => compare
  | .binary => binary
  | .scratch => scratch
  | .payload => payload
  | .reversed => reversed
  | .output => output

@[simp] theorem put_work (a b c d e f g h x : List Bool) (tape : Tape) :
    Function.update (work a b c d e f g h) tape x =
      match tape with
      | .input => work x b c d e f g h
      | .index => work a x c d e f g h
      | .compare => work a b x d e f g h
      | .binary => work a b c x e f g h
      | .scratch => work a b c d x f g h
      | .payload => work a b c d e x g h
      | .reversed => work a b c d e f x h
      | .output => work a b c d e f g x := by
  funext k; cases tape <;> cases k <;> rfl

@[simp] theorem io_work (a b c d e f g h input reversed : List Bool) :
    io (work a b c d e f g h) input reversed = work input b c d e f reversed h := by
  simp only [io, put, put_work]

def phaseWord (phase : Ambient) : List Bool := [phase.phaseHigh, phase.phaseLow]

theorem replaceTapes_eq (compare source index payload reversed : List Bool) :
    SearchFixedReplaceMachine.tapes replacePlace (work [] [] compare [] [] [] [] [])
      (SearchFixedReplaceMachine.words source index payload reversed) =
      work source index compare [] [] payload reversed [] := by
  funext k; cases k <;> rfl

noncomputable def rawTime : Polynomial Nat := Polynomial.C 100 * (Polynomial.X + 1) ^ 2

def cleanupTapes : List Tape :=
  [.input, .index, .compare, .binary, .scratch, .payload, .reversed]

end BinPackingGap.SearchUpdateMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchStageMachines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialEmitMachine

open Turing

abbrev Tape := Fin 7
abbrev Alphabet (_ : Tape) := Bool
abbrev Flags := Bool × Bool

def mulTape : Fin 5 → Tape
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 6
  | _ => 4

def mulSlots : Fin 5 ↪ Tape :=
  ⟨mulTape, by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [mulTape]⟩

@[simp] theorem mulSlots_apply (i : Fin 5) : mulSlots i = mulTape i := by
  simp only [mulSlots]
  rfl

def header (flags : Flags) : List Bool :=
  if flags.1 then
    if flags.2 then [false, false, true, false, false, false]
    else [true, false, false, false, false]
  else [true, true, false, false, false]

def tapes (input output left right scratch fixed counter : List Bool) : Tape → List Bool
  | 0 => input
  | 1 => output
  | 2 => left
  | 3 => right
  | 4 => scratch
  | 5 => fixed
  | _ => counter

@[simp] theorem tapes_input (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 0 = input := rfl

@[simp] theorem update_input (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 0 replacement =
      tapes replacement output left right scratch fixed counter := by
  funext k; fin_cases k <;> rfl

@[simp] theorem tapes_output (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 1 = output := rfl

@[simp] theorem update_output (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 1 replacement =
      tapes input replacement left right scratch fixed counter := by
  funext k; fin_cases k <;> rfl

@[simp] theorem tapes_left (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 2 = left := rfl

@[simp] theorem update_left (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 2 replacement =
      tapes input output replacement right scratch fixed counter := by
  funext k; fin_cases k <;> rfl

@[simp] theorem tapes_right (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 3 = right := rfl

@[simp] theorem update_right (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 3 replacement =
      tapes input output left replacement scratch fixed counter := by
  funext k; fin_cases k <;> rfl

@[simp] theorem tapes_scratch (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 4 = scratch := rfl

@[simp] theorem update_scratch (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 4 replacement =
      tapes input output left right replacement fixed counter := by
  funext k; fin_cases k <;> rfl

@[simp] theorem tapes_fixed (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 5 = fixed := rfl

@[simp] theorem update_fixed (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 5 replacement =
      tapes input output left right scratch replacement counter := by
  funext k; fin_cases k <;> rfl

@[simp] theorem tapes_counter (input output left right scratch fixed counter : List Bool) :
    tapes input output left right scratch fixed counter 6 = counter := rfl

@[simp] theorem update_counter (input output left right scratch fixed counter replacement : List Bool) :
    Function.update (tapes input output left right scratch fixed counter) 6 replacement =
      tapes input output left right scratch fixed replacement := by
  funext k; fin_cases k <;> rfl

def observed (n : Nat) (seen : Bool) : Bool := if n = 0 then seen else true

@[simp] theorem observed_zero (seen : Bool) : observed 0 seen = seen := rfl

@[simp] theorem observed_succ (n : Nat) (seen : Bool) : observed (n + 1) seen = true := by
  simp [observed]

@[simp] theorem observed_true (n : Nat) : observed n true = true := by
  simp [observed]

def initialFlags (valid : Bool) (n : Nat) : Flags := (valid, observed n false)

def fuelValue (valid : Bool) (n : Nat) : Nat := if valid then n * (n + 1) else 0

noncomputable def rawTime : Polynomial Nat := 100 * (Polynomial.X + 1) ^ 2

def cleanupTapes : List Tape := [0, 2, 3, 4, 5, 6]

end BinPackingGap.SearchInitialEmitMachine

end OAI
end


