-- Prove2me | Definitions.Def_OAIQ2Mt000
-- name    : OAIQ2Mt000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T01:21:30.227155+00:00
-- url     : https://prove2.me/theorems/77698322-7a8b-459f-9b91-a6318f951b5b
-- title:
--   Definitions bundle OAIQ2Mt000 of the split of OpenAI, Approximate counting of common bases of two matroids
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.common_bases_fpras`, carved from OpenAI's openai/math development (OpenAI, *Approximate counting of common bases of two matroids*, OpenAI Math Release, September 23, 2026, result family 114, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1071 declarations of OpenAI's Lean: 845 definitions, 13 inductive types or structures, 5 instances and 208 theorems. The definitions and types are `OAI.CommonBasesFPRAS.AccuratePhase`, `OAI.CommonBasesFPRAS.BitWord`, `OAI.CommonBasesFPRAS.ChainIndex`, `OAI.CommonBasesFPRAS.ChainState`, `OAI.CommonBasesFPRAS.ClassObservable`, `OAI.CommonBasesFPRAS.DefectState`, `OAI.CommonBasesFPRAS.DrawTree`, `OAI.CommonBasesFPRAS.DrawTree.All`, `OAI.CommonBasesFPRAS.DrawTree.Fits`, `OAI.CommonBasesFPRAS.DrawTree.Matches`, `OAI.CommonBasesFPRAS.DrawTree.Reindexed`, `OAI.CommonBasesFPRAS.DrawTree.bernoulli`, `OAI.CommonBasesFPRAS.DrawTree.bind`, `OAI.CommonBasesFPRAS.DrawTree.expectation`, `OAI.CommonBasesFPRAS.DrawTree.history`, `OAI.CommonBasesFPRAS.DrawTree.iterate`, `OAI.CommonBasesFPRAS.DrawTree.map`, `OAI.CommonBasesFPRAS.DrawTree.optionBind`, `OAI.CommonBasesFPRAS.DrawTree.optionValue`, `OAI.CommonBasesFPRAS.DrawTree.pureSome`, `OAI.CommonBasesFPRAS.DrawTree.rationalCoin`, `OAI.CommonBasesFPRAS.DrawTree.run`, `OAI.CommonBasesFPRAS.DrawTree.sample`, `OAI.CommonBasesFPRAS.DrawTree.uniformChoice`, `OAI.CommonBasesFPRAS.DrawTree.uniformVia`, `OAI.CommonBasesFPRAS.EdgeRespects`, `OAI.CommonBasesFPRAS.ExchangeAdjacent`, `OAI.CommonBasesFPRAS.ExchangeChoice`, `OAI.CommonBasesFPRAS.FPRASBank`, `OAI.CommonBasesFPRAS.FairBank`, `OAI.CommonBasesFPRAS.FiniteChain`, `OAI.CommonBasesFPRAS.FiniteChain.Inside`, `OAI.CommonBasesFPRAS.FiniteChain.Outside`, `OAI.CommonBasesFPRAS.FiniteChain.Sample`, `OAI.CommonBasesFPRAS.FiniteChain.Sample.toList`, `OAI.CommonBasesFPRAS.FiniteChain.apply`, `OAI.CommonBasesFPRAS.FiniteChain.cappedTrace`, `OAI.CommonBasesFPRAS.FiniteChain.cappedTraceKernel`, `OAI.CommonBasesFPRAS.FiniteChain.centeredPoint`, `OAI.CommonBasesFPRAS.FiniteChain.duration` and 818 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/MatroidCounting, in whole or in part: [`MatroidCounting_CommonBases`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatroidCounting/MatroidCounting/CommonBases.lean).
--
--   **Imports.** It imports the published bundle `Def_CommonBasesFPRAS`.
--
--   **Imported by** (directly, in this split): the statements `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_algorithmHistory`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_guard`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_historyTick`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_phaseSample`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_positiveTest`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_restartRepeat`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_sampleTick`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_start`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_storedStep`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_witness`, `OAI.CommonBasesFPRAS.MachineCode.frozen_machine`, `OAI.CommonBasesFPRAS.MachineCode.frozen_uniform_safe`, `OAI.CommonBasesFPRAS.MachineCode.output_certificate`, `OAI.CommonBasesFPRAS.MachineCode.safe_single`, `OAI.CommonBasesFPRAS.actual_history_success` and `OAI.CommonBasesFPRAS.rational_algorithm_success`; the proofs of `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_algorithmHistory`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_guard`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_historyTick`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_phaseSample`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_positiveTest`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_restartRepeat`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_sampleTick`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_start`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_storedStep`, `OAI.CommonBasesFPRAS.MachineCode.Effect.safe_witness`, `OAI.CommonBasesFPRAS.MachineCode.frozen_machine`, `OAI.CommonBasesFPRAS.MachineCode.frozen_uniform_safe`, `OAI.CommonBasesFPRAS.MachineCode.output_certificate`, `OAI.CommonBasesFPRAS.MachineCode.safe_single`, `OAI.CommonBasesFPRAS.actual_history_success`, `OAI.CommonBasesFPRAS.rational_algorithm_success` and `OAI.common_bases_fpras`.
-- source:
--   OpenAI, Approximate counting of common bases of two matroids, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 114; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Approximate-counting-of-common-bases-of-two-matroids-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/MatroidCounting at commit adc7f12

import Mathlib
import Definitions.Def_CommonBasesFPRAS

section
-- module Solutions.OAIQ2_Mat.Compat
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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
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
-- module Solutions.OAIQ2_Mat.MatroidCounting_CommonBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

section
open scoped RealInnerProductSpace BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def OnePositive (B : LinearMap.BilinForm ℝ V) : Prop :=
  ∀ e, 0 < B e e → ∀ v, B v e = 0 → B v v ≤ 0

section PositiveMatrix
variable {ι : Type*} [Fintype ι] [sectionInstance7 : DecidableEq ι]

def weightedSumLinear (a : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, a i * v i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

def diagonalScale (A : Matrix ι ι ℝ) (s : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => s i * A i j * s j

def cubicContraction (C : ι → Matrix ι ι ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  fun j k => ∑ i, x i*C i j k

end PositiveMatrix

section RawSignature
open scoped BigOperators Classical
variable {ι : Type*} [sectionInstance8 : Fintype ι] [sectionInstance9 : DecidableEq ι]

noncomputable def rankWeight (M : Matroid ι) (q : ℝ) (A : Set ι) : ℝ :=
  (q⁻¹) ^ (M.eRk A).toNat

noncomputable def rawHessian (M : Matroid ι) (q : ℝ) : Matrix ι ι ℝ :=
  fun i j => if i = j then 0 else rankWeight M q {i,j}

noncomputable def rawPositive (M : Matroid ι) (q : ℝ) (i : ι) : ℝ :=
  if M.IsNonloop i then q⁻¹ else 1

noncomputable def parallelIndicator (M : Matroid ι) (C : Set ι) (i : ι) : ℝ :=
  if M.IsNonloop i ∧ M.closure {i} = C then 1 else 0

end RawSignature
section MatroidFaces
open scoped Matroid BigOperators Classical
variable {ι : Type*} [sectionInstance10 : Fintype ι] [sectionInstance11 : DecidableEq ι]

noncomputable def faceHessian (f : Set ι → ℝ) (A : Set ι) :
    Matrix {i // i ∉ A} {i // i ∉ A} ℝ :=
  fun i j => if i = j then 0 else f (A ∪ {i.val,j.val})

noncomputable def faceMatroid (M : Matroid ι) (A : Set ι) : Matroid {i // i ∉ A} :=
  (M ／ A).comap Subtype.val

end MatroidFaces

section DerivativeClosure
open scoped BigOperators Classical Matrix
variable {ι : Type*} [sectionInstance12 : Fintype ι] [sectionInstance13 : DecidableEq ι]
noncomputable def coeffDeriv (a : ι → ℝ) (f : Set ι → ℝ) (A : Set ι) : ℝ :=
  ∑ i, if i ∈ A then 0 else a i * f (insert i A)

noncomputable def coeffDerivs : List (ι → ℝ) → (Set ι → ℝ) → Set ι → ℝ
  | [], f => f
  | a :: as, f => coeffDeriv a (coeffDerivs as f)

def FullPositive (f : Set ι → ℝ) (k : ℕ) : Prop :=
  (∀ A, A.ncard + k ≤ Fintype.card ι → 0 < f A) ∧
  (∀ A, Fintype.card ι < A.ncard + k → f A = 0)

noncomputable def padMatrix (p : ι → Prop) [DecidablePred p]
    (B : Matrix {i // p i} {i // p i} ℝ) : Matrix ι ι ℝ :=
  fun i j => if hi : p i then if hj : p j then B ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

noncomputable def faceEraseEquiv (A : Set ι) (i : {i // i ∉ A}) :
    {j : {j // j ∉ A} // j ≠ i} ≃ {j // j ∉ insert i.val A} where
  toFun j := ⟨j.val.val, by
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨fun h => j.property (Subtype.ext h), j.val.property⟩⟩
  invFun j := ⟨⟨j.val, fun h => j.property (Set.mem_insert_of_mem _ h)⟩,
    fun h => j.property (Or.inl (congrArg Subtype.val h))⟩
  left_inv j := rfl
  right_inv j := rfl

noncomputable def faceCubic (f : Set ι → ℝ) (A : Set ι) :
    {i // i ∉ A} → Matrix {i // i ∉ A} {i // i ∉ A} ℝ :=
  fun i j k => if i = j ∨ i = k ∨ j = k then 0 else f (insert i.val (A ∪ {j.val,k.val}))

noncomputable def slotDirection (E : Finset ι) (i : ι) : ℝ := if i ∈ E then 1 else 0

omit sectionInstance12 in
lemma slotDirection_nonneg [Fintype ι] (E : Finset ι) (i : ι) : 0 ≤ slotDirection E i := by
  unfold slotDirection
  split_ifs <;> norm_num

lemma coeffDeriv_slot (E : Finset ι) (f : Set ι → ℝ) (A : Set ι) :
    coeffDeriv (slotDirection E) f A =
      ∑ i ∈ E, if i ∈ A then 0 else f (insert i A) := by
  classical
  unfold coeffDeriv slotDirection
  rw [← Finset.sum_subset (Finset.subset_univ E)]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  · intro i _ hi
    simp [hi]

lemma coeffDeriv_pair (a b : ι) (hab : a ≠ b) (f : Set ι → ℝ) (A : Set ι)
    (ha : a ∉ A) (hb : b ∉ A) :
    coeffDeriv (slotDirection {a,b}) f A = f (insert a A) + f (insert b A) := by
  rw [coeffDeriv_slot]
  simp [hab, ha, hb]

end DerivativeClosure

section MatrixSplit

open scoped BigOperators
variable {ι : Type*} [Fintype ι] [sectionInstance15 : DecidableEq ι]

def splitMatrix (V : Matrix ι ι ℝ) (sa sb : ι → ℝ) (u : ℝ) :
    Matrix (ι ⊕ Bool) (ι ⊕ Bool) ℝ
  | .inl i, .inl j => V i j
  | .inl i, .inr false => sb i
  | .inl i, .inr true => sa i
  | .inr false, .inl i => sb i
  | .inr true, .inl i => sa i
  | .inr a, .inr b => if a = b then 0 else u

def oldVector (h : ι → ℝ) : (ι ⊕ Bool) → ℝ
  | .inl i => h i
  | .inr _ => 0

def splitPositive : (ι ⊕ Bool) → ℝ
  | .inl _ => 0
  | .inr _ => 1

def splitDifference : (ι ⊕ Bool) → ℝ
  | .inl _ => 0
  | .inr false => 1
  | .inr true => -1

def futureChild (V : Matrix ι ι ℝ) (c : ι → ℝ) : Matrix (Option ι) (Option ι) ℝ
  | some i, some j => V i j
  | some i, none => c i
  | none, some j => c j
  | none, none => 0

def extendVector (h : ι → ℝ) (a : ℝ) : Option ι → ℝ
  | some i => h i
  | none => a

end MatrixSplit

section RecursiveTransport
open scoped BigOperators Classical Matrix
variable {Γ : Type*} [sectionInstance16 : Fintype Γ] [sectionInstance17 : DecidableEq Γ]

noncomputable def pairDirection (p : Γ × Γ) : Γ → ℝ := slotDirection {p.1,p.2}

noncomputable def slotTotal (ps : List (Γ × Γ)) (f : Set Γ → ℝ) : Set Γ → ℝ :=
  coeffDerivs (ps.map pairDirection) f

lemma slotTotal_nil (f : Set Γ → ℝ) (A : Set Γ) : slotTotal [] f A = f A := rfl

lemma slotTotal_cons (p : Γ × Γ) (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (hp : p.1 ≠ p.2) (ha : p.1 ∉ A) (hb : p.2 ∉ A) :
    slotTotal (p::ps) f A = slotTotal ps f (insert p.1 A) +
      slotTotal ps f (insert p.2 A) := by
  exact coeffDeriv_pair p.1 p.2 hp (slotTotal ps f) A ha hb

def SlotsFresh : List (Γ × Γ) → Set Γ → Prop
  | [], _ => True
  | p::ps, B => p.1 ≠ p.2 ∧ p.1 ∉ B ∧ p.2 ∉ B ∧
      SlotsFresh ps (insert p.1 (insert p.2 B))

omit sectionInstance16 sectionInstance17 in
lemma SlotsFresh.mono [Fintype Γ] [DecidableEq Γ] {ps : List (Γ × Γ)} {A B : Set Γ}
    (h : SlotsFresh ps B) (hAB : A ⊆ B) : SlotsFresh ps A := by
  induction ps generalizing A B with
  | nil => trivial
  | cons p ps ih =>
    obtain ⟨hp,ha,hb,ht⟩ := h
    exact ⟨hp, fun hx => ha (hAB hx), fun hx => hb (hAB hx),
      ih ht (Set.insert_subset_insert (Set.insert_subset_insert hAB))⟩

lemma slotTotal_pos (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (hf : ∀ A, 0 < f A) (A : Set Γ) (hps : SlotsFresh ps A) :
    0 < slotTotal ps f A := by
  induction ps generalizing A with
  | nil => exact hf A
  | cons p ps ih =>
    obtain ⟨hp,ha,hb,ht⟩ := hps
    rw [slotTotal_cons p ps f A hp ha hb]
    apply add_pos
    · apply ih _ (ht.mono _)
      intro x hx
      rcases hx with rfl | hx
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx)
    · apply ih _ (ht.mono _)
      intro x hx
      exact Set.mem_insert_of_mem _ hx

def appendPoint {ι : Type*} (e : ι → Γ) (a : Γ) : Option ι → Γ
  | none => a
  | some i => e i

noncomputable def pairMatrix {ι : Type*} [DecidableEq ι]
    (f : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) : Matrix ι ι ℝ :=
  fun i j => if i = j then 0 else f (insert (e i) (insert (e j) A))

def HasSlotSignature (f : Set Γ → ℝ) : Prop :=
  ∀ (ps : List (Γ × Γ)) (A : Set Γ),
    OnePositive (faceHessian (slotTotal ps f) A).toBilin'

section Clique
variable {ι : Type*} [Fintype ι] [sectionInstance19 : DecidableEq ι]

noncomputable def cliqueEnergy (s W H : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, min (W i*s i) (W j*s j) * (H i-H j)^2) / 2

end Clique

variable {ι : Type*} [sectionInstance20 : Fintype ι] [sectionInstance21 : DecidableEq ι]

def splitEmbedding (e : ι → Γ) (a b : Γ) : (ι ⊕ Bool) → Γ
  | .inl i => e i
  | .inr false => a
  | .inr true => b

noncomputable def transportDemand (ps : List (Γ × Γ)) (f H : Set Γ → ℝ)
    (A : Set Γ) (e : ι → Γ) (h : ι → ℝ) : ℝ :=
  ∑ i, h i * slotTotal ps (fun S => f S*H S) (insert (e i) A)

noncomputable def transportPotential (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (e : ι → Γ) (h : ι → ℝ) (W : Γ → ℝ) : ℝ :=
  ∑ i, slotTotal ps f (insert (e i) A) * (h i)^2 / W (e i)

def slotPunctures : List (Γ × Γ) → List ((Γ × Γ) × List (Γ × Γ))
  | [] => []
  | p::ps => (p,ps) :: (slotPunctures ps).map (fun x => (x.1,p::x.2))

noncomputable def transportCorrection (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (e : ι → Γ) (h : ι → ℝ) (W : Γ → ℝ) : ℝ :=
  ((slotPunctures ps).map (fun x =>
    (pairMatrix (slotTotal x.2 f) A e).toBilin' h h / W x.1.1)).sum

noncomputable def transportEnergy {ι : Type*} [Fintype ι] (ps : List (Γ × Γ))
    (f H : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) (W : Γ → ℝ) : ℝ :=
  match ps with
  | [] => cliqueEnergy (fun i => f (insert (e i) A)) (fun i => W (e i))
      (fun i => H (insert (e i) A))
  | p::ps => transportEnergy ps f H (insert p.2 A) (appendPoint e p.1) W +
      transportEnergy ps f H (insert p.1 A) (appendPoint e p.2) W
termination_by ps.length

end RecursiveTransport

section TransportRoot
open scoped BigOperators Classical Matrix
variable {Γ ι : Type*} [sectionInstance22 : Fintype Γ] [sectionInstance23 : DecidableEq Γ]
  [Fintype ι] [sectionInstance25 : DecidableEq ι]

def rootEmbedding (p d : Γ) : Bool → Γ := fun b => if b then d else p

noncomputable def rootDemand (sp sd : ℝ) : Bool → ℝ :=
  fun b => if b then -(1/sd) else 1/sp

noncomputable def rootCoefficient (ps : List (Γ × Γ)) (f : Set Γ → ℝ)
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ) : ℝ :=
  let sp := slotTotal ps f (insert p A)
  let sd := slotTotal ps f (insert d A)
  1/(sp*W p) + 1/(sd*W d) + 2/(sp*sd)*
    ((slotPunctures ps).map (fun x => slotTotal x.2 f (insert p (insert d A))/W x.1.1)).sum

end TransportRoot

section TransportGraph
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance26 : Fintype Γ] [sectionInstance27 : DecidableEq Γ]

def ExchangeAdjacent (S T : Set Γ) : Prop :=
  ∃ (A : Set Γ) (a b : Γ), a ≠ b ∧ a ∉ A ∧ b ∉ A ∧
    S = insert a A ∧ T = insert b A

noncomputable def slotVertices {ι : Type*} [Fintype ι]
    (ps : List (Γ × Γ)) (A : Set Γ) (e : ι → Γ) : Finset (Set Γ) :=
  match ps with
  | [] => Finset.univ.image (fun i => insert (e i) A)
  | p::ps => slotVertices ps (insert p.2 A) (appendPoint e p.1) ∪
      slotVertices ps (insert p.1 A) (appendPoint e p.2)
termination_by ps.length

noncomputable def transportEdges {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ps : List (Γ × Γ)) (A : Set Γ) (e : ι → Γ) : Finset (Set Γ × Set Γ) :=
  match ps with
  | [] => (Finset.univ.filter (fun ij : ι × ι => ij.1 ≠ ij.2)).image
      (fun ij => (insert (e ij.1) A, insert (e ij.2) A))
  | p::ps => transportEdges ps (insert p.2 A) (appendPoint e p.1) ∪
      transportEdges ps (insert p.1 A) (appendPoint e p.2)
termination_by ps.length

noncomputable def missingMultiplier {ι : Type*} [Fintype ι]
    (ps : List (Γ × Γ)) (e : ι → Γ) (W : Γ → ℝ) (S : Set Γ) : ℝ :=
  (∑ i, if e i ∈ S then W (e i) else 0) +
    (ps.map (fun p => if p.1 ∈ S ∧ p.2 ∈ S then W p.1 else 0)).sum

noncomputable def slotEdgeEnergy {ι : Type*} [Fintype ι]
    (ps : List (Γ × Γ)) (e : ι → Γ) (W : Γ → ℝ)
    (f H : Set Γ → ℝ) (ST : Set Γ × Set Γ) : ℝ :=
  min (missingMultiplier ps e W ST.1 * f ST.1)
      (missingMultiplier ps e W ST.2 * f ST.2) * (H ST.1-H ST.2)^2

noncomputable def slotGraphEdges {ι : Type*} [Fintype ι]
    (ps : List (Γ × Γ)) (A : Set Γ) (e : ι → Γ) : Finset (Set Γ × Set Γ) :=
  ((slotVertices ps A e).product (slotVertices ps A e)).filter
    (fun ST => ExchangeAdjacent ST.1 ST.2)

noncomputable def slotGraphEnergy {ι : Type*} [Fintype ι]
    (ps : List (Γ × Γ)) (f H : Set Γ → ℝ) (A : Set Γ) (e : ι → Γ) (W : Γ → ℝ) : ℝ :=
  (∑ ST ∈ slotGraphEdges ps A e, slotEdgeEnergy ps e W f H ST)/2

end TransportGraph

section CoefficientInequalities
open scoped BigOperators Classical Matrix
variable {ι : Type*} [sectionInstance28 : Fintype ι] [sectionInstance29 : DecidableEq ι]

omit sectionInstance28 sectionInstance29 in
lemma SlotsFresh.swap [Fintype ι] [DecidableEq ι] {ps : List (ι × ι)} {p r : ι × ι} {A : Set ι}
    (h : SlotsFresh (p::r::ps) A) : SlotsFresh (r::p::ps) A := by
  obtain ⟨hp,hpa,hpb,hr,hra,hrb,hps⟩ := h
  refine ⟨hr,?_,?_,hp,?_,?_,?_⟩
  · exact fun hx => hra (Or.inr (Or.inr hx))
  · exact fun hx => hrb (Or.inr (Or.inr hx))
  · simp only [Set.mem_insert_iff, not_or] at hra hrb ⊢
    exact ⟨Ne.symm hra.1,Ne.symm hrb.1,hpa⟩
  · simp only [Set.mem_insert_iff, not_or] at hra hrb ⊢
    exact ⟨Ne.symm hra.2.1,Ne.symm hrb.2.1,hpb⟩
  · convert hps using 1 ; ext x ; simp ; tauto

end CoefficientInequalities

section MatroidWeights
open scoped BigOperators Classical Matrix
variable {ι : Type*} [sectionInstance30 : Fintype ι] [sectionInstance31 : DecidableEq ι]

omit sectionInstance31 in
lemma coeffDeriv_scale [DecidableEq ι] (a : ι → ℝ) (f : Set ι → ℝ) (c : ℝ) (A : Set ι) :
    coeffDeriv a (fun S => c * f S) A = c * coeffDeriv a f A := by
  simp only [coeffDeriv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

lemma coeffDerivs_scale (as : List (ι → ℝ)) (f : Set ι → ℝ) (c : ℝ) (A : Set ι) :
    coeffDerivs as (fun S => c * f S) A = c * coeffDerivs as f A := by
  induction as generalizing A with
  | nil => rfl
  | cons a as ih =>
    change coeffDeriv a (coeffDerivs as (fun S => c * f S)) A = _
    have h : coeffDerivs as (fun S => c * f S) = fun S => c * coeffDerivs as f S := by
      funext S; exact ih S
    rw [h,coeffDeriv_scale]
    rfl

noncomputable def matroidWeight (M : Matroid ι) (n : ℕ) (q : ℝ) (S : Set ι) : ℝ :=
  q ^ (n - (M.eRk S).toNat)

omit sectionInstance30 sectionInstance31 in
lemma matroidWeight_pos [Fintype ι] [DecidableEq ι] (M : Matroid ι) (n : ℕ) (q : ℝ) (hq : 0 < q) (S : Set ι) :
    0 < matroidWeight M n q S := pow_pos hq _

end MatroidWeights

section IndexedSlotCoefficients
open scoped BigOperators Classical
variable {ι : Type*} [sectionInstance32 : Fintype ι] [DecidableEq ι]

lemma SlotsFresh.perm {ps qs : List (ι × ι)} (hperm : ps.Perm qs) (A : Set ι) :
    SlotsFresh ps A ↔ SlotsFresh qs A := by
  induction hperm generalizing A with
  | nil => rfl
  | cons p h ih =>
    change (_ ∧ _ ∧ _ ∧ SlotsFresh _ _) ↔ (_ ∧ _ ∧ _ ∧ SlotsFresh _ _)
    rw [ih]
  | swap p r ps => exact ⟨SlotsFresh.swap,SlotsFresh.swap⟩
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ A).trans (ih₂ A)

noncomputable def slotDefect (ps : List (ι × ι)) (f : Set ι → ℝ)
    (A : Set ι) (p r : ι × ι) : ℝ :=
  slotTotal ((ps.erase p).erase r) f (insert r.1 (insert r.2 A))

omit sectionInstance32 in
lemma slots_perm_two [Fintype ι] {ps : List (ι × ι)} {p r : ι × ι}
    (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    ps.Perm (p::r::(ps.erase p).erase r) := by
  exact (List.perm_cons_erase hp).trans
    ((List.perm_cons_erase ((List.mem_erase_of_ne hpr.symm).mpr hr)).cons p)

lemma slotDefect_pos (ps : List (ι × ι)) (f : Set ι → ℝ)
    (hf : ∀ S, 0 < f S) (A : Set ι) (hps : SlotsFresh ps A)
    (p r : ι × ι) (hp : p ∈ ps) (hr : r ∈ ps) (hpr : p ≠ r) :
    0 < slotDefect ps f A p r := by
  have hh := (SlotsFresh.perm (slots_perm_two hp hr hpr) A).mp hps
  apply slotTotal_pos _ f hf _ (hh.2.2.2.2.2.2.mono _)
  intro x hx
  simp only [Set.mem_insert_iff] at hx ⊢
  tauto

end IndexedSlotCoefficients

section VarianceTree
open scoped BigOperators Classical
variable {ι : Type*} [sectionInstance34 : Fintype ι] [sectionInstance35 : DecidableEq ι]

noncomputable def slotVariance (ps : List (ι × ι)) (f H : Set ι → ℝ) (A : Set ι) : ℝ :=
  slotTotal ps (fun S => f S*(H S)^2) A -
    (slotTotal ps (fun S => f S*H S) A)^2 / slotTotal ps f A

end VarianceTree

section StateGeometry
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance36 : Fintype Γ] [sectionInstance37 : DecidableEq Γ]

def PairSingle (p : Γ × Γ) (S : Set Γ) : Prop :=
  (p.1 ∈ S ∧ p.2 ∉ S) ∨ (p.2 ∈ S ∧ p.1 ∉ S)
def PairFull (p : Γ × Γ) (S : Set Γ) : Prop := p.1 ∈ S ∧ p.2 ∈ S
def PairEmpty (p : Γ × Γ) (S : Set Γ) : Prop := p.1 ∉ S ∧ p.2 ∉ S

omit sectionInstance36 sectionInstance37 in
lemma PairSingle.not_full [Fintype Γ] [DecidableEq Γ] {p : Γ × Γ} {S : Set Γ} (h : PairSingle p S) : ¬ PairFull p S := by
  unfold PairSingle PairFull at *
  tauto
omit sectionInstance36 sectionInstance37 in
lemma PairSingle.not_empty [Fintype Γ] [DecidableEq Γ] {p : Γ × Γ} {S : Set Γ} (h : PairSingle p S) : ¬ PairEmpty p S := by
  unfold PairSingle PairEmpty at *
  tauto
omit sectionInstance36 sectionInstance37 in
lemma PairFull.not_empty [Fintype Γ] [DecidableEq Γ] {p : Γ × Γ} {S : Set Γ} (h : PairFull p S) : ¬ PairEmpty p S := by
  unfold PairFull PairEmpty at *
  tauto

def PlainState (gs : List (Γ × Γ)) (S : Set Γ) : Prop := ∀ p ∈ gs, PairSingle p S
def DefectState (gs : List (Γ × Γ)) (p r : Γ × Γ) (S : Set Γ) : Prop :=
  p ∈ gs ∧ r ∈ gs ∧ p ≠ r ∧ PairEmpty p S ∧ PairFull r S ∧
    ∀ t ∈ gs, t ≠ p → t ≠ r → PairSingle t S

lemma DefectState.not_plain {gs : List (Γ × Γ)} {p r : Γ × Γ} {S : Set Γ}
    (h : DefectState gs p r S) : ¬ PlainState gs S := by
  intro hs
  exact (hs p h.1).not_empty h.2.2.2.1

lemma DefectState.unique {gs : List (Γ × Γ)} {p r p' r' : Γ × Γ} {S : Set Γ}
    (h : DefectState gs p r S) (h' : DefectState gs p' r' S) : p = p' ∧ r = r' := by
  obtain ⟨hp,hr,hpr,hep,hfr,hs⟩ := h
  obtain ⟨hp',hr',hpr',hep',hfr',hs'⟩ := h'
  have hpp : p = p' := by
    by_contra hne
    by_cases hpr' : p = r'
    · subst r'; exact hfr'.not_empty hep
    · exact (hs' p hp hne hpr').not_empty hep
  subst p'
  refine ⟨rfl,?_⟩
  by_contra hne
  exact (hs' r hr hpr.symm hne).not_full hfr

omit sectionInstance36 sectionInstance37 in
lemma SlotsFresh.elements_fresh [Fintype Γ] [DecidableEq Γ] {ps : List (Γ × Γ)} {A : Set Γ}
    (h : SlotsFresh ps A) (p : Γ × Γ) (hp : p ∈ ps) : p.1 ∉ A ∧ p.2 ∉ A := by
  induction ps generalizing A with
  | nil => simp at hp
  | cons q ps ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨h.2.1,h.2.2.1⟩
    · have hh := ih h.2.2.2 hp
      exact ⟨fun hx => hh.1 (Or.inr (Or.inr hx)), fun hx => hh.2 (Or.inr (Or.inr hx))⟩

lemma SlotsFresh.pair_ne_of_mem {ps : List (Γ × Γ)} {A : Set Γ} {p : Γ × Γ}
    (h : SlotsFresh (p::ps) A) {r : Γ × Γ} (hr : r ∈ ps) : p ≠ r := by
  intro heq
  subst r
  exact (h.2.2.2.elements_fresh p hr).1 (Set.mem_insert _ _)

end StateGeometry

section RestrictedEnergy
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance38 : Fintype Γ] [sectionInstance39 : DecidableEq Γ]

def Respects (A B S : Set Γ) : Prop := A ⊆ S ∧ Disjoint B S

def EdgeRespects (A B : Set Γ) (ST : Set Γ × Set Γ) : Prop :=
  Respects A B ST.1 ∧ Respects A B ST.2

noncomputable def restrictedEnergy (E : Finset (Set Γ × Set Γ))
    (c : (Set Γ × Set Γ) → ℝ) (H : Set Γ → ℝ) (A B : Set Γ) : ℝ :=
  (∑ ST ∈ E, if EdgeRespects A B ST then c ST*(H ST.1-H ST.2)^2 else 0)/2

end RestrictedEnergy

section ChainIdentification
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance40 : Fintype Γ] [sectionInstance41 : DecidableEq Γ]

def FixedOutside (gs ps : List (Γ × Γ)) (A B : Set Γ) : Prop :=
  ∀ r ∈ gs, r ∉ ps → (r.1 ∈ A ∧ r.2 ∈ B) ∨ (r.2 ∈ A ∧ r.1 ∈ B)

noncomputable def chainMultiplier (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (S : Set Γ) : ℝ :=
  if h : ∃ p r, DefectState gs p r S then w h.choose h.choose_spec.choose else 1

lemma chainMultiplier_plain (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (S : Set Γ) (h : PlainState gs S) : chainMultiplier gs w S = 1 := by
  unfold chainMultiplier
  rw [dite_eq_right]
  rintro ⟨p,r,hpr⟩
  exact hpr.not_plain h

lemma chainMultiplier_defect (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (S : Set Γ) {p r : Γ × Γ} (h : DefectState gs p r S) :
    chainMultiplier gs w S = w p r := by
  have he : ∃ p r, DefectState gs p r S := ⟨p,r,h⟩
  unfold chainMultiplier
  rw [dite_eq_left he]
  have hh := he.choose_spec.choose_spec.unique h
  exact congrArg₂ w hh.1 hh.2

omit sectionInstance41 in
lemma chainMultiplier_pos [DecidableEq Γ] (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (hw : ∀ p r, 0 < w p r) (S : Set Γ) : 0 < chainMultiplier gs w S := by
  unfold chainMultiplier
  split_ifs <;> first | exact hw _ _ | norm_num

def ChainState (gs : List (Γ × Γ)) (S : Set Γ) : Prop :=
  PlainState gs S ∨ ∃ p r, DefectState gs p r S

noncomputable def chainEdges (gs : List (Γ × Γ)) : Finset (Set Γ × Set Γ) :=
  Finset.univ.filter (fun ST => ChainState gs ST.1 ∧ ChainState gs ST.2 ∧
    ExchangeAdjacent ST.1 ST.2)

noncomputable def chainConductance (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) (ST : Set Γ × Set Γ) : ℝ :=
  min (chainMultiplier gs w ST.1*f ST.1) (chainMultiplier gs w ST.2*f ST.2)

lemma SlotsFresh.pair_contains_unique {ps : List (Γ × Γ)} {A : Set Γ}
    (h : SlotsFresh ps A) {p r : Γ × Γ} (hp : p ∈ ps) (hr : r ∈ ps)
    {x : Γ} (hxp : x = p.1 ∨ x = p.2) (hxr : x = r.1 ∨ x = r.2) : p = r := by
  by_contra hne
  have hh := (SlotsFresh.perm (slots_perm_two hp hr hne) A).mp h
  have hr₁ := hh.2.2.2.2.1
  have hr₂ := hh.2.2.2.2.2.1
  rcases hxp with rfl | rfl <;> rcases hxr with heq | heq
  · exact hr₁ (Or.inl heq.symm)
  · exact hr₂ (Or.inl heq.symm)
  · exact hr₁ (Or.inr (Or.inl heq.symm))
  · exact hr₂ (Or.inr (Or.inl heq.symm))

noncomputable def pairMultiplier (ps : List (Γ × Γ)) (w : (Γ × Γ) → ℝ) (x : Γ) : ℝ :=
  if h : ∃ p ∈ ps, x = p.1 ∨ x = p.2 then w h.choose else 1

end ChainIdentification

section TransversalVariance
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance42 : Fintype Γ] [sectionInstance43 : DecidableEq Γ]

def VarianceNode (gs ps : List (Γ × Γ)) (A B : Set Γ) : Prop :=
  Disjoint A B ∧ SlotsFresh ps (A ∪ B) ∧ (∀ p ∈ ps, p ∈ gs) ∧ FixedOutside gs ps A B

end TransversalVariance

section ChoiceEnumeration
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance44 : Fintype Γ] [sectionInstance45 : DecidableEq Γ]

def pairSupport (ps : List (Γ × Γ)) : Set Γ :=
  {x | ∃ p ∈ ps, x = p.1 ∨ x = p.2}

omit sectionInstance44 sectionInstance45 in
@[simp] lemma pairSupport_nil [Fintype Γ] [DecidableEq Γ] : pairSupport ([] : List (Γ × Γ)) = ∅ := by ext; simp [pairSupport]
omit sectionInstance44 sectionInstance45 in
lemma pairSupport_cons [Fintype Γ] [DecidableEq Γ] (p : Γ × Γ) (ps : List (Γ × Γ)) :
    pairSupport (p::ps) = insert p.1 (insert p.2 (pairSupport ps)) := by
  ext x
  simp only [pairSupport,Set.mem_ofPred_eq,List.mem_cons,Set.mem_insert_iff]
  aesop

noncomputable def choiceVertices (ps : List (Γ × Γ)) (A : Set Γ) : Finset (Set Γ) :=
  match ps with
  | [] => {A}
  | p::ps => choiceVertices ps (insert p.1 A) ∪ choiceVertices ps (insert p.2 A)

omit sectionInstance44 sectionInstance45 in
lemma choiceVertices_fixed [Fintype Γ] [DecidableEq Γ] (ps : List (Γ × Γ)) (A S : Set Γ)
    (hS : S ∈ choiceVertices ps A) : A ⊆ S := by
  induction ps generalizing A with
  | nil =>
    rw [choiceVertices,Finset.mem_singleton] at hS
    exact hS ▸ Set.Subset.rfl
  | cons p ps ih =>
    rw [choiceVertices] at hS
    rcases Finset.mem_union.mp hS with hS | hS
    · exact (Set.subset_insert _ _).trans (ih _ hS)
    · exact (Set.subset_insert _ _).trans (ih _ hS)

omit sectionInstance44 sectionInstance45 in
lemma choiceVertices_excluded [Fintype Γ] [DecidableEq Γ] (ps : List (Γ × Γ)) (A B S : Set Γ)
    (hAB : Disjoint A B) (hps : ∀ p ∈ ps, p.1 ∉ B ∧ p.2 ∉ B)
    (hS : S ∈ choiceVertices ps A) : Disjoint B S := by
  induction ps generalizing A with
  | nil =>
    rw [choiceVertices,Finset.mem_singleton] at hS
    exact hS ▸ hAB.symm
  | cons p ps ih =>
    obtain ⟨ha,hb⟩ := hps p List.mem_cons_self
    have hrest := fun r hr => hps r (List.mem_cons_of_mem _ hr)
    rw [choiceVertices] at hS
    rcases Finset.mem_union.mp hS with hS | hS
    · exact ih _ (Set.disjoint_insert_left.mpr ⟨ha,hAB⟩) hrest hS
    · exact ih _ (Set.disjoint_insert_left.mpr ⟨hb,hAB⟩) hrest hS

lemma choiceVertices_disjoint (ps : List (Γ × Γ)) (A : Set Γ) (p : Γ × Γ)
    (hps : SlotsFresh (p::ps) A) :
    Disjoint (choiceVertices ps (insert p.1 A)) (choiceVertices ps (insert p.2 A)) := by
  apply Finset.disjoint_left.mpr
  intro S h₁ h₂
  have hp₁ : p.1 ∈ S := choiceVertices_fixed ps (insert p.1 A) S h₁ (Set.mem_insert _ _)
  have hp₂ : Disjoint {p.1} S := choiceVertices_excluded ps (insert p.2 A) {p.1} S
    (by simp only [Set.disjoint_singleton_right,Set.mem_insert_iff,not_or]; exact ⟨hps.1,hps.2.1⟩)
    (by
      intro r hr
      have hh := hps.2.2.2.elements_fresh r hr
      exact ⟨fun heq => hh.1 (Or.inl heq),fun heq => hh.2 (Or.inl heq)⟩) h₂
  exact Set.disjoint_left.mp hp₂ rfl hp₁

lemma slotTotal_eq_choice_sum (ps : List (Γ × Γ)) (A : Set Γ) (f : Set Γ → ℝ)
    (hps : SlotsFresh ps A) : slotTotal ps f A = ∑ S ∈ choiceVertices ps A, f S := by
  induction ps generalizing A with
  | nil => simp [choiceVertices,slotTotal_nil]
  | cons p ps ih =>
    rw [slotTotal_cons p ps f A hps.1 hps.2.1 hps.2.2.1,choiceVertices,
      Finset.sum_union (choiceVertices_disjoint ps A p hps)]
    congr 1
    · exact ih _ (hps.2.2.2.mono (by intro x hx; simp only [Set.mem_insert_iff] at hx ⊢; tauto))
    · exact ih _ (hps.2.2.2.mono (Set.subset_insert _ _))

lemma mem_choiceVertices_iff (ps : List (Γ × Γ)) (A S : Set Γ) (hps : SlotsFresh ps A) :
    S ∈ choiceVertices ps A ↔
      A ⊆ S ∧ S ⊆ A ∪ pairSupport ps ∧ PlainState ps S := by
  induction ps generalizing A with
  | nil => simp [choiceVertices,pairSupport_nil,PlainState,Set.Subset.antisymm_iff,and_comm]
  | cons p ps ih =>
    have hf₁ : SlotsFresh ps (insert p.1 A) := hps.2.2.2.mono (by
      intro x hx; simp only [Set.mem_insert_iff] at hx ⊢; tauto)
    have hf₂ : SlotsFresh ps (insert p.2 A) := hps.2.2.2.mono (Set.subset_insert _ _)
    rw [choiceVertices,Finset.mem_union,ih _ hf₁,ih _ hf₂]
    have hnot₁ : p.1 ∉ pairSupport ps := by
      rintro ⟨r,hr,h⟩
      have hh := hps.2.2.2.elements_fresh r hr
      rcases h with he | he
      · exact hh.1 (Or.inl he.symm)
      · exact hh.2 (Or.inl he.symm)
    have hnot₂ : p.2 ∉ pairSupport ps := by
      rintro ⟨r,hr,h⟩
      have hh := hps.2.2.2.elements_fresh r hr
      rcases h with he | he
      · exact hh.1 (Or.inr (Or.inl he.symm))
      · exact hh.2 (Or.inr (Or.inl he.symm))
    constructor
    · rintro (⟨hfix,hsupp,hsing⟩ | ⟨hfix,hsupp,hsing⟩)
      · refine ⟨(Set.subset_insert _ _).trans hfix,?_,?_⟩
        · intro x hx
          have hh := hsupp hx
          rw [pairSupport_cons]
          simp only [Set.mem_union,Set.mem_insert_iff] at hh ⊢
          tauto
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · left
            refine ⟨hfix (Set.mem_insert _ _),?_⟩
            intro hbad
            have hh := hsupp hbad
            rcases hh with hh | hh
            · rcases hh with hh | hh
              · exact hps.1 hh.symm
              · exact hps.2.2.1 hh
            · exact hnot₂ hh
          · exact hsing r hr
      · refine ⟨(Set.subset_insert _ _).trans hfix,?_,?_⟩
        · intro x hx
          have hh := hsupp hx
          rw [pairSupport_cons]
          simp only [Set.mem_union,Set.mem_insert_iff] at hh ⊢
          tauto
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · right
            refine ⟨hfix (Set.mem_insert _ _),?_⟩
            intro hbad
            have hh := hsupp hbad
            rcases hh with hh | hh
            · rcases hh with hh | hh
              · exact hps.1 hh
              · exact hps.2.1 hh
            · exact hnot₁ hh
          · exact hsing r hr
    · rintro ⟨hfix,hsupp,hsing⟩
      have hp := hsing p List.mem_cons_self
      have hrest : PlainState ps S := fun r hr => hsing r (List.mem_cons_of_mem _ hr)
      rcases hp with hp | hp
      · left
        refine ⟨Set.insert_subset hp.1 hfix,?_,hrest⟩
        intro x hx
        have hh := hsupp hx
        rw [pairSupport_cons] at hh
        simp only [Set.mem_union,Set.mem_insert_iff] at hh ⊢
        rcases hh with hh | rfl | rfl | hh
        · exact Or.inl (Or.inr hh)
        · exact Or.inl (Or.inl rfl)
        · exact False.elim (hp.2 hx)
        · exact Or.inr hh
      · right
        refine ⟨Set.insert_subset hp.1 hfix,?_,hrest⟩
        intro x hx
        have hh := hsupp hx
        rw [pairSupport_cons] at hh
        simp only [Set.mem_union,Set.mem_insert_iff] at hh ⊢
        rcases hh with hh | rfl | rfl | hh
        · exact Or.inl (Or.inr hh)
        · exact False.elim (hp.2 hx)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr hh

lemma choiceVertices_plain (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) :
    choiceVertices gs ∅ = Finset.univ.filter (PlainState gs) := by
  ext S
  rw [mem_choiceVertices_iff gs ∅ S hgs]
  simp [hcover]

lemma slotTotal_eq_plain_sum (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f : Set Γ → ℝ) :
    slotTotal gs f ∅ = ∑ S ∈ Finset.univ.filter (PlainState gs), f S := by
  rw [slotTotal_eq_choice_sum gs ∅ f hgs,choiceVertices_plain gs hgs hcover]

end ChoiceEnumeration

section DefectEnumeration
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance46 : Fintype Γ] [sectionInstance47 : DecidableEq Γ]

omit sectionInstance46 sectionInstance47 in
lemma pairSupport_perm [Fintype Γ] [DecidableEq Γ] {ps qs : List (Γ × Γ)} (hp : ps.Perm qs) : pairSupport ps = pairSupport qs := by
  ext x
  simp only [pairSupport,Set.mem_ofPred_eq,hp.mem_iff]

lemma SlotsFresh.support_disjoint {ps : List (Γ × Γ)} {A : Set Γ} (h : SlotsFresh ps A) :
    Disjoint (pairSupport ps) A := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p,hp,hx⟩ hxA
  rcases hx with rfl | rfl
  · exact (h.elements_fresh p hp).1 hxA
  · exact (h.elements_fresh p hp).2 hxA

lemma choiceVertices_defect (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (p r : Γ × Γ)
    (hp : p ∈ gs) (hr : r ∈ gs) (hpr : p ≠ r) :
    choiceVertices ((gs.erase p).erase r) {r.1,r.2} =
      Finset.univ.filter (DefectState gs p r) := by
  let ps := (gs.erase p).erase r
  have hperm : gs.Perm (p::r::ps) := slots_perm_two hp hr hpr
  have hslots := (SlotsFresh.perm hperm ∅).mp hgs
  have htail : SlotsFresh ps {r.1,r.2} := hslots.2.2.2.2.2.2.mono (by
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_empty_iff_false,or_false] at hx ⊢
    tauto)
  have hno : p.1 ∉ pairSupport (r::ps) ∧ p.2 ∉ pairSupport (r::ps) := by
    exact ⟨fun hx => Set.disjoint_left.mp hslots.2.2.2.support_disjoint hx (Or.inl rfl),
      fun hx => Set.disjoint_left.mp hslots.2.2.2.support_disjoint hx (Or.inr (Or.inl rfl))⟩
  have htailSupport : ({r.1,r.2} : Set Γ) ∪ pairSupport ps = pairSupport (r::ps) := by
    rw [pairSupport_cons]
    ext x
    simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have hcover' : pairSupport (p::r::ps) = Set.univ := (pairSupport_perm hperm).symm.trans hcover
  ext S
  rw [mem_choiceVertices_iff _ _ _ htail,Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hfix,hsupp,hsing⟩
    refine ⟨hp,hr,hpr,⟨?_,?_⟩,⟨hfix (Or.inl rfl),hfix (Or.inr rfl)⟩,?_⟩
    · intro hx; exact hno.1 (htailSupport ▸ hsupp hx)
    · intro hx; exact hno.2 (htailSupport ▸ hsupp hx)
    · intro t ht htp htr
      have ht' : t ∈ p::r::ps := hperm.mem_iff.mp ht
      simp only [List.mem_cons] at ht'
      exact hsing t (ht'.resolve_left htp |>.resolve_left htr)
  · intro hdef
    refine ⟨?_,?_,?_⟩
    · intro x hx
      rcases hx with rfl | hx
      · exact hdef.2.2.2.2.1.1
      · exact hx ▸ hdef.2.2.2.2.1.2
    · intro x hx
      have hh : x ∈ pairSupport (p::r::ps) := hcover' ▸ Set.mem_univ x
      rw [pairSupport_cons] at hh
      rcases hh with rfl | rfl | hh
      · exact False.elim (hdef.2.2.2.1.1 hx)
      · exact False.elim (hdef.2.2.2.1.2 hx)
      · exact htailSupport ▸ hh
    · intro t ht
      exact hdef.2.2.2.2.2 t (hperm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)))
        (hslots.pair_ne_of_mem (List.mem_cons_of_mem _ ht)).symm
        (hslots.2.2.2.pair_ne_of_mem ht).symm

lemma slotDefect_eq_defect_sum (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (f : Set Γ → ℝ) (p r : Γ × Γ)
    (hp : p ∈ gs) (hr : r ∈ gs) (hpr : p ≠ r) :
    slotDefect gs f ∅ p r = ∑ S ∈ Finset.univ.filter (DefectState gs p r), f S := by
  have hslots := (SlotsFresh.perm (slots_perm_two hp hr hpr) ∅).mp hgs
  have htail : SlotsFresh ((gs.erase p).erase r) {r.1,r.2} := hslots.2.2.2.2.2.2.mono (by
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_empty_iff_false,or_false] at hx ⊢
    tauto)
  unfold slotDefect
  simp only [insert_empty_eq]
  rw [slotTotal_eq_choice_sum _ _ f htail,choiceVertices_defect gs hgs hcover p r hp hr hpr]

end DefectEnumeration

section DefectTransport
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance48 : Fintype Γ] [sectionInstance49 : DecidableEq Γ]

def SamePair (p q : Γ × Γ) : Prop := q = p ∨ q = p.swap

end DefectTransport

section DefectMeans
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance50 : Fintype Γ] [sectionInstance51 : DecidableEq Γ]

def orientPair (p : Γ × Γ) (b : Bool) : Γ × Γ := if b then p.swap else p

end DefectMeans

section Observable
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance52 : Fintype Γ] [DecidableEq Γ]

noncomputable def chainStates (gs : List (Γ × Γ)) : Finset (Set Γ) :=
  Finset.univ.filter (ChainState gs)
noncomputable def defectTypes (gs : List (Γ × Γ)) : Finset ((Γ × Γ) × (Γ × Γ)) :=
  gs.toFinset.offDiag
noncomputable def chainWeight (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) (S : Set Γ) : ℝ :=
  chainMultiplier gs w S * f S
noncomputable def chainTotal (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) : ℝ :=
  ∑ S ∈ chainStates gs, chainWeight gs w f S
noncomputable def plainMean (gs : List (Γ × Γ)) (f H : Set Γ → ℝ) : ℝ :=
  slotTotal gs (fun S => f S*H S) ∅/slotTotal gs f ∅
noncomputable def defectMean (gs : List (Γ × Γ)) (f H : Set Γ → ℝ) (p r : Γ × Γ) : ℝ :=
  slotDefect gs (fun S => f S*H S) ∅ p r/slotDefect gs f ∅ p r
noncomputable def observableProjection (gs : List (Γ × Γ)) (f H : Set Γ → ℝ) (S : Set Γ) : ℝ :=
  if h : ∃ p r, DefectState gs p r S then defectMean gs f H h.choose h.choose_spec.choose else H S

omit sectionInstance52 in
lemma mem_defectTypes [Fintype Γ] (gs : List (Γ × Γ)) (pr : (Γ × Γ) × (Γ × Γ)) :
    pr ∈ defectTypes gs ↔ pr.1 ∈ gs ∧ pr.2 ∈ gs ∧ pr.1 ≠ pr.2 := by
  simp [defectTypes,Finset.mem_offDiag]

lemma chain_sum_decomposition (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (g : Set Γ → ℝ) :
    (∑ S ∈ chainStates gs, chainMultiplier gs w S*g S) =
      (∑ S ∈ Finset.univ.filter (PlainState gs),g S) +
      ∑ pr ∈ defectTypes gs, w pr.1 pr.2 *
        ∑ S ∈ Finset.univ.filter (DefectState gs pr.1 pr.2),g S := by
  simp only [chainStates,Finset.sum_filter,Finset.mul_sum]
  rw [Finset.sum_comm,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hp : PlainState gs S
  · have hd : ∀ p r, ¬ DefectState gs p r S := fun p r hh => hh.not_plain hp
    simp [hp,ChainState,chainMultiplier_plain gs w S hp,hd]
  · by_cases hd : ∃ p r, DefectState gs p r S
    · obtain ⟨p,r,hpr⟩ := hd
      have hmem : (p,r) ∈ defectTypes gs := (mem_defectTypes gs _).mpr ⟨hpr.1,hpr.2.1,hpr.2.2.1⟩
      have hu : ∀ pr ∈ defectTypes gs, pr ≠ (p,r) → ¬ DefectState gs pr.1 pr.2 S := by
        intro pr _ hn hh
        have he := hh.unique hpr
        exact hn (Prod.ext he.1 he.2)
      rw [ite_eq_left (show ChainState gs S from Or.inr ⟨p,r,hpr⟩),ite_eq_right hp,zero_add,
        Finset.sum_eq_single (p,r)]
      · simp [hpr,chainMultiplier_defect gs w S hpr]
      · intro pr hm hn
        simp [hu pr hm hn]
      · exact fun hn => False.elim (hn hmem)
    · have hd' : ∀ p r, ¬ DefectState gs p r S := fun p r hh => hd ⟨p,r,hh⟩
      simp [ChainState,hp,hd']

lemma chainTotal_eq (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) :
    chainTotal gs w f = slotTotal gs f ∅ +
      ∑ pr ∈ defectTypes gs, w pr.1 pr.2*slotDefect gs f ∅ pr.1 pr.2 := by
  unfold chainTotal chainWeight
  rw [chain_sum_decomposition,← slotTotal_eq_plain_sum gs hgs hcover f]
  congr 1
  apply Finset.sum_congr rfl
  intro pr hm
  obtain ⟨hp,hr,hpr⟩ := (mem_defectTypes gs pr).mp hm
  rw [slotDefect_eq_defect_sum gs hgs hcover f pr.1 pr.2 hp hr hpr]

lemma chainTotal_ge_plain (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hf : ∀ S, 0 < f S) (hw : ∀ p r, 0 < w p r) :
    slotTotal gs f ∅ ≤ chainTotal gs w f := by
  rw [chainTotal_eq gs hgs hcover w f]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro pr hm
  obtain ⟨hp,hr,hpr⟩ := (mem_defectTypes gs pr).mp hm
  exact mul_nonneg (hw _ _).le (slotDefect_pos gs f hf ∅ hgs pr.1 pr.2 hp hr hpr).le

lemma chainTotal_pos (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hf : ∀ S, 0 < f S) (hw : ∀ p r, 0 < w p r) :
    0 < chainTotal gs w f :=
  (slotTotal_pos gs f hf ∅ hgs).trans_le (chainTotal_ge_plain gs hgs hcover w f hf hw)

noncomputable def chainMean (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f H : Set Γ → ℝ) : ℝ :=
  (∑ S ∈ chainStates gs,chainWeight gs w f S*H S)/chainTotal gs w f
noncomputable def chainVariance (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f H : Set Γ → ℝ) : ℝ :=
  (∑ S ∈ chainStates gs,chainWeight gs w f S*(H S-chainMean gs w f H)^2)/chainTotal gs w f
noncomputable def chainDirichlet (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f H : Set Γ → ℝ) : ℝ :=
  restrictedEnergy (chainEdges gs) (chainConductance gs w f) H ∅ ∅/
    (2*(gs.length:ℝ)^2*chainTotal gs w f)

end Observable

section ChainGeometry
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance54 : Fintype Γ] [sectionInstance55 : DecidableEq Γ]

lemma pairSupport_ncard (ps : List (Γ × Γ)) (A : Set Γ) (hps : SlotsFresh ps A) :
    (A ∪ pairSupport ps).ncard = A.ncard+2*ps.length := by
  induction ps generalizing A with
  | nil => simp
  | cons p ps ih =>
    have he : A ∪ pairSupport (p::ps) = (insert p.1 (insert p.2 A)) ∪ pairSupport ps := by
      rw [pairSupport_cons]
      ext x
      simp only [Set.mem_union,Set.mem_insert_iff]
      tauto
    rw [he,ih _ hps.2.2.2,Set.ncard_insert_of_notMem (by
      simpa only [Set.mem_insert_iff,not_or] using And.intro hps.1 hps.2.1),
      Set.ncard_insert_of_notMem hps.2.2.1,List.length_cons]
    omega

lemma slots_ground_card (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) : Fintype.card Γ = 2*gs.length := by
  have h := pairSupport_ncard gs ∅ hgs
  simpa [hcover,Set.ncard_univ,Nat.card_eq_fintype_card] using h

lemma choiceVertices_ncard (ps : List (Γ × Γ)) (A S : Set Γ) (hps : SlotsFresh ps A)
    (hS : S ∈ choiceVertices ps A) : S.ncard = A.ncard+ps.length := by
  induction ps generalizing A with
  | nil =>
    simp only [choiceVertices,Finset.mem_singleton] at hS
    subst S
    simp
  | cons p ps ih =>
    rw [choiceVertices,Finset.mem_union] at hS
    rcases hS with hS | hS
    · have ht : SlotsFresh ps (insert p.1 A) := hps.2.2.2.mono (by
        intro x hx
        simp only [Set.mem_insert_iff] at hx ⊢
        tauto)
      rw [ih _ ht hS,Set.ncard_insert_of_notMem hps.2.1,List.length_cons]
      omega
    · have ht : SlotsFresh ps (insert p.2 A) := hps.2.2.2.mono (Set.subset_insert _ _)
      rw [ih _ ht hS,Set.ncard_insert_of_notMem hps.2.2.1,List.length_cons]
      omega

lemma PlainState.ncard {gs : List (Γ × Γ)} (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) {S : Set Γ} (hS : PlainState gs S) : S.ncard = gs.length := by
  have hm : S ∈ choiceVertices gs ∅ := by rw [choiceVertices_plain gs hgs hcover]; simp [hS]
  simpa using choiceVertices_ncard gs ∅ S hgs hm

lemma DefectState.ncard {gs : List (Γ × Γ)} (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) {p r : Γ × Γ} {S : Set Γ} (hS : DefectState gs p r S) :
    S.ncard = gs.length := by
  let ps := (gs.erase p).erase r
  have hperm : gs.Perm (p::r::ps) := slots_perm_two hS.1 hS.2.1 hS.2.2.1
  have hs := (SlotsFresh.perm hperm ∅).mp hgs
  have ht : SlotsFresh ps {r.1,r.2} := hs.2.2.2.2.2.2.mono (by
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_empty_iff_false,or_false] at hx ⊢
    tauto)
  have hm : S ∈ choiceVertices ps {r.1,r.2} := by
    rw [choiceVertices_defect gs hgs hcover p r hS.1 hS.2.1 hS.2.2.1]
    simp [hS]
  have hc := choiceVertices_ncard ps {r.1,r.2} S ht hm
  have hpair : ({r.1,r.2} : Set Γ).ncard = 2 := Set.ncard_pair hs.2.2.2.1
  rw [hpair] at hc
  have hl := hperm.length_eq
  simp only [List.length_cons] at hl
  omega

lemma ChainState.ncard {gs : List (Γ × Γ)} (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) {S : Set Γ} (hS : ChainState gs S) : S.ncard = gs.length := by
  rcases hS with hS | ⟨p,r,hS⟩
  · exact hS.ncard hgs hcover
  · exact hS.ncard hgs hcover

omit sectionInstance54 sectionInstance55 in
lemma ExchangeAdjacent.symm [Fintype Γ] [DecidableEq Γ] {S T : Set Γ} (h : ExchangeAdjacent S T) : ExchangeAdjacent T S := by
  obtain ⟨A,a,b,hab,ha,hb,hS,hT⟩ := h
  exact ⟨A,b,a,hab.symm,hb,ha,hT,hS⟩
omit sectionInstance54 sectionInstance55 in
lemma ExchangeAdjacent.ne [Fintype Γ] [DecidableEq Γ] {S T : Set Γ} (h : ExchangeAdjacent S T) : S ≠ T := by
  obtain ⟨A,a,b,hab,ha,hb,rfl,rfl⟩ := h
  intro he
  have hh : a ∈ insert b A := he ▸ Set.mem_insert a A
  exact (Set.mem_insert_iff.mp hh).elim hab ha

omit sectionInstance54 sectionInstance55 in
lemma ExchangeAdjacent.move [Fintype Γ] [DecidableEq Γ] {S T : Set Γ} (h : ExchangeAdjacent S T) :
    ∃ a ∈ S, ∃ b ∈ Sᶜ, T = insert b (S\{a}) := by
  obtain ⟨A,a,b,hab,ha,hb,rfl,rfl⟩ := h
  refine ⟨a,Set.mem_insert _ _,b,?_,?_⟩
  · simpa only [Set.mem_compl_iff,Set.mem_insert_iff,not_or] using And.intro hab.symm hb
  · congr 1
    ext x
    simp only [Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · intro hx
      exact ⟨Or.inr hx,fun he => ha (he ▸ hx)⟩
    · rintro ⟨hh,hn⟩
      exact hh.resolve_left hn

lemma exchange_neighbors_card (S : Set Γ) :
    (Finset.univ.filter (ExchangeAdjacent S)).card ≤ S.ncard*Sᶜ.ncard := by
  have hsub : Finset.univ.filter (ExchangeAdjacent S) ⊆
      (S.toFinset ×ˢ Sᶜ.toFinset).image (fun ab => insert ab.2 (S\{ab.1})) := by
    intro T hT
    obtain ⟨a,ha,b,hb,rfl⟩ := (Finset.mem_filter.mp hT).2.move
    exact Finset.mem_image.mpr ⟨(a,b),by simpa only [Finset.mem_product,Set.mem_toFinset] using And.intro ha hb,rfl⟩
  calc
    _ ≤ ((S.toFinset ×ˢ Sᶜ.toFinset).image (fun ab => insert ab.2 (S\{ab.1}))).card := Finset.card_le_card hsub
    _ ≤ (S.toFinset ×ˢ Sᶜ.toFinset).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_product,← Set.ncard_eq_toFinset_card',← Set.ncard_eq_toFinset_card']

abbrev ChainIndex (gs : List (Γ × Γ)) := {S : Set Γ // ChainState gs S}

lemma chain_neighbors_card (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) (S : ChainIndex gs) :
    (Finset.univ.filter (fun T : ChainIndex gs => ExchangeAdjacent S.val T.val)).card ≤ gs.length^2 := by
  let e : ChainIndex gs → Set Γ := Subtype.val
  have he : Function.Injective e := Subtype.val_injective
  have hsub : (Finset.univ.filter (fun T : ChainIndex gs => ExchangeAdjacent S.val T.val)).image e ⊆
      Finset.univ.filter (ExchangeAdjacent S.val) := by
    intro T hT
    obtain ⟨U,hU,hUT⟩ := Finset.mem_image.mp hT
    subst T
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hU).2⟩
  have hcompl : S.valᶜ.ncard = gs.length := by
    have hc := S.val.ncard_add_ncard_compl
    rw [Nat.card_eq_fintype_card,slots_ground_card gs hgs hcover,S.property.ncard hgs hcover] at hc
    omega
  calc
    _ = ((Finset.univ.filter (fun T : ChainIndex gs => ExchangeAdjacent S.val T.val)).image e).card :=
      (Finset.card_image_of_injective _ he).symm
    _ ≤ (Finset.univ.filter (ExchangeAdjacent S.val)).card := Finset.card_le_card hsub
    _ ≤ S.val.ncard*S.valᶜ.ncard := exchange_neighbors_card _
    _ = gs.length^2 := by rw [S.property.ncard hgs hcover,hcompl,pow_two]

end ChainGeometry

open scoped BigOperators Classical

structure FiniteChain (X : Type*) [Fintype X] where
  P : X → X → ℝ
  π : X → ℝ
  positive : ∀ x, 0 < π x
  normalized : ∑ x, π x = 1
  nonnegative : ∀ x y, 0 ≤ P x y
  stochastic : ∀ x, ∑ y, P x y = 1
  reversible : ∀ x y, π x*P x y = π y*P y x
  lazy : ∀ x, 1/2 ≤ P x x

namespace FiniteChain
variable {X : Type*} [sectionInstance56 : Fintype X] (C : FiniteChain X)

noncomputable def inner (f g : X → ℝ) : ℝ := ∑ x, C.π x*f x*g x
noncomputable def apply (f : X → ℝ) (x : X) : ℝ := ∑ y, C.P x y*f y
noncomputable def energy (f : X → ℝ) : ℝ := C.inner f (fun x => f x-C.apply f x)
noncomputable def iterate (k : ℕ) (f : X → ℝ) : X → ℝ := Nat.iterate C.apply k f

lemma inner_symm (f g : X → ℝ) : C.inner f g = C.inner g f := by
  unfold inner
  apply Finset.sum_congr rfl
  intro x _
  ring
lemma inner_sub_right (f g h : X → ℝ) : C.inner f (fun x => g x-h x) = C.inner f g-C.inner f h := by
  simp [inner,mul_sub,Finset.sum_sub_distrib]
lemma apply_selfAdjoint (f g : X → ℝ) : C.inner f (C.apply g) = C.inner (C.apply f) g := by
  unfold inner apply
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  have h := C.reversible x y
  calc
    _ = (C.π x*C.P x y)*(f x*g y) := by ring
    _ = (C.π y*C.P y x)*(f x*g y) := by rw [h]
    _ = _ := by ring

@[simp] lemma iterate_zero (f : X → ℝ) : C.iterate 0 f = f := rfl

noncomputable def partialResolvent (N : ℕ) (f : X → ℝ) (x : X) : ℝ :=
  ∑ k ∈ Finset.range N,C.iterate k f x

noncomputable def pathExpectation : ℕ → X → (List X → ℝ) → ℝ
  | 0,x,F => F [x]
  | N+1,x,F => ∑ y,C.P x y*pathExpectation N y (fun l => F (x::l))

noncomputable def pathSum (g : X → ℝ) (l : List X) : ℝ := (l.map g).sum
noncomputable def squareMoment (g : X → ℝ) (N : ℕ) (x : X) : ℝ :=
  if N=0 then 0 else C.pathExpectation (N-1) x (fun l => (pathSum g l)^2)

variable [DecidableEq X]

noncomputable def ofMoves (π : X → ℝ) (m : X → X → ℝ)
    (hπ : ∀ x,0 < π x) (hπsum : ∑ x,π x = 1)
    (hm : ∀ x y,0 ≤ m x y) (hrow : ∀ x,∑ y,m x y ≤ 1/2)
    (hrev : ∀ x y,π x*m x y = π y*m y x) : FiniteChain X where
  P x y := m x y+if x=y then 1-∑ z,m x z else 0
  π := π
  positive := hπ
  normalized := hπsum
  nonnegative x y := by
    split_ifs
    · linarith [hm x y,hrow x]
    · simpa using hm x y
  stochastic x := by simp [Finset.sum_add_distrib]
  reversible x y := by
    by_cases h : x=y
    · subst y; rfl
    · simp [h,Ne.symm h,hrev]
  lazy x := by simp only [ite_true]; linarith [hm x x,hrow x]

end FiniteChain
section Metropolis
open scoped BigOperators Classical
variable {Γ : Type*} [Fintype Γ] [sectionInstance59 : DecidableEq Γ]

lemma chainWeight_pos (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) (S : Set Γ) :
    0 < chainWeight gs w f S := mul_pos (chainMultiplier_pos gs w hw S) (hf S)

omit sectionInstance59 in
lemma chain_sum_subtype [DecidableEq Γ] (gs : List (Γ × Γ)) (g : Set Γ → ℝ) :
    (∑ S ∈ chainStates gs,g S) = ∑ S : ChainIndex gs,g S.val := by
  exact Finset.sum_subtype _ (by intro S; simp [chainStates]) g

noncomputable def metropolisMove (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) (S T : ChainIndex gs) : ℝ :=
  if ExchangeAdjacent S.val T.val then
    min (chainWeight gs w f S.val) (chainWeight gs w f T.val)/
      (2*(gs.length:ℝ)^2*chainWeight gs w f S.val) else 0

lemma metropolisMove_nonneg (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ)
    (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) (S T : ChainIndex gs) :
    0 ≤ metropolisMove gs w f S T := by
  have hS := chainWeight_pos gs w f hw hf S.val
  unfold metropolisMove
  split_ifs
  · exact div_nonneg (le_min (chainWeight_pos gs w f hw hf _).le (chainWeight_pos gs w f hw hf _).le)
      (by positivity)
  · rfl

lemma metropolisMove_row (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) (S : ChainIndex gs) :
    ∑ T,metropolisMove gs w f S T ≤ 1/2 := by
  have hS := chainWeight_pos gs w f hw hf S.val
  have hn : (0:ℝ) < gs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  have hinc (T : ChainIndex gs) : metropolisMove gs w f S T ≤
      if ExchangeAdjacent S.val T.val then 1/(2*(gs.length:ℝ)^2) else 0 := by
    unfold metropolisMove
    split_ifs
    · apply (div_le_iff₀ (by positivity : 0 < 2*(gs.length:ℝ)^2*chainWeight gs w f S.val)).mpr
      have he : 1/(2*(gs.length:ℝ)^2)*(2*(gs.length:ℝ)^2*chainWeight gs w f S.val) = chainWeight gs w f S.val := by
        field_simp
      rw [he]
      exact min_le_left _ _
    · rfl
  have hs := Finset.sum_le_sum (fun T (_ : T ∈ Finset.univ) => hinc T)
  have hc : ((Finset.univ.filter (fun T : ChainIndex gs => ExchangeAdjacent S.val T.val)).card:ℝ) ≤ (gs.length:ℝ)^2 := by
    exact_mod_cast chain_neighbors_card gs hgs hcover S
  have he : (gs.length:ℝ)^2*(1/(2*(gs.length:ℝ)^2)) = 1/2 := by field_simp
  calc
    _ ≤ _ := hs
    _ = ((Finset.univ.filter (fun T : ChainIndex gs => ExchangeAdjacent S.val T.val)).card:ℝ)*(1/(2*(gs.length:ℝ)^2)) := by
      rw [← Finset.sum_filter]; simp
    _ ≤ (gs.length:ℝ)^2*(1/(2*(gs.length:ℝ)^2)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := he

lemma metropolisMove_balanced (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) (S T : ChainIndex gs) :
    (chainWeight gs w f S.val/chainTotal gs w f)*metropolisMove gs w f S T =
    (chainWeight gs w f T.val/chainTotal gs w f)*metropolisMove gs w f T S := by
  have hs := (chainWeight_pos gs w f hw hf S.val).ne'
  have ht := (chainWeight_pos gs w f hw hf T.val).ne'
  by_cases h : ExchangeAdjacent S.val T.val
  · simp only [metropolisMove,ite_eq_left h,ite_eq_left h.symm]
    rw [min_comm (chainWeight gs w f T.val)]
    field_simp
  · have hh : ¬ ExchangeAdjacent T.val S.val := fun hh => h hh.symm
    simp [metropolisMove,h,hh]

noncomputable def metropolisChain (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S) : FiniteChain (ChainIndex gs) :=
  FiniteChain.ofMoves (fun S => chainWeight gs w f S.val/chainTotal gs w f) (metropolisMove gs w f)
    (fun S => div_pos (chainWeight_pos gs w f hw hf S.val) (chainTotal_pos gs hgs hcover w f hf hw))
    (by rw [← Finset.sum_div,← chain_sum_subtype]; exact div_self (chainTotal_pos gs hgs hcover w f hf hw).ne')
    (metropolisMove_nonneg gs w f hw hf)
    (metropolisMove_row gs hgs hne hcover w f hw hf)
    (metropolisMove_balanced gs w f hw hf)

end Metropolis

namespace FiniteChain
variable {X : Type*} [Fintype X] (C : FiniteChain X)

noncomputable def mean (f : X → ℝ) : ℝ := ∑ x,C.π x*f x
noncomputable def variance (f : X → ℝ) : ℝ := C.inner (fun x => f x-C.mean f) (fun x => f x-C.mean f)

end FiniteChain
section ProjectionBridge
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance61 : Fintype Γ] [sectionInstance62 : DecidableEq Γ]

def ClassObservable (gs : List (Γ × Γ)) (G : Set Γ → ℝ) : Prop :=
  ∀ p r S T, DefectState gs p r S → DefectState gs p r T → G S = G T

noncomputable def extendChainFun (gs : List (Γ × Γ)) (H : ChainIndex gs → ℝ) (S : Set Γ) : ℝ :=
  if h : ChainState gs S then H ⟨S,h⟩ else 0

end ProjectionBridge

structure KilledKernel (B : Type*) [Fintype B] where
  Q : B → B → ℝ
  r : ℝ
  nonnegative : ∀ x y,0 ≤ Q x y
  rnonneg : 0 ≤ r
  rlt : r < 1
  rowbound : ∀ x,∑ y,Q x y ≤ r

namespace KilledKernel
open scoped BigOperators Classical
open Filter
variable {B : Type*} [Fintype B] (Q : KilledKernel B)
noncomputable def apply (f : B → ℝ) (x : B) : ℝ := ∑ y,Q.Q x y*f y
noncomputable def iterate (k : ℕ) (f : B → ℝ) : B → ℝ := Nat.iterate Q.apply k f
@[simp] lemma iterate_zero (f : B → ℝ) : Q.iterate 0 f = f := rfl
lemma iterate_succ (k : ℕ) (f : B → ℝ) : Q.iterate (k+1) f = Q.apply (Q.iterate k f) :=
  Function.iterate_succ_apply' Q.apply k f
lemma iterate_succ' (k : ℕ) (f : B → ℝ) : Q.iterate (k+1) f = Q.iterate k (Q.apply f) :=
  Function.iterate_succ_apply Q.apply k f
lemma apply_sub (f g : B → ℝ) : Q.apply (fun x => f x-g x) = fun x => Q.apply f x-Q.apply g x := by
  funext x
  simp [apply,mul_sub,Finset.sum_sub_distrib]
lemma apply_sum {J : Type*} (s : Finset J) (f : J → B → ℝ) :
    Q.apply (fun x => ∑ j ∈ s,f j x) = fun x => ∑ j ∈ s,Q.apply (f j) x := by
  funext x
  simp only [apply,Finset.mul_sum]
  exact Finset.sum_comm
lemma apply_nonneg (f : B → ℝ) (hf : ∀ x,0 ≤ f x) (x : B) : 0 ≤ Q.apply f x :=
  Finset.sum_nonneg (fun y _ => mul_nonneg (Q.nonnegative x y) (hf y))
lemma iterate_nonneg (k : ℕ) (f : B → ℝ) (hf : ∀ x,0 ≤ f x) (x : B) : 0 ≤ Q.iterate k f x := by
  induction k generalizing x with
  | zero => exact hf x
  | succ k ih =>
    rw [Q.iterate_succ]
    exact Q.apply_nonneg _ ih x

lemma apply_abs_bound (f : B → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ x,|f x| ≤ M) (x : B) :
    |Q.apply f x| ≤ Q.r*M := by
  calc
    _ ≤ ∑ y,|Q.Q x y*f y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y,Q.Q x y*|f y| := by simp_rw [abs_mul,abs_of_nonneg (Q.nonnegative x _) ]
    _ ≤ ∑ y,Q.Q x y*M := Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hf y) (Q.nonnegative x y))
    _ = (∑ y,Q.Q x y)*M := (Finset.sum_mul _ _ _).symm
    _ ≤ Q.r*M := mul_le_mul_of_nonneg_right (Q.rowbound x) hM

lemma iterate_abs_bound (k : ℕ) (f : B → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ x,|f x| ≤ M) (x : B) :
    |Q.iterate k f x| ≤ Q.r^k*M := by
  induction k generalizing x with
  | zero => simpa using hf x
  | succ k ih =>
    rw [Q.iterate_succ,pow_succ']
    simpa only [mul_assoc] using Q.apply_abs_bound (Q.iterate k f) (Q.r^k*M)
      (mul_nonneg (pow_nonneg Q.rnonneg _) hM) ih x

lemma summable_iterate (f : B → ℝ) (x : B) : Summable (fun k => Q.iterate k f x) := by
  let M := ∑ y,|f y|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun y _ => abs_nonneg _)
  have hf : ∀ y,|f y| ≤ M := fun y => Finset.single_le_sum (f := fun z => |f z|) (fun z _ => abs_nonneg _) (Finset.mem_univ y)
  exact (Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => Q.iterate_abs_bound k f M hM hf x)
    ((summable_geometric_of_lt_one Q.rnonneg Q.rlt).mul_right M)).of_abs

lemma iterate_tendsto_zero (f : B → ℝ) (x : B) : Tendsto (fun k => Q.iterate k f x) atTop (nhds 0) := by
  let M := ∑ y,|f y|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun y _ => abs_nonneg _)
  have hf : ∀ y,|f y| ≤ M := fun y => Finset.single_le_sum (f := fun z => |f z|) (fun z _ => abs_nonneg _) (Finset.mem_univ y)
  have ht : Tendsto (fun k => Q.r^k*M) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one Q.rnonneg Q.rlt).mul_const M
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr (squeeze_zero (fun k => abs_nonneg _)
    (fun k => Q.iterate_abs_bound k f M hM hf x) ht)

noncomputable def green (f : B → ℝ) (x : B) : ℝ := ∑' k,Q.iterate k f x
lemma green_nonneg (f : B → ℝ) (hf : ∀ x,0 ≤ f x) (x : B) : 0 ≤ Q.green f x :=
  tsum_nonneg (fun k => Q.iterate_nonneg k f hf x)

lemma green_firstStep (f : B → ℝ) (x : B) : Q.green f x = f x+Q.apply (Q.green f) x := by
  unfold green
  rw [(Q.summable_iterate f x).tsum_eq_zero_add]
  simp only [Q.iterate_zero,Q.iterate_succ,apply]
  congr 1
  rw [Summable.tsum_finsetSum (fun y (_ : y ∈ Finset.univ) => (Q.summable_iterate f y).mul_left (Q.Q x y))]
  simp_rw [tsum_mul_left]

lemma iterate_sub (k : ℕ) (f g : B → ℝ) :
    Q.iterate k (fun x => f x-g x) = fun x => Q.iterate k f x-Q.iterate k g x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Q.iterate_succ,ih,Q.apply_sub,← Q.iterate_succ,← Q.iterate_succ]
lemma iterate_sum {J : Type*} (s : Finset J) (f : J → B → ℝ) (k : ℕ) :
    Q.iterate k (fun x => ∑ j ∈ s,f j x) = fun x => ∑ j ∈ s,Q.iterate k (f j) x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Q.iterate_succ,ih,Q.apply_sum]; simp_rw [← Q.iterate_succ]

lemma green_sum {J : Type*} (s : Finset J) (f : J → B → ℝ) (x : B) :
    Q.green (fun x => ∑ j ∈ s,f j x) x = ∑ j ∈ s,Q.green (f j) x := by
  unfold green
  simp_rw [Q.iterate_sum]
  exact Summable.tsum_finsetSum (fun j _ => Q.summable_iterate (f j) x)

lemma iterate_residual_sum (f : B → ℝ) (N : ℕ) (x : B) :
    (∑ k ∈ Finset.range N,Q.iterate k (fun y => f y-Q.apply f y) x) = f x-Q.iterate N f x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,Q.iterate_sub,← Q.iterate_succ']
    simp only
    ring

lemma green_residual (f : B → ℝ) (x : B) : Q.green (fun y => f y-Q.apply f y) x = f x := by
  have hs := (Q.summable_iterate (fun y => f y-Q.apply f y) x).tendsto_sum_tsum_nat
  simp_rw [Q.iterate_residual_sum] at hs
  have ht : Tendsto (fun N => f x-Q.iterate N f x) atTop (nhds (f x)) := by
    simpa using tendsto_const_nhds.sub (Q.iterate_tendsto_zero f x)
  exact tendsto_nhds_unique hs ht

end KilledKernel
namespace FiniteChain

section
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance66 : Fintype X] (C : FiniteChain X) (A : X → Prop)

abbrev Inside := {x : X // A x}
abbrev Outside := {x : X // ¬ A x}

noncomputable def mergeFun (h : Inside A → ℝ) (b : Outside A → ℝ) (x : X) : ℝ :=
  if hx : A x then h ⟨x,hx⟩ else b ⟨x,hx⟩
omit sectionInstance66 in
@[simp] lemma mergeFun_inside [Fintype X] (h : Inside A → ℝ) (b : Outside A → ℝ) (x : Inside A) :
    mergeFun A h b x.val = h x := by simp [mergeFun,x.property]
omit sectionInstance66 in
@[simp] lemma mergeFun_outside [Fintype X] (h : Inside A → ℝ) (b : Outside A → ℝ) (x : Outside A) :
    mergeFun A h b x.val = b x := by simp [mergeFun,x.property]

variable (Q : KilledKernel (Outside A)) (hQ : ∀ x y : Outside A,Q.Q x y = C.P x.val y.val)

noncomputable def hitKernel (x : Outside A) (y : Inside A) : ℝ :=
  Q.green (fun z => C.P z.val y.val) x
lemma hitKernel_nonneg (x : Outside A) (y : Inside A) : 0 ≤ C.hitKernel A Q x y :=
  Q.green_nonneg _ (fun z => C.nonnegative z.val y.val) x

include hQ in
lemma exitRow (x : Outside A) : (∑ y : Inside A,C.P x.val y.val) = 1-Q.apply (fun _ => 1) x := by
  have hh := Fintype.sum_subtype_add_sum_subtype A (fun y => C.P x.val y)
  rw [C.stochastic] at hh
  have he : Q.apply (fun _ => 1) x = ∑ y : Outside A,C.P x.val y.val := by
    simp [KilledKernel.apply,hQ]
  rw [he]
  linarith

include hQ in
lemma hitKernel_row (x : Outside A) : ∑ y : Inside A,C.hitKernel A Q x y = 1 := by
  unfold hitKernel
  rw [← Q.green_sum Finset.univ]
  have he : (fun z : Outside A => ∑ y : Inside A,C.P z.val y.val) =
      fun z => 1-Q.apply (fun _ => 1) z := by
    funext z
    exact C.exitRow A Q hQ z
  rw [he,Q.green_residual]

include hQ in
lemma hitKernel_firstStep (x : Outside A) (y : Inside A) :
    C.hitKernel A Q x y = C.P x.val y.val+∑ z : Outside A,C.P x.val z.val*C.hitKernel A Q z y := by
  unfold hitKernel
  rw [Q.green_firstStep]
  simp only [KilledKernel.apply,hQ]

noncomputable def traceMatrix (x y : Inside A) : ℝ :=
  C.P x.val y.val+∑ z : Outside A,C.P x.val z.val*C.hitKernel A Q z y
noncomputable def traceApply (h : Inside A → ℝ) (x : Inside A) : ℝ :=
  ∑ y,C.traceMatrix A Q x y*h y

lemma traceMatrix_nonneg (x y : Inside A) : 0 ≤ C.traceMatrix A Q x y :=
  add_nonneg (C.nonnegative _ _) (Finset.sum_nonneg (fun z _ => mul_nonneg
    (C.nonnegative _ _) (C.hitKernel_nonneg A Q z y)))
lemma traceMatrix_lazy (x : Inside A) : 1/2 ≤ C.traceMatrix A Q x x := by
  exact (C.lazy x.val).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun z _ =>
    mul_nonneg (C.nonnegative _ _) (C.hitKernel_nonneg A Q z x))))
include hQ in
lemma traceMatrix_stochastic (x : Inside A) : ∑ y,C.traceMatrix A Q x y = 1 := by
  unfold traceMatrix
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,C.hitKernel_row A Q hQ,mul_one]
  rw [Fintype.sum_subtype_add_sum_subtype A,C.stochastic]

noncomputable def offExtension (h : Inside A → ℝ) (x : Outside A) : ℝ :=
  ∑ y : Inside A,C.hitKernel A Q x y*h y
noncomputable def harmonicExtension (h : Inside A → ℝ) : X → ℝ := mergeFun A h (C.offExtension A Q h)
@[simp] lemma harmonicExtension_inside (h : Inside A → ℝ) (x : Inside A) :
    C.harmonicExtension A Q h x.val = h x := mergeFun_inside _ _ _ _
@[simp] lemma harmonicExtension_outside (h : Inside A → ℝ) (x : Outside A) :
    C.harmonicExtension A Q h x.val = C.offExtension A Q h x := mergeFun_outside _ _ _ _

include hQ in
lemma offExtension_firstStep (h : Inside A → ℝ) (x : Outside A) :
    C.offExtension A Q h x = (∑ y : Inside A,C.P x.val y.val*h y)+
      ∑ z : Outside A,C.P x.val z.val*C.offExtension A Q h z := by
  unfold offExtension
  calc
    _ = ∑ y : Inside A,(C.P x.val y.val+∑ z : Outside A,C.P x.val z.val*C.hitKernel A Q z y)*h y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [C.hitKernel_firstStep A Q hQ]
    _ = _ := ?_
  simp only [add_mul,Finset.sum_mul,Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp_rw [mul_assoc,← Finset.mul_sum]

include hQ in
lemma harmonicExtension_harmonic (h : Inside A → ℝ) (x : Outside A) :
    C.apply (C.harmonicExtension A Q h) x.val = C.harmonicExtension A Q h x.val := by
  unfold apply
  rw [← Fintype.sum_subtype_add_sum_subtype A]
  simp only [C.harmonicExtension_inside,C.harmonicExtension_outside]
  exact (C.offExtension_firstStep A Q hQ h x).symm

lemma apply_harmonicExtension_inside (h : Inside A → ℝ) (x : Inside A) :
    C.apply (C.harmonicExtension A Q h) x.val = C.traceApply A Q h x := by
  unfold apply
  rw [← Fintype.sum_subtype_add_sum_subtype A]
  simp only [C.harmonicExtension_inside,C.harmonicExtension_outside]
  unfold traceApply traceMatrix offExtension
  simp_rw [add_mul,Finset.sum_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

include hQ in
lemma harmonic_inner_residual (h g : Inside A → ℝ) :
    C.inner (C.harmonicExtension A Q h)
      (fun x => C.harmonicExtension A Q g x-C.apply (C.harmonicExtension A Q g) x) =
    ∑ x : Inside A,C.π x.val*h x*(g x-C.traceApply A Q g x) := by
  unfold inner
  rw [← Fintype.sum_subtype_add_sum_subtype A]
  simp only [C.harmonicExtension_inside,C.apply_harmonicExtension_inside,
    C.harmonicExtension_harmonic A Q hQ,sub_self,mul_zero,Finset.sum_const_zero,add_zero]

end
section
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X) (A : X → Prop)
variable (Q : KilledKernel (Outside A)) (hQ : ∀ x y : Outside A,Q.Q x y = C.P x.val y.val)

lemma residual_symmetric (f g : X → ℝ) :
    C.inner f (fun x => g x-C.apply g x) = C.inner g (fun x => f x-C.apply f x) := by
  rw [C.inner_sub_right,C.inner_sub_right,C.apply_selfAdjoint,C.inner_symm f g,
    C.inner_symm (C.apply f) g]

include hQ in
lemma traceMatrix_reversible (x y : Inside A) :
    C.π x.val*C.traceMatrix A Q x y = C.π y.val*C.traceMatrix A Q y x := by
  by_cases hxy : x = y
  · subst y; rfl
  have h := C.residual_symmetric (C.harmonicExtension A Q (fun z => if z=x then 1 else 0))
    (C.harmonicExtension A Q (fun z => if z=y then 1 else 0))
  rw [C.harmonic_inner_residual A Q hQ,C.harmonic_inner_residual A Q hQ] at h
  simp [traceApply,hxy,Ne.symm hxy] at h
  linarith

noncomputable def insideMass : ℝ := ∑ x : Inside A,C.π x.val
lemma insideMass_pos [Nonempty (Inside A)] : 0 < C.insideMass A := by
  apply Finset.sum_pos
  · intro x _; exact C.positive _
  · exact Finset.univ_nonempty

noncomputable def traceChain [Nonempty (Inside A)] : FiniteChain (Inside A) where
  P := C.traceMatrix A Q
  π := fun x => C.π x.val/C.insideMass A
  positive := fun x => div_pos (C.positive _) (C.insideMass_pos A)
  normalized := by rw [← Finset.sum_div]; exact div_self (C.insideMass_pos A).ne'
  nonnegative := C.traceMatrix_nonneg A Q
  stochastic := C.traceMatrix_stochastic A Q hQ
  reversible := by
    intro x y
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,C.traceMatrix_reversible A Q hQ]
  lazy := C.traceMatrix_lazy A Q

noncomputable def duration (x : Outside A) : ℝ := Q.green (fun _ => 1) x
noncomputable def returnCost (x : Inside A) : ℝ :=
  1+∑ y : Outside A,C.P x.val y.val*duration A Q y
end
section
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X) (A : X → Prop)
variable (hExit : ∀ x : Outside A,∃ y : Inside A,0 < C.P x.val y.val)
noncomputable def exitProbability (x : Outside A) : ℝ := ∑ y : Inside A,C.P x.val y.val
lemma exitProbability_nonneg (x : Outside A) : 0 ≤ C.exitProbability A x :=
  Finset.sum_nonneg (fun y _ => C.nonnegative x.val y.val)
include hExit in
lemma exitProbability_pos (x : Outside A) : 0 < C.exitProbability A x := by
  obtain ⟨y,hy⟩ := hExit x
  exact hy.trans_le (Finset.single_le_sum (fun z _ => C.nonnegative _ _) (Finset.mem_univ y))
lemma exitProbability_le_one (x : Outside A) : C.exitProbability A x ≤ 1 := by
  have h := Fintype.sum_subtype_add_sum_subtype A (fun y => C.P x.val y)
  rw [C.stochastic] at h
  have hn : 0 ≤ ∑ y : Outside A,C.P x.val y.val := Finset.sum_nonneg (fun y _ => C.nonnegative _ _)
  change (∑ y : Inside A,C.P x.val y.val) ≤ 1
  linarith
noncomputable def killedChain : KilledKernel (Outside A) where
  Q := fun x y => C.P x.val y.val
  r := 1-∏ x : Outside A,C.exitProbability A x
  nonnegative := fun x y => C.nonnegative _ _
  rnonneg := sub_nonneg.mpr (Finset.prod_le_one (fun x _ => C.exitProbability_nonneg A x)
    (fun x _ => C.exitProbability_le_one A x))
  rlt := by
    have h : 0 < ∏ x : Outside A,C.exitProbability A x := Finset.prod_pos (fun x _ => C.exitProbability_pos A hExit x)
    linarith
  rowbound := by
    intro x
    have hprod : (∏ z : Outside A,C.exitProbability A z) ≤ C.exitProbability A x := by
      have h := Finset.prod_le_prod_of_subset_of_le_one (Finset.singleton_subset_iff.mpr (Finset.mem_univ x))
        (fun z (_ : z ∈ Finset.univ) => C.exitProbability_nonneg A z)
        (fun z _ _ => C.exitProbability_le_one A z)
      simpa only [Finset.prod_singleton] using h
    have hs := Fintype.sum_subtype_add_sum_subtype A (fun y => C.P x.val y)
    rw [C.stochastic] at hs
    change (∑ y : Inside A,C.P x.val y.val)+(∑ y : Outside A,C.P x.val y.val) = 1 at hs
    unfold exitProbability at hprod ⊢
    linarith
end
open scoped Classical BigOperators
variable {X : Type*} [Fintype X] (C : FiniteChain X)

noncomputable def pointDensity (x : X) (y : X) : ℝ := if y=x then 1/C.π x else 0
noncomputable def centeredPoint (x : X) (y : X) : ℝ := C.pointDensity x y-1
end FiniteChain
section TraceGeometry
open scoped Classical BigOperators
variable {Γ : Type*} [Fintype Γ] [sectionInstance71 : DecidableEq Γ]

lemma SlotsFresh.cross_ne {gs : List (Γ × Γ)} {A : Set Γ} (hgs : SlotsFresh gs A)
    {p r : Γ × Γ} (hp : p ∈ gs) (hr : r ∈ gs) (hpr : p ≠ r)
    {x y : Γ} (hx : x=p.1 ∨ x=p.2) (hy : y=r.1 ∨ y=r.2) : x ≠ y := by
  intro hxy
  have := hgs.pair_contains_unique hp hr hx (hxy ▸ hy)
  exact hpr this

lemma DefectState.plain_neighbor {gs : List (Γ × Γ)} (hgs : SlotsFresh gs ∅)
    {p r : Γ × Γ} {S : Set Γ} (hS : DefectState gs p r S) :
    ∃ T,PlainState gs T ∧ ExchangeAdjacent S T := by
  obtain ⟨hp,hr,hpr,he,hf,ht⟩ := hS
  let T := insert p.1 (S\{r.1})
  have hpne : p.1 ≠ p.2 := ((SlotsFresh.perm (List.perm_cons_erase hp) ∅).mp hgs).1
  have hrne : r.1 ≠ r.2 := ((SlotsFresh.perm (List.perm_cons_erase hr) ∅).mp hgs).1
  have hpr11 : p.1 ≠ r.1 := hgs.cross_ne hp hr hpr (Or.inl rfl) (Or.inl rfl)
  have hpr21 : p.2 ≠ r.1 := hgs.cross_ne hp hr hpr (Or.inr rfl) (Or.inl rfl)
  have hpr12 : p.1 ≠ r.2 := hgs.cross_ne hp hr hpr (Or.inl rfl) (Or.inr rfl)
  refine ⟨T,?_,?_⟩
  · intro t htm
    by_cases htp : t=p
    · subst t
      simp [PairSingle,T,hpne.symm,he.1,he.2]
    by_cases htr : t=r
    · subst t
      simp [PairSingle,T,hpr11.symm,hpr12.symm,hrne.symm,hf.2]
    have h₁ : t.1 ≠ p.1 := hgs.cross_ne htm hp htp (Or.inl rfl) (Or.inl rfl)
    have h₂ : t.2 ≠ p.1 := hgs.cross_ne htm hp htp (Or.inr rfl) (Or.inl rfl)
    have h₃ : t.1 ≠ r.1 := hgs.cross_ne htm hr htr (Or.inl rfl) (Or.inl rfl)
    have h₄ : t.2 ≠ r.1 := hgs.cross_ne htm hr htr (Or.inr rfl) (Or.inl rfl)
    simpa only [PairSingle,T,Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff,
      h₁,h₂,h₃,h₄,false_or,not_false_eq_true,and_true] using ht t htm htp htr
  · refine ⟨S\{r.1},r.1,p.1,hpr11.symm,by simp,?_,?_,rfl⟩
    · exact fun h => he.1 h.1
    · ext x
      simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
      constructor
      · intro hx
        by_cases h : x=r.1
        · exact Or.inl h
        · exact Or.inr ⟨hx,h⟩
      · rintro (rfl|⟨hx,_⟩)
        · exact hf.1
        · exact hx

abbrev PlainIndex (gs : List (Γ × Γ)) :=
  FiniteChain.Inside (fun S : ChainIndex gs => PlainState gs S.val)

omit sectionInstance71 in
lemma plainIndex_sum [DecidableEq Γ] (gs : List (Γ × Γ)) (g : Set Γ → ℝ) :
    (∑ S : PlainIndex gs,g S.val.val) = ∑ S ∈ Finset.univ.filter (PlainState gs),g S := by
  let e : PlainIndex gs ≃ {S : Set Γ // PlainState gs S} :=
    { toFun := fun S => ⟨S.val.val,S.property⟩
      invFun := fun S => ⟨⟨S.val,Or.inl S.property⟩,S.property⟩
      left_inv := by intro; rfl
      right_inv := by intro; rfl }
  calc
    _ = ∑ S : {S : Set Γ // PlainState gs S},g S.val :=
      Fintype.sum_equiv e _ _ (by intro S; rfl)
    _ = _ := (Finset.sum_subtype _ (by intro S; simp) g).symm

lemma plainIndex_nonempty (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs = Set.univ) : Nonempty (PlainIndex gs) := by
  have hz := slotTotal_pos gs (fun _ => (1:ℝ)) (by intro; norm_num) ∅ hgs
  rw [slotTotal_eq_plain_sum gs hgs hcover,← plainIndex_sum] at hz
  by_contra h
  have : IsEmpty (PlainIndex gs) := not_nonempty_iff.mp h
  simp at hz

lemma metropolis_plain_exit (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
    (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S)
    (S : FiniteChain.Outside (fun S : ChainIndex gs => PlainState gs S.val)) :
    ∃ T : PlainIndex gs,0 < (metropolisChain gs hgs hne hcover w f hw hf).P S.val T.val := by
  obtain ⟨p,r,hS⟩ := S.val.property.resolve_left S.property
  obtain ⟨T,hT,hST⟩ := hS.plain_neighbor hgs
  let t : PlainIndex gs := ⟨⟨T,Or.inl hT⟩,hT⟩
  refine ⟨t,?_⟩
  have hneST : S.val ≠ t.val := by intro h; exact hST.ne (congrArg Subtype.val h)
  change 0 < metropolisMove gs w f S.val t.val+if S.val=t.val then _ else _
  rw [ite_eq_right hneST,add_zero]
  unfold metropolisMove
  rw [ite_eq_left hST]
  have hn : (0:ℝ) < gs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  exact div_pos (lt_min (chainWeight_pos gs w f hw hf _) (chainWeight_pos gs w f hw hf _))
    (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hn)) (chainWeight_pos gs w f hw hf _))
end TraceGeometry
section TracePoincare
open scoped Classical BigOperators
variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
variable (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs ≠ [])
  (hcover : pairSupport gs = Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
  (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S)

abbrev plainPredicate (gs : List (Γ × Γ)) (S : ChainIndex gs) := PlainState gs S.val
noncomputable def metropolisKilled : KilledKernel (FiniteChain.Outside (plainPredicate gs)) :=
  (metropolisChain gs hgs hne hcover w f hw hf).killedChain (plainPredicate gs)
    (metropolis_plain_exit gs hgs hne hcover w f hw hf)

noncomputable def metropolisTrace : FiniteChain (PlainIndex gs) := by
  letI := plainIndex_nonempty gs hgs hcover
  exact (metropolisChain gs hgs hne hcover w f hw hf).traceChain (plainPredicate gs)
    (metropolisKilled gs hgs hne hcover w f hw hf) (by intro _ _; rfl)

end TracePoincare

namespace KilledKernel
open scoped BigOperators Classical
variable {B : Type*} [Fintype B] (Q : KilledKernel B)
noncomputable def partialGreen (N : ℕ) (f : B → ℝ) (x : B) : ℝ :=
  ∑ k ∈ Finset.range N,Q.iterate k f x
lemma partialGreen_nonneg (N : ℕ) (f : B → ℝ) (hf : ∀ x,0 ≤ f x) (x : B) :
    0 ≤ Q.partialGreen N f x := Finset.sum_nonneg (fun k _ => Q.iterate_nonneg k f hf x)
lemma partialGreen_le (N : ℕ) (f : B → ℝ) (hf : ∀ x,0 ≤ f x) (x : B) :
    Q.partialGreen N f x ≤ Q.green f x :=
  (Q.summable_iterate f x).sum_le_tsum (Finset.range N) (fun k _ => Q.iterate_nonneg k f hf x)
end KilledKernel

namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X) (A : X → Prop)
  (Q : KilledKernel (Outside A)) (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)

noncomputable def cappedTrace (N : ℕ) (x y : Inside A) : ℝ :=
  C.P x.val y.val + ∑ z : Outside A,C.P x.val z.val*
    Q.partialGreen N (fun t => C.P t.val y.val) z
lemma cappedTrace_nonneg (N : ℕ) (x y : Inside A) : 0 ≤ C.cappedTrace A Q N x y := by
  apply add_nonneg (C.nonnegative _ _)
  exact Finset.sum_nonneg (fun z _ => mul_nonneg (C.nonnegative _ _)
    (Q.partialGreen_nonneg N _ (fun t => C.nonnegative _ _) z))
lemma cappedTrace_le (N : ℕ) (x y : Inside A) : C.cappedTrace A Q N x y ≤ C.traceMatrix A Q x y := by
  unfold cappedTrace traceMatrix
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro z _
  exact mul_le_mul_of_nonneg_left (Q.partialGreen_le N _ (fun t => C.nonnegative _ _) z) (C.nonnegative _ _)

include hQ in
lemma cappedTrace_substochastic (N : ℕ) (x : Inside A) : ∑ y,C.cappedTrace A Q N x y ≤ 1 := by
  calc
    _ ≤ ∑ y,C.traceMatrix A Q x y := Finset.sum_le_sum (fun y _ => C.cappedTrace_le A Q N x y)
    _ = 1 := C.traceMatrix_stochastic A Q hQ x

end FiniteChain

structure FiniteKernel (X Y : Type*) [Fintype Y] where
  P : X → Y → ℝ
  nonnegative : ∀ x y,0 ≤ P x y
  substochastic : ∀ x,∑ y,P x y ≤ 1
namespace FiniteKernel
open scoped BigOperators Classical
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
noncomputable def identity : FiniteKernel X X where
  P x y := if x=y then 1 else 0
  nonnegative := by intros; split_ifs <;> norm_num
  substochastic := by intro x; simp
noncomputable def comp (K : FiniteKernel X Y) (L : FiniteKernel Y Z) : FiniteKernel X Z where
  P x z := ∑ y,K.P x y*L.P y z
  nonnegative := by intros; exact Finset.sum_nonneg (fun y _ => mul_nonneg (K.nonnegative _ _) (L.nonnegative _ _))
  substochastic := by
    intro x
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ y,K.P x y*1 := Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (L.substochastic y) (K.nonnegative x y))
      _ ≤ 1 := by simp only [mul_one]; exact K.substochastic x
noncomputable def push (K : FiniteKernel X Y) (ν : X → ℝ) (y : Y) := ∑ x,ν x*K.P x y
noncomputable def power (K : FiniteKernel X X) : ℕ → FiniteKernel X X
  | 0 => identity
  | n+1 => (K.power n).comp K
end FiniteKernel

namespace FiniteChain

section
open scoped BigOperators Classical
variable {X : Type*} [Fintype X] (C : FiniteChain X)
noncomputable def kernel : FiniteKernel X X where
  P := C.P
  nonnegative := C.nonnegative
  substochastic := fun x => (C.stochastic x).le

variable (A : X → Prop) (Q : KilledKernel (Outside A)) (hQ : ∀ x y,Q.Q x y=C.P x.val y.val)
noncomputable def cappedTraceKernel (N : ℕ) : FiniteKernel (Inside A) (Inside A) where
  P := C.cappedTrace A Q N
  nonnegative := C.cappedTrace_nonneg A Q N
  substochastic := C.cappedTrace_substochastic A Q hQ N
end

section
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance81 : Fintype X] (C : FiniteChain X)

noncomputable def pathProbability (ν : X → ℝ) (N : ℕ) (E : List X → Prop) : ℝ :=
  ∑ x,ν x*C.pathExpectation N x (fun l => if E l then 1 else 0)
end

open scoped BigOperators Classical
end FiniteChain

section SamplingObservables
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance85 : Fintype Γ] [DecidableEq Γ]
noncomputable def plainObservable (gs : List (Γ × Γ)) (g : Set Γ → ℝ) (S : Set Γ) : ℝ :=
  if PlainState gs S then g S else 0
noncomputable def defectIndicator (gs : List (Γ × Γ)) (p r : Γ × Γ) (S : Set Γ) : ℝ :=
  if DefectState gs p r S then 1 else 0
lemma plainObservable_mean (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f g : Set Γ → ℝ) : chainMean gs w f (plainObservable gs g) =
      slotTotal gs (fun S =>  f S*g S) ∅/chainTotal gs w f := by
  unfold chainMean
  congr 1
  simp only [chainWeight,mul_assoc]
  rw [chain_sum_decomposition,slotTotal_eq_plain_sum gs hgs hcover]
  have hplain : (∑ S with PlainState gs S,f S*plainObservable gs g S)=
      ∑ S with PlainState gs S,f S*g S := by
    apply Finset.sum_congr rfl
    intro S hS
    simp [plainObservable,(Finset.mem_filter.mp hS).2]
  rw [hplain]
  have hdef : ∀ pr ∈ defectTypes gs,(∑ S with DefectState gs pr.1 pr.2 S,f S*plainObservable gs g S)=0 := by
    intro pr hpr
    apply Finset.sum_eq_zero
    intro S hS
    simp [plainObservable,((Finset.mem_filter.mp hS).2).not_plain]
  rw [add_eq_left]
  apply Finset.sum_eq_zero
  intro pr hpr
  rw [hdef pr hpr,mul_zero]
lemma defectIndicator_mean (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (p r : Γ × Γ) (hp : p∈gs) (hr : r∈gs) (hpr : p≠r) :
    chainMean gs w f (defectIndicator gs p r) =
      w p r*slotDefect gs f ∅ p r/chainTotal gs w f := by
  unfold chainMean
  congr 1
  simp only [chainWeight,mul_assoc]
  rw [chain_sum_decomposition,slotDefect_eq_defect_sum gs hgs hcover f p r hp hr hpr]
  have hplain : (∑ S with PlainState gs S,f S*defectIndicator gs p r S)=0 := by
    apply Finset.sum_eq_zero
    intro S hS
    have hh : ¬DefectState gs p r S := fun h =>  h.not_plain (Finset.mem_filter.mp hS).2
    simp [defectIndicator,hh]
  rw [hplain,zero_add]
  rw [Finset.sum_eq_single (p,r)]
  · congr 1
    apply Finset.sum_congr rfl
    intro S hS
    simp [defectIndicator,(Finset.mem_filter.mp hS).2]
  · intro pr hm hne
    have he : ∀ S,DefectState gs pr.1 pr.2 S → ¬DefectState gs p r S := by
      intro S hS h
      exact hne (Prod.ext (hS.unique h).1 (hS.unique h).2)
    have hz : (∑ S with DefectState gs pr.1 pr.2 S,f S*defectIndicator gs p r S)=0 := by
      apply Finset.sum_eq_zero
      intro S hS
      simp [defectIndicator,he S (Finset.mem_filter.mp hS).2]
    rw [hz,mul_zero]
  · intro h
    exact (h ((mem_defectTypes gs (p,r)).mpr ⟨hp,hr,hpr⟩)).elim

abbrev PhaseObservables (gs : List (Γ × Γ)) := Option {pr // pr∈defectTypes gs} ⊕ Unit
noncomputable def phaseObservable (gs : List (Γ × Γ)) (g : Set Γ → ℝ) :
    PhaseObservables gs → Set Γ → ℝ
  | .inl none => plainObservable gs (fun _ => 1)
  | .inl (some pr) => defectIndicator gs pr.val.1 pr.val.2
  | .inr _ => plainObservable gs g
end SamplingObservables

open Set

section PairedReduction
variable {α β : Type*}

def pairedMatroid (M₁ M₂ : Matroid α) : Matroid (α ⊕ α) := M₁.sum M₂✶

def transversal (A : Set α) : Set (α ⊕ α) := Sum.inl '' A ∪ Sum.inr '' Aᶜ

@[simp] lemma preimage_inl_transversal (A : Set α) :
    Sum.inl ⁻¹' transversal A = A := by
  simp [transversal, Set.preimage_image_eq _ Sum.inl_injective]

@[simp] lemma preimage_inr_transversal (A : Set α) :
    Sum.inr ⁻¹' transversal A = Aᶜ := by
  simp [transversal, 
    Set.preimage_image_eq _ Sum.inr_injective]

end PairedReduction

open scoped BigOperators Classical

noncomputable def annealRho (n : ℕ) : ℝ := 1 - 1 / (2 * (n : ℝ))
def annealLength (n b : ℕ) : ℕ := 2*n*(n+b)
noncomputable def annealTolerance (ε : ℝ) (L : ℕ) : ℝ := ε/(32*((L:ℝ)+1))

lemma annealRho_bounds (n : ℕ) (hn : 0<n) : 1/2 ≤ annealRho n ∧ annealRho n < 1 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  unfold annealRho
  have hh : 0 < 2*(n:ℝ) := by positivity
  constructor
  · have := (div_le_iff₀ hh).mpr (show (1:ℝ) ≤ (1/2)*(2*n) by nlinarith)
    linarith
  · have := div_pos (show (0:ℝ)<1 by norm_num) hh
    linarith
lemma annealRho_pow_lower (n : ℕ) (hn : 0<n) : 1/2 ≤ annealRho n ^ n := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have h := one_add_mul_le_pow (a := -(1/(2*(n:ℝ)))) (by
    have hh := (annealRho_bounds n hn).1
    unfold annealRho at hh
    linarith) n
  have he : 1+(n:ℝ)*(-(1/(2*n))) = 1/2 := by field_simp; ring
  simpa only [he,annealRho,sub_eq_add_neg] using h
lemma annealStep_bounds (n d : ℕ) (hn : 0<n) (hd : d≤n) :
    1/2 ≤ annealRho n ^ d ∧ annealRho n ^ d ≤ 1 := by
  have hr := annealRho_bounds n hn
  have h0 : 0 ≤ annealRho n := by linarith
  exact ⟨(annealRho_pow_lower n hn).trans (pow_le_pow_of_le_one h0 hr.2.le hd),
    pow_le_one₀ h0 hr.2.le⟩

section CoefficientDrift
variable {X : Type*} [Fintype X]

noncomputable def deficiencyPartition (d : X → ℕ) (q : ℝ) : ℝ := ∑ x,q^(d x)
end CoefficientDrift

lemma estimated_ratio_bounds (η p u phat uhat : ℝ) (hη0 : 0≤η) (hη1 : η<1)
    (hp : 0<p) (hu : 0<u)
    (hphat : (1-η)*p ≤ phat ∧ phat ≤ (1+η)*p)
    (huhat : (1-η)*u ≤ uhat ∧ uhat ≤ (1+η)*u) :
    0<phat ∧ (1-η)/(1+η) ≤ (uhat/phat)/(u/p) ∧
      (uhat/phat)/(u/p) ≤ (1+η)/(1-η) := by
  have hp' : 0<phat := lt_of_lt_of_le (mul_pos (by linarith) hp) hphat.1
  have hu' : 0<uhat := lt_of_lt_of_le (mul_pos (by linarith) hu) huhat.1
  refine ⟨hp',?_,?_⟩
  · rw [le_div_iff₀ (div_pos hu hp),div_mul_div_comm,div_le_div_iff₀ (mul_pos (by linarith) hp) hp']
    have h1 := mul_le_mul_of_nonneg_left hphat.2 (mul_nonneg (by linarith : 0≤1-η) hu.le)
    have h2 := mul_le_mul_of_nonneg_right huhat.1 (mul_nonneg (by linarith : 0≤1+η) hp.le)
    nlinarith
  · rw [div_le_iff₀ (div_pos hu hp),div_mul_div_comm,
      div_le_div_iff₀ hp' (mul_pos (by linarith) hp)]
    have h1 := mul_le_mul_of_nonneg_left hphat.1 (mul_nonneg (by linarith : 0≤1+η) hu.le)
    have h2 := mul_le_mul_of_nonneg_right huhat.2 (mul_nonneg (by linarith : 0≤1-η) hp.le)
    nlinarith

lemma ratio_coarse_bounds (η : ℝ) (h0 : 0≤η) (h1 : η≤1/3) :
    1/2 ≤ (1-η)/(1+η) ∧ (1+η)/(1-η) ≤ 2 := by
  constructor
  · rw [le_div_iff₀ (by linarith : 0<1+η)]; linarith
  · rw [div_le_iff₀ (by linarith : 0<1-η)]; linarith

lemma learned_multiplier_good (w p0 pt phat0 phatt ideal nextIdeal η : ℝ)
    (hw : 0<w) (hp0 : 0<p0) (hpt : 0<pt) (_ : 0 < ideal)
    (hidentity : w*(p0/pt)=ideal) (hη0 : 0≤η) (hη1 : η≤1/3)
    (hphat0 : (1-η)*p0≤phat0 ∧ phat0≤(1+η)*p0)
    (hphatt : (1-η)*pt≤phatt ∧ phatt≤(1+η)*pt)
    (hdrift : ideal/2≤nextIdeal ∧ nextIdeal≤2*ideal) :
    nextIdeal/4 ≤ w*(phat0/phatt) ∧ w*(phat0/phatt)≤4*nextIdeal := by
  have hb := estimated_ratio_bounds η pt p0 phatt phat0 hη0 (by linarith) hpt hp0 hphatt hphat0
  have hc := ratio_coarse_bounds η hη0 hη1
  have hl := (le_div_iff₀ (div_pos hp0 hpt)).mp (hc.1.trans hb.2.1)
  have hu := (div_le_iff₀ (div_pos hp0 hpt)).mp (hb.2.2.trans hc.2)
  have hl' := mul_le_mul_of_nonneg_left hl hw.le
  have hu' := mul_le_mul_of_nonneg_left hu hw.le
  have hl'' : ideal/2 ≤ w*(phat0/phatt) := by nlinarith [hidentity]
  have hu'' : w*(phat0/phatt) ≤ 2*ideal := by nlinarith [hidentity]
  constructor <;> linarith

section Contamination
variable {X : Type*} [Fintype X]
noncomputable def zeroDeficiencyCount (d : X → ℕ) : ℕ := (Finset.univ.filter (fun x => d x=0)).card
end Contamination

namespace FiniteExperiment
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance89 : Fintype X]

noncomputable def expect (K : List X → X → ℝ) : ℕ → List X → (List X → ℝ) → ℝ
  | 0,h,φ => φ h
  | t+1,h,φ => ∑ x,K h x*expect K t (h++[x]) φ
noncomputable def mass (K : List X → X → ℝ) (t : ℕ) (h : List X) : ℝ :=
  expect K t h (fun _ => 1)

noncomputable def restrict (P : List X → X → ℝ) (Good : List X → Prop) (h : List X) (x : X) : ℝ :=
  if Good (h++[x]) then P h x else 0
end FiniteExperiment
section PairedSlots
open scoped BigOperators Classical
variable {α : Type*} [sectionInstance90 : Fintype α] [sectionInstance91 : DecidableEq α]
def slotPair (i : α) : (α ⊕ α) × (α ⊕ α) := (Sum.inl i,Sum.inr i)
def pairedSlots (n : ℕ) : List ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) :=
  (List.finRange n).map slotPair
omit sectionInstance90 sectionInstance91 in
lemma slotPairList_fresh [Fintype α] [DecidableEq α] (l : List α) (hl : l.Nodup) (B : Set (α ⊕ α))
    (hB : ∀ i ∈ l,Sum.inl i ∉ B ∧ Sum.inr i ∉ B) : SlotsFresh (l.map slotPair) B := by
  induction l generalizing B with
  | nil => trivial
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hl
    refine ⟨by simp [slotPair],(hB a (by simp)).1,(hB a (by simp)).2,?_⟩
    apply ih hl
    intro i hi
    have hn : i ≠ a := fun he => ha (he ▸ hi)
    have hb := hB i (by simp [hi])
    simpa [slotPair,hn] using hb
lemma pairedSlots_fresh (n : ℕ) : SlotsFresh (pairedSlots n) ∅ :=
  slotPairList_fresh _ (List.nodup_finRange n) ∅ (by intros; simp)
@[simp] lemma pairedSlots_length (n : ℕ) : (pairedSlots n).length = n := by simp [pairedSlots]
lemma pairedSlots_ne_nil (n : ℕ) (hn : 0<n) : pairedSlots n ≠ [] := by
  intro h; have hh := congrArg List.length h
  simp only [pairedSlots_length,List.length_nil] at hh
  omega
lemma pairedSlots_cover (n : ℕ) : pairSupport (pairedSlots n) = Set.univ := by
  ext x
  simp only [pairSupport,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  cases x with
  | inl i => exact ⟨slotPair i,by simp [pairedSlots],Or.inl rfl⟩
  | inr i => exact ⟨slotPair i,by simp [pairedSlots],Or.inr rfl⟩
lemma pairedSlots_plain (n : ℕ) (S : Set (Fin n ⊕ Fin n)) :
    PlainState (pairedSlots n) S ↔ ∀ i, (Sum.inl i ∈ S ↔ Sum.inr i ∉ S) := by
  simp only [PlainState,pairedSlots,List.mem_map,forall_exists_index,and_imp]
  constructor
  · intro h i
    have hh := h (slotPair i) i (by simp) rfl
    simp only [PairSingle,slotPair] at hh
    tauto
  · intro h p i hi he
    subst p
    have hh := h i
    simp only [PairSingle,slotPair]
    tauto
lemma transversal_plain (n : ℕ) (A : Set (Fin n)) : PlainState (pairedSlots n) (transversal A) := by
  rw [pairedSlots_plain]
  intro i
  have hl : Sum.inl i ∈ transversal A ↔ i ∈ A := by
    change i ∈ Sum.inl ⁻¹' transversal A ↔ _
    rw [preimage_inl_transversal]
  have hr : Sum.inr i ∈ transversal A ↔ i ∉ A := by
    change i ∈ Sum.inr ⁻¹' transversal A ↔ _
    rw [preimage_inr_transversal]; rfl
  rw [hl,hr,not_not]
lemma plain_eq_transversal (n : ℕ) (S : Set (Fin n ⊕ Fin n)) (hS : PlainState (pairedSlots n) S) :
    S = transversal (Sum.inl ⁻¹' S) := by
  rw [pairedSlots_plain] at hS
  ext x
  cases x with
  | inl i =>
    change i ∈ Sum.inl ⁻¹' S ↔ i ∈ Sum.inl ⁻¹' transversal (Sum.inl ⁻¹' S)
    rw [preimage_inl_transversal]
  | inr i =>
    change Sum.inr i ∈ S ↔ i ∈ Sum.inr ⁻¹' transversal (Sum.inl ⁻¹' S)
    rw [preimage_inr_transversal]
    change Sum.inr i ∈ S ↔ Sum.inl i ∉ S
    have hh := hS i
    tauto
noncomputable def plainEquivSubsets (n : ℕ) :
    {S : Set (Fin n ⊕ Fin n) // PlainState (pairedSlots n) S} ≃ Set (Fin n) where
  toFun S := Sum.inl ⁻¹' S.val
  invFun A := ⟨transversal A,transversal_plain n A⟩
  left_inv S := Subtype.ext (plain_eq_transversal n S.val S.property).symm
  right_inv A := preimage_inl_transversal A
lemma pairedPlain_card (n : ℕ) : Fintype.card {S : Set (Fin n ⊕ Fin n) // PlainState (pairedSlots n) S} = 2^n := by
  rw [Fintype.card_congr (plainEquivSubsets n),Fintype.card_set,Fintype.card_fin]
end PairedSlots
open scoped BigOperators Classical
noncomputable def subsetDeficiency {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (A : Set (Fin n)) : ℕ :=
  n-((pairedMatroid M₁ M₂).eRk (transversal A)).toNat

noncomputable def commonSetFinsetEquiv {n : ℕ} (M₁ M₂ : Matroid (Fin n)) :
    {A : Set (Fin n) // M₁.IsBase A ∧ M₂.IsBase A} ≃
    {A : Finset (Fin n) // M₁.IsBase (A:Set (Fin n)) ∧ M₂.IsBase (A:Set (Fin n))} where
  toFun A := ⟨A.val.toFinset,by simpa only [Set.coe_toFinset] using A.property⟩
  invFun A := ⟨(A.val:Set (Fin n)),A.property⟩
  left_inv A := by apply Subtype.ext; exact Set.coe_toFinset _
  right_inv A := by apply Subtype.ext; simp
open scoped BigOperators Classical
section ActualAnnealing
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance93 : Fintype Γ] [sectionInstance94 : DecidableEq Γ]
lemma slotTotal_mono (ps : List (Γ × Γ)) (f g : Set Γ → ℝ)
    (h : ∀ S,f S ≤ g S) (A : Set Γ) : slotTotal ps f A ≤ slotTotal ps g A := by
  induction ps generalizing A with
  | nil => exact h A
  | cons p ps ih =>
    change coeffDeriv (pairDirection p) (slotTotal ps f) A ≤ coeffDeriv (pairDirection p) (slotTotal ps g) A
    unfold coeffDeriv
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · rfl
    · exact mul_le_mul_of_nonneg_left (ih _) (slotDirection_nonneg _ _)
lemma slotTotal_scale (ps : List (Γ × Γ)) (f : Set Γ → ℝ) (c : ℝ) (A : Set Γ) :
    slotTotal ps (fun S => c*f S) A=c*slotTotal ps f A := coeffDerivs_scale _ _ _ _
noncomputable def annealWeight (M : Matroid Γ) (n j : ℕ) : Set Γ → ℝ :=
  matroidWeight M n (annealRho n^j)
lemma annealWeight_pos (M : Matroid Γ) (n j : ℕ) (hn : 0<n) (S : Set Γ) :
    0<annealWeight M n j S :=
  matroidWeight_pos M n _ (pow_pos (lt_of_lt_of_le (by norm_num) (annealRho_bounds n hn).1) _) S
omit sectionInstance93 sectionInstance94 in
lemma annealWeight_step [Fintype Γ] [DecidableEq Γ] (M : Matroid Γ) (n j : ℕ) (_ : 0<n) (S : Set Γ) :
    annealWeight M n (j+1) S=annealWeight M n j S*annealRho n^(n-(M.eRk S).toNat) := by
  unfold annealWeight matroidWeight
  rw [pow_succ,mul_pow]
lemma annealWeight_drift (M : Matroid Γ) (n j : ℕ) (hn : 0<n) (S : Set Γ) :
    (1/2)*annealWeight M n j S ≤ annealWeight M n (j+1) S ∧
      annealWeight M n (j+1) S ≤ annealWeight M n j S := by
  rw [annealWeight_step M n j hn]
  have h := annealStep_bounds n (n-(M.eRk S).toNat) hn (Nat.sub_le _ _)
  have hp := (annealWeight_pos M n j hn S).le
  constructor
  · nlinarith [mul_nonneg hp (sub_nonneg.mpr h.1)]
  · nlinarith [mul_nonneg hp (sub_nonneg.mpr h.2)]
lemma anneal_slot_drift (ps : List (Γ × Γ)) (M : Matroid Γ) (n j : ℕ) (hn : 0<n) (A : Set Γ) :
    (1/2)*slotTotal ps (annealWeight M n j) A ≤ slotTotal ps (annealWeight M n (j+1)) A ∧
      slotTotal ps (annealWeight M n (j+1)) A ≤ slotTotal ps (annealWeight M n j) A := by
  constructor
  · rw [← slotTotal_scale]
    exact slotTotal_mono _ _ _ (fun S => (annealWeight_drift M n j hn S).1) _
  · exact slotTotal_mono _ _ _ (fun S => (annealWeight_drift M n j hn S).2) _
lemma anneal_ideal_drift (ps : List (Γ × Γ)) (hps : SlotsFresh ps ∅)
    (M : Matroid Γ) (n j : ℕ) (hn : 0<n) (p r : Γ × Γ)
    (hp : p∈ps) (hr : r∈ps) (hpr : p≠r) :
    (slotTotal ps (annealWeight M n j) ∅/slotDefect ps (annealWeight M n j) ∅ p r)/2  ≤
      slotTotal ps (annealWeight M n (j+1)) ∅/slotDefect ps (annealWeight M n (j+1)) ∅ p r ∧
    slotTotal ps (annealWeight M n (j+1)) ∅/slotDefect ps (annealWeight M n (j+1)) ∅ p r  ≤
      2*(slotTotal ps (annealWeight M n j) ∅/slotDefect ps (annealWeight M n j) ∅ p r) := by
  have h0 := slotTotal_pos ps _ (annealWeight_pos M n j hn) ∅ hps
  have h1 := slotTotal_pos ps _ (annealWeight_pos M n (j+1) hn) ∅ hps
  have hd0 := slotDefect_pos ps _ (annealWeight_pos M n j hn) ∅ hps p r hp hr hpr
  have hd1 := slotDefect_pos ps _ (annealWeight_pos M n (j+1) hn) ∅ hps p r hp hr hpr
  have ha := anneal_slot_drift ps M n j hn ∅
  have hb := anneal_slot_drift ((ps.erase p).erase r) M n j hn (insert r.1 (insert r.2 ∅))
  change (1/2)*slotDefect ps (annealWeight M n j) ∅ p r ≤ slotDefect ps (annealWeight M n (j+1)) ∅ p r ∧ slotDefect ps (annealWeight M n (j+1)) ∅ p r ≤ slotDefect ps (annealWeight M n j) ∅ p r at hb
  constructor
  · rw [div_div,div_le_div_iff₀ (mul_pos hd0 (by norm_num)) hd1]
    nlinarith [mul_nonneg h0.le (sub_nonneg.mpr hb.2),mul_nonneg hd0.le (sub_nonneg.mpr ha.1)]
  · rw [← mul_div_assoc,div_le_div_iff₀ hd1 hd0]
    nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr ha.2),mul_nonneg h0.le (sub_nonneg.mpr hb.1)]

structure GoodMultipliers (gs : List (Γ × Γ)) (f : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) : Prop where
  positive : ∀ p r,0<w p r
  lower : ∀ p∈gs,∀ r∈gs,p≠r → slotTotal gs f ∅/(4*slotDefect gs f ∅ p r) ≤ w p r
  upper : ∀ p∈gs,∀ r∈gs,p≠r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r

lemma plain_probability_mean (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (f : Set Γ → ℝ)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) :
    chainMean gs w f (plainObservable gs (fun _ => 1))=slotTotal gs f ∅/chainTotal gs w f := by
  rw [plainObservable_mean gs hgs hcover]
  simp
lemma weight_mean_identity (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (f : Set Γ → ℝ) (hf : ∀ S,0<f S)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hw : ∀ p r,0<w p r)
    (p r : Γ × Γ) (hp : p∈gs) (hr : r∈gs) (hpr : p≠r) :
    w p r*(chainMean gs w f (plainObservable gs (fun _ => 1))/
      chainMean gs w f (defectIndicator gs p r))=slotTotal gs f ∅/slotDefect gs f ∅ p r := by
  rw [plain_probability_mean gs hgs hcover,defectIndicator_mean gs hgs hcover _ _ p r hp hr hpr]
  field_simp [(chainTotal_pos gs hgs hcover w f hf hw).ne',(hw p r).ne']

lemma plainIndex_card (n : ℕ) : Fintype.card (PlainIndex (pairedSlots n))=2^n := by
  let e : PlainIndex (pairedSlots n) ≃ {S : Set (Fin n ⊕ Fin n) // PlainState (pairedSlots n) S} :=
    { toFun := fun S => ⟨S.val.val,S.property⟩
      invFun := fun S => ⟨⟨S.val,Or.inl S.property⟩,S.property⟩
      left_inv := by intro S; rfl
      right_inv := by intro S; rfl }
  rw [Fintype.card_congr e,pairedPlain_card]
lemma slotTotal_one (ps : List (Γ × Γ)) (A : Set Γ) (hps : SlotsFresh ps A) :
    slotTotal ps (fun _ => 1) A=(2:ℝ)^ps.length := by
  induction ps generalizing A with
  | nil => rfl
  | cons p ps ih =>
    rw [slotTotal_cons p ps _ A hps.1 hps.2.1 hps.2.2.1]
    have hleft : SlotsFresh ps (insert p.1 A) := hps.2.2.2.mono (by intro i hi; simp only [Set.mem_insert_iff] at hi ⊢; tauto)
    have hright : SlotsFresh ps (insert p.2 A) := hps.2.2.2.mono (by intro i hi; simp only [Set.mem_insert_iff] at hi ⊢; tauto)
    rw [ih _ hleft,ih _ hright,List.length_cons,pow_succ]
    ring
lemma initial_ideal (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (p r : Γ × Γ)
    (hp : p∈gs) (hr : r∈gs) (hpr : p≠r) :
    slotTotal gs (fun _ => 1) ∅/slotDefect gs (fun _ => 1) ∅ p r=4 := by
  have hperm := slots_perm_two hp hr hpr
  have hh := (SlotsFresh.perm hperm ∅).mp hgs
  have hrest : SlotsFresh ((gs.erase p).erase r) (insert r.1 (insert r.2 ∅)) :=
    hh.2.2.2.2.2.2.mono (by intro i hi; simp only [Set.mem_insert_iff] at hi ⊢; tauto)
  have hlen := List.Perm.length_eq hperm
  simp only [List.length_cons] at hlen
  rw [slotTotal_one _ _ hgs,slotDefect,slotTotal_one _ _ hrest,hlen,pow_succ,pow_succ]
  have hp : (2:ℝ)^((gs.erase p).erase r).length≠0 := by positivity
  field_simp
  ; ring
lemma initial_good (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (M : Matroid Γ) (n : ℕ) :
    GoodMultipliers gs (annealWeight M n 0) (fun _ _ => 4) := by
  have he : annealWeight M n 0=(fun _ => 1) := by funext S; simp [annealWeight,matroidWeight]
  rw [he]
  refine ⟨by intros; norm_num,?_,?_⟩
  · intro p hp r hr hpr
    rw [mul_comm (4:ℝ),← div_div,initial_ideal gs hgs p r hp hr hpr]
    norm_num
  · intro p hp r hr hpr
    rw [mul_div_assoc,initial_ideal gs hgs p r hp hr hpr]
    norm_num

noncomputable def empirical (H : Set Γ → ℝ) (l : List (Set Γ)) : ℝ :=
  (l.map H).sum/(l.length:ℝ)
noncomputable def learnedMultipliers (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (l : List (Set Γ)) (p r : Γ × Γ) : ℝ :=
  if p∈gs ∧ r∈gs ∧ p≠r then
    w p r*(empirical (plainObservable gs (fun _ => 1)) l/empirical (defectIndicator gs p r) l)
  else w p r
noncomputable def empiricalRatio (gs : List (Γ × Γ)) (g : Set Γ → ℝ) (l : List (Set Γ)) : ℝ :=
  empirical (plainObservable gs g) l/empirical (plainObservable gs (fun _ => 1)) l

def AccuratePhase (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f g : Set Γ → ℝ) (η : ℝ) (l : List (Set Γ)) : Prop :=
  ∀ j : PhaseObservables gs,
    |empirical (phaseObservable gs g j) l-chainMean gs w f (phaseObservable gs g j)| ≤
      η*chainMean gs w f (phaseObservable gs g j)
lemma relative_error_bounds (x m η : ℝ) (h : |x-m| ≤ η*m) :
    (1-η)*m ≤ x ∧ x ≤ (1+η)*m := by
  obtain ⟨h1,h2⟩ := abs_le.mp h
  constructor <;> nlinarith
lemma accurate_plain (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f g : Set Γ → ℝ) (η : ℝ) (l : List (Set Γ)) (h : AccuratePhase gs w f g η l) :
    (1-η)*chainMean gs w f (plainObservable gs (fun _ => 1)) ≤ empirical (plainObservable gs (fun _ => 1)) l ∧
    empirical (plainObservable gs (fun _ => 1)) l ≤ (1+η)*chainMean gs w f (plainObservable gs (fun _ => 1)) :=
  relative_error_bounds _ _ _ (h (.inl none))
lemma accurate_defect (gs : List (Γ × Γ)) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f g : Set Γ → ℝ) (η : ℝ) (l : List (Set Γ)) (h : AccuratePhase gs w f g η l)
    (p r : Γ × Γ) (hp : p∈gs) (hr : r∈gs) (hpr : p≠r) :
    (1-η)*chainMean gs w f (defectIndicator gs p r) ≤ empirical (defectIndicator gs p r) l ∧
    empirical (defectIndicator gs p r) l ≤ (1+η)*chainMean gs w f (defectIndicator gs p r) :=
  relative_error_bounds _ _ _ (h (.inl (some ⟨(p,r),(mem_defectTypes gs (p,r)).mpr ⟨hp,hr,hpr⟩⟩)))

theorem successful_phase_learns (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (M : Matroid Γ) (n j : ℕ) (hn : 0<n)
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (hw : ∀ p r,0<w p r)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1/3) (l : List (Set Γ))
    (hacc : AccuratePhase gs w (annealWeight M n j)
      (fun S => annealRho n^(n-(M.eRk S).toNat)) η l) :
    GoodMultipliers gs (annealWeight M n (j+1)) (learnedMultipliers gs w l) := by
  let f := annealWeight M n j
  let g := fun S => annealRho n^(n-(M.eRk S).toNat)
  have hf := annealWeight_pos M n j hn
  have hΛ := chainTotal_pos gs hgs hcover w f hf hw
  have hp0 : 0<chainMean gs w f (plainObservable gs (fun _ => 1)) := by
    rw [plain_probability_mean gs hgs hcover]
    exact div_pos (slotTotal_pos gs f hf ∅ hgs) hΛ
  have hp0h := accurate_plain gs w f g η l hacc
  have hp0hp : 0<empirical (plainObservable gs (fun _ => 1)) l :=
    lt_of_lt_of_le (mul_pos (by linarith) hp0) hp0h.1
  have hpt : ∀ p∈gs,∀ r∈gs,p≠r → 0<chainMean gs w f (defectIndicator gs p r) := by
    intro p hp r hr hpr
    rw [defectIndicator_mean gs hgs hcover w f p r hp hr hpr]
    exact div_pos (mul_pos (hw p r) (slotDefect_pos gs f hf ∅ hgs p r hp hr hpr)) hΛ
  have hptp : ∀ p∈gs,∀ r∈gs,p≠r → 0<empirical (defectIndicator gs p r) l := by
    intro p hp r hr hpr
    exact lt_of_lt_of_le (mul_pos (by linarith) (hpt p hp r hr hpr))
      (accurate_defect gs w f g η l hacc p r hp hr hpr).1
  have hb : ∀ p∈gs,∀ r∈gs,p≠r →
      (slotTotal gs (annealWeight M n (j+1)) ∅/slotDefect gs (annealWeight M n (j+1)) ∅ p r)/4 ≤
        learnedMultipliers gs w l p r ∧
      learnedMultipliers gs w l p r ≤ 4*(slotTotal gs (annealWeight M n (j+1)) ∅/slotDefect gs (annealWeight M n (j+1)) ∅ p r) := by
    intro p hp r hr hpr
    rw [learnedMultipliers,ite_eq_left ⟨hp,hr,hpr⟩]
    exact learned_multiplier_good _ _ _ _ _ _ _ η (hw p r) hp0 (hpt p hp r hr hpr)
      (div_pos (slotTotal_pos gs f hf ∅ hgs) (slotDefect_pos gs f hf ∅ hgs p r hp hr hpr))
      (weight_mean_identity gs hgs hcover f hf w hw p r hp hr hpr) hη0 hη1 hp0h
      (accurate_defect gs w f g η l hacc p r hp hr hpr)
      (anneal_ideal_drift gs hgs M n j hn p r hp hr hpr)
  refine ⟨?_,?_,?_⟩
  · intro p r
    unfold learnedMultipliers
    split_ifs with h
    · exact mul_pos (hw p r) (div_pos hp0hp (hptp p h.1 r h.2.1 h.2.2))
    · exact hw p r
  · intro p hp r hr hpr
    simpa only [div_div,mul_comm] using (hb p hp r hr hpr).1
  · intro p hp r hr hpr
    simpa only [mul_div_assoc] using (hb p hp r hr hpr).2

end ActualAnnealing

section RestartBridge
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n))
    (hE : M.E=Set.univ) (hR : M.eRank=(n:ℕ∞))
local notation "GS" => pairedSlots n
local notation "W" => (((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ℝ)
noncomputable def actualTrace (j : ℕ) (w : W) (hw : ∀ p r,0<w p r) : FiniteChain (PlainIndex GS) :=
  metropolisTrace GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
    w (annealWeight M n j) hw (annealWeight_pos M n j hn)
end RestartBridge

section ActualRestart
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n))
local notation "GS" => pairedSlots n
local notation "W" => (((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ℝ)
noncomputable def actualCappedTrace (j : ℕ) (w : W) (hw : ∀ p r,0<w p r) (cap : ℕ) :
    FiniteKernel (PlainIndex GS) (PlainIndex GS) :=
  (metropolisChain GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
    w (annealWeight M n j) hw (annealWeight_pos M n j hn)).cappedTraceKernel (plainPredicate GS)
    (metropolisKilled GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
      w (annealWeight M n j) hw (annealWeight_pos M n j hn)) (by intros; rfl) cap
noncomputable def uniformPlain (_ : PlainIndex GS) : ℝ := by
  exact 1/(2:ℝ)^n
noncomputable def restartLaw (L cap : ℕ) (w : ℕ → W) (hw : ∀ j p r,0<w j p r) : ℕ → PlainIndex GS → ℝ
  | 0 => uniformPlain n
  | j+1 => ((actualCappedTrace n hn M (j+1) (w (j+1)) (hw (j+1)) cap).power
      (20*n^4*(n*(L+1)+2))).push (restartLaw L cap w hw j)
end ActualRestart
namespace FiniteChain
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance101 : Fintype X]
universe u

def Sample (X : Type u) : ℕ → Type u
  | 0 => X
  | k+1 => X × Sample X k
instance sampleFintype (k : ℕ) : Fintype (Sample X k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype X)
  | succ k ih =>
    letI : Fintype (Sample X k) := ih
    exact inferInstanceAs (Fintype (X × Sample X k))
def Sample.toList : {k : ℕ} → Sample X k → List X
  | 0,x => [x]
  | _+1,(x,v) => x::v.toList
variable (C : FiniteChain X)
noncomputable def sampleMass (C : FiniteChain X) (ν : X → ℝ) : {k : ℕ} → Sample X k → ℝ
  | 0,x => ν x
  | _+1,(x,v) => ν x*sampleMass C (C.P x) v
end FiniteChain
section WarmLift
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance102 : Fintype Γ] [sectionInstance103 : DecidableEq Γ]
noncomputable def plainLift (gs : List (Γ × Γ)) (ν : PlainIndex gs → ℝ) (S : ChainIndex gs) : ℝ :=
  if h : PlainState gs S.val then ν ⟨S,h⟩ else 0
end WarmLift
section ActualHistory
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance105 : Fintype Γ] [DecidableEq Γ]
variable (gs : List (Γ × Γ))
noncomputable def historyWeights {X : Type*} (sample : X → List (Set Γ)) (h : List X) :
    (Γ × Γ) → (Γ × Γ) → ℝ :=
  h.foldl (fun w x => learnedMultipliers gs w (sample x)) (fun _ _ => 4)
omit sectionInstance105 in
lemma historyWeights_snoc [Fintype Γ] {X : Type*} (sample : X → List (Set Γ)) (h : List X) (x : X) :
    historyWeights gs sample (h++[x])=learnedMultipliers gs (historyWeights gs sample h) (sample x) := by
  simp [historyWeights,List.foldl_append]
variable (M : Matroid Γ) (n : ℕ) (η : ℝ)
inductive SuccessfulHistory {X : Type*} (sample : X → List (Set Γ)) : List X → Prop
  | nil : SuccessfulHistory sample []
  | snoc (h : List X) (x : X) (hh : SuccessfulHistory sample h)
      (hx : AccuratePhase gs (historyWeights gs sample h) (annealWeight M n h.length)
        (fun S => annealRho n^(n-(M.eRk S).toNat)) η (sample x)) : SuccessfulHistory sample (h++[x])
lemma successfulHistory_take {X : Type*} (sample : X → List (Set Γ)) (h : List X)
    (hh : SuccessfulHistory gs M n η sample h) (a : ℕ) :
    SuccessfulHistory gs M n η sample (h.take a) := by
  induction hh with
  | nil => simpa using SuccessfulHistory.nil (gs := gs) (M := M) (n := n) (η := η) (sample := sample)
  | snoc h x hh hx ih =>
    by_cases ha : a ≤ h.length
    · rw [List.take_append_of_le_length ha]
      exact ih
    · have he : a ≥ (h++[x]).length := by simp; omega
      rw [List.take_of_length_le he]
      exact SuccessfulHistory.snoc h x hh hx
lemma successfulHistory_good {X : Type*} (sample : X → List (Set Γ))
    (hgs : SlotsFresh gs ∅) (hcover : pairSupport gs=Set.univ) (hn : 0<n)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1/3) (h : List X) (hh : SuccessfulHistory gs M n η sample h) :
    GoodMultipliers gs (annealWeight M n h.length) (historyWeights gs sample h) := by
  induction hh with
  | nil => exact initial_good gs hgs M n
  | snoc h x hh hx ih =>
    rw [historyWeights_snoc,List.length_append,List.length_singleton]
    exact successful_phase_learns gs hgs hcover M n h.length hn (historyWeights gs sample h)
      ih.positive η hη0 hη1 (sample x) hx
end ActualHistory
section ActualPhase
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n))
local notation "GS" => pairedSlots n
local notation "W" => (((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ℝ)
def restartCap (n L : ℕ) : ℕ := 2000*(L+1)^2*n^2*(20*n^4*(n*(L+1)+2))
variable (N : ℕ)
abbrev PhaseSample := FiniteChain.Sample (ChainIndex GS) (N-1)
def observedSets (v : PhaseSample n N) : List (Set (Fin n ⊕ Fin n)) := v.toList.map Subtype.val
noncomputable def storedWeights (h : List (PhaseSample n N)) (j : ℕ) : W :=
  historyWeights GS (observedSets n N) (h.take j)
def HistoryPositive (h : List (PhaseSample n N)) : Prop :=
  ∀ j ≤ h.length,∀ p r,0<storedWeights n N h j p r
lemma historyPositive_all (h : List (PhaseSample n N)) (hp : HistoryPositive n N h) (j : ℕ) (p r) :
    0<storedWeights n N h j p r := by
  by_cases hj : j ≤ h.length
  · exact hp j hj p r
  · have he : h.take j=h := List.take_of_length_le (by omega)
    simpa only [storedWeights,he,List.take_length] using hp h.length le_rfl p r
include hn in
lemma successfulHistory_positive (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1/3)
    (h : List (PhaseSample n N)) (hh : SuccessfulHistory GS M n η (observedSets n N) h) :
    HistoryPositive n N h := by
  intro j hj
  exact (successfulHistory_good GS M n η (observedSets n N) (pairedSlots_fresh n) (pairedSlots_cover n)
    hn hη0 hη1 (h.take j) (successfulHistory_take GS M n η (observedSets n N) h hh j)).positive
variable (L : ℕ)
noncomputable def phaseStart (h : List (PhaseSample n N)) (hp : HistoryPositive n N h) : ChainIndex GS → ℝ :=
  plainLift GS (restartLaw n hn M L (restartCap n L) (storedWeights n N h) (historyPositive_all n N h hp) h.length)
noncomputable def phaseChain (h : List (PhaseSample n N)) (hp : HistoryPositive n N h) : FiniteChain (ChainIndex GS) :=
  metropolisChain GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
    (storedWeights n N h h.length) (annealWeight M n h.length) (hp h.length le_rfl)
    (annealWeight_pos M n h.length hn)
noncomputable def phaseKernel (h : List (PhaseSample n N)) (v : PhaseSample n N) : ℝ :=
  if hp : HistoryPositive n N h then
    (phaseChain n hn M N h hp).sampleMass (phaseStart n hn M N L h hp) v else 0
end ActualPhase
section HistoryEstimate
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance107 : Fintype Γ] [sectionInstance108 : DecidableEq Γ]
variable {X : Type*} (sample : X → List (Set Γ))
def historySample (h : List X) (j : ℕ) : List (Set Γ) := (h[j]?.map sample).getD []
end HistoryEstimate
section ActualHistoryEstimate
open scoped BigOperators Classical
variable (n : ℕ) (N L : ℕ) (M : Matroid (Fin n ⊕ Fin n))
noncomputable def historyEstimate (h : List (PhaseSample n N)) : ℝ :=
  (2:ℝ)^n * ∏ j ∈ Finset.range L,
    empiricalRatio (pairedSlots n) (fun S => annealRho n^(n-(M.eRk S).toNat))
      (historySample (observedSets n N) h j)
end ActualHistoryEstimate
section WitnessRestart
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n))
local notation "K" => pairedMatroid M₁ M₂
local notation "GS" => pairedSlots n
def Witnessed (x : PlainIndex GS) : Prop := n-((K).eRk x.val.val).toNat=0
variable (N : ℕ)
noncomputable def witnessKernel (L : ℕ) (h : List (PhaseSample n N)) (x : PlainIndex GS) : ℝ :=
  if hp : HistoryPositive n N h then
    restartLaw n hn K L (restartCap n L) (storedWeights n N h) (historyPositive_all n N h hp) h.length x
  else 0
end WitnessRestart
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ)
local notation "K" => pairedMatroid M₁ M₂
local notation "GS" => pairedSlots n
noncomputable def guardedEstimate (h : List (PhaseSample n N)) (x : PlainIndex GS) : ℝ :=
  if Witnessed n M₁ M₂ x then historyEstimate n N L K h else 0
noncomputable def actualRealSuccess (ε : ℝ) : ℝ :=
  FiniteExperiment.expect (phaseKernel n hn K N L) L [] (fun h =>
    ∑ x,if (1-ε)*(commonBaseCount M₁ M₂:ℝ) ≤ guardedEstimate n M₁ M₂ N L h x ∧
      guardedEstimate n M₁ M₂ N L h x ≤ (1+ε)*(commonBaseCount M₁ M₂:ℝ)
      then witnessKernel n hn M₁ M₂ N L h x else 0)

end

section

open scoped BigOperators Classical
abbrev BitWord (h : ℕ) := Fin h → Bool

def wordEquiv : (h : ℕ) → BitWord h ≃ Fin (2^h)
  | 0 => { toFun := fun _ => 0
           invFun := fun _ => Fin.elim0
           left_inv := fun _ => Subsingleton.elim _ _
           right_inv := by
             intro i
             apply Fin.ext
             have hi : i.val < 1 := by exact i.isLt
             change 0=i.val
             omega }
  | h+1 => (Fin.consEquiv (fun _ : Fin (h+1) => Bool)).symm |>.trans
      ((Equiv.prodCongr finTwoEquiv.symm (wordEquiv h)).trans
        (finProdFinEquiv.trans (finCongr (by rw [pow_succ]; omega : 2*2^h=2^(h+1)))))
noncomputable def uniformAverage {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (∑ x,f x)/(Fintype.card X:ℝ)

def boundedUniform (v h : ℕ) : (D : ℕ) → (Fin D → BitWord h) → Option (Fin v)
  | 0,_ => none
  | D+1,bits =>
      let x := wordEquiv h (bits 0)
      if hx : x.val < v then some ⟨x.val,hx⟩ else boundedUniform v h D (Fin.tail bits)
noncomputable def rejectionRate (v h : ℕ) : ℝ := (2^h-v:ℕ)/(2:ℝ)^h

def bitPrefix (h H : ℕ) (hh : h≤H) (w : BitWord H) : BitWord h :=
  fun i => w ⟨i.val,lt_of_lt_of_le i.isLt hh⟩

inductive DrawTree (A : Type*) where
  | leaf (a : A)
  | draw (v : ℕ) (next : Fin (v+1) → DrawTree A)
namespace DrawTree

section
open scoped BigOperators Classical
variable {A : Type*}
noncomputable def expectation (φ : A → ℝ) : DrawTree A → ℝ
  | .leaf a => φ a
  | .draw _ k => uniformAverage (fun i => expectation φ (k i))

def Fits (H : ℕ) : ℕ → DrawTree A → Prop
  | _,.leaf _ => True
  | 0,.draw _ _ => False
  | M+1,.draw v k => Nat.clog 2 (v+1)≤H ∧ ∀ i,Fits H M (k i)

def run (H D : ℕ) : (M : ℕ) → DrawTree A → (Fin M → Fin D → BitWord H) → Option A
  | _,.leaf a,_ => some a
  | 0,.draw _ _,_ => none
  | M+1,.draw v k,bits =>
    if hh : Nat.clog 2 (v+1)≤H then
      match boundedUniform (v+1) (Nat.clog 2 (v+1)) D
        (fun d => bitPrefix _ H hh (bits 0 d)) with
      | none => none
      | some a => run H D M (k a) (Fin.tail bits)
    else none

def optionValue (φ : A → ℝ) : Option A → ℝ
  | none => 0
  | some a => φ a
end
open scoped BigOperators Classical
variable {A B : Type*}
def bind : DrawTree A → (A → DrawTree B) → DrawTree B
  | .leaf a,k => k a
  | .draw v f,k => .draw v (fun i => (f i).bind k)
def map (f : A → B) (t : DrawTree A) : DrawTree B := t.bind (fun a => .leaf (f a))

def rationalCoin (a v : ℕ) : DrawTree Bool :=
  .draw v (fun i => .leaf (decide (i.val<a)))
def bernoulli (p : ℚ) : DrawTree Bool := rationalCoin p.num.natAbs (p.den-1)
end DrawTree

section MetropolisSampling
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance110 : Fintype Γ] [sectionInstance111 : DecidableEq Γ]
abbrev ExchangeChoice (S : Set Γ) := ↥S × ↥(Sᶜ)
def exchangedSet (S : Set Γ) (a : ExchangeChoice S) : Set Γ := insert a.2.val (S\{a.1.val})
lemma exchangeChoice_card (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅)
    (hcover : pairSupport gs=Set.univ) (S : ChainIndex gs) :
    Fintype.card (ExchangeChoice S.val)=gs.length^2 := by
  rw [Fintype.card_prod]
  have hs : Fintype.card S.val=S.val.ncard := by rw [Set.ncard_eq_toFinset_card',Set.toFinset_card]
  have hc : Fintype.card ↥(S.valᶜ)=S.valᶜ.ncard := by rw [Set.ncard_eq_toFinset_card',Set.toFinset_card]
  rw [hs,hc]
  have ht := S.val.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card,slots_ground_card gs hgs hcover,S.property.ncard hgs hcover] at ht
  have hh : S.valᶜ.ncard=gs.length := by omega
  rw [S.property.ncard hgs hcover,hh,pow_two]

noncomputable def metropolisAcceptance (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) (S T : ChainIndex gs) : ℝ :=
  min 1 (chainWeight gs w f T.val/chainWeight gs w f S.val)
noncomputable def exchangeOffer (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℝ) (f : Set Γ → ℝ) (S : ChainIndex gs)
    (a : ExchangeChoice S.val) (φ : ChainIndex gs → ℝ) : ℝ :=
  if ht : ChainState gs (exchangedSet S.val a) then
    let T : ChainIndex gs := ⟨exchangedSet S.val a,ht⟩
    metropolisAcceptance gs w f S T*φ T+(1-metropolisAcceptance gs w f S T)*φ S
  else φ S
end MetropolisSampling
section RationalSampling
open scoped BigOperators Classical
variable {Γ : Type*} [sectionInstance112 : Fintype Γ] [sectionInstance113 : DecidableEq Γ]
noncomputable def rationalMultiplier (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℚ) (S : Set Γ) : ℚ :=
  if h : ∃ p r,DefectState gs p r S then w h.choose h.choose_spec.choose else 1
noncomputable def rationalWeight (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℚ) (f : Set Γ → ℚ) (S : Set Γ) : ℚ :=
  rationalMultiplier gs w S*f S
noncomputable def rationalEmpirical (H : Set Γ → ℚ) (l : List (Set Γ)) : ℚ :=
  (l.map H).sum/(l.length:ℚ)
noncomputable def rationalPlain (gs : List (Γ × Γ)) (g : Set Γ → ℚ) (S : Set Γ) : ℚ :=
  if PlainState gs S then g S else 0
noncomputable def rationalDefect (gs : List (Γ × Γ)) (p r : Γ × Γ) (S : Set Γ) : ℚ :=
  if DefectState gs p r S then 1 else 0
noncomputable def rationalLearn (gs : List (Γ × Γ))
    (w : (Γ × Γ) → (Γ × Γ) → ℚ) (l : List (Set Γ)) (p r : Γ × Γ) : ℚ :=
  if p∈gs ∧ r∈gs ∧ p≠r then
    w p r*(rationalEmpirical (rationalPlain gs (fun _ => 1)) l/rationalEmpirical (rationalDefect gs p r) l)
  else w p r
noncomputable def rationalHistory {X : Type*} (gs : List (Γ × Γ))
    (sample : X → List (Set Γ)) (h : List X) : (Γ × Γ) → (Γ × Γ) → ℚ :=
  h.foldl (fun w x => rationalLearn gs w (sample x)) (fun _ _ => 4)

def rationalRho (n : ℕ) : ℚ := 1-1/(2*(n:ℚ))
noncomputable def rationalAnneal (M : Matroid Γ) (n j : ℕ) (S : Set Γ) : ℚ :=
  (rationalRho n^j)^(n-(M.eRk S).toNat)
noncomputable def rationalRatio (gs : List (Γ × Γ)) (g : Set Γ → ℚ) (l : List (Set Γ)) : ℚ :=
  rationalEmpirical (rationalPlain gs g) l / rationalEmpirical (rationalPlain gs (fun _ => 1)) l
end RationalSampling

namespace DrawTree
open scoped BigOperators Classical
noncomputable def uniformChoice (A : Type*) [Fintype A] [Nonempty A] : DrawTree A :=
  let h : Fintype.card A-1+1=Fintype.card A := by have hh := Fintype.card_pos (α := A); omega
  .draw (Fintype.card A-1) (fun i => .leaf ((Fintype.equivFin A).symm (Fin.cast h i)))
end DrawTree

section RationalMetropolis
open scoped BigOperators Classical
variable {Γ : Type*} [Fintype Γ] [sectionInstance115 : DecidableEq Γ]
variable (gs : List (Γ × Γ))
noncomputable def rationalAcceptance (w : (Γ × Γ) → (Γ × Γ) → ℚ) (f : Set Γ → ℚ)
    (S T : ChainIndex gs) : ℚ := min 1 (rationalWeight gs w f T.val/rationalWeight gs w f S.val)
noncomputable def rationalExchange (w : (Γ × Γ) → (Γ × Γ) → ℚ) (f : Set Γ → ℚ)
    (S : ChainIndex gs) (a : ExchangeChoice S.val) : DrawTree (ChainIndex gs) :=
  if ht : ChainState gs (exchangedSet S.val a) then
    let T : ChainIndex gs := ⟨exchangedSet S.val a,ht⟩
    (DrawTree.bernoulli (rationalAcceptance gs w f S T)).map (fun accept => if accept then T else S)
  else .leaf S
noncomputable def rationalMetropolis (hgs : SlotsFresh gs ∅) (hne : gs≠[])
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℚ) (f : Set Γ → ℚ)
    (S : ChainIndex gs) : DrawTree (ChainIndex gs) :=
  letI : Nonempty (ExchangeChoice S.val) := Fintype.card_pos_iff.mp (by
    rw [exchangeChoice_card gs hgs hcover S]; exact pow_pos (List.length_pos_iff.mpr hne) _)
  (DrawTree.bernoulli (1/2)).bind (fun lazy => if lazy then .leaf S else
    (DrawTree.uniformChoice (ExchangeChoice S.val)).bind (rationalExchange gs w f S))
end RationalMetropolis
namespace DrawTree
open scoped BigOperators Classical
variable {A B D : Type*}
def optionBind (t : DrawTree (Option A)) (k : A → DrawTree (Option B)) : DrawTree (Option B) :=
  t.bind (fun z => match z with | none => .leaf none | some a => k a)
def pureSome (a : A) : DrawTree (Option A) := .leaf (some a)

def Matches [Fintype B] (t : A → DrawTree (Option B)) (P : A → B → ℝ) : Prop :=
  ∀ a φ,(t a).expectation (optionValue φ)=∑ b,P a b*φ b

def iterate (t : A → DrawTree (Option A)) : ℕ → A → DrawTree (Option A)
  | 0,a => pureSome a
  | k+1,a => (iterate t k a).optionBind t
end DrawTree

section DrawHitting
open scoped BigOperators Classical
variable {X : Type*} [sectionInstance116 : Fintype X]
variable (step : X → DrawTree X) (A : X → Prop)
noncomputable def hittingTree : ℕ → X → DrawTree (Option (FiniteChain.Inside A))
  | 0,_ => .leaf none
  | k+1,x => (step x).bind (fun y => if hy : A y then .leaf (some ⟨y,hy⟩) else hittingTree k y)
end DrawHitting
namespace DrawTree
open scoped BigOperators Classical
variable {X Y : Type*} [sectionInstance117 : Fintype X]
def sample (step : X → DrawTree X) : (k : ℕ) → X → DrawTree (FiniteChain.Sample X k)
  | 0,x => .leaf x
  | k+1,x => (step x).bind (fun y => (sample step k y).map (fun v => (x,v)))

def history (K : List X → DrawTree (Option X)) : ℕ → List X → DrawTree (Option (List X))
  | 0,h => pureSome h
  | k+1,h => (K h).optionBind (fun x => history K k (h++[x]))
end DrawTree
section DrawActual
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n)) (N L : ℕ)
local notation "GS" => pairedSlots n
noncomputable def rationalStored (h : List (PhaseSample n N)) (j : ℕ) :=
  rationalHistory GS (observedSets n N) (h.take j)
noncomputable def actualStepTree (h : List (PhaseSample n N)) (j : ℕ) : ChainIndex GS → DrawTree (ChainIndex GS) :=
  rationalMetropolis GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
    (rationalStored n N h j) (rationalAnneal M n j)
noncomputable def actualTraceTree (h : List (PhaseSample n N)) (j cap : ℕ) :
    PlainIndex GS → DrawTree (Option (PlainIndex GS)) :=
  fun x => hittingTree (actualStepTree n hn M N h j) (plainPredicate GS) (cap+1) x.val
noncomputable def actualRestartTree (h : List (PhaseSample n N)) (cap : ℕ) : ℕ → DrawTree (Option (PlainIndex GS))
  | 0 =>
    letI := plainIndex_nonempty GS (pairedSlots_fresh n) (pairedSlots_cover n)
    (DrawTree.uniformChoice (PlainIndex GS)).map some
  | j+1 => (actualRestartTree h cap j).optionBind
      (DrawTree.iterate (actualTraceTree n hn M N h (j+1) cap) (20*n^4*(n*(L+1)+2)))
noncomputable def actualStartTree (h : List (PhaseSample n N)) : DrawTree (Option (ChainIndex GS)) :=
  (actualRestartTree n hn M N L h (restartCap n L) h.length).map (Option.map Subtype.val)
noncomputable def actualPhaseTree (h : List (PhaseSample n N)) : DrawTree (Option (PhaseSample n N)) :=
  if HistoryPositive n N h then
    (actualStartTree n hn M N L h).optionBind
      (fun x => (DrawTree.sample (actualStepTree n hn M N h h.length) (N-1) x).map some)
  else .leaf none
end DrawActual
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ)
local notation "K" => pairedMatroid M₁ M₂
local notation "GS" => pairedSlots n
noncomputable def rationalEstimate (h : List (PhaseSample n N)) : ℚ :=
  (2:ℚ)^n * ∏ j ∈ Finset.range L,
    rationalRatio GS (fun S => rationalRho n^(n-((K).eRk S).toNat))
      (historySample (observedSets n N) h j)
noncomputable def rationalGuard (h : List (PhaseSample n N)) (x : PlainIndex GS) : ℚ :=
  if Witnessed n M₁ M₂ x then rationalEstimate n M₁ M₂ N L h else 0
noncomputable def rationalWitnessTree (h : List (PhaseSample n N)) : DrawTree (Option (PlainIndex GS)) :=
  if HistoryPositive n N h then actualRestartTree n hn K N L h (restartCap n L) h.length else .leaf none
noncomputable def rationalAlgorithmTree : DrawTree (Option ℚ) :=
  (DrawTree.history (actualPhaseTree n hn K N L) L []).optionBind (fun h =>
    (rationalWitnessTree n hn M₁ M₂ N L h).map (Option.map (rationalGuard n M₁ M₂ N L h)))

end

open scoped BigOperators Classical

def RatBound (q : ℚ) (B : ℕ) : Prop :=
  ∃ a b : ℕ,a≤B ∧ b≤B ∧ 0<b ∧ q=(a:ℚ)/(b:ℚ)

open scoped BigOperators Classical
def drawWordBound (n N L : ℕ) : ℕ := 2*(2+N*L+(2*n)*(n*L))+n^2+n+4

section ActualFits
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M : Matroid (Fin n ⊕ Fin n)) (N L : ℕ) (hN : 0<N)

def phaseDrawBound (n N L : ℕ) : ℕ := 1+3*L*(restartCap n L+1)*(20*n^4*(n*(L+1)+2))+3*N
end ActualFits

section AlgorithmFits
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ) (hN : 0<N)
def algorithmDrawBound (n N L : ℕ) : ℕ := phaseDrawBound n N L*(L+1)
end AlgorithmFits

namespace DrawTree
variable {A B : Type*}
def All (p : A → Prop) : DrawTree A → Prop
  | .leaf a => p a
  | .draw _ k => ∀ i,All p (k i)
end DrawTree
open scoped BigOperators Classical
abbrev FairBank (n N L : ℕ) :=
  Fin (algorithmDrawBound n N L) → Fin (algorithmDrawBound n N L+6) → BitWord (drawWordBound n N L)
noncomputable def fairOutput (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ) (bits : FairBank n N L) : ℚ :=
  ((DrawTree.run (drawWordBound n N L) (algorithmDrawBound n N L+6) (algorithmDrawBound n N L)
    (rationalAlgorithmTree n hn M₁ M₂ N L) bits).join).getD 0
open scoped BigOperators Classical

def rationalMedian (l : List ℚ) : ℚ := (l.mergeSort (· ≤ ·)).getD (l.length/2) 0

def outsideInterval (a b x : ℚ) : Bool := decide (¬(a≤x ∧ x≤b))

def repetitionCount (δ : ℚ) : ℕ := 64*(δ.den.bits.length+1)

open scoped BigOperators Classical

def accuracyExponent (ε : ℚ) : ℕ := ε.den.bits.length+5

def sampleCount (n L : ℕ) (ε : ℚ) : ℕ := 10^14*(L+1)^3*n^14*⌈ε⁻¹⌉₊^2+1

noncomputable def amplifiedOutput (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ) (δ : ℚ)
    (bits : Fin (repetitionCount δ) → FairBank n N L) : ℚ :=
  rationalMedian (List.ofFn (fun i => fairOutput n hn M₁ M₂ N L (bits i)))

abbrev FPRASBank (n : ℕ) (ε δ : ℚ) := Fin (repetitionCount δ) →
  FairBank n (sampleCount n (annealLength n (accuracyExponent ε)) ε) (annealLength n (accuracyExponent ε))
noncomputable def boundedFPRASOutput (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (ε δ : ℚ) (bits : FPRASBank n ε δ) : ℚ :=
  amplifiedOutput n hn M₁ M₂ (sampleCount n (annealLength n (accuracyExponent ε)) ε)
    (annealLength n (accuracyExponent ε)) δ bits

section GreedyOracle
variable {α : Type*} [sectionInstance120 : DecidableEq α]

def greedyOracle (O : Finset α → Bool) : List α → Finset α
  | [] => ∅
  | a::l => let I := greedyOracle O l
            if O (insert a I) then insert a I else I
end GreedyOracle

open scoped Classical

def queryFinset {n : ℕ} (O : IndependenceOracle n) (which : Bool) (I : Finset (Fin n)) : Bool :=
  O which (fun i => decide (i ∈ I))
def rankOracle {n : ℕ} (O : IndependenceOracle n) (which : Bool) (S : Finset (Fin n)) : ℕ :=
  (greedyOracle (queryFinset O which) ((List.finRange n).filter (fun i => decide (i ∈ S)))).card

open scoped Classical

def pairedDeficiencyOracle {n : ℕ} (r : ℕ) (O : IndependenceOracle n)
    (Sx Sy : Finset (Fin n)) : ℕ :=
  n+r-(rankOracle O false Sx+Sy.card+rankOracle O true Syᶜ)

section

open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (r : ℕ) (O : IndependenceOracle n) (N L : ℕ)
local notation "GS" => pairedSlots n
noncomputable def oracleDeficiency (S : Set (Fin n ⊕ Fin n)) : ℕ :=
  pairedDeficiencyOracle r O (Sum.inl ⁻¹' S).toFinset (Sum.inr ⁻¹' S).toFinset
noncomputable def oracleAnneal (j : ℕ) (S : Set (Fin n ⊕ Fin n)) : ℚ :=
  (rationalRho n^j)^(oracleDeficiency n r O S)
def rationalHistoryPositive (h : List (PhaseSample n N)) : Prop :=
  ∀ j ≤ h.length,∀ p q,0<rationalStored n N h j p q
noncomputable def oracleStepTree (h : List (PhaseSample n N)) (j : ℕ) : ChainIndex GS → DrawTree (ChainIndex GS) :=
  rationalMetropolis GS (pairedSlots_fresh n) (pairedSlots_ne_nil n hn) (pairedSlots_cover n)
    (rationalStored n N h j) (oracleAnneal n r O j)
noncomputable def oracleTraceTree (h : List (PhaseSample n N)) (j cap : ℕ) :
    PlainIndex GS → DrawTree (Option (PlainIndex GS)) :=
  fun x => hittingTree (oracleStepTree n hn r O N h j) (plainPredicate GS) (cap+1) x.val
noncomputable def oracleRestartTree (h : List (PhaseSample n N)) (cap : ℕ) : ℕ → DrawTree (Option (PlainIndex GS))
  | 0 =>
    letI := plainIndex_nonempty GS (pairedSlots_fresh n) (pairedSlots_cover n)
    (DrawTree.uniformChoice (PlainIndex GS)).map some
  | j+1 => (oracleRestartTree h cap j).optionBind
      (DrawTree.iterate (oracleTraceTree n hn r O N h (j+1) cap) (20*n^4*(n*(L+1)+2)))
noncomputable def oracleStartTree (h : List (PhaseSample n N)) : DrawTree (Option (ChainIndex GS)) :=
  (oracleRestartTree n hn r O N L h (restartCap n L) h.length).map (Option.map Subtype.val)
noncomputable def oraclePhaseTree (h : List (PhaseSample n N)) : DrawTree (Option (PhaseSample n N)) :=
  if rationalHistoryPositive n N h then
    (oracleStartTree n hn r O N L h).optionBind
      (fun x => (DrawTree.sample (oracleStepTree n hn r O N h h.length) (N-1) x).map some)
  else .leaf none
noncomputable def oracleEstimate (h : List (PhaseSample n N)) : ℚ :=
  (2:ℚ)^n * ∏ j ∈ Finset.range L,
    rationalRatio GS (fun S => rationalRho n^(oracleDeficiency n r O S))
      (historySample (observedSets n N) h j)
noncomputable def oracleGuard (h : List (PhaseSample n N)) (x : PlainIndex GS) : ℚ :=
  if oracleDeficiency n r O x.val.val=0 then oracleEstimate n r O N L h else 0
noncomputable def oracleWitnessTree (h : List (PhaseSample n N)) : DrawTree (Option (PlainIndex GS)) :=
  if rationalHistoryPositive n N h then oracleRestartTree n hn r O N L h (restartCap n L) h.length else .leaf none

noncomputable def oracleAlgorithmTree : DrawTree (Option ℚ) :=
  (DrawTree.history (oraclePhaseTree n hn r O N L) L []).optionBind (fun h =>
    (oracleWitnessTree n hn r O N L h).map (Option.map (oracleGuard n r O N L h)))

end

def bitResourceParameter (n : ℕ) (ε δ : ℚ) : ℕ :=
  1+n+ε.den.bits.length+δ.den.bits.length+⌈ε⁻¹⌉₊
def fairBitCount (n : ℕ) (ε δ : ℚ) : ℕ :=
  let L := annealLength n (accuracyExponent ε)
  let N := sampleCount n L ε
  repetitionCount δ * drawWordBound n N L * (algorithmDrawBound n N L+6) * algorithmDrawBound n N L

open scoped BigOperators Classical

open scoped BigOperators Classical

noncomputable def wordPlainEquiv (n : ℕ) : BitWord n ≃ PlainIndex (pairedSlots n) where
  toFun b := ⟨⟨transversal {i | b i=true},Or.inl (transversal_plain n _)⟩,transversal_plain n _⟩
  invFun S := fun i => decide (Sum.inl i∈S.val.val)
  left_inv b := by
    funext i
    change decide (Sum.inl i∈transversal {i | b i=true})=b i
    change decide (i∈Sum.inl ⁻¹' transversal {i | b i=true})=b i
    rw [preimage_inl_transversal]
    cases h : b i <;> simp [h]
  right_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    change transversal {i | decide (Sum.inl i∈S.val.val)=true}=S.val.val
    have he : {i | decide (Sum.inl i∈S.val.val)=true}=Sum.inl ⁻¹' S.val.val := by
      ext i
      simp
    rw [he]
    exact (plain_eq_transversal n S.val.val S.property).symm

noncomputable def sortedMemberEquiv {Γ : Type*} [Fintype Γ] [LinearOrder Γ] (S : Set Γ) :
    Fin (Fintype.card S) ≃ S := by
  let c : ↥S.toFinset ≃ S :=
    { toFun := fun a => ⟨a.val,Set.mem_toFinset.mp a.property⟩
      invFun := fun a => ⟨a.val,Set.mem_toFinset.mpr a.property⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl }
  let e := (S.toFinset.orderIsoOfFin rfl).toEquiv.trans c
  have he : Fintype.card S=S.toFinset.card := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm
  exact (finCongr he).trans e
noncomputable def canonicalPlainEnumeration (n : ℕ) :
    Fin (Fintype.card (PlainIndex (pairedSlots n))) ≃ PlainIndex (pairedSlots n) :=
  (finCongr (plainIndex_card n)).trans ((wordEquiv n).symm.trans (wordPlainEquiv n))
noncomputable def canonicalExchangeEnumeration (n : ℕ) (S : Set (Fin n ⊕ Fin n)) :
    Fin (Fintype.card (ExchangeChoice S)) ≃ ExchangeChoice S := by
  letI : LinearOrder (Fin n ⊕ Fin n) := LinearOrder.lift' (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n+n)) (Equiv.injective _)
  let e := finProdFinEquiv.symm.trans ((sortedMemberEquiv S).prodCongr (sortedMemberEquiv Sᶜ))
  have he : Fintype.card (ExchangeChoice S)=_ := (Fintype.card_congr e).symm
  exact (finCongr (by simpa only [Fintype.card_fin] using he)).trans e

section
namespace DrawTree
open scoped BigOperators Classical
variable {A B : Type*}

inductive Reindexed : DrawTree A → DrawTree A → Prop
  | leaf (a : A) : Reindexed (.leaf a) (.leaf a)
  | draw (v : ℕ) (k l : Fin (v+1) → DrawTree A) (e : Fin (v+1) ≃ Fin (v+1))
      (h : ∀ i,Reindexed (k i) (l (e i))) : Reindexed (.draw v k) (.draw v l)
noncomputable def uniformVia (A : Type*) [Fintype A] [Nonempty A]
    (e : Fin (Fintype.card A) ≃ A) : DrawTree A :=
  let h : Fintype.card A-1+1=Fintype.card A := by have hh := Fintype.card_pos (α := A); omega
  .draw (Fintype.card A-1) (fun i => .leaf (e (Fin.cast h i)))
end DrawTree

open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (r : ℕ) (O : IndependenceOracle n) (N L : ℕ)
local notation "GS" => pairedSlots n
noncomputable def canonicalMetropolis (w : ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) →
    ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) → ℚ) (f : Set (Fin n ⊕ Fin n) → ℚ)
    (S : ChainIndex GS) : DrawTree (ChainIndex GS) :=
  letI : Nonempty (ExchangeChoice S.val) := Fintype.card_pos_iff.mp (by
    rw [exchangeChoice_card GS (pairedSlots_fresh n) (pairedSlots_cover n),pairedSlots_length]; positivity)
  (DrawTree.bernoulli (1/2)).bind (fun lazy => if lazy then .leaf S else
    (DrawTree.uniformVia (ExchangeChoice S.val) (canonicalExchangeEnumeration n S.val)).bind
      (rationalExchange GS w f S))
noncomputable def canonicalStepTree (h : List (PhaseSample n N)) (j : ℕ) : ChainIndex GS → DrawTree (ChainIndex GS) :=
  canonicalMetropolis n hn (rationalStored n N h j) (oracleAnneal n r O j)
noncomputable def canonicalTraceTree (h : List (PhaseSample n N)) (j cap : ℕ) :
    PlainIndex GS → DrawTree (Option (PlainIndex GS)) :=
  fun x => hittingTree (canonicalStepTree n hn r O N h j) (plainPredicate GS) (cap+1) x.val
noncomputable def canonicalRestartTree (h : List (PhaseSample n N)) (cap : ℕ) : ℕ → DrawTree (Option (PlainIndex GS))
  | 0 =>
    letI := plainIndex_nonempty GS (pairedSlots_fresh n) (pairedSlots_cover n)
    (DrawTree.uniformVia (PlainIndex GS) (canonicalPlainEnumeration n)).map some
  | j+1 => (canonicalRestartTree h cap j).optionBind
      (DrawTree.iterate (canonicalTraceTree n hn r O N h (j+1) cap) (20*n^4*(n*(L+1)+2)))
noncomputable def canonicalStartTree (h : List (PhaseSample n N)) : DrawTree (Option (ChainIndex GS)) :=
  (canonicalRestartTree n hn r O N L h (restartCap n L) h.length).map (Option.map Subtype.val)
noncomputable def canonicalPhaseTree (h : List (PhaseSample n N)) : DrawTree (Option (PhaseSample n N)) :=
  if rationalHistoryPositive n N h then
    (canonicalStartTree n hn r O N L h).optionBind
      (fun x => (DrawTree.sample (canonicalStepTree n hn r O N h h.length) (N-1) x).map some)
  else .leaf none
noncomputable def canonicalWitnessTree (h : List (PhaseSample n N)) : DrawTree (Option (PlainIndex GS)) :=
  if rationalHistoryPositive n N h then canonicalRestartTree n hn r O N L h (restartCap n L) h.length else .leaf none
noncomputable def canonicalAlgorithmTree : DrawTree (Option ℚ) :=
  (DrawTree.history (canonicalPhaseTree n hn r O N L) L []).optionBind (fun h =>
    (canonicalWitnessTree n hn r O N L h).map (Option.map (oracleGuard n r O N L h)))

end

section CanonicalFair
open scoped BigOperators Classical
noncomputable def canonicalFairOutput (n : ℕ) (hn : 0<n) (r : ℕ) (O : IndependenceOracle n)
    (N L : ℕ) (bits : FairBank n N L) : ℚ :=
  ((DrawTree.run (drawWordBound n N L) (algorithmDrawBound n N L+6) (algorithmDrawBound n N L)
    (canonicalAlgorithmTree n hn r O N L) bits).join).getD 0
noncomputable def canonicalAmplifiedOutput (n : ℕ) (hn : 0<n) (r : ℕ) (O : IndependenceOracle n)
    (N L : ℕ) (δ : ℚ) (bits : Fin (repetitionCount δ) → FairBank n N L) : ℚ :=
  rationalMedian (List.ofFn (fun i => canonicalFairOutput n hn r O N L (bits i)))
noncomputable def canonicalBoundedOutput (n r : ℕ) (O : IndependenceOracle n)
    (ε δ : ℚ) (bits : FPRASBank n ε δ) : ℚ :=
  if hn : 0<n then
    canonicalAmplifiedOutput n hn r O (sampleCount n (annealLength n (accuracyExponent ε)) ε)
      (annealLength n (accuracyExponent ε)) δ bits
  else 1
end CanonicalFair

open scoped BigOperators Classical

open scoped BigOperators Classical

def bitMatrixEquiv (a b : ℕ) : BitWord (a*b) ≃ (Fin a → BitWord b) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin a) (Fin b) Bool)
def fourBitEquiv (a b c d : ℕ) : BitWord (a*(b*(c*d))) ≃
    (Fin a → Fin b → Fin c → BitWord d) :=
  (bitMatrixEquiv a (b*(c*d))).trans
    (Equiv.piCongrRight (fun _ => (bitMatrixEquiv b (c*d)).trans
      (Equiv.piCongrRight (fun _ => bitMatrixEquiv c d))))

open scoped BigOperators Classical

section

variable {k n : ℕ}
def workConfig (R : Fin (k+8) → List Bool) (pc : Fin 6) (q c : ℕ) : MachineConfig k 5 :=
  ⟨R,pc,none,q,c⟩
def pairRegisters (R : Fin (k+8) → List Bool) (a b : Fin (k+8)) (xs ys : List Bool) :=
  Function.update (Function.update R a xs) b ys
def incrementProgram (a b : Fin (k+8)) : Program k 5 := fun pc =>
  match pc.val with
  | 0 => .pop a 1 1 2
  | 1 => .push a true 3
  | 2 => .push b false 0
  | 3 => .pop b 5 4 4
  | 4 => .push a false 3
  | _ => .halt
def leadingOnes : List Bool → ℕ
  | [] => 0
  | false::_ => 0
  | true::xs => leadingOnes xs+1
def carryTail : List Bool → List Bool
  | [] => [true]
  | false::xs => true::xs
  | true::xs => carryTail xs
def incrementBits (xs : List Bool) : List Bool := List.replicate (leadingOnes xs) false ++ carryTail xs

end

section

variable {k s t n : ℕ}
def Instruction.relabel (e : Fin (s+1) → Fin (t+1)) : Instruction k s → Instruction k t
  | .push i b j => .push i b (e j)
  | .pop i x y z => .pop i (e x) (e y) (e z)
  | .coin x y => .coin (e x) (e y)
  | .query w i x y => .query w i (e x) (e y)
  | .halt => .halt
def relabelConfig (e : Fin (s+1) → Fin (t+1)) (c : MachineConfig k s) : MachineConfig k t :=
  ⟨c.registers,e c.control,c.output,c.oracleCalls,c.bitOperations⟩
def firstLabel (s t : ℕ) (i : Fin (s+1)) : Fin (s+t+1) := ⟨i.val,by omega⟩
def secondLabel (s t : ℕ) (i : Fin (t+1)) : Fin (s+t+1) := ⟨s+i.val,by omega⟩
def lastLabel (s : ℕ) : Fin (s+1) := ⟨s,by omega⟩

def concatProgram (P : Program k s) (Q : Program k t) : Program k (s+t) := fun i =>
  if hi : i.val<s then (P ⟨i.val,by omega⟩).relabel (firstLabel s t)
  else (Q ⟨i.val-s,by omega⟩).relabel (secondLabel s t)
lemma concatProgram_second (P : Program k s) (Q : Program k t) (i : Fin (t+1)) :
    concatProgram P Q (secondLabel s t i)=(Q i).relabel (secondLabel s t) := by
  simp [concatProgram,secondLabel,show ¬s+i.val<s by omega]

def restartControl (c : MachineConfig k s) (j : Fin (t+1)) : MachineConfig k t :=
  ⟨c.registers,j,c.output,c.oracleCalls,c.bitOperations⟩

end

section
variable {k n : ℕ}
def tripleRegisters (R : Fin (k+8) → List Bool) (a b d : Fin (k+8)) (xs ys zs : List Bool) :=
  Function.update (pairRegisters R a b xs ys) d zs
def copyConfig (R : Fin (k+8) → List Bool) (pc : Fin 9) (q c : ℕ) : MachineConfig k 8 :=
  ⟨R,pc,none,q,c⟩
def copyProgram (a b d : Fin (k+8)) : Program k 8 := fun pc =>
  match pc.val with
  | 0 => .pop a 3 1 2
  | 1 => .push b false 0
  | 2 => .push b true 0
  | 3 => .pop b 8 4 5
  | 4 => .push a false 6
  | 5 => .push a true 7
  | 6 => .push d false 3
  | 7 => .push d true 3
  | _ => .halt

def sumDigit (x y c : Bool) : Bool := xor (xor x y) c
def sumCarry (x y c : Bool) : Bool := (x && y) || (x && c) || (y && c)
def addDigits (c : Bool) (xs ys : List Bool) : List Bool :=
  match xs,ys with
  | [],[] => if c then [true] else []
  | x::xs,[] => sumDigit x false c :: addDigits (sumCarry x false c) xs []
  | [],y::ys => sumDigit false y c :: addDigits (sumCarry false y c) [] ys
  | x::xs,y::ys => sumDigit x y c :: addDigits (sumCarry x y c) xs ys
termination_by xs.length+ys.length
def addCost (c : Bool) (xs ys : List Bool) : ℕ :=
  match xs,ys with
  | [],[] => if c then 3 else 2
  | x::xs,[] => 3+addCost (sumCarry x false c) xs []
  | [],y::ys => 3+addCost (sumCarry false y c) [] ys
  | x::xs,y::ys => 3+addCost (sumCarry x y c) xs ys
termination_by xs.length+ys.length

def addConfig (R : Fin (k+8) → List Bool) (pc : Fin 17) (q c : ℕ) : MachineConfig k 16 :=
  ⟨R,pc,none,q,c⟩
def addProgram (a b d : Fin (k+8)) : Program k 16 := fun pc =>
  match pc.val with
  | 0 => .pop a 2 3 4
  | 1 => .pop a 5 6 7
  | 2 => .pop b 12 8 9
  | 3 => .pop b 8 8 9
  | 4 => .pop b 9 9 10
  | 5 => .pop b 13 9 10
  | 6 => .pop b 9 9 10
  | 7 => .pop b 10 10 11
  | 8 => .push d false 0
  | 9 => .push d true 0
  | 10 => .push d false 1
  | 11 => .push d true 1
  | 12 => .pop d 16 14 15
  | 13 => .push d true 12
  | 14 => .push a false 12
  | 15 => .push a true 12
  | _ => .halt

def mulRegisters (R : Fin (k+8) → List Bool) (xs ys zs ws : List Bool) : Fin (k+8) → List Bool :=
  fun i => if i=0 then xs else if i=1 then ys else if i=2 then zs
    else if i=3 then [] else if i=4 then ws else R i

def mulBody : Program k 24 := concatProgram (copyProgram 0 3 4) (addProgram 2 4 3)
def mulBodyConfig (R : Fin (k+8) → List Bool) (pc : Fin 25) (q c : ℕ) : MachineConfig k 24 :=
  ⟨R,pc,none,q,c⟩
def mulBodyCost (xs zs : List Bool) : ℕ :=
  (5*xs.length+2)+(addCost false zs xs+2*(addDigits false zs xs).length+1)

def mulBodyLabel (i : Fin 25) : Fin 27 := ⟨i.val+1,by omega⟩
def mulProgram : Program k 26 := fun i =>
  if hi : i.val=0 then .pop 1 26 25 1
  else if hj : i.val<25 then
    ((mulBody : Program k 24) ⟨i.val-1,by omega⟩).relabel mulBodyLabel
  else if i.val=25 then .push 0 false 0 else .halt
def mulConfig (R : Fin (k+8) → List Bool) (pc : Fin 27) (q c : ℕ) : MachineConfig k 26 :=
  ⟨R,pc,none,q,c⟩

def mulDigits (xs ys zs : List Bool) : List Bool :=
  match ys with
  | [] => zs
  | bit::ys => mulDigits (false::xs) ys (if bit then addDigits false zs xs else zs)
def mulCost (xs ys zs : List Bool) : ℕ :=
  match ys with
  | [] => 1
  | bit::ys => 2+(if bit then mulBodyCost xs zs else 0)+
      mulCost (false::xs) ys (if bit then addDigits false zs xs else zs)

def coinWord : ℕ → (ℕ → Bool) → List Bool
  | 0,_ => []
  | m+1,bits => bits 1::coinWord m (fun i => bits (3+i))
def randomProgram (counter dest : Fin (k+8)) : Program k 4 := fun pc =>
  match pc.val with
  | 0 => .pop counter 4 1 1
  | 1 => .coin 2 3
  | 2 => .push dest false 0
  | 3 => .push dest true 0
  | _ => .halt

end

open scoped Classical

section

variable {k n : ℕ}
def wordOracle (which : Bool) (O : IndependenceOracle n) (l : List Bool) : Bool :=
  O which (fun i => l[i.val]?.getD false)
def wordGreedy (W : List Bool → Bool) : List Bool → List Bool → List Bool
  | [],ps => ps
  | b::xs,ps => wordGreedy W xs ((b && W (List.replicate xs.length false++true::ps))::ps)
def greedyTime (n : ℕ) : List Bool → ℕ
  | [] => 1
  | b::xs => (if b then 6*n+5 else 3)+greedyTime n xs
def greedyWork (n : ℕ) : List Bool → ℕ
  | [] => 1
  | b::xs => (if b then 8*n+5 else 3)+greedyWork n xs
def greedyCalls : List Bool → ℕ
  | [] => 0
  | b::xs => (if b then 1 else 0)+greedyCalls xs

def greedyRegisters (R : Fin (k+8) → List Bool) (xs zs ps qs : List Bool) : Fin (k+8) → List Bool :=
  fun i => if i=0 then xs else if i=1 then zs else if i=2 then ps else if i=3 then [] else if i=4 then qs else R i
def greedyConfig (R : Fin (k+8) → List Bool) (pc : Fin 27) (q c : ℕ) : MachineConfig k 26 :=
  ⟨R,pc,none,q,c⟩
def greedyCopy₁ (i : Fin 9) : Fin 27 := ⟨i.val+4,by omega⟩
def greedyCopy₂ (i : Fin 9) : Fin 27 := ⟨i.val+13,by omega⟩
def greedyProgram (which : Bool) : Program k 26 := fun pc =>
  if h₁ : 4≤pc.val ∧ pc.val<12 then
    ((copyProgram 2 3 4) ⟨pc.val-4,by omega⟩).relabel greedyCopy₁
  else if h₂ : 13≤pc.val ∧ pc.val<21 then
    ((copyProgram 1 3 4) ⟨pc.val-13,by omega⟩).relabel greedyCopy₂
  else match pc.val with
    | 0 => .pop 0 26 1 2
    | 1 => .pop 1 3 3 3
    | 2 => .pop 1 4 4 4
    | 3 => .push 2 false 0
    | 12 => .push 4 true 13
    | 21 => .query which 4 22 23
    | 22 => .pop 4 24 22 22
    | 23 => .pop 4 25 23 23
    | 24 => .push 2 false 0
    | 25 => .push 2 true 0
    | _ => .halt

end

section

variable {n : ℕ}
def wordSet (n : ℕ) (l : List Bool) : Set (Fin n) := {i | l[i.val]?.getD false=true}

end

section

variable {k n : ℕ}

def popcountBits : List Bool → List Bool → List Bool
  | [],ys => ys
  | b::xs,ys => popcountBits xs (if b then incrementBits ys else ys)
def popcountTime : List Bool → List Bool → ℕ
  | [],_ => 1
  | b::xs,ys => 1+(if b then 4*leadingOnes ys+3 else 0)+popcountTime xs (if b then incrementBits ys else ys)

def popcountConfig (R : Fin (k+8) → List Bool) (pc : Fin 7) (q c : ℕ) : MachineConfig k 6 :=
  ⟨R,pc,none,q,c⟩
def popcountLabel (i : Fin 6) : Fin 7 := if i.val<5 then ⟨i.val+1,by omega⟩ else 0
def popcountProgram : Program k 6 := fun pc =>
  if h0 : pc.val=0 then .pop 2 6 0 1
  else if h1 : pc.val<6 then
    ((incrementProgram 0 3) ⟨pc.val-1,by omega⟩).relabel popcountLabel
  else .halt

end

section
open scoped BigOperators Classical
variable {k n : ℕ}

def rankProgram (which : Bool) : Program k 32 := concatProgram (greedyProgram which) popcountProgram
def rankConfig (R : Fin (k+8) → List Bool) (pc : Fin 33) (q c : ℕ) : MachineConfig k 32 :=
  ⟨R,pc,none,q,c⟩
def rankBits (which : Bool) (O : IndependenceOracle n) (xs : List Bool) : List Bool :=
  popcountBits (wordGreedy (wordOracle which O) xs []) []
def rankTime (which : Bool) (O : IndependenceOracle n) (xs : List Bool) : ℕ :=
  greedyTime n xs+popcountTime (wordGreedy (wordOracle which O) xs []) []
def rankWork (which : Bool) (O : IndependenceOracle n) (xs : List Bool) : ℕ :=
  greedyWork n xs+popcountTime (wordGreedy (wordOracle which O) xs []) []

end

section

variable {k n : ℕ}
def compareBits : Bool → List Bool → List Bool → Bool
  | b,[],[] => b
  | b,[],y::ys => compareBits (if y then true else b) [] ys
  | b,x::xs,[] => compareBits (if x then false else b) xs []
  | b,x::xs,y::ys => compareBits (if x=y then b else y) xs ys

def compareConfig (R : Fin (k+8) → List Bool) (pc : Fin 10) (q c : ℕ) : MachineConfig k 9 :=
  ⟨R,pc,none,q,c⟩
def compareProgram (a b : Fin (k+8)) : Program k 9 := fun pc =>
  match pc.val with
  | 0 => .pop a 1 2 3
  | 1 => .pop b 8 0 4
  | 2 => .pop b 0 0 4
  | 3 => .pop b 0 0 0
  | 4 => .pop a 5 6 7
  | 5 => .pop b 9 4 4
  | 6 => .pop b 4 4 4
  | 7 => .pop b 0 0 4
  | _ => .halt

def subBorrow (x y c : Bool) : Bool := ((!x) && (y || c)) || (y && c)
def subDigits (c : Bool) (xs ys : List Bool) : List Bool :=
  match xs,ys with
  | [],[] => []
  | x::xs,[] => sumDigit x false c :: subDigits (subBorrow x false c) xs []
  | [],y::ys => sumDigit false y c :: subDigits (subBorrow false y c) [] ys
  | x::xs,y::ys => sumDigit x y c :: subDigits (subBorrow x y c) xs ys
termination_by xs.length+ys.length
def subCost (c : Bool) (xs ys : List Bool) : ℕ :=
  match xs,ys with
  | [],[] => 2
  | x::xs,[] => 3+subCost (subBorrow x false c) xs []
  | [],y::ys => 3+subCost (subBorrow false y c) [] ys
  | x::xs,y::ys => 3+subCost (subBorrow x y c) xs ys
termination_by xs.length+ys.length

def subConfig (R : Fin (k+8) → List Bool) (pc : Fin 17) (q c : ℕ) : MachineConfig k 16 :=
  ⟨R,pc,none,q,c⟩
def subProgram (a b d : Fin (k+8)) : Program k 16 := fun pc =>
  match pc.val with
  | 0 => .pop a 2 3 4
  | 1 => .pop a 5 6 7
  | 2 => .pop b 12 8 11
  | 3 => .pop b 8 8 11
  | 4 => .pop b 9 9 8
  | 5 => .pop b 12 11 10
  | 6 => .pop b 11 11 10
  | 7 => .pop b 8 8 11
  | 8 => .push d false 0
  | 9 => .push d true 0
  | 10 => .push d false 1
  | 11 => .push d true 1
  | 12 => .pop d 16 14 15
  | 13 => .halt
  | 14 => .push a false 12
  | 15 => .push a true 12
  | _ => .halt

end

section

variable {k n : ℕ}
def divRegisters (R : Fin (k+8) → List Bool) (xs ys zs ws as bs : List Bool) : Fin (k+8) → List Bool :=
  fun i => if i=0 then xs else if i=1 then ys else if i=2 then zs else if i=3 then ws
    else if i=4 then [] else if i=5 then as else if i=6 then bs else R i
def divCopies : Program k 16 := concatProgram (copyProgram 2 4 5) (copyProgram 1 4 6)
def divCheck : Program k 25 := concatProgram divCopies (compareProgram 5 6)
def divSubtract : Program k 24 := concatProgram (copyProgram 1 4 5) (subProgram 2 5 4)
def divCopiesConfig (R : Fin (k+8) → List Bool) (pc : Fin 17) (q c : ℕ) : MachineConfig k 16 := ⟨R,pc,none,q,c⟩
def divCheckConfig (R : Fin (k+8) → List Bool) (pc : Fin 26) (q c : ℕ) : MachineConfig k 25 := ⟨R,pc,none,q,c⟩
def divSubtractConfig (R : Fin (k+8) → List Bool) (pc : Fin 25) (q c : ℕ) : MachineConfig k 24 := ⟨R,pc,none,q,c⟩

def divCheckCost (ys zs : List Bool) : ℕ := (5*zs.length+2)+(5*ys.length+2)+(2*max zs.length ys.length+2)

def divSubtractCost (ys zs : List Bool) : ℕ := (5*ys.length+2)+(subCost false zs ys+2*(subDigits false zs ys).length+1)

def divisionCheckLabel (i : Fin 26) : Fin 54 :=
  if h : i.val<24 then ⟨3+i.val,by omega⟩ else if i.val=24 then 27 else 52
def divisionSubLabel (i : Fin 25) : Fin 54 := ⟨27+i.val,by omega⟩
def divisionProgram : Program k 53 := fun i =>
  if i.val=0 then .pop 0 53 1 2
  else if i.val=1 then .push 2 false 3
  else if i.val=2 then .push 2 true 3
  else if h : i.val<27 then
    ((divCheck : Program k 25) ⟨i.val-3,by omega⟩).relabel divisionCheckLabel
  else if h : i.val<51 then
    ((divSubtract : Program k 24) ⟨i.val-27,by omega⟩).relabel divisionSubLabel
  else if i.val=51 then .push 3 true 0
  else if i.val=52 then .push 3 false 0
  else .halt
def divisionConfig (R : Fin (k+8) → List Bool) (pc : Fin 54) (q c : ℕ) : MachineConfig k 53 :=
  ⟨R,pc,none,q,c⟩

def divisionRemainder (ys zs : List Bool) : List Bool :=
  if binaryValue zs<binaryValue ys then zs else subDigits false zs ys
def divisionDigit (ys zs : List Bool) : Bool := decide (binaryValue ys≤binaryValue zs)
def divisionDigitCost (ys zs : List Bool) : ℕ :=
  2+divCheckCost ys zs+(if binaryValue zs<binaryValue ys then 0 else divSubtractCost ys zs)+1

def divisionWords : List Bool → List Bool → List Bool → List Bool → List Bool × List Bool
  | [],_,zs,ws => (zs,ws)
  | x::xs,ys,zs,ws => divisionWords xs ys (divisionRemainder ys (x::zs)) (divisionDigit ys (x::zs)::ws)
def divisionCost : List Bool → List Bool → List Bool → ℕ
  | [],_,_ => 1
  | x::xs,ys,zs => divisionDigitCost ys (x::zs)+divisionCost xs ys (divisionRemainder ys (x::zs))

def streamValue : List Bool → ℕ → ℕ
  | [],a => a
  | x::xs,a => streamValue xs (2*a+(if x then 1 else 0))

end

variable {k n : ℕ}
def bitFrame : List Bool → List Bool
  | [] => [true]
  | b::bs => false::b::bitFrame bs

def framePackProgram (a d : Fin (k+8)) : Program k 5 := fun pc =>
  match pc.val with
  | 0 => .push d true 1
  | 1 => .pop a 5 2 3
  | 2 => .push d false 4
  | 3 => .push d true 4
  | 4 => .push d false 1
  | _ => .halt
def frameConfig (R : Fin (k+8) → List Bool) (pc : Fin 6) (q c : ℕ) : MachineConfig k 5 :=
  ⟨R,pc,none,q,c⟩

def frameUnpackProgram (a d : Fin (k+8)) : Program k 5 := fun pc =>
  match pc.val with
  | 0 => .pop a 5 1 4
  | 1 => .pop a 5 2 3
  | 2 => .push d false 0
  | 3 => .push d true 0
  | _ => .halt

end

namespace MachineCode
abbrev Registers (k : ℕ) := Fin (k+8) → List Bool
structure Block (k : ℕ) where
  size : ℕ
  code : Program k size
  exit_halt : code (lastLabel size) = .halt

def state {k s : ℕ} (R : Registers k) (pc : Fin (s+1)) (q w : ℕ) : MachineConfig k s :=
  ⟨R,pc,none,q,w⟩

def Runs {k n : ℕ} (p : Block k) (O : IndependenceOracle n) (bits : ℕ → Bool)
    (R R' : Registers k) (t q w : ℕ) : Prop :=
  ∀ q₀ w₀, execution p.code O (state R 0 q₀ w₀) bits t =
    state R' (lastLabel p.size) (q₀+q) (w₀+w)

def skip (k : ℕ) : Block k := ⟨0,fun _ => .halt,rfl⟩

def seq {k : ℕ} (p q : Block k) : Block k where
  size := p.size+q.size
  code := concatProgram p.code q.code
  exit_halt := by
    have he : lastLabel (p.size+q.size)=secondLabel p.size q.size (lastLabel q.size) := by
      apply Fin.ext; rfl
    rw [he,concatProgram_second,q.exit_halt]
    rfl

def push {k : ℕ} (a : Fin (k+8)) (b : Bool) : Block k where
  size := 1
  code := fun pc => if pc=0 then .push a b 1 else .halt
  exit_halt := by simp [lastLabel]

inductive Test (k : ℕ) where
  | pop (a : Fin (k+8)) (empty zero one : Bool)
  | query (which : Bool) (a : Fin (k+8))
  | coin

def Test.instruction {k s : ℕ} (test : Test k) (no yes : Fin (s+1)) : Instruction k s :=
  match test with
  | .pop a e z o => .pop a (if e then yes else no) (if z then yes else no) (if o then yes else no)
  | .query which a => .query which a no yes
  | .coin => .coin no yes

def Test.result {k n : ℕ} (test : Test k) (O : IndependenceOracle n) (bit : Bool)
    (R : Registers k) : Option (Bool × Registers k) :=
  match test with
  | .pop a e z o => match R a with
    | [] => some (e,R)
    | b::xs => some ((if b then o else z),Function.update R a xs)
  | .query which a => if (R a).length=n then
      some (O which (fun i => (R a)[i.val]?.getD false),R) else none
  | .coin => some (bit,R)

def Test.queries {k : ℕ} : Test k → ℕ
  | .query _ _ => 1
  | _ => 0

def Test.work {k : ℕ} (test : Test k) (n : ℕ) (R : Registers k) : ℕ :=
  match test with
  | .query _ a => (R a).length+n+1
  | _ => 1

def noLabel (s t : ℕ) (i : Fin (s+1)) : Fin (s+t+2) :=
  if i.val=s then lastLabel (s+t+1) else ⟨i.val+1,by omega⟩
def yesLabel (s t : ℕ) (i : Fin (t+1)) : Fin (s+t+2) :=
  if i.val=t then lastLabel (s+t+1) else ⟨s+i.val+1,by omega⟩

def fork {k : ℕ} (test : Test k) (p q : Block k) : Block k where
  size := p.size+q.size+1
  code := fun pc =>
    if pc.val=0 then test.instruction (noLabel p.size q.size 0) (yesLabel p.size q.size 0)
    else if h : pc.val≤p.size then
      (p.code ⟨pc.val-1,by omega⟩).relabel (noLabel p.size q.size)
    else if h : pc.val≤p.size+q.size then
      (q.code ⟨pc.val-p.size-1,by omega⟩).relabel (yesLabel p.size q.size)
    else .halt
  exit_halt := by simp [lastLabel,show ¬p.size+q.size+1≤p.size by omega]

end MachineCode

section MachineLoops
variable {k s n : ℕ}
def loopLabel (s : ℕ) (i : Fin (s+1)) : Fin (s+2) :=
  if h : i.val=s then 0 else ⟨i.val+1,by omega⟩
def repeatProgram (P : Program k s) (a : Fin (k+8)) : Program k (s+1) := fun pc =>
  if pc.val=0 then .pop a (lastLabel (s+1)) (loopLabel s 0) (loopLabel s 0)
  else if h : pc.val≤ s then (P ⟨pc.val-1,by omega⟩).relabel (loopLabel s)
  else .halt
def loopConfig (R : Fin (k+8) → List Bool) (pc : Fin (s+1)) (q c : ℕ) : MachineConfig k s :=
  ⟨R,pc,none,q,c⟩
end MachineLoops

section MachineMove
variable {k n : ℕ}
def reverseProgram (a d : Fin (k+8)) : Program k 3 := fun pc =>
  match pc.val with
  | 0 => .pop a 3 1 2
  | 1 => .push d false 0
  | 2 => .push d true 0
  | _ => .halt
def reverseConfig (R : Fin (k+8) → List Bool) (pc : Fin 4) (q c : ℕ) : MachineConfig k 3 :=
  ⟨R,pc,none,q,c⟩
def clearProgram (a : Fin (k+8)) : Program k 1 := fun pc => if pc.val=0 then .pop a 1 0 0 else .halt
def clearConfig (R : Fin (k+8) → List Bool) (pc : Fin 2) (q c : ℕ) : MachineConfig k 1 :=
  ⟨R,pc,none,q,c⟩
def moveProgram (a b d : Fin (k+8)) : Program k 6 := concatProgram (reverseProgram a b) (reverseProgram b d)
def moveConfig (R : Fin (k+8) → List Bool) (pc : Fin 7) (q c : ℕ) : MachineConfig k 6 :=
  ⟨R,pc,none,q,c⟩
end MachineMove

namespace MachineCode

def reverse {k : ℕ} (a d : Fin (k+8)) : Block k :=
  ⟨3,reverseProgram a d,rfl⟩
def clear {k : ℕ} (a : Fin (k+8)) : Block k :=
  ⟨1,clearProgram a,rfl⟩
def move {k : ℕ} (a b d : Fin (k+8)) : Block k :=
  ⟨6,moveProgram a b d,rfl⟩
def pack {k : ℕ} (a d : Fin (k+8)) : Block k :=
  ⟨5,framePackProgram a d,rfl⟩
def unpack {k : ℕ} (a d : Fin (k+8)) : Block k where
  size := 4
  code := fun pc => match pc.val with
    | 0 => .pop a 4 1 4
    | 1 => .pop a 4 2 3
    | 2 => .push d false 0
    | 3 => .push d true 0
    | _ => .halt
  exit_halt := rfl

def repeatBlock {k : ℕ} (p : Block k) (a : Fin (k+8)) : Block k where
  size := p.size+1
  code := repeatProgram p.code a
  exit_halt := by simp [repeatProgram,lastLabel]

abbrev Word := List Bool

def regs (x y z saved : Word) : Registers 1 := fun i =>
  if i=0 then x else if i=1 then y else if i=2 then z else if i=8 then saved else []
@[simp] lemma regs_zero (x y z s : Word) : regs x y z s 0=x := by simp [regs]
@[simp] lemma regs_one (x y z s : Word) : regs x y z s 1=y := by simp [regs]
@[simp] lemma regs_eight (x y z s : Word) : regs x y z s 8=s := by simp [regs]

def pair (x y : Word) : Word := bitFrame x.reverse++y

def Computes {n : ℕ} (p : Block 1) (O : IndependenceOracle n)
    (x y : Word) (t q w : ℕ) : Prop :=
  ∀ saved bits, Runs p O bits (regs x [] [] saved) (regs y [] [] saved) t q w

def Bounded {n : ℕ} (p : Block 1) (O : IndependenceOracle n) (x y : Word) (B : ℕ) : Prop :=
  ∃ t q w, t≤B ∧ q≤B ∧ w≤B ∧ Computes p O x y t q w

def copy {k : ℕ} (a b d : Fin (k+8)) : Block k := ⟨8,copyProgram a b d,rfl⟩

def duplicate : Block 1 := seq (copy 0 2 1) (pack 1 0)

def first : Block 1 := seq (unpack 0 1) (seq (clear 0) (move 1 2 0))
def second : Block 1 := seq (unpack 0 1) (clear 1)

def swap : Block 1 := seq (unpack 0 1) (seq (pack 0 1) (move 1 2 0))

def left (p : Block 1) : Block 1 :=
  seq (unpack 0 1) (seq (pack 0 8) (seq (move 1 2 0)
    (seq p (seq (unpack 8 1) (seq (pack 0 1) (move 1 2 0))))))

def right (p : Block 1) : Block 1 := seq swap (seq (left p) swap)

def parallel (p q : Block 1) : Block 1 := seq (left p) (right q)
def fanout (p q : Block 1) : Block 1 := seq duplicate (parallel p q)

def stripZeros : Word → Word
  | [] => []
  | false::xs => stripZeros xs
  | true::xs => true::xs
def stripCost : Word → ℕ
  | [] => 1
  | false::xs => 1+stripCost xs
  | true::_ => 2

def normalWord (x : Word) : Word := (stripZeros x.reverse).reverse

def stripCode {k : ℕ} (a : Fin (k+8)) : Block k where
  size := 2
  code := fun pc => match pc.val with
    | 0 => .pop a 2 0 1
    | 1 => .push a true 2
    | _ => .halt
  exit_halt := rfl

def normalCode : Block 1 := seq (reverse 0 1) (seq (stripCode 1) (reverse 1 0))
def normalCost (x : Word) : ℕ := 2*x.length+1+(stripCost x.reverse+(2*(stripZeros x.reverse).length+1))

def addBlock : Block 1 := ⟨16,addProgram 0 1 2,rfl⟩
def addTime (x y : Word) : ℕ := addCost false x y+2*(addDigits false x y).length+1

def addCode : Block 1 := seq (unpack 0 1) (seq addBlock normalCode)

def mulBlock : Block 1 := ⟨26,mulProgram,rfl⟩

def mulCode : Block 1 := seq (unpack 0 1) (seq mulBlock (seq (clear 0) (seq (move 2 1 0) normalCode)))
def mulTime (x y : Word) : ℕ :=
  3*x.length+1+mulCost y x []+(x.length+y.length+1)+(4*(mulDigits y x []).length+2)+normalCost (mulDigits y x [])

def prependCode : Word → Block 1
  | [] => skip 1
  | b::xs => seq (prependCode xs) (push 0 b)

def constCode (x : Word) : Block 1 := seq (clear 0) (prependCode x)

def selectCode (p q : Block 1) : Block 1 := seq (unpack 0 1) (fork (.pop 1 false false true) p q)

def queryCode (which : Bool) : Block 1 := fork (.query which 0) (constCode [false]) (constCode [true])

def quadRegs (x y z u s : Word) : Registers 1 := Function.update (regs x y z s) 3 u
@[simp] lemma quadRegs_three (x y z u s : Word) : quadRegs x y z u s 3=u := by simp [quadRegs]
@[simp] lemma update_quad_three (x y z u s v : Word) : Function.update (quadRegs x y z u s) 3 v=quadRegs x y z v s := by
  simp [quadRegs]

def divBlock : Block 1 := ⟨53,divisionProgram,rfl⟩

def rawDivCode : Block 1 := seq (unpack 0 1)
  (seq (seq (reverse 0 2) (move 2 3 0)) (seq divBlock
    (seq (clear 1) (seq (pack 2 3) (move 3 1 0)))))
def divResult (x y : Word) : Word × Word := divisionWords y.reverse x [] []
def rawDivTime (x y : Word) : ℕ :=
  4*x.length+6*y.length+11*(divResult x y).1.length+4*(divResult x y).2.length+13+divisionCost y.reverse x []

def divCode : Block 1 := seq rawDivCode (parallel normalCode normalCode)
def normalizedResult (x y : Word) : Word := pair (binaryValue (divResult x y).1).bits (binaryValue (divResult x y).2).bits

def cmpLabel (i : Fin 10) : Fin 11 := ⟨i.val,by omega⟩
def cmpBlock : Block 1 where
  size := 10
  code := fun pc => if h : pc.val < 8 then
      (compareProgram (1 : Fin 9) 0 ⟨pc.val,by omega⟩).relabel cmpLabel
    else if pc.val=8 then .push 0 false 10
    else if pc.val=9 then .push 0 true 10 else .halt
  exit_halt := rfl

def cmpCode : Block 1 := seq (unpack 0 1) cmpBlock

def words : List Word → Word
  | [] => []
  | x::xs => true :: pair x (words xs)

def listBody (p : Block 1) : Block 1 :=
  seq (unpack 1 2) (seq (pack 1 8) (seq (pack 2 0) (seq p (unpack 8 1))))

def foldCode (p : Block 1) : Block 1 := seq (unpack 0 1) (repeatBlock (listBody p) 1)

def reverseCode : Block 1 := seq (reverse 0 1) (move 1 2 0)

def boolListBlock : Block 1 where
  size := 7
  code := fun pc => match pc.val with
    | 0 => .pop 1 7 1 2
    | 1 => .push 0 true 3
    | 2 => .push 0 true 4
    | 3 => .push 0 false 5
    | 4 => .push 0 true 5
    | 5 => .push 0 false 6
    | 6 => .push 0 true 0
    | _ => .halt
  exit_halt := rfl

def boolListCode : Block 1 := seq (reverse 0 1) boolListBlock

def consWordCode : Block 1 := seq (unpack 0 1)
  (fork (.pop 1 false false true) (push 0 false) (push 0 true))

def consListCode : Block 1 := push 0 true

def appendCode : Block 1 := seq (unpack 0 1) (move 1 2 0)

def subBlock : Block 1 := ⟨16,subProgram 1 0 2,rfl⟩
def subTime (x y : Word) : ℕ := subCost false x y+2*(subDigits false x y).length+1

def subCode : Block 1 := seq (unpack 0 1) (seq subBlock (seq (move 1 2 0) normalCode))

def rankPrep : Block 1 where
  size := 5
  code := fun pc => match pc.val with
    | 0 => .pop 0 5 1 3
    | 1 => .push 2 false 2
    | 2 => .push 1 false 0
    | 3 => .push 2 true 4
    | 4 => .push 1 false 0
    | _ => .halt
  exit_halt := rfl

def readyRank (which : Bool) : Block 1 := ⟨32,rankProgram which,rfl⟩
def rankCode (which : Bool) : Block 1 := seq rankPrep (seq (move 2 3 0) (seq (readyRank which) normalCode))
def rankWord {n : ℕ} (O : IndependenceOracle n) (which : Bool) (x : Word) : ℕ :=
  binaryValue (rankBits which O x.reverse)

inductive DataType where
  | unit | bool | nat | word
  | prod : DataType → DataType → DataType
  | list : DataType → DataType

@[reducible] def Value : DataType → Type
  | .unit => Unit
  | .bool => Bool
  | .nat => ℕ
  | .word => Word
  | .prod a b => Value a × Value b
  | .list a => List (Value a)

def encode : {a : DataType} → Value a → Word
  | .unit,_ => []
  | .bool,b => [b]
  | .nat,m => m.bits
  | .word,w => w
  | .prod _ _,(x,y) => pair (encode x) (encode y)
  | .list _,xs => words (xs.map encode)

def width {a : DataType} (x : Value a) : ℕ := (encode x).length

inductive Expression : DataType → DataType → Type where
  | ident {a} : Expression a a
  | constant {a b} : Value b → Expression a b
  | compose {a b c} : Expression a b → Expression b c → Expression a c
  | both {a b c} : Expression a b → Expression a c → Expression a (.prod b c)
  | fst {a b} : Expression (.prod a b) a
  | snd {a b} : Expression (.prod a b) b
  | branch {a b} : Expression a b → Expression a b → Expression (.prod .bool a) b
  | fold {a b} : Expression (.prod a b) b → Expression (.prod (.list a) b) b
  | cons {a} : Expression (.prod a (.list a)) (.list a)
  | consBit : Expression (.prod .bool .word) .word
  | append : Expression (.prod .word .word) .word
  | reverse : Expression .word .word
  | toList : Expression .word (.list .bool)
  | toBits : Expression .nat .word
  | toNat : Expression .word .nat
  | add : Expression (.prod .nat .nat) .nat
  | sub : Expression (.prod .nat .nat) .nat
  | rank : Bool → Expression .word .nat
  | mul : Expression (.prod .nat .nat) .nat
  | less : Expression (.prod .nat .nat) .bool
  | divRem : Expression (.prod .nat .nat) (.prod .nat .nat)
  | query : Bool → Expression .word .bool

def compile : {a b : DataType} → Expression a b → Block 1
  | _,_,.ident => skip 1
  | _,_,.constant x => constCode (encode x)
  | _,_,.compose p q => seq (compile p) (compile q)
  | _,_,.both p q => fanout (compile p) (compile q)
  | _,_,.fst => first
  | _,_,.snd => second
  | _,_,.branch p q => selectCode (compile p) (compile q)
  | _,_,.fold p => foldCode (compile p)
  | _,_,.cons => consListCode
  | _,_,.consBit => consWordCode
  | _,_,.append => appendCode
  | _,_,.reverse => reverseCode
  | _,_,.toList => boolListCode
  | _,_,.toBits => skip 1
  | _,_,.toNat => normalCode
  | _,_,.add => addCode
  | _,_,.sub => subCode
  | _,_,.rank b => rankCode b
  | _,_,.mul => mulCode
  | _,_,.less => cmpCode
  | _,_,.divRem => divCode
  | _,_,.query b => queryCode b

def evalFold {a b : DataType} (step : Value (.prod a b) → Option (Value b × ℕ)) :
    List (Value a) → Value b → Option (Value b × ℕ)
  | [],z => some (z,0)
  | x::xs,z => do
    let (z',c) ← step (x,z)
    let (y,d) ← evalFold step xs z'
    pure (y,7+6*width x+6*width (a:=.list a) xs+c+d)

def evaluate {n : ℕ} (O : IndependenceOracle n) : {a b : DataType} → Expression a b →
    Value a → Option (Value b × ℕ)
  | _,_,.ident,x => some (x,0)
  | _,_,.constant y,x => some (y,width x+width y+1)
  | _,_,.compose p q,x => do
    let (y,c) ← evaluate O p x
    let (z,d) ← evaluate O q y
    pure (z,c+d)
  | _,_,.both p q,x => do
    let (y,c) ← evaluate O p x
    let (z,d) ← evaluate O q x
    pure ((y,z),43*width x+39*width y+18*width z+50+c+d)
  | _,_,.fst,(x,y) => some (x,7*width x+width y+4)
  | _,_,.snd,(x,y) => some (y,4*width x+2)
  | _,_,.branch p q,(b,x) => do
    let (y,c) ← (if b then evaluate O q x else evaluate O p x)
    pure (y,5+c)
  | _,_,.fold p,(xs,z) => do
    let (y,c) ← evalFold (evaluate O p) xs z
    pure (y,3*width xs+2+c)
  | _,_,.cons,(x,xs) => some (x::xs,1)
  | _,_,.consBit,(b,xs) => some (b::xs,6)
  | _,_,.append,(x,y) => some (x++y,7*x.length+3)
  | _,_,.reverse,x => some (x.reverse,6*x.length+3)
  | _,_,.toList,x => some (x,7*x.length+2)
  | _,_,.toBits,x => some (x.bits,0)
  | _,_,.toNat,x => some (binaryValue x,5*x.length+4)
  | _,_,.add,(x,y) => some (x+y,20*(x.bits.length+y.bits.length+1))
  | _,_,.sub,(x,y) => if y≤x then some (x-y,30*(x.bits.length+y.bits.length+1)) else none
  | _,_,.rank b,x => if x.length=n then some (rankWord O b x,100*(n+1)^2) else none
  | _,_,.mul,(x,y) => some (x*y,60*(x.bits.length+y.bits.length+1)^2)
  | _,_,.less,(x,y) => some (decide (x<y),5*(x.bits.length+y.bits.length+1))
  | _,_,.divRem,(x,y) => if x=0 then none else
      some ((y%x,y/x),300*(x.bits.length+y.bits.length+1)^2)
  | _,_,.query b,x => if x.length=n then
      some (O b (fun i => x[i.val]?.getD false),3*n+3) else none

def foldValue {A B : Type*} (step : A × B → Option B) : List A → B → Option B
  | [],z => some z
  | x::xs,z => (step (x,z)).bind (foldValue step xs)

def run {n : ℕ} (O : IndependenceOracle n) : {a b : DataType} → Expression a b → Value a → Option (Value b)
  | _,_,.ident,x => some x
  | _,_,.constant y,_ => some y
  | _,_,.compose p q,x => (run O p x).bind (run O q)
  | _,_,.both p q,x => do let y ← run O p x; let z ← run O q x; pure (y,z)
  | _,_,.fst,(x,_) => some x
  | _,_,.snd,(_,y) => some y
  | _,_,.branch p q,(b,x) => if b then run O q x else run O p x
  | _,_,.fold p,(xs,z) => foldValue (run O p) xs z
  | _,_,.cons,(x,xs) => some (x::xs)
  | _,_,.consBit,(b,xs) => some (b::xs)
  | _,_,.append,(x,y) => some (x++y)
  | _,_,.reverse,x => some x.reverse
  | _,_,.toList,x => some x
  | _,_,.toBits,x => some x.bits
  | _,_,.toNat,x => some (binaryValue x)
  | _,_,.add,(x,y) => some (x+y)
  | _,_,.sub,(x,y) => if y≤x then some (x-y) else none
  | _,_,.mul,(x,y) => some (x*y)
  | _,_,.less,(x,y) => some (decide (x<y))
  | _,_,.divRem,(x,y) => if x=0 then none else some (y%x,y/x)
  | _,_,.query b,x => if x.length=n then some (O b (fun i => x[i.val]?.getD false)) else none
  | _,_,.rank b,x => if x.length=n then some (rankWord O b x) else none

namespace Expression
infixr:80 " >>> " => compose

def onLeft {a b c} (p : Expression a b) : Expression (.prod a c) (.prod b c) :=
  both (fst >>> p) snd
def onRight {a b c} (p : Expression a b) : Expression (.prod c a) (.prod c b) :=
  both fst (snd >>> p)
def swap {a b} : Expression (.prod a b) (.prod b a) := both snd fst
def letIn {a b c} (p : Expression a b) (q : Expression (.prod a b) c) : Expression a c :=
  both ident p >>> q
def applyIf {a b} (test : Expression a .bool) (no yes : Expression a b) : Expression a b :=
  both test ident >>> branch no yes

def boolNot : Expression .bool .bool := both ident ident >>> branch (constant true) (constant false)
def boolAnd : Expression (.prod .bool .bool) .bool := branch (constant false) ident
def natEqZero : Expression .nat .bool := both ident (constant 1) >>> less
def natSub : Expression (.prod .nat .nat) .nat := applyIf less sub (constant 0)
def natDivRem : Expression (.prod .nat .nat) (.prod .nat .nat) :=
  applyIf (fst >>> natEqZero) divRem (both snd (constant 0))
def natDiv : Expression (.prod .nat .nat) .nat := natDivRem >>> snd
def natMod : Expression (.prod .nat .nat) .nat := natDivRem >>> fst

def listReverse {a} : Expression (.list a) (.list a) := both ident (constant []) >>> fold cons

def mapStep {a b c} (p : Expression (.prod a c) b) : Expression (.prod a (.prod (.list b) c)) (.prod (.list b) c) :=
  both
    (both (both fst (snd >>> snd) >>> p) (snd >>> fst) >>> cons)
    (snd >>> snd)
def mapWith {a b c} (p : Expression (.prod a c) b) : Expression (.prod (.list a) c) (.list b) :=
  both fst (both (constant []) snd) >>> fold (mapStep p) >>> fst >>> listReverse

def listLength {a} : Expression (.list a) .nat :=
  both ident (constant 0) >>> fold (both snd (constant 1) >>> add)
def wordLength : Expression .word .nat := toList >>> listLength

def wordRepeatStep : Expression (.prod .bool .word) .word :=
  letIn (snd >>> both ident ident >>> append)
    (both fst snd >>> both (fst >>> fst) snd >>> branch ident (both (constant false) ident >>> consBit))

def unary : Expression .nat .word :=
  both (toBits >>> reverse >>> toList) (constant []) >>> fold wordRepeatStep

end Expression

namespace Expression
variable {n : ℕ} (O : IndependenceOracle n)
@[simp] lemma run_boolNot (b : Bool) : run O boolNot b=some (!b) := by
  cases b <;> rfl
@[simp] lemma run_boolAnd (b c : Bool) : run O boolAnd (b,c)=some (b && c) := by
  cases b <;> rfl
@[simp] lemma run_natEqZero (m : ℕ) : run O natEqZero m=some (decide (m=0)) := by
  simp [natEqZero,run]
@[simp] lemma run_natSub (x y : ℕ) : run O natSub (x,y)=some (x-y) := by
  simp only [natSub,applyIf,run]
  by_cases h : x<y
  · simp [h,Nat.sub_eq_zero_of_le (Nat.le_of_lt h)]
  · simp [h,Nat.le_of_not_gt h]
@[simp] lemma run_natDivRem (x y : ℕ) : run O natDivRem (x,y)=some (y%x,y/x) := by
  simp only [natDivRem,applyIf,run,run_natEqZero]
  by_cases h : x=0 <;> simp [h]
@[simp] lemma run_natDiv (x y : ℕ) : run O natDiv (x,y)=some (y/x) := by
  change ((run O natDivRem (x,y)).bind fun p => some p.2)=some (y/x)
  rw [run_natDivRem]; rfl
@[simp] lemma run_natMod (x y : ℕ) : run O natMod (x,y)=some (y%x) := by
  change ((run O natDivRem (x,y)).bind fun p => some p.1)=some (y%x)
  rw [run_natDivRem]; rfl
end Expression

@[simp] lemma width_nil {a : DataType} : width (a:=.list a) []=0 := rfl

def FoldSafe {A B : Type*} (ok : A×B → Prop) (f : A×B → Option B) : List A → B → Prop
  | [],_ => True
  | x::xs,z => ok (x,z) ∧ ∀ y,f (x,z)=some y → FoldSafe ok f xs y

def Safe {n : ℕ} (O : IndependenceOracle n) (S : ℕ) : {a b : DataType} →
    Expression a b → Value a → Prop
  | _,_,e,x => width x≤S ∧ (∀ y,run O e x=some y → width y≤S) ∧
    match e,x with
    | .compose p q,x => Safe O S p x ∧ ∀ y,run O p x=some y → Safe O S q y
    | .both p q,x => Safe O S p x ∧ Safe O S q x
    | .branch p q,(b,x) => if b then Safe O S q x else Safe O S p x
    | .fold p,(xs,z) => FoldSafe (Safe O S p) (run O p) xs z
    | _,_ => True

def chargeBound : {a b : DataType} → Expression a b → ℕ → ℕ
  | _,_,.compose p q,T => 10000*(T+1)^2+chargeBound p T+chargeBound q T
  | _,_,.both p q,T => 10000*(T+1)^2+chargeBound p T+chargeBound q T
  | _,_,.branch p q,T => 10000*(T+1)^2+chargeBound p T+chargeBound q T
  | _,_,.fold p,T => 10000*(T+1)^2+(T+1)*(10000*(T+1)^2+chargeBound p T)
  | _,_,_,T => 10000*(T+1)^2

def chargeDegree : {a b : DataType} → Expression a b → ℕ
  | _,_,.compose p q => chargeDegree p+chargeDegree q+3
  | _,_,.both p q => chargeDegree p+chargeDegree q+3
  | _,_,.branch p q => chargeDegree p+chargeDegree q+3
  | _,_,.fold p => chargeDegree p+3
  | _,_,_ => 2

def chargeCoefficient : {a b : DataType} → Expression a b → ℕ
  | _,_,.compose p q => 10000+chargeCoefficient p+chargeCoefficient q
  | _,_,.both p q => 10000+chargeCoefficient p+chargeCoefficient q
  | _,_,.branch p q => 10000+chargeCoefficient p+chargeCoefficient q
  | _,_,.fold p => 20000+chargeCoefficient p
  | _,_,_ => 10000

inductive SizePolynomial where
  | constant : ℕ → SizePolynomial
  | input : SizePolynomial
  | add : SizePolynomial → SizePolynomial → SizePolynomial
  | mul : SizePolynomial → SizePolynomial → SizePolynomial
namespace SizePolynomial
def eval : SizePolynomial → ℕ → ℕ
  | .constant c,_ => c
  | .input,x => x
  | .add p q,x => p.eval x+q.eval x
  | .mul p q,x => p.eval x*q.eval x
def degree : SizePolynomial → ℕ
  | .constant _ => 0
  | .input => 1
  | .add p q | .mul p q => p.degree+q.degree
def coefficient : SizePolynomial → ℕ
  | .constant c => c
  | .input => 1
  | .add p q => p.coefficient+q.coefficient
  | .mul p q => p.coefficient*q.coefficient
def subst : SizePolynomial → SizePolynomial → SizePolynomial
  | .constant c,_ => .constant c
  | .input,q => q
  | .add p r,q => .add (p.subst q) (r.subst q)
  | .mul p r,q => .mul (p.subst q) (r.subst q)
end SizePolynomial

def Controlled {a b : DataType} (p : Expression a b) : Prop :=
  ∃ f : SizePolynomial,∀ {n : ℕ} (O : IndependenceOracle n) (x : Value a),Safe O (f.eval (width x)) p x

@[simp] lemma width_nat (x : ℕ) : width (a:=.nat) x=x.bits.length := rfl
@[simp] lemma width_word (x : Word) : width (a:=.word) x=x.length := rfl
@[simp] lemma width_bool (x : Bool) : width (a:=.bool) x=1 := rfl
@[simp] lemma width_unit (x : Unit) : width (a:=.unit) x=0 := rfl

def Atomic : {a b : DataType} → Expression a b → Prop
  | _,_,.compose _ _ | _,_,.both _ _ | _,_,.branch _ _ | _,_,.fold _ => False
  | _,_,_ => True

def constantWidth : {a b : DataType} → Expression a b → ℕ
  | _,_,.constant x => width x
  | _,_,_ => 0

def gcdStep (p : ℕ × ℕ) : ℕ × ℕ := if p.2=0 then p else (p.2,p.1%p.2)
def gcdSteps : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0,p => p
  | k+1,p => gcdSteps k (gcdStep p)

namespace Expression
abbrev NN := DataType.prod .nat .nat

def sortPair : Expression NN NN := applyIf less ident swap
def gcdStepCode : Expression NN NN :=
  applyIf (snd >>> natEqZero) (both snd (swap >>> natMod)) ident

def gcdCode : Expression NN .nat :=
  sortPair >>> both
    (both (fst >>> toBits) (snd >>> toBits) >>> append >>> toList)
    ident >>> fold (snd >>> gcdStepCode) >>> fst
end Expression

open Expression

open Expression

def PolySafe {a b : DataType} (p : Expression a b) (R : ℕ → Value a → Prop) : Prop :=
  ∃ f : SizePolynomial,∀ {n : ℕ} (O : IndependenceOracle n) (S : ℕ) (x : Value a),
    R S x → Safe O (f.eval S) p x

def rationalPair (q : ℚ) : ℕ × ℕ := (q.num.natAbs,q.den)
def normalizePair (a b : ℕ) : ℕ × ℕ :=
  if b=0 then (0,1) else (a/Nat.gcd a b,b/Nat.gcd a b)

namespace Expression

def normalizeRat : Expression NN NN := applyIf (snd >>> natEqZero)
  (letIn gcdCode (both
    (both snd (fst >>> fst) >>> natDiv)
    (both snd (fst >>> snd) >>> natDiv)))
  (constant (0,1))

def ratCross : Expression (.prod NN NN) NN := both
  (both (fst >>> fst) (snd >>> snd) >>> mul)
  (both (snd >>> fst) (fst >>> snd) >>> mul)
def ratAdd : Expression (.prod NN NN) NN :=
  both (ratCross >>> add) (both (fst >>> snd) (snd >>> snd) >>> mul) >>> normalizeRat
def ratMul : Expression (.prod NN NN) NN :=
  both (both (fst >>> fst) (snd >>> fst) >>> mul)
       (both (fst >>> snd) (snd >>> snd) >>> mul) >>> normalizeRat
def ratDiv : Expression (.prod NN NN) NN := ratCross >>> normalizeRat
def ratLess : Expression (.prod NN NN) .bool := ratCross >>> less

def ratMinOne : Expression NN NN := applyIf (swap >>> less) ident (constant (1,1))

def iterateWord {a : DataType} (p : Expression a a) : Expression (.prod .word a) a :=
  onLeft toList >>> fold (snd >>> p)
def iterateNat {a : DataType} (p : Expression a a) : Expression (.prod .nat a) a :=
  onLeft unary >>> iterateWord p

def fromList : Expression (.list .bool) .word :=
  both (listReverse) (constant []) >>> fold consBit

def rangeStepCode : Expression (.prod .nat (.list .nat)) (.prod .nat (.list .nat)) :=
  both (both fst (constant 1) >>> add) (both fst snd >>> cons)
def rangeCode : Expression .nat (.list .nat) :=
  both ident (constant (0,[])) >>> iterateNat rangeStepCode >>> snd >>> listReverse

def rangeStep (p : ℕ × List ℕ) : ℕ × List ℕ := (p.1+1,p.1::p.2)

abbrev SplitState (a : DataType) := DataType.prod .nat (.prod (.list a) (.list a))
def splitStep {a : DataType} : Expression (.prod a (SplitState a)) (SplitState a) :=
  applyIf (snd >>> fst >>> natEqZero)
    (both (both (snd >>> fst) (constant 1) >>> natSub)
      (both (both fst (snd >>> snd >>> fst) >>> cons) (snd >>> snd >>> snd)))
    (both (snd >>> fst)
      (both (snd >>> snd >>> fst) (both fst (snd >>> snd >>> snd) >>> cons)))
def splitAtCode {a : DataType} : Expression (.prod (.list a) .nat) (.prod (.list a) (.list a)) :=
  both fst (both snd (constant ([],[]))) >>> fold splitStep >>> snd >>>
    both (fst >>> listReverse) (snd >>> listReverse)
def takeCode {a : DataType} : Expression (.prod (.list a) .nat) (.list a) := splitAtCode >>> fst
def dropCode {a : DataType} : Expression (.prod (.list a) .nat) (.list a) := splitAtCode >>> snd

def splitStepValue {a : DataType} (p : Value a × (ℕ × (List (Value a) × List (Value a)))) :=
  if p.2.1=0 then (0,(p.2.2.1,p.1::p.2.2.2)) else (p.2.1-1,(p.1::p.2.2.1,p.2.2.2))

def headD {a} : Expression (.prod (.list a) a) a := onLeft listReverse >>> fold fst
def getDCode {a} : Expression (.prod (.prod (.list a) .nat) a) a :=
  both (fst >>> dropCode) snd >>> headD

def boolOr : Expression (.prod .bool .bool) .bool := branch ident (constant true)
def natEqual : Expression NN .bool := both less (swap >>> less) >>> boolOr >>> boolNot

def listAll : Expression (.list .bool) .bool := both ident (constant true) >>> fold boolAnd

def filterStep {a b} (p : Expression (.prod a b) .bool) :
    Expression (.prod a (.prod (.list a) b)) (.prod (.list a) b) :=
  both (applyIf (both fst (snd >>> snd) >>> p) (snd >>> fst)
    (both fst (snd >>> fst) >>> cons)) (snd >>> snd)
def filterWith {a b} (p : Expression (.prod a b) .bool) :
    Expression (.prod (.list a) b) (.list a) :=
  both fst (both (constant []) snd) >>> fold (filterStep p) >>> fst >>> listReverse

def foldLast {A : Type*} : List A → A → A
  | [],d => d
  | x::xs,_ => foldLast xs x

def powStepCode : Expression (.prod .nat .nat) (.prod .nat .nat) := both fst mul
def powCode : Expression NN .nat :=
  both snd (both fst (constant 1)) >>> iterateNat powStepCode >>> snd

def ratPowCode : Expression (.prod NN .nat) NN :=
  both (both (fst >>> fst) snd >>> powCode) (both (fst >>> snd) snd >>> powCode) >>> normalizeRat
end Expression

open Expression

open Expression
def wordDouble (w : Word) (b : Bool) : Word := if b then false::(w++w) else w++w

abbrev StateData := DataType.prod .word .word

def representedState (n : ℕ) (p : Word×Word) : Set (Fin n⊕Fin n) :=
  {i | Sum.elim (fun j => j∈wordSet n p.1) (fun j => j∈wordSet n p.2) i}
@[simp] lemma representedState_inl (n : ℕ) (p : Word×Word) (i : Fin n) :
    Sum.inl i∈representedState n p ↔ p.1[i.val]?.getD false=true := Iff.rfl
@[simp] lemma representedState_inr (n : ℕ) (p : Word×Word) (i : Fin n) :
    Sum.inr i∈representedState n p ↔ p.2[i.val]?.getD false=true := Iff.rfl
@[simp] lemma representedState_preinl (n : ℕ) (p : Word×Word) :
    Sum.inl ⁻¹' representedState n p=wordSet n p.1 := rfl
@[simp] lemma representedState_preinr (n : ℕ) (p : Word×Word) :
    Sum.inr ⁻¹' representedState n p=wordSet n p.2 := rfl

namespace Expression

def wordGet : Expression (.prod .word .nat) .bool :=
  both (both (fst >>> toList) snd) (constant false) >>> getDCode
def wordNot : Expression .word .word :=
  toList >>> both ident (constant (b:=.unit) ()) >>> mapWith (c:=.unit) (fst >>> boolNot) >>> fromList
def wordCountStep : Expression (.prod .bool .nat) .nat := branch ident (both ident (constant 1) >>> add)
def wordCount : Expression .word .nat := toList >>> both ident (constant 0) >>> fold wordCountStep

def deficiencyCode : Expression (.prod .nat StateData) .nat :=
  both (both (snd >>> fst >>> wordLength) fst >>> add)
    (both (both (snd >>> fst >>> rank false) (snd >>> snd >>> wordCount) >>> add)
      (snd >>> snd >>> wordNot >>> rank true) >>> add) >>> natSub
end Expression

abbrev Optional (a : DataType) := DataType.prod .bool a
abbrev RandomRows := DataType.list .word

def optionData {a : DataType} (d : Value a) : Option (Value a) → Value (Optional a)
  | none => (false,d)
  | some x => (true,x)

namespace Expression
@[simp] lemma run_ident {n : ℕ} (O : IndependenceOracle n) {a : DataType} (x : Value a) :
  run O (ident (a:=a)) x=some x := rfl
@[simp] lemma run_fst {n : ℕ} (O : IndependenceOracle n) {a b : DataType} :
  run O (fst (a:=a) (b:=b))=(fun x => some x.1) := rfl
@[simp] lemma run_snd {n : ℕ} (O : IndependenceOracle n) {a b : DataType} :
  run O (snd (a:=a) (b:=b))=(fun x => some x.2) := rfl
@[simp] lemma run_constant {n : ℕ} (O : IndependenceOracle n) {a b : DataType} (x : Value a) (y : Value b) :
  run O (constant (a:=a) (b:=b) y) x=some y := rfl
@[simp] lemma run_reverse {n : ℕ} (O : IndependenceOracle n) (x : Word) :
  run O reverse x=some x.reverse := rfl
@[simp] lemma run_toNat {n : ℕ} (O : IndependenceOracle n) (x : Word) :
  run O toNat x=some (binaryValue x) := rfl
@[simp] lemma run_less {n : ℕ} (O : IndependenceOracle n) (x y : ℕ) :
  run O less (x,y)=some (decide (x<y)) := rfl

def wordTake : Expression (.prod .word .nat) .word := onLeft toList >>> takeCode >>> fromList

abbrev RejectState := DataType.prod NN (Optional .nat)
def rejectStep : Expression (.prod .word RejectState) RejectState :=
  both (snd >>> fst)
    (letIn (both fst (snd >>> fst >>> snd) >>> wordTake >>> reverse >>> toNat)
      (applyIf (both snd (fst >>> snd >>> fst >>> fst) >>> less)
        (fst >>> snd >>> snd) (both (constant true) snd)))
def rejectCode : Expression (.prod RandomRows NN) (Optional .nat) :=
  both (fst >>> listReverse) (both snd (constant (false,0))) >>> fold rejectStep >>> snd

def rejectValue (v k : ℕ) : List Word → Option ℕ
  | [] => none
  | x::xs => let z := binaryValue (x.take k).reverse
      if z<v then some z else rejectValue v k xs
end Expression

abbrev BankData := DataType.list RandomRows
abbrev Bank := List (List Word)
lemma rejectValue_lt (v h : ℕ) (xs : List Word) {i : ℕ}
    (hi : Expression.rejectValue v h xs=some i) : i<v := by
  induction xs with
  | nil => cases hi
  | cons x xs ih =>
    simp only [Expression.rejectValue] at hi
    split_ifs at hi with hx
    · cases hi; exact hx
    · exact ih hi

def bankEval {A : Type*} : DrawTree A → Bank → Option A × Bank
  | .leaf a,bank => (some a,bank)
  | .draw _ _,[] => (none,[])
  | .draw v k,rows::bank =>
    match hi : Expression.rejectValue (v+1) (Nat.clog 2 (v+1)) rows with
    | none => (none,bank)
    | some i => bankEval (k ⟨i,rejectValue_lt _ _ _ hi⟩) bank

def bankEncode {H D M : ℕ} (bits : Fin M → Fin D → BitWord H) : Bank :=
  List.ofFn (fun m => List.ofFn (fun d => List.ofFn (bits m d)))

open Expression

def zeroValue : (a : DataType) → Value a
  | .unit => ()
  | .bool => false
  | .nat => 0
  | .word => []
  | .prod a b => (zeroValue a,zeroValue b)
  | .list _ => []
def optionalValue (a : DataType) : Option (Value a) → Value (Optional a) := optionData (zeroValue a)

abbrev Effect (a b : DataType) := Expression (.prod a BankData) (.prod (Optional b) BankData)
namespace Expression

def clogCode : Expression .nat .nat := both ident (constant 1) >>> natSub >>> toBits >>> wordLength

end Expression
open Expression
namespace Effect

def pure {a b} (p : Expression a b) : Effect a b := both (both (constant true) (fst >>> p)) snd

def bind {a b c} (p : Effect a b) (q : Effect b c) : Effect a c :=
  p >>> applyIf (fst >>> fst)
    (both (constant (optionalValue c none)) snd)
    (both (fst >>> snd) snd >>> q)

def keep {a b} (p : Effect a b) : Effect a (.prod a b) :=
  _root_.OAI.CommonBasesFPRAS.MachineCode.Expression.letIn p (both
    (applyIf (snd >>> fst >>> fst) (constant (optionalValue (.prod a b) none))
      (both (constant true) (both (fst >>> fst) (snd >>> fst >>> snd))))
    (snd >>> snd))

def letIn {a b c} (p : Effect a b) (q : Effect (.prod a b) c) : Effect a c :=
  bind (keep p) q

def draw : Effect .nat .nat :=
  both
    (both (snd >>> both ident (constant []) >>> headD) (both fst (fst >>> clogCode)) >>> rejectCode)
    (snd >>> both ident (constant 1) >>> dropCode)

def Realizes {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b : DataType}
    (p : Effect a b) (encode : A → Value b) (x : Value a) (t : DrawTree A) : Prop :=
  ∀ bank, run O p (x,bank)=some
    (optionalValue b ((bankEval t bank).1.map encode),(bankEval t bank).2)

def map {a b c} (p : Effect a b) (q : Expression b c) : Effect a c := bind p (pure q)
def precompose {a b c} (p : Expression a b) (q : Effect b c) : Effect a c := onLeft p >>> q

def choose {a b} (test : Expression a .bool) (p q : Effect a b) : Effect a b :=
  applyIf (fst >>> test) p q

end Effect

def iterateM {A : Type*} (f : A → Option A) : ℕ → A → Option A
  | 0,x => some x
  | k+1,x => (f x).bind (iterateM f k)
namespace Effect

def loopStep {a} (p : Effect a a) : Expression (.prod (Optional a) BankData) (.prod (Optional a) BankData) :=
  applyIf (fst >>> fst) ident (both (fst >>> snd) snd >>> p)
def repeatCode {a} (p : Effect a a) : Effect (.prod .nat a) a :=
  both (fst >>> fst) (both (both (constant (b:=.bool) true) (fst >>> snd)) snd) >>> iterateNat (loopStep p)

def treeRepeat {A : Type*} (f : A → DrawTree A) : ℕ → A → DrawTree A
  | 0,x => .leaf x
  | k+1,x => (f x).bind (treeRepeat f k)

end Effect
end MachineCode

namespace MachineCode
open Expression
namespace Effect

def RealizesLaw {n : ℕ} (O : IndependenceOracle n) {A : Type*} {a b : DataType}
    (p : Effect a b) (encode : A → Value b) (x : Value a) (t : DrawTree A) : Prop :=
  ∃ u, DrawTree.Reindexed t u ∧ Realizes O p encode x u
end Effect
end MachineCode

namespace MachineCode

open Expression

def optionEncode {A : Type*} {a} (e : A → Value a) (x : Option A) : Value (Optional a) :=
  optionalValue a (x.map e)
@[simp] lemma optionEncode_none {A : Type*} {a} (e : A → Value a) :
    optionEncode e none=(false,zeroValue a) := rfl
@[simp] lemma optionEncode_some {A : Type*} {a} (e : A → Value a) (x : A) :
    optionEncode e (some x)=(true,e x) := rfl
namespace Effect

def someCode {a b} (p : Effect a b) : Effect a (Optional b) :=
  map p (both (constant true) ident)
def noneCode {a b} : Effect a (Optional b) := pure (constant (optionalValue b none))
def optionContinue {a b} (q : Effect a (Optional b)) : Effect (Optional a) (Optional b) :=
  choose fst noneCode (precompose snd q)
def optionBind {a b c} (p : Effect a (Optional b)) (q : Effect b (Optional c)) : Effect a (Optional c) :=
  bind p (optionContinue q)

def iterateCode {a} (p : Effect a (Optional a)) : Effect (.prod .nat a) (Optional a) :=
  precompose (both fst (both (constant true) snd)) (repeatCode (optionContinue p))
end Effect

open scoped Classical
noncomputable def stateEncode {n : ℕ} (S : Set (Fin n⊕Fin n)) : Value StateData :=
  (List.ofFn (fun i => decide (Sum.inl i∈S)),List.ofFn (fun i => decide (Sum.inr i∈S)))
@[simp] lemma stateEncode_left_length {n : ℕ} (S : Set (Fin n⊕Fin n)) :
    (stateEncode S).1.length=n := List.length_ofFn
@[simp] lemma stateEncode_right_length {n : ℕ} (S : Set (Fin n⊕Fin n)) :
    (stateEncode S).2.length=n := List.length_ofFn
@[simp] lemma stateEncode_repr {n : ℕ} (S : Set (Fin n⊕Fin n)) :
    representedState n (stateEncode S)=S := by
  ext i
  cases i <;> simp [representedState,stateEncode,wordSet]
lemma stateEncode_get_left {n : ℕ} (S : Set (Fin n⊕Fin n)) (i : Fin n) :
    (stateEncode S).1[i.val]?.getD false=decide (Sum.inl i∈S) := by simp [stateEncode]

namespace Expression

def boolXor : Expression (.prod .bool .bool) .bool := branch ident boolNot

def singleAt : Expression (.prod .nat StateData) .bool :=
  both (both (snd >>> fst) fst >>> wordGet) (both (snd >>> snd) fst >>> wordGet) >>> boolXor
def fullAt : Expression (.prod .nat StateData) .bool :=
  both (both (snd >>> fst) fst >>> wordGet) (both (snd >>> snd) fst >>> wordGet) >>> boolAnd
def emptyAt : Expression (.prod .nat StateData) .bool :=
  both (both (snd >>> fst) fst >>> wordGet) (both (snd >>> snd) fst >>> wordGet) >>> boolOr >>> boolNot

def singleValue (i : ℕ) (S : Word×Word) : Bool := xor (S.1[i]?.getD false) (S.2[i]?.getD false)
def fullValue (i : ℕ) (S : Word×Word) : Bool := (S.1[i]?.getD false) && (S.2[i]?.getD false)
def emptyValue (i : ℕ) (S : Word×Word) : Bool := !(S.1[i]?.getD false || S.2[i]?.getD false)

def plainValue (S : Word×Word) : Bool := ((List.range S.1.length).map (fun i => singleValue i S)).all id
def plainCode : Expression StateData .bool :=
  both (fst >>> wordLength >>> rangeCode) ident >>> mapWith singleAt >>> listAll
end Expression

abbrev DefectInput := DataType.prod Expression.NN StateData
namespace Expression

def defectAt : Expression (.prod .nat DefectInput) .bool :=
  applyIf (both fst (snd >>> fst >>> fst) >>> natEqual)
    (applyIf (both fst (snd >>> fst >>> snd) >>> natEqual)
      (both fst (snd >>> snd) >>> singleAt) (both fst (snd >>> snd) >>> fullAt))
    (both fst (snd >>> snd) >>> emptyAt)
def defectAtValue (i : ℕ) (p : (ℕ×ℕ)×(Word×Word)) : Bool :=
  if i=p.1.1 then emptyValue i p.2 else if i=p.1.2 then fullValue i p.2 else singleValue i p.2

def defectValue (p r : ℕ) (S : Word×Word) : Bool :=
  decide (p≠r) && ((List.range S.1.length).map (fun i => defectAtValue i ((p,r),S))).all id
def defectCode : Expression DefectInput .bool :=
  both (fst >>> natEqual >>> boolNot)
    (both (snd >>> fst >>> wordLength >>> rangeCode) ident >>> mapWith defectAt >>> listAll) >>> boolAnd
end Expression

abbrev SampleData := DataType.list StateData
abbrev HistoryData := DataType.list SampleData
namespace Expression

def countWith {a b} (p : Expression (.prod a b) .bool) : Expression (.prod (.list a) b) .nat :=
  filterWith p >>> listLength

def countPlainCode : Expression SampleData .nat :=
  both ident (constant (b:=.unit) ()) >>> countWith (fst >>> plainCode)
def countDefectCode : Expression (.prod SampleData NN) .nat := countWith (swap >>> defectCode)
def countPlainValue (xs : List (Word×Word)) : ℕ := xs.countP plainValue
def countDefectValue (xs : List (Word×Word)) (p r : ℕ) : ℕ := xs.countP (fun S => defectValue p r S)

def learningRatioCode : Expression (.prod SampleData NN) NN :=
  both (fst >>> countPlainCode) countDefectCode >>> normalizeRat
def learningRatio (xs : List (Word×Word)) (p r : ℕ) : ℚ := (countPlainValue xs:ℚ)/countDefectValue xs p r

def weightStep : Expression (.prod SampleData (.prod NN NN)) (.prod NN NN) :=
  both (snd >>> fst)
    (applyIf (snd >>> fst >>> natEqual)
      (both (snd >>> snd) (both fst (snd >>> fst) >>> learningRatioCode) >>> ratMul)
      (snd >>> snd))
def weightUpdate (p r : ℕ) (xs : List (Word×Word)) (q : ℚ) : ℚ :=
  if p=r then q else q*learningRatio xs p r

def historyWeightValue (p r : ℕ) (h : List (List (Word×Word))) : ℚ :=
  h.foldl (fun q xs => weightUpdate p r xs q) 4
def historyWeightCode : Expression (.prod HistoryData NN) NN :=
  both fst (both snd (constant (b:=NN) (4,1))) >>> fold weightStep >>> snd
end Expression

noncomputable def sampleEncode {n : ℕ} (xs : List (Set (Fin n⊕Fin n))) : Value SampleData := xs.map stateEncode
noncomputable def historyEncode {n : ℕ} (h : List (List (Set (Fin n⊕Fin n)))) : Value HistoryData := h.map sampleEncode

namespace Expression

def listAppend {a} : Expression (.prod (.list a) (.list a)) (.list a) :=
  onLeft listReverse >>> fold cons

def productStep {a b} : Expression (.prod a (.prod (.list (.prod a b)) (.list b)))
    (.prod (.list (.prod a b)) (.list b)) :=
  both (both (snd >>> fst) (both (snd >>> snd) fst >>> mapWith swap) >>> listAppend) (snd >>> snd)
def productCode {a b} : Expression (.prod (.list a) (.list b)) (.list (.prod a b)) :=
  both fst (both (constant []) snd) >>> fold productStep >>> fst

def indexPairs : Expression .nat (.list NN) := both rangeCode rangeCode >>> productCode
end Expression

open Expression

open Expression
open Expression
open scoped Classical
namespace Effect

def phaseRepeat {A : Type*} (f : ℕ → A → DrawTree (Option A)) : ℕ → A → DrawTree (Option A)
  | 0,x => .leaf (some x)
  | k+1,x => (phaseRepeat f k x).optionBind (f (k+1))

def hitStepCode {a} (step : Effect a a) (test : Expression a .bool) : Effect (.prod a .bool) (.prod a .bool) :=
  choose snd (map (precompose fst step) (both ident test)) (pure ident)
def hitFinish {a} : Expression (.prod a .bool) (Optional a) :=
  applyIf snd (constant (optionalValue a none)) (both (constant true) fst)
def hittingCode {a} (step : Effect a a) (test : Expression a .bool) : Effect (.prod .nat a) (Optional a) :=
  precompose (both fst (both snd (constant false))) (map (repeatCode (hitStepCode step test)) hitFinish)

abbrev SearchState (X : Type*) (P : X → Prop) := X ⊕ FiniteChain.Inside P
noncomputable def searchStep {X : Type*} (step : X → DrawTree X) (P : X → Prop) :
    SearchState X P → DrawTree (SearchState X P)
  | .inl x => (step x).map (fun y => if hy : P y then .inr ⟨y,hy⟩ else .inl y)
  | .inr y => .leaf (.inr y)
def searchFinish {X : Type*} {P : X → Prop} : SearchState X P → Option (FiniteChain.Inside P)
  | .inl _ => none
  | .inr y => some y
def searchEncode {X : Type*} {P : X → Prop} {a} (e : X → Value a) : SearchState X P → Value (.prod a .bool)
  | .inl x => (e x,false)
  | .inr y => (e y.val,true)

end Effect

open Expression
namespace Expression

def optionMapCode {a b} (p : Expression a b) : Expression (Optional a) (Optional b) :=
  applyIf fst (constant (optionalValue b none)) (both (constant true) (snd >>> p))
end Expression
namespace Effect

def withContext {a b c} (p : Effect (.prod c a) b) : Effect (.prod c a) (.prod c b) :=
  letIn p (pure (both (fst >>> fst) snd))
end Effect

open scoped Classical
namespace Expression

def defectPairsValue (S : Word×Word) : List (ℕ×ℕ) :=
  ((List.range S.1.length) ×ˢ (List.range S.1.length)).filter (fun pr => defectValue pr.1 pr.2 S)
def defectPairsCode : Expression StateData (.list NN) :=
  both (fst >>> wordLength >>> indexPairs) ident >>> filterWith defectCode

def chainValue (S : Word×Word) : Bool := plainValue S || decide ((defectPairsValue S).length≠0)
def chainCode : Expression StateData .bool :=
  both plainCode (defectPairsCode >>> listLength >>> natEqZero >>> boolNot) >>> boolOr

def multiplierValue (h : List (List (Word×Word))) (S : Word×Word) : ℚ :=
  if (defectPairsValue S).length=0 then 1 else
    historyWeightValue ((defectPairsValue S).headD (0,0)).1 ((defectPairsValue S).headD (0,0)).2 h
def multiplierCode : Expression (.prod HistoryData StateData) NN :=
  letIn (snd >>> defectPairsCode)
    (applyIf (snd >>> listLength >>> natEqZero)
      (both (fst >>> fst) (both snd (constant (0,0)) >>> headD) >>> historyWeightCode)
      (constant (1,1)))
end Expression

namespace Expression

@[simp] lemma run_append {n : ℕ} (O : IndependenceOracle n) (S : Word×Word) :
    run O append S=some (S.1++S.2) := rfl

def updateAt : Expression (.prod .nat (.prod .word (.prod .nat .bool))) .bool :=
  applyIf (both fst (snd >>> snd >>> fst) >>> natEqual)
    (both (snd >>> fst) fst >>> wordGet) (snd >>> snd >>> snd)
def updateWord : Expression (.prod .word (.prod .nat .bool)) .word :=
  both (fst >>> wordLength >>> rangeCode) ident >>> mapWith updateAt >>> fromList

def splitWord : Expression (.prod .word .nat) StateData :=
  onLeft toList >>> splitAtCode >>> both (fst >>> fromList) (snd >>> fromList)

def exchangeWord : Expression (.prod .word NN) .word :=
  letIn (both fst (both (snd >>> fst) (constant false)) >>> updateWord)
    (both snd (both (fst >>> snd >>> snd) (constant true)) >>> updateWord)

def exchangeSetCode : Expression (.prod StateData NN) StateData :=
  both (both (fst >>> append) snd >>> exchangeWord) (fst >>> fst >>> wordLength) >>> splitWord
end Expression

open scoped Classical
noncomputable def combinedEncode {n : ℕ} (S : Set (Fin n⊕Fin n)) : Word := (stateEncode S).1++(stateEncode S).2
def position {n : ℕ} (i : Fin n⊕Fin n) : ℕ := (finSumFinEquiv i).val
@[simp] lemma combinedEncode_length {n : ℕ} (S : Set (Fin n⊕Fin n)) : (combinedEncode S).length=n+n := by
  simp [combinedEncode]
lemma combinedEncode_get {n : ℕ} (S : Set (Fin n⊕Fin n)) (i : Fin n⊕Fin n) :
    (combinedEncode S)[position i]?.getD false=decide (i∈S) := by
  cases i with
  | inl i =>
    simp only [combinedEncode,position,finSumFinEquiv,Equiv.coe_fn_mk]
    rw [List.getElem?_append_left (by simp)]
    exact stateEncode_get_left S i
  | inr i => simp [combinedEncode,stateEncode,position,finSumFinEquiv,i.isLt]

open scoped Classical
namespace Expression

def rhoCode : Expression .nat NN := applyIf natEqZero
  (letIn (both ident (constant 2) >>> mul)
    (both (both snd (constant 1) >>> natSub) snd >>> normalizeRat))
  (constant (1,1))

abbrev WeightContext := DataType.prod NN HistoryData
abbrev WeightInput := DataType.prod WeightContext StateData

def annealCode : Expression WeightInput NN :=
  both (both (snd >>> fst >>> wordLength >>> rhoCode) (fst >>> fst >>> snd) >>> ratPowCode)
    (both (fst >>> fst >>> fst) snd >>> deficiencyCode) >>> ratPowCode
def weightCode : Expression WeightInput NN :=
  both (both (fst >>> snd) snd >>> multiplierCode) annealCode >>> ratMul
end Expression

open Expression
namespace Effect

def bernoulliCode : Effect NN .bool :=
  letIn (precompose snd draw) (pure (both snd (fst >>> fst) >>> less))
end Effect

open Expression
open scoped Classical
namespace Expression
abbrev AcceptanceInput := DataType.prod WeightContext (.prod StateData StateData)
def acceptanceCode : Expression AcceptanceInput NN :=
  both (both fst (snd >>> snd) >>> weightCode) (both fst (snd >>> fst) >>> weightCode) >>>
    ratDiv >>> ratMinOne
end Expression

open scoped Classical
namespace Expression

def memberPositions (w : Word) : List ℕ := (List.range w.length).filter (fun i => w[i]?.getD false)
def membersCode : Expression .word (.list .nat) :=
  both (wordLength >>> rangeCode) ident >>> filterWith (swap >>> wordGet)
lemma memberPositions_nodup (w : Word) : (memberPositions w).Nodup :=
  List.nodup_range.filter _
end Expression

lemma mem_memberPositions_source {n : ℕ} (S : Set (Fin n⊕Fin n)) (i : Fin n⊕Fin n) :
    position i∈Expression.memberPositions (combinedEncode S) ↔ i∈S := by
  simp only [Expression.memberPositions,List.mem_filter,List.mem_range,combinedEncode_length,
    combinedEncode_get,decide_eq_true_eq]
  exact and_iff_right (finSumFinEquiv i).isLt

noncomputable def memberPositionEquiv {n : ℕ} (S : Set (Fin n⊕Fin n)) :
    {i : ℕ // i∈Expression.memberPositions (combinedEncode S)} ≃ S where
  toFun i := by
    have hi : i.val<n+n := by
      have hh := (List.mem_filter.mp i.property).1
      simpa only [List.mem_range,combinedEncode_length] using hh
    let j := finSumFinEquiv.symm ⟨i.val,hi⟩
    have hj : position j=i.val := by simp [position,j]
    exact ⟨j,(mem_memberPositions_source S j).mp (hj.symm ▸ i.property)⟩
  invFun i := ⟨position i.val,(mem_memberPositions_source S i.val).mpr i.property⟩
  left_inv i := by apply Subtype.ext; simp [position]
  right_inv i := by apply Subtype.ext; simp [position]

open Expression
namespace Effect

def uniformList {a} : Effect (.list a) a :=
  letIn (precompose listLength draw) (pure (both (both fst snd) (constant (zeroValue a)) >>> getDCode))

end Effect

open scoped Classical
open Expression
lemma combinedEncode_compl {n : ℕ} (S : Set (Fin n⊕Fin n)) :
    combinedEncode Sᶜ=(combinedEncode S).map Bool.not := by
  simp [combinedEncode,stateEncode,List.map_append,List.map_ofFn,Function.comp_def]

def exchangePositions (S : Word×Word) : List (ℕ×ℕ) :=
  memberPositions (S.1++S.2) ×ˢ memberPositions ((S.1++S.2).map Bool.not)
def Expression.exchangePositionsCode : Expression StateData (.list NN) :=
  append >>> both membersCode (wordNot >>> membersCode) >>> productCode
lemma exchangePositions_nodup (S : Word×Word) : (exchangePositions S).Nodup := by
  exact List.Nodup.product (memberPositions_nodup _) (memberPositions_nodup _)

lemma memberPositionEquiv_val {n : ℕ} (S : Set (Fin n⊕Fin n))
    (i : {i : ℕ // i∈memberPositions (combinedEncode S)}) :
    position (memberPositionEquiv S i).val=i.val := by simp [memberPositionEquiv,position]

noncomputable def exchangePositionEquiv {n : ℕ} (S : Set (Fin n⊕Fin n)) :
    {p : ℕ×ℕ // p∈exchangePositions (stateEncode S)} ≃ ExchangeChoice S where
  toFun p :=
    let hp : p.val∈memberPositions (combinedEncode S) ×ˢ memberPositions (combinedEncode Sᶜ) := by
      rw [combinedEncode_compl]
      exact p.property
    (memberPositionEquiv S ⟨p.val.1,(List.mem_product.mp hp).1⟩,
      memberPositionEquiv Sᶜ ⟨p.val.2,(List.mem_product.mp hp).2⟩)
  invFun p := ⟨(position p.1.val,position p.2.val),by
    change (position p.1.val, position p.2.val)∈
      memberPositions (combinedEncode S) ×ˢ memberPositions ((combinedEncode S).map Bool.not)
    rw [←combinedEncode_compl]
    exact List.mem_product.mpr ⟨(mem_memberPositions_source S _).mpr p.1.property,
      (mem_memberPositions_source Sᶜ _).mpr p.2.property⟩⟩
  left_inv p := by apply Subtype.ext; simp [memberPositionEquiv_val]
  right_inv p := by
    apply Prod.ext <;> apply Subtype.ext <;> simp [memberPositionEquiv,position]

noncomputable def exchangeListEquiv {n : ℕ} (S : Set (Fin n⊕Fin n)) :
    Fin (exchangePositions (stateEncode S)).length ≃ ExchangeChoice S :=
  (exchangePositions_nodup (stateEncode S)).getEquiv.trans (exchangePositionEquiv S)

namespace Effect

def proposal : Effect StateData NN := precompose exchangePositionsCode uniformList
end Effect

section
open Expression
open scoped Classical
namespace Effect
abbrev OfferInput := DataType.prod WeightInput StateData

def acceptancePrep : Expression OfferInput AcceptanceInput :=
  both (fst >>> fst) (both (fst >>> snd) snd)
def offerCore : Effect OfferInput StateData :=
  choose (snd >>> chainCode) (pure (fst >>> snd))
    (letIn (precompose (acceptancePrep >>> acceptanceCode) bernoulliCode)
      (pure (applyIf snd (fst >>> fst >>> snd) (fst >>> snd))))
def offerCode : Effect (.prod WeightInput NN) StateData :=
  precompose (both fst (both (fst >>> snd) snd >>> exchangeSetCode)) offerCore

def activeStepCode : Effect WeightInput StateData :=
  letIn (precompose snd proposal) offerCode

def stepCode : Effect WeightInput StateData :=
  letIn (precompose (constant (1,2)) bernoulliCode)
    (choose snd (precompose fst activeStepCode) (pure (fst >>> snd)))
end Effect

open Effect
end

section
open Expression
open scoped Classical

namespace Expression

def paddedBitsCode : Expression NN .word :=
  both (fst >>> rangeCode) (snd >>> toBits) >>> mapWith (swap >>> wordGet) >>> fromList >>> reverse

def plainDecodeCode : Expression NN StateData := paddedBitsCode >>> both ident wordNot
end Expression
namespace Effect
noncomputable local instance instNonemptyPlainIndexSumFinPairedSlots {n : ℕ} : Nonempty (PlainIndex (pairedSlots n)) :=
  plainIndex_nonempty _ (pairedSlots_fresh n) (pairedSlots_cover n)

def plainCode : Effect .nat StateData :=
  letIn (precompose (both (constant 2) ident >>> powCode) draw) (pure plainDecodeCode)

def storedStepPrep : Expression WeightInput WeightInput :=
  both (both (fst >>> fst) (both (fst >>> snd) (fst >>> fst >>> snd) >>> takeCode)) snd

def storedStepCode : Effect WeightInput StateData := precompose storedStepPrep stepCode

def traceCode : Effect (.prod .nat WeightInput) (Optional StateData) :=
  map (hittingCode (withContext storedStepCode) (snd >>> Expression.plainCode)) (optionMapCode snd)
end Effect

open Effect
end

section
open Expression
namespace Effect

def withOptionContext {a b c} (p : Effect (.prod c a) (Optional b)) : Effect (.prod c a) (Optional (.prod c b)) :=
  letIn p (pure (applyIf (snd >>> fst) (constant (optionalValue (.prod c b) none))
    (both (constant true) (both (fst >>> fst) (snd >>> snd)))))
end Effect

open Expression
open scoped Classical
abbrev RestartContext : DataType := .prod (.prod .nat HistoryData) (.prod .nat .nat)
abbrev RestartState : DataType := .prod (.prod RestartContext .nat) StateData
abbrev RestartInput : DataType := .prod .nat (.prod .nat RestartContext)
namespace Effect

def traceAtPrep : Expression RestartState (.prod .nat WeightInput) :=
  both (fst >>> fst >>> snd >>> fst >>> (both ident (constant 1) >>> add))
    (both (both (both (fst >>> fst >>> fst >>> fst) (fst >>> snd))
      (fst >>> fst >>> fst >>> snd)) snd)
def traceAtCode : Effect RestartState (Optional StateData) := precompose traceAtPrep traceCode

def restartTickPrep : Expression RestartState (.prod .nat RestartState) :=
  both (fst >>> fst >>> snd >>> snd)
    (both (both (fst >>> fst) (fst >>> snd >>> (both ident (constant 1) >>> add))) snd)
def restartTick : Effect RestartState (Optional RestartState) :=
  precompose restartTickPrep (iterateCode (withOptionContext traceAtCode))

def restartPrep : Expression (.prod RestartInput StateData) (.prod .nat (Optional RestartState)) :=
  both (fst >>> snd >>> fst) (both (constant true)
    (both (both (fst >>> snd >>> snd) (constant 0)) snd))
def restartCode : Effect RestartInput (Optional StateData) :=
  map (letIn (precompose fst plainCode)
    (precompose restartPrep (repeatCode (optionContinue restartTick)))) (optionMapCode snd)
end Effect

open Effect
open Effect
end

open Expression
open scoped Classical
namespace Expression

def allRange {a} (p : Expression (.prod .nat a) .bool) : Expression (.prod .nat a) .bool :=
  both (fst >>> rangeCode) snd >>> mapWith p >>> listAll
end Expression
namespace Expression

def pairPositiveCode : Expression (.prod HistoryData NN) .bool :=
  historyWeightCode >>> fst >>> natEqZero >>> boolNot

def slotRowCode : Expression (.prod .nat (.prod .nat HistoryData)) .bool :=
  both (snd >>> fst) (both fst (snd >>> snd)) >>>
    allRange (both (snd >>> snd) (both (snd >>> fst) fst) >>> pairPositiveCode)
def slotsPositiveCode : Expression (.prod .nat HistoryData) .bool :=
  both fst ident >>> allRange slotRowCode
def prefixPositiveCode : Expression (.prod .nat (.prod .nat HistoryData)) .bool :=
  both (snd >>> fst) (both (snd >>> snd) fst >>> takeCode) >>> slotsPositiveCode
def historyPositiveCode : Expression (.prod .nat HistoryData) .bool :=
  both (snd >>> listLength >>> (both ident (constant 1) >>> add)) ident >>> allRange prefixPositiveCode

end Expression

end MachineCode

namespace MachineCode

open Expression
namespace Effect

def sampleTick {a} (p : Effect a a) : Effect (.prod (.list a) a) (.prod (.list a) a) :=
  letIn (precompose snd p) (pure (both (both (fst >>> snd) (fst >>> fst) >>> cons) snd))
def sampleFinish {a} : Expression (.prod (.list a) a) (.list a) :=
  both (fst >>> listReverse) (both snd (constant []) >>> cons) >>> listAppend
def sampleCode {a} (p : Effect a a) : Effect (.prod .nat a) (.list a) :=
  precompose (both fst (both (constant []) snd)) (map (repeatCode (sampleTick p)) sampleFinish)

def sampleTickTree {X : Type*} (f : X → DrawTree X) (s : List X × X) : DrawTree (List X × X) :=
  (f s.2).map (fun y => (s.2::s.1,y))
end Effect

section
open Expression
open scoped Classical
abbrev AlgorithmParams : DataType := .prod NN (.prod NN NN)
abbrev PhaseInput : DataType := .prod AlgorithmParams HistoryData
def params (n r N L : ℕ) : Value AlgorithmParams :=
  ((n,r),((N,L),(restartCap n L,20*n^4*(n*(L+1)+2))))
namespace Expression
def mapEach {a b} (p : Expression a b) : Expression (.list a) (.list b) :=
  both ident (constant (b:=.unit) ()) >>> mapWith (fst >>> p)
end Expression
namespace Effect
def retainOption {a b} (p : Effect a (Optional b)) : Effect a (Optional (.prod a b)) :=
  letIn p (pure (applyIf (snd >>> fst) (constant (optionalValue (.prod a b) none))
    (both (constant true) (both fst (snd >>> snd)))))

def phaseRestartPrep : Expression PhaseInput RestartInput :=
  both (fst >>> fst >>> fst) (both (snd >>> listLength)
    (both (both (fst >>> fst >>> snd) snd) (fst >>> snd >>> snd)))
def phaseRestartCode : Effect PhaseInput (Optional StateData) := precompose phaseRestartPrep restartCode
def startCode : Effect PhaseInput (Optional StateData) := map phaseRestartCode (optionMapCode ident)
def phaseStepPrep : Expression (.prod PhaseInput StateData) WeightInput :=
  both (both (both (fst >>> fst >>> fst >>> snd) (fst >>> snd >>> listLength)) (fst >>> snd)) snd
def phaseStepCode : Effect (.prod PhaseInput StateData) StateData := precompose phaseStepPrep storedStepCode

def phaseSamplePrep : Expression (.prod PhaseInput StateData) (.prod .nat (.prod PhaseInput StateData)) :=
  both (both (fst >>> fst >>> snd >>> fst >>> fst) (constant 1) >>> natSub) ident
def phaseSampleCode : Effect (.prod PhaseInput StateData) SampleData :=
  precompose phaseSamplePrep (map (sampleCode (withContext phaseStepCode)) (mapEach snd))
def positiveTest : Expression PhaseInput .bool := both (fst >>> fst >>> fst) snd >>> historyPositiveCode
def phaseCode : Effect PhaseInput (Optional SampleData) :=
  choose positiveTest noneCode (optionBind (retainOption startCode) (someCode phaseSampleCode))
def witnessCode : Effect PhaseInput (Optional StateData) := choose positiveTest noneCode phaseRestartCode
end Effect
open Effect
end

open Expression
namespace Expression

def ratSumCode : Expression (.list NN) NN := both ident (constant (b:=NN) (0,1)) >>> fold ratAdd
def ratProductCode : Expression (.list NN) NN := both ident (constant (b:=NN) (1,1)) >>> fold ratMul

def natRatCode : Expression .nat NN := both ident (constant 1) >>> normalizeRat
end Expression

def pairHeight (p : ℕ × ℕ) : ℕ := max 1 (max p.1.bits.length p.2.bits.length)

open Expression

open Expression
def weightSmall (S : ℕ) (x : Value WeightInput) : Prop :=
  width x≤S ∧ x.1.1.1≤S ∧ x.1.1.2≤S

abbrev OraclePredicate (a : DataType) := (n : ℕ) → IndependenceOracle n → ℕ → Value a → Prop

def OracleSafe {a b : DataType} (p : Expression a b) (R : OraclePredicate a) : Prop :=
  ∃ f : SizePolynomial,∀ {n : ℕ} (O : IndependenceOracle n) S x,R n O S x → Safe O (f.eval S) p x

namespace Effect
def bankScope {a : DataType} (R : OraclePredicate a) : OraclePredicate (.prod a BankData) :=
  fun n O S x => R n O S x.1 ∧ width (a:=BankData) x.2≤S
end Effect
end MachineCode

namespace MachineCode

open Expression

open Expression
abbrev Attribute (a : DataType) := ℕ → Value a → Prop
def Attribute.Mono {a : DataType} (R : Attribute a) : Prop :=
  ∀ S T,S≤T → ∀ x,R S x → R T x
def AttrSafe {a b : DataType} (p : Expression a b) (R : Attribute a) : Prop :=
  PolySafe p (fun S x => width x≤S ∧ R S x)
namespace Effect
abbrev EffectSafe {a b : DataType} (p : Effect a b) (R : Attribute a) :=
  AttrSafe p (fun S x => R S x.1)
end Effect

namespace Effect

def optionScope {a : DataType} (R : OraclePredicate a) : OraclePredicate (Optional a) :=
  fun n O S x => x=optionalValue a none ∨ x.1=true ∧ R n O S x.2
end Effect

def contextAttr (S : ℕ) (x : Value WeightContext) : Prop := x.1.1≤S ∧ x.1.2≤S
def weightAttr (S : ℕ) (x : Value WeightInput) : Prop := contextAttr S x.1
def acceptanceAttr (S : ℕ) (x : Value AcceptanceInput) : Prop := contextAttr S x.1
namespace Effect
def offerAttr (S : ℕ) (x : Value OfferInput) : Prop := weightAttr S x.1
def pairOfferAttr (S : ℕ) (x : Value (.prod WeightInput NN)) : Prop := weightAttr S x.1
end Effect

open scoped Classical

open Expression
open Effect
open scoped Classical

structure SamplerModel (n : ℕ) (O : IndependenceOracle n) where
  M₁ : Matroid (Fin n)
  M₂ : Matroid (Fin n)
  exact : ExactOracles M₁ M₂ O
  ground₁ : M₁.E=Set.univ
  ground₂ : M₂.E=Set.univ
  positive : 0<n
  rank : ℕ
  samples : ℕ
  phases : ℕ
namespace SamplerModel
variable {n : ℕ} {O : IndependenceOracle n}
def tau (m : SamplerModel n O) := 20*n^4*(n*(m.phases+1)+2)
def cap (m : SamplerModel n O) := restartCap n m.phases
def Bounded (m : SamplerModel n O) (S : ℕ) : Prop :=
  n≤S ∧ m.rank≤S ∧ m.samples≤S ∧ m.phases≤S ∧ m.cap≤S ∧ m.tau≤S
abbrev Hist (m : SamplerModel n O) := List (PhaseSample n m.samples)
noncomputable def histValue (m : SamplerModel n O) (history : m.Hist) : Value HistoryData :=
  historyEncode (history.map (observedSets n m.samples))
noncomputable def weightContext (m : SamplerModel n O) (h : m.Hist) (j : ℕ) : Value WeightContext :=
  ((m.rank,j),m.histValue h)
noncomputable def weightValue (m : SamplerModel n O) (h : m.Hist) (j : ℕ)
    (x : ChainIndex (pairedSlots n)) : Value WeightInput := (m.weightContext h j,stateEncode x.val)
noncomputable def restartContext (m : SamplerModel n O) (h : m.Hist) : Value RestartContext :=
  ((m.rank,m.histValue h),(m.cap,m.tau))
noncomputable def restartValue (m : SamplerModel n O) (h : m.Hist) (j : ℕ)
    (x : PlainIndex (pairedSlots n)) : Value RestartState := ((m.restartContext h,j),stateEncode x.val.val)
noncomputable def phaseValue (m : SamplerModel n O) (h : m.Hist) : Value PhaseInput :=
  (params n m.rank m.samples m.phases,m.histValue h)
end SamplerModel

def sourceWidthPoly (c : ℕ) : SizePolynomial :=
  .mul (.constant c) (.mul (.add .input (.constant 1))
    (.mul (.add .input (.constant 1)) (.add .input (.constant 1))))

def weightScope : OraclePredicate WeightInput := fun n O S z =>
  ∃ (m : SamplerModel n O),m.Bounded S ∧ ∃ h : m.Hist,h.length≤S ∧
    ∃ j,j≤S ∧ ∃ x : ChainIndex (pairedSlots n),z=m.weightValue h j x
end MachineCode

namespace MachineCode

open Expression
open scoped Classical
namespace Effect

abbrev SearchData := DataType.prod WeightInput .bool
def searchScope : OraclePredicate SearchData := fun n O S x => weightScope n O S x.1
def searchInputScope : OraclePredicate (.prod .nat SearchData) := fun n O S x =>
  x.1≤S+1 ∧ ∃ (m : SamplerModel n O),m.Bounded S ∧ ∃ h : m.Hist,h.length≤S ∧
    ∃ j,j≤S ∧ ∃ u : SearchState (ChainIndex (pairedSlots n)) (plainPredicate (pairedSlots n)),
      x.2=searchEncode (m.weightValue h j) u

def traceScope : OraclePredicate (.prod .nat WeightInput) := fun n O S x =>
  x.1≤S+1 ∧ weightScope n O S x.2
end Effect

open Expression

open Expression
open scoped Classical
namespace Effect
def restartScope : OraclePredicate RestartState := fun n O S z =>
  ∃ (m : SamplerModel n O),m.Bounded S ∧ ∃ h : m.Hist,h.length≤S ∧
    ∃ j,j≤S ∧ ∃ x : PlainIndex (pairedSlots n),z=m.restartValue h j x

def traceRepeatScope : OraclePredicate (.prod .nat (Optional RestartState)) := fun n O S z =>
  z.1≤S ∧ ∃ (m : SamplerModel n O),m.Bounded S ∧ ∃ h : m.Hist,h.length≤S ∧
    ∃ j,j≤S ∧ ∃ x : PlainIndex (pairedSlots n),z.2=optionEncode (m.restartValue h j) (some x)
def restartOptWidth : SizePolynomial :=
  .add (sourceWidthPoly 200) (.constant (width (zeroValue RestartState)+3))

def iterateTraceScope : OraclePredicate (.prod .nat RestartState) := fun n O S z =>
  z.1≤S ∧ restartScope n O S z.2
end Effect

open Expression
open scoped Classical
namespace SamplerModel
noncomputable def restartInput {n : ℕ} {O : IndependenceOracle n} (m : SamplerModel n O)
    (h : m.Hist) (k : ℕ) : Value RestartInput := (n,(k,m.restartContext h))
end SamplerModel
namespace Effect
def restartRepeatScope : OraclePredicate (.prod .nat (Optional RestartState)) := fun n O S z =>
  z.1≤S ∧ ∃ (m : SamplerModel n O),m.Bounded S ∧ ∃ h : m.Hist,h.length≤S ∧
    ∃ x : PlainIndex (pairedSlots n),z.2=optionEncode (m.restartValue h 0) (some x)
def restartInputScope : OraclePredicate RestartInput := fun n O S z =>
  ∃ (m : SamplerModel n O),m.Bounded S ∧ ∃ h : m.Hist,h.length≤S ∧
    ∃ k,k≤S ∧ z=m.restartInput h k
def restartAfterPlainScope : OraclePredicate (.prod RestartInput StateData) := fun n O S z =>
  ∃ (m : SamplerModel n O),m.Bounded S ∧ ∃ h : m.Hist,h.length≤S ∧
    ∃ k,k≤S ∧ ∃ x : PlainIndex (pairedSlots n),z=(m.restartInput h k,stateEncode x.val.val)
end Effect

namespace SamplerModel
noncomputable def phaseState {n : ℕ} {O : IndependenceOracle n} (m : SamplerModel n O)
    (h : m.Hist) (x : ChainIndex (pairedSlots n)) : Value (.prod PhaseInput StateData) :=
  (m.phaseValue h,stateEncode x.val)
end SamplerModel
namespace Effect
def phaseScope : OraclePredicate PhaseInput := fun n O S z =>
  ∃ (m : SamplerModel n O),m.Bounded S ∧ ∃ h : m.Hist,h.length≤S ∧ z=m.phaseValue h
def phaseStateScope : OraclePredicate (.prod PhaseInput StateData) := fun n O S z =>
  ∃ (m : SamplerModel n O),m.Bounded S ∧ ∃ h : m.Hist,h.length≤S ∧
    ∃ x : ChainIndex (pairedSlots n),z=m.phaseState h x

abbrev SampleNodeData := DataType.prod PhaseInput StateData
abbrev SampleAccData := DataType.prod (.list SampleNodeData) SampleNodeData
noncomputable def sampleAccValue {n : ℕ} {O : IndependenceOracle n} (m : SamplerModel n O)
    (h : m.Hist) (s : List (ChainIndex (pairedSlots n)) × ChainIndex (pairedSlots n)) : Value SampleAccData :=
  (s.1.map (m.phaseState h),m.phaseState h s.2)
def sampleAccWidth : SizePolynomial :=
  .add (.mul (.constant 2) (.mul .input (.add (.mul (.constant 2) (sourceWidthPoly 210)) (.constant 2))))
    (.add (.constant 1) (sourceWidthPoly 210))
def sampleAccScope : OraclePredicate SampleAccData := fun n O S z =>
  ∃ (m : SamplerModel n O),m.Bounded S ∧ ∃ h : m.Hist,h.length≤S ∧
    ∃ acc : List (ChainIndex (pairedSlots n)),acc.length≤S ∧
    ∃ x : ChainIndex (pairedSlots n),z=sampleAccValue m h (acc,x)
def sampleRepeatScope : OraclePredicate (.prod .nat SampleAccData) := fun n O S z =>
  z.1≤S ∧ ∃ (m : SamplerModel n O),m.Bounded S ∧ ∃ h : m.Hist,h.length≤S ∧
    ∃ x : ChainIndex (pairedSlots n),z.2=sampleAccValue m h ([],x)
def sampleInputScope : OraclePredicate (.prod .nat SampleNodeData) := fun n O S z =>
  z.1≤S ∧ phaseStateScope n O S z.2
end Effect

open Expression

open Expression
open scoped Classical

section
open Expression
open scoped Classical
namespace Expression

def weightedPlainCode : Expression (.prod .nat StateData) NN :=
  applyIf (snd >>> plainCode) (constant (0,1))
    (both (both (both fst (constant 1)) (constant [])) snd >>> annealCode)
def weightedListCode : Expression (.prod .nat SampleData) (.list NN) :=
  both snd fst >>> mapWith (Expression.swap >>> weightedPlainCode)
def weightedMeanCode : Expression (.prod .nat SampleData) NN :=
  letIn weightedListCode (both (snd >>> ratSumCode) (fst >>> snd >>> listLength >>> natRatCode) >>> ratDiv)
def plainMeanCode : Expression (.prod .nat SampleData) NN :=
  both (snd >>> countPlainCode) (snd >>> listLength) >>> normalizeRat
def ratioCode : Expression (.prod .nat SampleData) NN := both weightedMeanCode plainMeanCode >>> ratDiv
end Expression
end

section
open Expression
namespace Effect

def historyTickCode {a c} (p : Effect (.prod c (.list a)) (Optional a)) :
    Effect (.prod c (.list a)) (Optional (.prod c (.list a))) :=
  map (retainOption p) (optionMapCode (both (fst >>> fst)
    (both (fst >>> snd) (both snd (constant []) >>> cons) >>> listAppend)))
def historyTickTree {X : Type*} (K : List X → DrawTree (Option X)) (h : List X) : DrawTree (Option (List X)) :=
  (K h).map (Option.map (fun x => h++[x]))

def historyCode {a c} (p : Effect (.prod c (.list a)) (Optional a)) :
    Effect (.prod .nat (.prod c (.list a))) (Optional (.prod c (.list a))) := iterateCode (historyTickCode p)
end Effect

open Expression
open scoped BigOperators Classical
namespace Expression

def historyAtCode : Expression (.prod HistoryData .nat) SampleData := both ident (constant []) >>> getDCode
def ratioAtCode : Expression (.prod .nat PhaseInput) NN :=
  both (snd >>> fst >>> fst >>> snd) (both (snd >>> snd) fst >>> historyAtCode) >>> ratioCode

def estimateCode : Expression PhaseInput NN :=
  both (both (constant (b:=.nat) 2) (fst >>> fst >>> fst : Expression PhaseInput .nat) >>> Expression.powCode >>> natRatCode)
    (both (fst >>> snd >>> fst >>> snd >>> rangeCode) ident >>> mapWith ratioAtCode >>> ratProductCode) >>> ratMul

def guardCode : Expression (.prod PhaseInput StateData) NN :=
  applyIf (both (fst >>> fst >>> fst >>> snd) snd >>> deficiencyCode >>> natEqZero)
    (constant (0,1)) (fst >>> estimateCode)
end Expression

end

section
open Expression
open Effect
open scoped Classical
namespace Effect

def finalGuardCode : Effect PhaseInput (Optional NN) :=
  map (retainOption witnessCode) (optionMapCode guardCode)
def algorithmHistoryCode : Effect AlgorithmParams (Optional PhaseInput) :=
  precompose (both (snd >>> fst >>> snd) (both ident (constant []))) (historyCode phaseCode)
def algorithmCode : Effect AlgorithmParams (Optional NN) := optionBind algorithmHistoryCode finalGuardCode
end Effect
end

open Expression
open scoped Classical
namespace Effect
noncomputable def phaseOptWidth : SizePolynomial :=
  .add (sourceWidthPoly 100) (.constant (width (zeroValue PhaseInput)+3))

def historyRepeatScope : OraclePredicate (.prod .nat (Optional PhaseInput)) := fun n O S z =>
  z.1≤S ∧ ∃ (m : SamplerModel n O),m.Bounded S ∧ z.2=optionEncode m.phaseValue (some [])
def historyInputScope : OraclePredicate (.prod .nat PhaseInput) := fun n O S z =>
  z.1≤S ∧ ∃ (m : SamplerModel n O),m.Bounded S ∧ z.2=m.phaseValue []
def algorithmScope : OraclePredicate AlgorithmParams := fun n O S z =>
  ∃ (m : SamplerModel n O),m.Bounded S ∧ z=params n m.rank m.samples m.phases
end Effect

open Expression
def estimatorAttr (S : ℕ) (z : Value PhaseInput) : Prop :=
  z.1.1.1≤S ∧ z.1.1.2≤S ∧ z.1.2.1.2≤S

open Expression Effect

open Expression
open scoped Classical

open Expression

namespace Expression
abbrev InsertState := DataType.prod NN (.prod (.list NN) (.list NN))
def insertStep : Expression (.prod NN InsertState) InsertState :=
  both (snd >>> fst) (both (both fst (snd >>> snd >>> fst) >>> Expression.cons)
    (applyIf (both fst (snd >>> fst) >>> ratLess)
      (both (snd >>> fst) (both fst (snd >>> snd >>> fst) >>> Expression.cons) >>> Expression.cons)
      (both fst (snd >>> snd >>> snd) >>> Expression.cons)))
def insertInit : Expression (.prod NN (.list NN)) InsertState :=
  both fst (both (constant (b:=.list NN) [])
    (both fst (constant (b:=.list NN) []) >>> Expression.cons (a:=NN)))
def insertRatCode : Expression (.prod NN (.list NN)) (.list NN) :=
  both (snd >>> listReverse) insertInit >>> fold insertStep >>> snd >>> snd
def sortRatCode : Expression (.list NN) (.list NN) :=
  both listReverse (constant []) >>> fold insertRatCode
def medianCode : Expression (.list NN) NN :=
  both (both sortRatCode (listLength >>> both (constant 2) ident >>> natDiv)) (constant (0,1)) >>> getDCode

end Expression

namespace Expression

def optionalRatCode : Expression (Optional NN) NN := applyIf fst (constant (0,1)) snd
def singleCode : Expression (.prod AlgorithmParams BankData) NN :=
  Effect.algorithmCode >>> fst >>> applyIf fst (constant (0,1)) (snd >>> optionalRatCode)
def amplifiedCode : Expression (.prod AlgorithmParams (.list BankData)) NN :=
  swap >>> mapWith (swap >>> singleCode) >>> medianCode
end Expression

open Expression Effect
def amplificationScope : OraclePredicate (.prod AlgorithmParams (.list BankData)) :=
  fun n O S z => algorithmScope n O S z.1 ∧ width (a:=.list BankData) z.2≤S

open Expression
abbrev FrozenData := DataType.prod NN (.prod NN NN)
def frozenValue (n r : ℕ) (ε δ : ℚ) : Value FrozenData :=
  ((n,r),((ε.num.natAbs,ε.den),(δ.num.natAbs,δ.den)))
namespace Expression

def natPow : ℕ → Expression .nat .nat
  | 0 => constant 1
  | k+1 => both ident (natPow k) >>> mul

def sumE {a} (p q : Expression a .nat) : Expression a .nat := both p q >>> add
def prodE {a} (p q : Expression a .nat) : Expression a .nat := both p q >>> mul

def ceilDivCode : Expression NN .nat :=
  both fst (both (sumE snd fst) (constant 1) >>> natSub) >>> divRem >>> snd

def lengthNatCode : Expression .nat .nat := toBits >>> toList >>> listLength

def annealLengthCode : Expression NN .nat :=
  prodE (prodE (constant 2) fst) (sumE fst (sumE snd (constant 5)))

def sampleCountCode : Expression (.prod .nat NN) .nat :=
  sumE (prodE (prodE (prodE (constant (10^14))
    (sumE (snd >>> fst) (constant 1) >>> natPow 3)) (fst >>> natPow 14))
      (snd >>> snd >>> natPow 2)) (constant 1)

def tauCode : Expression NN .nat :=
  prodE (prodE (constant 20) (fst >>> natPow 4))
    (sumE (prodE fst (sumE snd (constant 1))) (constant 2))
def capCode : Expression NN .nat :=
  prodE (prodE (prodE (constant 2000) (sumE snd (constant 1) >>> natPow 2))
    (fst >>> natPow 2)) tauCode

def chunkValues {α : Type*} (m h : ℕ) (xs : List α) : List (List α) :=
  (List.range m).map (fun i => (xs.drop (i*h)).take h)
def chunkStep {a : DataType} : Expression (.prod .nat (.prod (.list a) .nat)) (.list a) :=
  both (both (snd >>> fst) (prodE fst (snd >>> snd)) >>> dropCode) (snd >>> snd) >>> takeCode
def chunksCode {a : DataType} : Expression (.prod (.list a) NN) (.list (.list a)) :=
  both ((snd >>> fst) >>> rangeCode) (both fst (snd >>> snd)) >>> mapWith chunkStep
end Expression
open Expression Effect
namespace Expression
def frozenN : Expression FrozenData .nat := fst >>> fst
def frozenL : Expression FrozenData .nat :=
  both frozenN (snd >>> fst >>> snd >>> lengthNatCode) >>> annealLengthCode
def frozenE : Expression FrozenData .nat := snd >>> fst >>> ceilDivCode
def frozenSamples : Expression FrozenData .nat :=
  both frozenN (both frozenL frozenE) >>> sampleCountCode
def frozenParams : Expression FrozenData AlgorithmParams :=
  both fst (both (both frozenSamples frozenL)
    (both (both frozenN frozenL >>> capCode) (both frozenN frozenL >>> tauCode)))
def frozenReps : Expression FrozenData .nat :=
  prodE (constant 64) (sumE (snd >>> snd >>> snd >>> lengthNatCode) (constant 1))

abbrev Recipe3 := DataType.prod .nat NN
def drawsCode : Expression Recipe3 .nat :=
  prodE (sumE (sumE (constant 1)
     (prodE (prodE (prodE (constant 3) (snd >>> snd))
        (sumE (both fst (snd >>> snd) >>> capCode) (constant 1)))
          (both fst (snd >>> snd) >>> tauCode)))
      (prodE (constant 3) (snd >>> fst))) (sumE (snd >>> snd) (constant 1))
def wordBoundCode : Expression Recipe3 .nat :=
  sumE (sumE (sumE
    (prodE (constant 2) (sumE (sumE (constant 2) (prodE (snd >>> fst) (snd >>> snd)))
      (prodE (prodE (constant 2) fst) (prodE fst (snd >>> snd)))))
    (fst >>> natPow 2)) fst) (constant 4)
def frozenRecipe3 : Expression FrozenData Recipe3 := both frozenN (both frozenSamples frozenL)
def frozenDraws : Expression FrozenData .nat := frozenRecipe3 >>> drawsCode
def frozenWordBound : Expression FrozenData .nat := frozenRecipe3 >>> wordBoundCode
abbrev BankShape := DataType.prod .nat NN
abbrev PreparedData := DataType.prod AlgorithmParams BankShape
def frozenPrepared : Expression FrozenData PreparedData :=
  both frozenParams (both frozenReps (both frozenDraws frozenWordBound))
def bitCountCode : Expression BankShape .nat :=
  prodE (prodE (prodE fst (snd >>> snd)) (sumE (snd >>> fst) (constant 6))) (snd >>> fst)
def frozenBitCount : Expression FrozenData .nat :=
  frozenPrepared >>> snd >>> bitCountCode

abbrev Shape3 := DataType.prod .nat NN
abbrev Shape4 := DataType.prod .nat Shape3

def rowsCode : Expression (.prod (.list .bool) NN) RandomRows :=
  chunksCode >>> mapEach fromList
def bankCode : Expression (.prod (.list .bool) Shape3) BankData :=
  both (both fst (both (snd >>> fst) (prodE (snd >>> snd >>> fst) (snd >>> snd >>> snd))) >>> chunksCode)
    (snd >>> snd) >>> mapWith rowsCode
def banksCode : Expression (.prod (.list .bool) Shape4) (.list BankData) :=
  both (both fst (both (snd >>> fst) (prodE (snd >>> snd >>> fst)
      (prodE (snd >>> snd >>> snd >>> fst) (snd >>> snd >>> snd >>> snd)))) >>> chunksCode)
    (snd >>> snd) >>> mapWith bankCode
def shape4Code : Expression BankShape Shape4 :=
  both fst (both (snd >>> fst) (both (sumE (snd >>> fst) (constant 6)) (snd >>> snd)))
def reshapeCode : Expression (.prod .word BankShape) (.list BankData) :=
  both (fst >>> toList) (snd >>> shape4Code) >>> banksCode

def preambleCode : Expression FrozenData (.prod .word PreparedData) :=
  both (frozenBitCount >>> unary) frozenPrepared
abbrev RawData := DataType.prod .word PreparedData
abbrev AmplifyInput := DataType.prod AlgorithmParams (.list BankData)
def reshapePrepared : Expression RawData AmplifyInput :=
  both (snd >>> fst) (both fst (snd >>> snd) >>> reshapeCode)
def finishCode : Expression AmplifyInput NN :=
  applyIf (fst >>> fst >>> fst >>> natEqZero) amplifiedCode (constant (1,1))
def postambleCode : Expression RawData NN := reshapePrepared >>> finishCode
end Expression
def rawScope : OraclePredicate RawData := fun n O S z =>
  width z≤S ∧ z.2.2.1≤S ∧ z.2.2.2.1+6≤S ∧
    z.2.1.1.1=n ∧ (0<n → algorithmScope n O S z.2.1)
def finishScope : OraclePredicate AmplifyInput := fun n O S z =>
  width z≤S ∧ z.1.1.1=n ∧ (0<n → algorithmScope n O S z.1)

def coinPush {k : ℕ} (a : Fin (k+8)) : Block k := fork .coin (push a false) (push a true)

def sampledWord : ℕ → (ℕ → Bool) → Word
  | 0,_ => []
  | m+1,bits => sampledWord m (fun i => bits (3+i)) ++ [bits 1]
lemma sampledWord_length (m : ℕ) (bits : ℕ → Bool) : (sampledWord m bits).length=m := by
  induction m generalizing bits with
  | zero => rfl
  | succ m ih => simp [sampledWord,ih]
def sixRegs (a b c d e f : Word) : Registers 1 := fun i =>
  match i.val with
  | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | _ => []
def inputPack : Block 1 :=
  seq (pack 4 5) (seq (pack 2 3) (seq (pack 3 5) (seq (pack 0 1)
    (seq (pack 1 5) (move 5 2 0)))))
def inputTime (a b c d e f : Word) : ℕ :=
  (3*e.length+2)+((3*c.length+2)+((3*(pair c d).length+2)+((3*a.length+2)+
    ((3*(pair a b).length+2)+(4*(pair (pair a b) (pair (pair c d) (pair e f))).length+2)))))

open Expression
def preparedValue (n r : ℕ) (ε δ : ℚ) : Value PreparedData :=
  let L := annealLength n (accuracyExponent ε)
  let N := sampleCount n L ε
  (params n r N L,(repetitionCount δ,(algorithmDrawBound n N L,drawWordBound n N L)))
def rawValue (n r : ℕ) (ε δ : ℚ) (w : BitWord (fairBitCount n ε δ)) : Value RawData :=
  (List.ofFn w,preparedValue n r ε δ)

open Expression
namespace SizePolynomial
def pow (p : SizePolynomial) : ℕ → SizePolynomial
  | 0 => .constant 1
  | k+1 => .mul (pow p k) p
end SizePolynomial

def masterParameter (n r : ℕ) (ε δ : ℚ) : ℕ :=
  1+n+inputLength n r ε δ+⌈ε⁻¹⌉₊+Nat.clog 2 ⌈δ⁻¹⌉₊
def atomPoly : SizePolynomial := .mul (.constant (10^22)) (.pow (.add .input (.constant 1)) 24)
def tauPoly : SizePolynomial :=
  .mul (.mul (.constant 20) (atomPoly.pow 4))
    (.add (.mul atomPoly (.add atomPoly (.constant 1))) (.constant 2))
def capPoly : SizePolynomial :=
  .mul (.mul (.mul (.constant 2000) ((SizePolynomial.add atomPoly (.constant 1)).pow 2)) (atomPoly.pow 2)) tauPoly
def fairPoly : SizePolynomial := .mul (.constant (10^66)) ((SizePolynomial.add .input (.constant 1)).pow 73)
def sourceEnvelope : SizePolynomial :=
  .add (.add (.add (.add atomPoly tauPoly) capPoly) fairPoly) (.constant 6)
def scopeEnvelope : SizePolynomial := .mul (.constant 100) (.add sourceEnvelope (.constant 1))

open Expression Effect

open Expression

def compiledMajorant {a b : DataType} (p : Expression a b) (f : SizePolynomial) : SizePolynomial :=
  .mul (.constant (chargeCoefficient p)) ((SizePolynomial.add
    (.add f .input) (.constant 1)).pow (chargeDegree p))

def outRegs (a b : Word) : Registers 1 := fun i => if i=6 then a else if i=7 then b else []
def outputPack : Block 1 := seq (unpack 0 6) (move 0 1 7)
def outputTime (a b : Word) : ℕ := (3*a.length+1)+(4*b.length+2)

def pipeline (pre post : Block 1) : Block 1 :=
  seq inputPack (seq pre (seq (unpack 0 1) (seq (repeatBlock (coinPush 2) 1)
    (seq (pack 2 0) (seq post outputPack)))))
def pipelineTime (i pre f post a b : ℕ) : ℕ :=
  i+(pre+((3*f+1)+((3*f+1)+((3*f+2)+(post+((3*a+1)+(4*b+2)))))))

def physicalWord (start m : ℕ) (bits : ℕ → Bool) : BitWord m :=
  fun i => bits (start+3*(m-1-i.val)+1)
def physicalPosition (start m B : ℕ) (h : start+3*m+1≤B) (i : Fin m) : Fin B :=
  ⟨start+3*(m-1-i.val)+1,by have hi := i.isLt; omega⟩

def terminalState (p : Block 1) (x y : Word) (q w : ℕ) : MachineConfig 1 p.size :=
  ⟨outRegs x y,lastLabel p.size,some ((binaryValue x:ℚ)/(binaryValue y:ℚ)),q,w+x.length+y.length+1⟩

def pipelineBudget (i F cp cq W : ℕ) : ℕ := i+cp+9*F+cq+5*W+10

open Expression

def totalResourcePoly (fp fq : SizePolynomial) : SizePolynomial :=
  .mul (.constant 200) (.add (.add (.add sourceEnvelope (compiledMajorant preambleCode fp))
    (compiledMajorant postambleCode fq)) (.add fq (.constant 1)))

def fprasBlock : Block 1 := pipeline (compile preambleCode) (compile postambleCode)

open Expression Effect
open scoped Classical
noncomputable def treeBankOutput (t : DrawTree (Option ℚ)) (bank : Bank) : ℚ :=
  (bankEval t bank).1.join.getD 0
noncomputable def treeBanksOutput (t : DrawTree (Option ℚ)) (banks : List Bank) : ℚ :=
  rationalMedian (banks.map (treeBankOutput t))

open Expression

def bankReshapeEquiv {a : ℕ} (R M H : ℕ) (h : a=R*(M*((M+6)*H))) :
    BitWord a ≃ (Fin R → Fin M → Fin (M+6) → BitWord H) :=
  (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)).trans (fourBitEquiv R M (M+6) H)
lemma reshape_count (n : ℕ) (ε δ : ℚ) :
    let L := annealLength n (accuracyExponent ε)
    let N := sampleCount n L ε
    let M := algorithmDrawBound n N L
    let H := drawWordBound n N L
    fairBitCount n ε δ=repetitionCount δ*(M*((M+6)*H)) := by
  change repetitionCount δ * drawWordBound n (sampleCount n (annealLength n (accuracyExponent ε)) ε)
    (annealLength n (accuracyExponent ε)) * _ * _ = _
  ac_rfl

def reshapeWordEquiv (n : ℕ) (ε δ : ℚ) : BitWord (fairBitCount n ε δ) ≃ FPRASBank n ε δ :=
  bankReshapeEquiv (repetitionCount δ)
    (algorithmDrawBound n (sampleCount n (annealLength n (accuracyExponent ε)) ε) (annealLength n (accuracyExponent ε)))
    (drawWordBound n (sampleCount n (annealLength n (accuracyExponent ε)) ε) (annealLength n (accuracyExponent ε)))
    (reshape_count n ε δ)

open Expression
open scoped Classical

def OutputCertificate {n : ℕ} (r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (O : IndependenceOracle n) (ε δ : ℚ)
    (v : BitWord (fairBitCount n ε δ) → ℚ) : Prop :=
  (∀ w,run O postambleCode (rawValue n r ε δ w)=some (rationalPair (v w))) ∧
  (∀ w,0≤v w ∧ (commonBaseCount M₁ M₂=0 → v w=0)) ∧
  (∀ φ : ℚ → ℝ,uniformAverage (fun w => φ (v w))=
    uniformAverage (fun banks : FPRASBank n ε δ => φ (canonicalBoundedOutput n r O ε δ banks)))

open Expression

open scoped Classical

end MachineCode
end CommonBasesFPRAS

open CommonBasesFPRAS CommonBasesFPRAS.MachineCode

end OAI
end


