-- Prove2me | Definitions.Def_OAIQ5T1001
-- name    : OAIQ5T1001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T07:54:28.005471+00:00
-- url     : https://prove2.me/theorems/27a5f678-5829-4738-926d-9316981f10ca
-- title:
--   Definitions bundle OAIQ5T1001 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionConsistency.main_consistency`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 31 definitions, 1 inductive type or structure, 6 instances and 18 theorems. The definitions and types are `OAI.PartitionConsistency.CohenForcing.Condition.flip`, `OAI.PartitionConsistency.CosetPredicate.Invariant`, `OAI.PartitionConsistency.CosetPredicate.shift`, `OAI.PartitionConsistency.CountableHull.Arity`, `OAI.PartitionConsistency.CountableHull.carrier`, `OAI.PartitionConsistency.CountableHull.evaluate`, `OAI.PartitionConsistency.CountableHull.stage`, `OAI.PartitionConsistency.DiagramOrder.OldGateStep`, `OAI.PartitionConsistency.DiagramOrder.Replaces`, `OAI.PartitionConsistency.ForcingQuotient.Compatible`, `OAI.PartitionConsistency.ForcingQuotient.Dense`, `OAI.PartitionConsistency.OrderAssignment.Table`, `OAI.PartitionConsistency.OrderAssignment.chooseTable`, `OAI.PartitionConsistency.OrderAssignment.indices`, `OAI.PartitionConsistency.OrderAssignment.smallRel`, `OAI.PartitionConsistency.ProductForcing.RootProbes`, `OAI.PartitionConsistency.SetForcingNames.SymmetricSystem.ChainBound`, `OAI.PartitionConsistency.TailSelector.Eventual`, `OAI.PartitionConsistency.TailSelector.TailData`, `OAI.PartitionConsistency.TailSelector.TailData.Cosets`, `OAI.PartitionConsistency.TailSelector.TailData.Nonidentity`, `OAI.PartitionConsistency.TailSelector.TailData.Pattern`, `OAI.PartitionConsistency.TailSelector.TailData.bestCoset`, `OAI.PartitionConsistency.TailSelector.TailData.detector`, `OAI.PartitionConsistency.TailSelector.TailData.detectorSites`, `OAI.PartitionConsistency.TailSelector.TailData.leastBound`, `OAI.PartitionConsistency.TailSelector.TailData.moveRows`, `OAI.PartitionConsistency.TailSelector.TailData.pattern`, `OAI.PartitionConsistency.TailSelector.TailData.rawPattern`, `OAI.PartitionConsistency.TailSelector.TailData.selector`, `OAI.PartitionConsistency.TailSelector.eventualMk`, `OAI.PartitionConsistency.TailSelector.eventualSetoid`.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory/PartitionConsistency, in whole or in part: [`PartitionConsistency_Algebra_GateTowers`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/SetTheory/PartitionConsistency/PartitionConsistency/Algebra/GateTowers.lean), [`PartitionConsistency_Algebra_Placements`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/SetTheory/PartitionConsistency/PartitionConsistency/Algebra/Placements.lean), [`PartitionConsistency_Construction_ConservativeHulls`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/SetTheory/PartitionConsistency/PartitionConsistency/Construction/ConservativeHulls.lean), [`PartitionConsistency_Construction_DiagramPlacements`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/SetTheory/PartitionConsistency/PartitionConsistency/Construction/DiagramPlacements.lean), [`PartitionConsistency_Forcing_ForcingQuotient`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/SetTheory/PartitionConsistency/PartitionConsistency/Forcing/ForcingQuotient.lean), [`PartitionConsistency_Forcing_ProductForcing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/SetTheory/PartitionConsistency/PartitionConsistency/Forcing/ProductForcing.lean), [`PartitionConsistency_Models_AssignedGraphs`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/SetTheory/PartitionConsistency/PartitionConsistency/Models/AssignedGraphs.lean), [`PartitionConsistency_Models_GermSelectors`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/SetTheory/PartitionConsistency/PartitionConsistency/Models/GermSelectors.lean), [`PartitionConsistency_Models_OrdinalCodes`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/SetTheory/PartitionConsistency/PartitionConsistency/Models/OrdinalCodes.lean), [`PartitionConsistency_Models_OrdinalPresentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/SetTheory/PartitionConsistency/PartitionConsistency/Models/OrdinalPresentation.lean), [`PartitionConsistency_Models_StableSelectors`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/SetTheory/PartitionConsistency/PartitionConsistency/Models/StableSelectors.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ5T1002`.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); definitions carved from lean/OAI/SetTheory/PartitionConsistency at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ5_T1.Compat
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
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_Placements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
namespace SmallPlacements
open Cardinal
universe u
variable {α β : Type u}

/-- A small ground partial placement extends to a permutation. -/
theorem extend_permutation {s : Set α} (f : s ↪ α) (hs : #s < #α) :
    ∃ π : Equiv.Perm α, ∀ x : s, π x = f x :=
  Cardinal.extend_function_of_lt f hs ⟨Equiv.refl α⟩

end SmallPlacements
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ForcingQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
/-! External generic filters and the name-quotient truth lemma.
These results do not supply the internal symmetric system or its ZF axioms.
They work on a set of name codes with specified atomic forcing relations. -/
namespace ForcingQuotient

/-- Stronger conditions are smaller. -/
def Dense {P : Type*} [Preorder P] (D : Set P) : Prop :=
  ∀ p, ∃ q, q ≤ p ∧ q ∈ D

variable {P : Type*} [Preorder P]

/-- Conditions have a common strengthening. -/
def Compatible (p q : P) : Prop := ∃ r, r ≤ p ∧ r ≤ q

end ForcingQuotient

end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_GateTowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Finite descent through a continuous tower of old gates -/

namespace PartitionConsistency.DiagramOrder

universe u v
variable {T : Type u} [Monoid T]

/-- The least-old-multiple alternative at a successor stage, including the
old-input implication used for descent. The new word must belong to the
successor stage; arbitrary elements of the final monoid are not called new
at this stage. -/
def OldGateStep (B C : Submonoid T) : Prop :=
  ∀ w ∈ C, w ∉ B → (∃ y ∈ B, w ∣ y) →
    ∃ g ∈ B, w ∣ g ∧ (∀ y ∈ B, w ∣ y → g ∣ y) ∧
      ∀ d ∈ B, g ∣ w * d → w * d ∈ B

/-- A single admissible replacement, with both endpoints in the stipulated
set of alignments. Its right factor is the same as that of the path indices. -/
def Replaces (n : ℕ → T) (A : Set (ℕ × T)) (p q : ℕ × T) : Prop :=
  p ∈ A ∧ q ∈ A ∧ p.1 ≤ q.1 ∧ ∃ d, n p.1 * d = n q.1 ∧ p.2 * d = q.2

end PartitionConsistency.DiagramOrder

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_ConservativeHulls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## MonoidColimit -/

/-! The directed unions used by the monoid construction retain their
universal property against arbitrary monoid homomorphisms. The stronger
category of conservative height/cost embeddings is not a restriction on
the presentation universal property. -/


/-! ## DirectedPushout -/


/-! ## ConservativeHull -/

/-! Countable conservative submonoids.  This closes an arbitrary countable
set under specified countable dependencies, right factors and joins.  It is
only the hull part of the countable-base rearrangement; it does not identify
the complement presentation with an iterated gate tower. -/
namespace PartitionConsistency.CountableHull
universe u
noncomputable section
open scoped Classical
variable {A : Type u} (s : Set A) (op : A → A → Set A)

def stage : ℕ → Set A
  | 0 => s
  | n+1 => stage n ∪ ⋃ x ∈ stage n, ⋃ y ∈ stage n, op x y

def carrier : Set A := ⋃ n, stage s op n

theorem stage_mono : Monotone (stage s op) :=
  monotone_nat_of_le_succ (fun _ => Set.subset_union_left)

theorem subset_carrier : s ⊆ carrier s op := fun _ h => Set.mem_iUnion.mpr ⟨0,h⟩

theorem closed {x y : A} (hx : x ∈ carrier s op) (hy : y ∈ carrier s op) :
    op x y ⊆ carrier s op := by
  obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hx
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hy
  intro z hz
  apply Set.mem_iUnion.mpr
  refine ⟨max m n+1,Or.inr ?_⟩
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨stage_mono s op (le_max_left _ _) hm,
    Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨stage_mono s op (le_max_right _ _) hn,hz⟩⟩⟩⟩

end
end PartitionConsistency.CountableHull


/-! ## ConservativeCategory -/

/-! Conservative monoids without height/cost bookkeeping. The original
saturated tower forgets to this category. It is used for rearrangements:
heights are needed for scheduling ideals, but not for old-gate descent. -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ProductForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
namespace SmallPlacements
universe u
variable {I : Type u}

theorem union_bound {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    {s t : Set I} (hs : Cardinal.mk s ≤ μ) (ht : Cardinal.mk t ≤ μ) :
    Cardinal.mk (s ∪ t : Set I) ≤ μ :=
  (Cardinal.mk_union_le s t).trans ((add_le_add hs ht).trans_eq (Cardinal.add_eq_self hμ))

/-- An independent placement has exactly the stated common root. -/
theorem intersection_eq_root {s t r : Set I} (hrs : r ⊆ s) (hrt : r ⊆ t)
    (π : Equiv.Perm I) (hfix : ∀ x ∈ r, π x = x)
    (hdisj : Disjoint (π '' (s \ r)) (t ∪ r)) : t ∩ π '' s = r := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxt, y, hys, rfl⟩
    by_cases hyr : y ∈ r
    · simpa [hfix y hyr] using hyr
    · exact False.elim (Set.disjoint_left.1 hdisj ⟨y, ⟨hys, hyr⟩, rfl⟩ (Or.inl hxt))
  · intro x hxr
    exact ⟨hrt hxr, x, hrs hxr, hfix x hxr⟩

end SmallPlacements

end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_DiagramPlacements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## ProbePlacement -/

namespace PartitionConsistency.ProductForcing
universe u
noncomputable section
variable {M I κ : Type u}
  [LeftCancelMonoid M]

/-- The part of probe saturation used for simultaneous ordinal choice.
This is a purely algebraic statement about the actual monoid, and will be
instantiated by its executed saturation, not assumed at the endpoint. -/
def RootProbes (e : M) (K : Type u) : Prop :=
  ∀ b : M, b ≠ 1 → ∃ m : K → M,
    (∀ i, m i * b = e) ∧ ∀ i j, i ≠ j → ∀ z : M,
      m i ∣ z ∧ m j ∣ z ↔ e ∣ z

end
end PartitionConsistency.ProductForcing


/-! ## TriplePlacement -/

namespace PartitionConsistency.SmallPlacements
universe u
open Cardinal
noncomputable section
variable {I : Type u} [Infinite I] {μ : Cardinal.{u}}

omit [Infinite I] in
/-- Two pointwise placements on independent sets can be pasted whenever
both source and target intersections are the fixed root. -/
theorem paste_placements {s₀ s₁ p : Set I} (hinter : s₀ ∩ s₁ = p)
    (α β : Equiv.Perm I) (hα : ∀ j ∈ p, α j = j) (hβ : ∀ j ∈ p, β j = j)
    (himage : (α '' s₀) ∩ (β '' s₁) = p) :
    ∃ f : (s₀ ∪ s₁ : Set I) ↪ I,
      (∀ j (hj : j ∈ s₀), f ⟨j,Or.inl hj⟩ = α j) ∧
      (∀ j (hj : j ∈ s₁), f ⟨j,Or.inr hj⟩ = β j) := by
  classical
  let f : (s₀ ∪ s₁ : Set I) → I := fun x => if x.val ∈ s₀ then α x else β x
  have hcross {x y : I} (hx : x ∈ s₀) (hy : y ∈ s₁) (he : α x = β y) : x = y := by
    have hxp : α x ∈ p := himage ▸ ⟨⟨x,hx,rfl⟩,⟨y,hy,he.symm⟩⟩
    have hxx : α x = x := (α.injective (hα _ hxp))
    have hyp : β y ∈ p := he ▸ hxp
    have hyy : β y = y := (β.injective (hβ _ hyp))
    exact hxx.symm.trans (he.trans hyy)
  have hfi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    by_cases hx : x.val ∈ s₀ <;> by_cases hy : y.val ∈ s₀
    · exact α.injective (by simpa only [f,ite_eq_left hx,ite_eq_left hy] using he)
    · exact hcross hx (y.property.resolve_left hy)
        (by simpa only [f,ite_eq_left hx,ite_eq_right hy] using he)
    · exact (hcross hy (x.property.resolve_left hx)
        (by simpa only [f,ite_eq_right hx,ite_eq_left hy] using he.symm)).symm
    · exact β.injective (by simpa only [f,ite_eq_right hx,ite_eq_right hy] using he)
  refine ⟨⟨f,hfi⟩,?_,?_⟩
  · intro j hj
    simp [f,hj]
  · intro j hj
    dsimp [f]
    split_ifs with hj₀
    · have hp : j ∈ p := hinter ▸ ⟨hj₀,hj⟩
      rw [hα j hp,hβ j hp]
    · rfl

omit [Infinite I] in
/-- Compute an overlap when every coordinate not already prescribed was
placed freshly. -/
theorem image_inter_of_fresh {s₀ s₁ v K : Set I} (h₀ : s₀ ⊆ v) (h₁ : s₁ ⊆ v)
    (π : Equiv.Perm I) (hfresh : Disjoint (π '' (v \ (s₀ ∪ s₁))) K) :
    (π '' v) ∩ K = ((π '' s₀) ∪ (π '' s₁)) ∩ K := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨y,hy,rfl⟩,hx⟩
    by_cases hys : y ∈ s₀ ∪ s₁
    · refine ⟨?_,hx⟩
      rw [← Set.image_union]
      exact ⟨y,hys,rfl⟩
    · exact False.elim (Set.disjoint_left.mp hfresh ⟨y,⟨hy,hys⟩,rfl⟩ hx)
  · exact Set.inter_subset_inter_left K
      (Set.union_subset (Set.image_mono h₀) (Set.image_mono h₁))

omit [Infinite I] in
/-- If an overlap with a larger forbidden set is exact, then so is its
overlap with any intermediate set containing the indicated root. -/
theorem inter_eq_of_between {A K t r : Set I} (h : A ∩ K = r)
    (hrt : r ⊆ t) (htK : t ⊆ K) : A ∩ t = r := by
  apply Set.Subset.antisymm
  · intro x hx
    exact h ▸ ⟨hx.1,htK hx.2⟩
  · intro x hx
    exact ⟨(show x ∈ A ∩ K from h.symm ▸ hx).1,hrt hx⟩

end
end PartitionConsistency.SmallPlacements

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrdinalCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## OrdinalSelection -/

/-! A wellordered subset selected by forcing conditions has an actual
ordinal name for its order type and names for the ranks of its elements.
This construction uses ordinary set names, not evaluated ambient generics.
The pointwise invariance of each selection predicate gives literal fixation
of every rank name. -/


/-! ## SelectedRank -/


/-! ## CohenSelection -/

/-! The ordinal coding of a condition-defined wellorder can be carried out
inside the product symmetric system itself. Its rank names have the given
tail support. Reflection to a supporting diagram permits all ordinal
decisions to be made by strengthening just the Cohen coordinate. -/


/-! ## CodeRoot -/

/-! Connecting the persistent ground codes to literal root-supported names.
The comparison of two codes is equivalent to forced equality of any of their
root representatives. No generic evaluator is presumed in this step. -/


/-! ## OrderAssignment -/

/-! Enumeration using one fixed, bounded table of bijections with ordinals.
This is the order-theoretic part of the preliminary component assignment.
The table is chosen once and never depends on the wellordered set being
enumerated. -/
namespace PartitionConsistency.OrderAssignment
universe u v w
noncomputable section

/-- A set-indexed table, bounded by the order type of the ground code set. -/
def Table (L : Type u) (Λ : Ordinal.{u}) :=
  ∀ θ : Set.Iic Λ, θ.val.card = Cardinal.mk L → L ≃ θ.val.ToType

def chooseTable (L : Type u) (Λ : Ordinal.{u}) : Table L Λ :=
  fun θ h => Classical.choice (Cardinal.eq.mp (by rw [Cardinal.mk_toType,h]))

variable {L A B : Type u} {Λ : Ordinal.{u}}

/-- Transfer the fixed table's indices to ordinal initial segments. -/
def indices (e : Table L Λ) (θ : Ordinal.{u}) (hb : θ ≤ Λ)
    (hc : θ.card = Cardinal.mk L) : L ≃ Set.Iio θ :=
  (e ⟨θ,hb⟩ hc).trans Ordinal.ToType.mk.toEquiv.symm

variable {X : Type v} {Y : Type w} [Small.{u} X] [Small.{u} Y]

/-- Shrinking only changes the carrier; the selected relation is retained. -/
def smallRel (r : X → X → Prop) : Shrink.{u} X → Shrink.{u} X → Prop :=
  InvImage r (equivShrink X).symm

instance smallRel_isWellOrder (r : X → X → Prop) [IsWellOrder X r] :
    IsWellOrder (Shrink.{u} X) (smallRel r) where
  wf := InvImage.wf (equivShrink X).symm IsWellFounded.wf
  trichotomous := @Std.Trichotomous.trichotomous _
    (InvImage r (equivShrink X).symm)
    (InvImage.trichotomous (r := r) (equivShrink X).symm.injective)

end
end PartitionConsistency.OrderAssignment

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrdinalPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Completion -/


/-! ## Presentation -/

namespace PartitionConsistency
universe u
noncomputable section

/-- Every small type can be enumerated by the elements of an actual ground
ordinal. This is an external use of Choice, not of Choice in the symmetric
model being constructed. -/
theorem exists_ordinal_equiv (α : Type (u+1)) [Small.{u} α] :
    ∃ o : Ordinal.{u}, Nonempty (o.toZFSet ≃ α) := by
  let o := (Cardinal.mk (Shrink.{u} α)).ord
  refine ⟨o,Cardinal.eq.mp ?_⟩
  rw [ZFSet.cardinalMk_coe_sort,Ordinal.card_toZFSet]
  change Cardinal.lift.{u+1} (Cardinal.mk (Shrink.{u} α)).ord.card = Cardinal.mk α
  rw [Cardinal.card_ord]
  exact Cardinal.lift_mk_shrink''.{u+1,u} α

end
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_GermSelectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## PreAssignment -/

/-! The preliminary component assignment, as a persistent relation on actual
forcing conditions and actual HS names. The ordinal table is fixed once,
and the names for ranks/order types are computed from the persistent least
codes rather than from arbitrary principal-filter wellorders. -/


/-! ## Germ -/


/-! ## Selector -/

/-! A combinatorial coset-selector argument. The existence of a countable-base
tower and symmetric names for its assignments are established separately. -/

namespace PartitionConsistency.TailSelector
universe u v w
noncomputable section
open scoped Classical

/-- Equality after discarding a finite initial segment of a sequence. -/
def eventualSetoid (A : Type*) : Setoid (ℕ → A) where
  r f g := ∃ N, ∀ n, N ≤ n → f n = g n
  iseqv := ⟨fun _ => ⟨0,fun _ _ => rfl⟩,
    fun ⟨N,hN⟩ => ⟨N,fun n hn => (hN n hn).symm⟩,
    fun ⟨N,hN⟩ ⟨M,hM⟩ =>
      ⟨max N M,fun n hn => (hN n ((le_max_left _ _).trans hn)).trans
        (hM n ((le_max_right _ _).trans hn))⟩⟩

abbrev Eventual (A : Type*) := Quotient (eventualSetoid A)

def eventualMk {A : Type*} (f : ℕ → A) : Eventual A := Quotient.mk _ f

/-- The tails and the actual normal subgroup of eventual pointwise fixers.
For components, these data are supplied by `Chain.tailFixer_normal`.
No bijections or selector are included among the data. -/
structure TailData (G : Type u) (I : Type v) [Group G] [MulAction G I] where
  tail : ℕ → Set I
  antitone : Antitone tail
  K : Subgroup G
  normal : K.Normal
  mem_iff : ∀ k, k ∈ K ↔ ∃ N, ∀ i ∈ tail N, k • i = i

namespace TailData
variable {G : Type u} {I : Type v} [Group G] [MulAction G I] (D : TailData G I)
instance instNormalK : D.K.Normal := D.normal

abbrev Cosets := G ⧸ D.K
abbrev Nonidentity := {δ : D.Cosets // δ ≠ 1}

/-- The fixed representative of a nonidentity coset cannot fix any entire
chain tail. -/
theorem detector_exists (δ : D.Nonidentity) (n : ℕ) :
    ∃ i ∈ D.tail n, δ.val.out • i ≠ i := by
  by_contra! h
  have hk : δ.val.out ∈ D.K := (D.mem_iff _).mpr ⟨n,h⟩
  have he := (QuotientGroup.eq_one_iff δ.val.out).mpr hk
  exact δ.property (by simpa only [QuotientGroup.out_eq'] using he)

def detector (δ : D.Nonidentity) (n : ℕ) : I := (D.detector_exists δ n).choose

variable {κ : Type w} [LinearOrder κ]

/-- A pattern is a tuple of sequences of bounded binary rows, modulo eventual
equality. The order later used on this type is fixed, not recomputed from rows. -/
abbrev Pattern (α : κ) := D.Nonidentity → Eventual (Set.Iio α → Bool)

def rawPattern (R : I → κ → Bool) (α : κ) (g : G) : D.Pattern α :=
  fun δ => eventualMk (fun n b => R (g • D.detector δ n) b.val)

/-- Evaluating at the standard representative is harmless: the preceding
lemma proves independence of the representative. -/
def pattern (R : I → κ → Bool) (α : κ) (c : D.Cosets) : D.Pattern α :=
  D.rawPattern R α c.out

/-- This is transport of the row data, not an automorphism of one fixed
universe of evaluated symmetric names. -/
def moveRows (σ : G) (R : I → κ → Bool) : I → κ → Bool :=
  fun i => R (σ⁻¹ • i)

@[simp] theorem rawPattern_moveRows (σ g : G) (R : I → κ → Bool) (α : κ) :
    D.rawPattern (moveRows σ R) α (σ*g) = D.rawPattern R α g := by
  funext δ
  apply congrArg eventualMk
  funext n b
  change R (σ⁻¹ • ((σ*g) • D.detector δ n)) b.val = R (g • D.detector δ n) b.val
  rw [mul_smul,inv_smul_smul]

variable [WellFoundedLT κ]

/-- The first distinguishing bound in the fixed ordinal ordering. The proof
of existence is an input only to this definition, not to its application to
countable germs in `distinguished_bound`. -/
def leastBound (R : I → κ → Bool) (h : ∃ α, Function.Injective (D.pattern R α)) : κ :=
  wellFounded_lt.min {α | Function.Injective (D.pattern R α)} h

/-- Minimization is on pattern objects with their fixed wellordering, not on
an arbitrary ordering of the cosets. -/
def bestCoset (R : I → κ → Bool) (α : κ) : D.Cosets :=
  (InvImage.wf (D.pattern R α) WellOrderingRel.isWellOrder.wf).min
    Set.univ Set.univ_nonempty

/-- The coset selected at the least distinguishing bound. -/
def selector (R : I → κ → Bool) (h : ∃ α, Function.Injective (D.pattern R α)) : D.Cosets :=
  D.bestCoset R (D.leastBound R h)

end TailData
end
end PartitionConsistency.TailSelector

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_StableSelectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## ConditionSelector -/

/-! The countable-germ selector as a genuine condition-by-condition recipe.
There is no total family of generic rows in the ambient universe in this
construction.  A countable condition suffices to decide each selection, and
the decisions are both persistent and covariant. -/

namespace PartitionConsistency.TailSelector.TailData
universe u
noncomputable section
open scoped Classical
variable {G I κ : Type u} [Group G] [MulAction G I] (D : TailData G I)
variable [LinearOrder κ]

/-- The countable coordinate family used by the fixed representatives. -/
def detectorSites : Set I :=
  Set.range (fun z : D.Cosets × D.Nonidentity × ℕ => z.1.out • D.detector z.2.1 z.2.2)

end
end PartitionConsistency.TailSelector.TailData


/-! ## CosetPredicate -/

/-! Coset transport for predicates on the total space of computations.
The inverse moves every argument, in particular the actual Cohen condition. -/

namespace PartitionConsistency.CosetPredicate
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
noncomputable section

def shift (g : G) (R : X → Prop) : X → Prop := fun x => R (g⁻¹ • x)

@[simp] theorem shift_one (R : X → Prop) : shift (1 : G) R = R := by
  funext x
  simp only [shift, inv_one, one_smul]

def Invariant (K : Subgroup G) (R : X → Prop) : Prop :=
  ∀ k ∈ K, ∀ x, R (k • x) ↔ R x

end
end PartitionConsistency.CosetPredicate


/-! ## Corrected -/

/-! A component assignment on actual conditions: select a residual coset,
compute at the inverse-moved condition, then transport every argument back.
The quotient operation uses proved tail invariance, not an arbitrary choice
of a bijection. -/


/-! ## StableTransport -/

/-! Coordinate transport for the permanently decided availability ideal.
This is used both for coset correction and for moving between component
orbits. -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_AssignedGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## AssignedGraph -/


/-! ## GraphDensity -/


/-! ## CountableHull -/

/-! Small hulls for countably-ary operations, used for the chain condition of
countable Cohen forcing. The construction is a genuine well-founded term
algebra; no elementary-submodel or large-cardinal assumption is needed. -/
namespace PartitionConsistency.CountableHull
universe u
noncomputable section
open scoped Classical
variable {A X : Type u}

def Arity : Option A → Type u
  | none => PEmpty
  | some _ => ULift.{u} ℕ

def evaluate (base : X) (op : A → (ℕ → X) → X) : WType (@Arity A) → X :=
  WType.elim _ (fun ⟨a,args⟩ => match a with
    | none => base
    | some a => op a (fun n => args ⟨n⟩))

end
end PartitionConsistency.CountableHull


/-! ## CohenChain -/

/-! Chain condition for the actual countable Cohen conditions. The small
hull is a well-founded term algebra, so this proof adds no hypothesis about
an elementary submodel or a delta-system. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u
noncomputable section
open scoped Classical
variable {I κ : Type u}

def flip : Option ((I × κ) × Bool) → Option ((I × κ) × Bool)
  | none => none
  | some (a,b) => some (a,!b)

end
end PartitionConsistency.CohenForcing.Condition


/-! ## ChainPreservation -/

/-! Cardinal preservation from the actual chain condition. The statements
below concern the internal set-graph surjection sentence and arbitrary name
ranks. No existence of an ambient fully generic filter is used. -/
namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v
noncomputable section
open ForcingQuotient
variable {P : Type u} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]

/-- A chain bound on the concrete forcing order. Compatibility here means
existence of a common stronger condition, not agreement of two names. -/
def ChainBound (ν : Cardinal.{u}) : Prop :=
  ∀ A : Set P, (∀ p ∈ A, ∀ q ∈ A, Compatible p q → p = q) → Cardinal.mk A ≤ ν

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end


