-- Prove2me | Definitions.Def_OAIQ5T1002
-- name    : OAIQ5T1002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T08:01:52.051553+00:00
-- url     : https://prove2.me/theorems/c1fdd450-6f25-469b-aedc-694ce7494784
-- title:
--   Definitions bundle OAIQ5T1002 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionConsistency.main_consistency`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 327 declarations of OpenAI's Lean: 154 definitions, 2 inductive types or structures, 14 instances and 157 theorems. The definitions and types are `OAI.PartitionConsistency.CohenForcing.Condition.code`, `OAI.PartitionConsistency.CohenForcing.Condition.compatibleChoice`, `OAI.PartitionConsistency.CohenForcing.Condition.decode`, `OAI.PartitionConsistency.CohenForcing.Condition.restrictedGraph`, `OAI.PartitionConsistency.ConservativeMonoids.CellTower.future`, `OAI.PartitionConsistency.ConservativeMonoids.CellTower.hull`, `OAI.PartitionConsistency.ConservativeMonoids.CellTower.reordered`, `OAI.PartitionConsistency.ConservativeMonoids.RequestCell`, `OAI.PartitionConsistency.ConservativeMonoids.Subobject.Square.attachment`, `OAI.PartitionConsistency.ConservativeMonoids.forgetMargins`, `OAI.PartitionConsistency.DiagramForcing.Diagram.ExactOverlap`, `OAI.PartitionConsistency.DiagramOrder.ConservativeHull.seed`, `OAI.PartitionConsistency.DiagramOrder.ConservativeHull.submonoid`, `OAI.PartitionConsistency.LocalDiagramSystem.ReindexIso.componentEquiv`, `OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Chain.Alignments`, `OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Chain.tailData`, `OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Chain.tailFixer`, `OAI.PartitionConsistency.LocalDiagramSystem.Vertex.ComponentOrbit`, `OAI.PartitionConsistency.LocalDiagramSystem.Vertex.OrbitRel`, `OAI.PartitionConsistency.LocalDiagramSystem.Vertex.orbit`, `OAI.PartitionConsistency.LocalDiagramSystem.Vertex.orbitChain`, `OAI.PartitionConsistency.LocalDiagramSystem.Vertex.orbitRep`, `OAI.PartitionConsistency.LocalDiagramSystem.Vertex.orbitSetoid`, `OAI.PartitionConsistency.LocalDiagramSystem.labelFiberEmbedding`, `OAI.PartitionConsistency.LocalDiagramSystem.labelVertex`, `OAI.PartitionConsistency.MonoidConstruction.Saturation.FlatIndex`, `OAI.PartitionConsistency.MonoidConstruction.Saturation.blockBase`, `OAI.PartitionConsistency.MonoidConstruction.Saturation.blockFunctor`, `OAI.PartitionConsistency.MonoidConstruction.Saturation.blockIndex`, `OAI.PartitionConsistency.MonoidConstruction.Saturation.blockMap`, `OAI.PartitionConsistency.MonoidConstruction.Saturation.blockStage`, `OAI.PartitionConsistency.MonoidConstruction.Saturation.blocks`, `OAI.PartitionConsistency.MonoidConstruction.Saturation.cells`, `OAI.PartitionConsistency.MonoidConstruction.Saturation.outerStage`, `OAI.PartitionConsistency.ProductForcing.ChainCode`, `OAI.PartitionConsistency.ProductForcing.ChainCode.Assigned`, `OAI.PartitionConsistency.ProductForcing.ChainCode.AssignmentPoint`, `OAI.PartitionConsistency.ProductForcing.ChainCode.At`, `OAI.PartitionConsistency.ProductForcing.ChainCode.Corrected`, `OAI.PartitionConsistency.ProductForcing.ChainCode.GraphHolds` and 116 more.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory/PartitionConsistency, in whole or in part: `PartitionConsistency_Algebra_DiagramOrder`, `PartitionConsistency_Algebra_Placements`, `PartitionConsistency_Construction_BlockTowers`, `PartitionConsistency_Construction_CellCuts`, `PartitionConsistency_Construction_CellReorder`, `PartitionConsistency_Construction_CellTowers`, `PartitionConsistency_Construction_ConservativeCells`, `PartitionConsistency_Construction_ConservativeHulls`, `PartitionConsistency_Construction_DiagramPlacements`, `PartitionConsistency_Construction_MergerPushouts`, `PartitionConsistency_Forcing_ChoiceFailure`, `PartitionConsistency_Forcing_Diagrams`, `PartitionConsistency_Forcing_EquivariantMixing`, `PartitionConsistency_Forcing_ForcingNames`, `PartitionConsistency_Forcing_ForcingTruth`, `PartitionConsistency_Forcing_ProductForcing`, `PartitionConsistency_Forcing_ProductNames`, `PartitionConsistency_Forcing_RelationCalculus`, `PartitionConsistency_Forcing_SymmetricChoice`, `PartitionConsistency_Forcing_SymmetricNames`, `PartitionConsistency_Forcing_SymmetricSets`, `PartitionConsistency_Models_AssignedGraphs`, `PartitionConsistency_Models_AvailableRecords`, `PartitionConsistency_Models_ClassFibers`, `PartitionConsistency_Models_CodeLinks`, `PartitionConsistency_Models_ComponentGluing`, `PartitionConsistency_Models_ConcreteSystem`, `PartitionConsistency_Models_GermSelectors`, `PartitionConsistency_Models_GraphFusion`, `PartitionConsistency_Models_LocalQuotients`, `PartitionConsistency_Models_LocalRecords`, `PartitionConsistency_Models_OrbitAssignments`, `PartitionConsistency_Models_OrbitNames`, `PartitionConsistency_Models_OrderedSections`, `PartitionConsistency_Models_OrdinalChoice`, `PartitionConsistency_Models_OrdinalCodes`, `PartitionConsistency_Models_OrdinalPresentation`, `PartitionConsistency_Models_PersistentCodes`, `PartitionConsistency_Models_QuotientActions`, `PartitionConsistency_Models_QuotientTransport`, `PartitionConsistency_Models_SliceAssembly`, `PartitionConsistency_Models_SliceGeometry`, `PartitionConsistency_Models_StableSelectors`, `PartitionConsistency_Models_TailGraphs`, `PartitionConsistency_Models_UniformNames`.
--
--   **Imports.** It imports the published bundle `Def_PartitionConsistency`; the bundles `OAIQ5T1000` and `OAIQ5T1001` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.PartitionConsistency.main_consistency`.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); definitions carved from lean/OAI/SetTheory/PartitionConsistency at commit adc7f12

import Mathlib
import Definitions.Def_PartitionConsistency
import Definitions.Def_OAIQ5T1000
import Definitions.Def_OAIQ5T1001

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_DiagramOrder
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
namespace DiagramOrder

variable {α : Type*} [PartialOrder α]

namespace HeightCost
variable (H : HeightCost α)

include H in
/-- The central countability argument of `lem:mono-countable-ideal`.
In fact, only nonemptiness and directedness of the set are needed. No
cardinality assumption, inaccessible, or prechosen sequence is used. -/
theorem directed_cofinal_sequence {U : Set α} (hne : U.Nonempty)
    (hdir : DirectedOn (· ≤ ·) U) :
    ∃ f : ℕ → α, (∀ n, f n ∈ U) ∧ Monotone f ∧ ∀ d ∈ U, ∃ n, d ≤ f n := by
  classical
  let r := sSup (H.height '' U)
  have hb : BddAbove (H.height '' U) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    exact (H.height_lt_one x).le
  have approx : ∀ n : ℕ, ∃ u : U, r - 1 / (n + 1 : ℝ) < H.height u := by
    intro n
    have hpos : 0 < (1 : ℝ) / (n + 1 : ℝ) := by positivity
    have hr : r - 1 / (n + 1 : ℝ) < r := by linarith
    obtain ⟨_, ⟨u, hu, rfl⟩, hr'⟩ := (lt_csSup_iff hb (hne.image H.height)).1 hr
    exact ⟨⟨u, hu⟩, hr'⟩
  choose u hu using approx
  have upper : ∀ x y : U, ∃ z : U, x.val ≤ z.val ∧ y.val ≤ z.val := by
    intro x y
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x.val x.property y.val y.property
    exact ⟨⟨z, hz⟩, hxz, hyz⟩
  choose b hb₁ hb₂ using upper
  let f : ℕ → U := Nat.rec (u 0) (fun n prev => b prev (u (n + 1)))
  have hmono : Monotone (fun n => (f n).val) := by
    apply monotone_nat_of_le_succ
    intro n
    exact hb₁ (f n) (u (n + 1))
  have hu_le : ∀ n, (u n).val ≤ (f n).val := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ n => exact hb₂ (f n) (u (n + 1))
  have happrox : ∀ n : ℕ, r - 1 / (n + 1 : ℝ) < H.height (f n).val := by
    intro n
    exact (hu n).trans_le (H.strictMono_height.monotone (hu_le n))
  refine ⟨fun n => (f n).val, fun n => (f n).property, hmono, ?_⟩
  intro d hd
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (H.cost_pos d)
  refine ⟨n, ?_⟩
  by_contra hdn
  let z := b (f n) ⟨d, hd⟩
  have hxz : (f n).val ≤ z.val := hb₁ _ _
  have hdz : d ≤ z.val := hb₂ (f n) ⟨d, hd⟩
  have hlt : (f n).val < z.val := lt_of_le_not_ge hxz (fun h => hdn (hdz.trans h))
  have hgap := H.point_margin hlt hdz hdn
  have hbound : H.height z.val ≤ r := le_csSup hb ⟨z.val, z.property, rfl⟩
  have happ := happrox n
  linarith

end HeightCost

namespace ConeIdeal

theorem directed {a : α} (U : ConeIdeal a) (hj : HasConditionalJoins α) :
    DirectedOn (· ≤ ·) U.carrier := by
  intro x hx y hy
  obtain ⟨j, hxy⟩ := hj x y a (U.bounded hx) (U.bounded hy)
  exact ⟨j, U.join_closed hx hy hxy,
    hxy.1 (Set.mem_insert _ _), hxy.1 (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

/-- Source `lem:mono-countable-ideal`, including the stipulated first entry.
When `α = LeftDivOrder M`, the bottom element in this statement is `1`. -/
theorem countable_cofinal_sequence [OrderBot α] (H : HeightCost α)
    (hj : HasConditionalJoins α) {a : α} (U : ConeIdeal a) :
    ∃ f : ℕ → α, f 0 = ⊥ ∧ (∀ n, f n ∈ U.carrier) ∧ Monotone f ∧
      ∀ d ∈ U.carrier, ∃ n, d ≤ f n := by
  obtain ⟨g, hg, hmono, hcof⟩ := H.directed_cofinal_sequence U.nonempty (U.directed hj)
  let f : ℕ → α := fun n => match n with
    | 0 => ⊥
    | k + 1 => g k
  refine ⟨f, rfl, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero =>
        obtain ⟨u, hu⟩ := U.nonempty
        exact U.lower bot_le hu
    | succ n => exact hg n
  · apply monotone_nat_of_le_succ
    intro n
    cases n with
    | zero => exact bot_le
    | succ n => exact hmono (Nat.le_succ n)
  · intro d hd
    obtain ⟨n, hn⟩ := hcof d hd
    exact ⟨n + 1, hn⟩

end ConeIdeal
end DiagramOrder
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Algebra_Placements
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
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

/-- A partial injection on a subset of a smaller set can be completed to an
injection into the larger infinite set. This is a ground-choice construction. -/
theorem extend_embedding [Infinite β] (h : #α < #β) {s : Set α} (f : s ↪ β) :
    ∃ g : α ↪ β, ∀ x : s, g x = f x := by
  classical
  have hf : #(Set.range f) < #β := by
    rw [← Cardinal.mk_congr (Equiv.ofInjective f f.injective)]
    exact (Cardinal.mk_le_of_injective Subtype.val_injective).trans_lt h
  have hc : #(sᶜ : Set α) ≤ #((Set.range f)ᶜ : Set β) := by
    rw [Cardinal.mk_compl_of_infinite _ hf]
    exact (Cardinal.mk_le_of_injective Subtype.val_injective).trans h.le
  obtain ⟨k⟩ := hc
  let g : α → β := fun a => if ha : a ∈ s then f ⟨a, ha⟩ else k ⟨a, ha⟩
  have hg : Function.Injective g := by
    intro a b hab
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ s
    · simp only [g, dite_eq_left ha, dite_eq_left hb] at hab
      exact congrArg Subtype.val (f.injective hab)
    · simp only [g, dite_eq_left ha, dite_eq_right hb] at hab
      exact False.elim ((k ⟨b, hb⟩).property ⟨⟨a, ha⟩, hab⟩)
    · simp only [g, dite_eq_right ha, dite_eq_left hb] at hab
      exact False.elim ((k ⟨a, ha⟩).property ⟨⟨b, hb⟩, hab.symm⟩)
    · simp only [g, dite_eq_right ha, dite_eq_right hb] at hab
      exact congrArg Subtype.val (k.injective (Subtype.ext hab))
  exact ⟨⟨g, hg⟩, fun x => by simp [g, x.property]⟩

/-- Move a small set off any other small set, leaving a specified common
root fixed. The complement of the forbidden union supplies the fresh labels. -/
theorem move_off [Infinite α] {s t r : Set α}
    (hst : #(s ∪ t ∪ r : Set α) < #α) :
    ∃ π : Equiv.Perm α, (∀ x ∈ r, π x = x) ∧
      Disjoint (π '' (s \ r)) (t ∪ r) := by
  classical
  have hc : #((s ∪ t ∪ r)ᶜ : Set α) = #α :=
    Cardinal.mk_compl_of_infinite _ hst
  have he : #(s \ r : Set α) ≤ #((s ∪ t ∪ r)ᶜ : Set α) := by
    rw [hc]
    exact Cardinal.mk_le_of_injective Subtype.val_injective
  obtain ⟨e⟩ := he
  let f : (s ∪ r : Set α) → α :=
    fun x => if hx : x.val ∈ r then x.val else e ⟨x.val, (x.property.resolve_right hx), hx⟩
  have hf : Function.Injective f := by
    intro a b hab
    by_cases ha : a.val ∈ r <;> by_cases hb : b.val ∈ r
    · simp only [f, dite_eq_left ha, dite_eq_left hb] at hab
      exact Subtype.ext hab
    · simp only [f, dite_eq_left ha, dite_eq_right hb] at hab
      exact False.elim ((e ⟨b.val, b.property.resolve_right hb, hb⟩).property
        (hab ▸ Or.inr ha))
    · simp only [f, dite_eq_right ha, dite_eq_left hb] at hab
      exact False.elim ((e ⟨a.val, a.property.resolve_right ha, ha⟩).property
        (hab.symm ▸ Or.inr hb))
    · simp only [f, dite_eq_right ha, dite_eq_right hb] at hab
      apply Subtype.ext
      exact congrArg (fun z : (s \ r : Set α) => z.val) (e.injective (Subtype.ext hab))
  have hsr : #(s ∪ r : Set α) < #α :=
    (Cardinal.mk_le_mk_of_subset (by intro x hx; simp only [Set.mem_union] at hx ⊢; tauto)).trans_lt hst
  obtain ⟨π, hπ⟩ := extend_permutation ⟨f, hf⟩ hsr
  refine ⟨π, ?_, ?_⟩
  · intro x hx
    simpa [f, hx] using hπ ⟨x, Or.inr hx⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, ⟨hx, hxr⟩, rfl⟩ ht
    have hp : π x = e ⟨x, hx, hxr⟩ := by
      simpa [f, hxr] using hπ ⟨x, Or.inl hx⟩
    rw [hp] at ht
    apply (e ⟨x, hx, hxr⟩).property
    rcases ht with ht | ht
    · exact Or.inl (Or.inr ht)
    · exact Or.inr ht

end SmallPlacements
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_Diagrams
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramForcing.OverlapPrescription.copiesRightFreeAction _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instIsConicalDirectLimitMonoidHom _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.MergerAlgebra.RightDivOrder.instPartialOrder _root_.OAI.PartitionConsistency.MergerAlgebra.Word.instIsConical _root_.OAI.PartitionConsistency.MonoidConstruction.Base.instIsConicalM _root_.OAI.PartitionConsistency.ProbeAlgebra.Word.instIsConical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency
namespace DiagramForcing
universe u
variable {M I : Type u}

namespace Diagram
variable [LeftCancelMonoid M]

/-- The pairwise hypothesis of the diagram amalgamation lemma. -/
def ExactOverlap (r s : Diagram M I) : Prop :=
  Disjoint r.range s.range ∨ ∃ a b : M,
    sub r a = sub s b ∧ r.range ∩ s.range = (sub r a).range

theorem equal_iff_of_common_sub {r s : Diagram M I} {a b : M}
    (he : sub r a = sub s b) (hr : r.range ∩ s.range = (sub r a).range) (x y : M) :
    r x = s y ↔ ∃ t, x = a * t ∧ y = b * t := by
  constructor
  · intro hxy
    have hm : r x ∈ (sub r a).range := hr ▸ ⟨⟨x, rfl⟩, ⟨y, hxy.symm⟩⟩
    obtain ⟨t, ht⟩ := hm
    refine ⟨t, (r.injective ht).symm, ?_⟩
    apply s.injective
    have hte := congrArg (fun d : Diagram M I => d t) he
    exact hxy.symm.trans (ht.symm.trans hte)
  · rintro ⟨t, rfl, rfl⟩
    exact congrArg (fun d : Diagram M I => d t) he

/-- Actual equality of labels gives a valid finite prescription whenever all
pairwise range intersections are exact common subdiagrams. -/
theorem exists_overlap_prescription {n : ℕ} (s : Fin n → Diagram M I)
    (hs : ∀ i j, i ≠ j → ExactOverlap (s i) (s j)) :
    ∃ P : OverlapPrescription M n, P.Valid ∧ ∀ z w : Fin n × M,
      s z.1 z.2 = s w.1 w.2 ↔ P.Rel z w := by
  classical
  have choices : ∀ i j : Fin n, ∃ o : Option (M × M), ∀ x y : M,
      s i x = s j y ↔ (if i = j then x = y else
        match o with
        | none => False
        | some (a, b) => ∃ t, x = a * t ∧ y = b * t) := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact ⟨none, fun x y => by simp⟩
    · rcases hs i j hij with hdisj | ⟨a, b, he, hr⟩
      · refine ⟨none, ?_⟩
        intro x y
        simp only [hij, ↓reduceIte, iff_false]
        intro heq
        exact Set.disjoint_left.1 hdisj ⟨x, rfl⟩ ⟨y, heq.symm⟩
      · exact ⟨some (a, b), fun x y => by
          simpa only [hij, ↓reduceIte] using equal_iff_of_common_sub he hr x y⟩
  choose start hstart using choices
  let P : OverlapPrescription M n := ⟨start⟩
  have hp : ∀ z w : Fin n × M, s z.1 z.2 = s w.1 w.2 ↔ P.Rel z w :=
    fun z w => hstart z.1 w.1 z.2 w.2
  refine ⟨P, ⟨?_, ?_, ?_⟩, hp⟩
  · intro z
    exact (hp z z).1 rfl
  · intro z w hzw
    exact (hp w z).1 ((hp z w).2 hzw).symm
  · intro z w v hzw hwv
    exact (hp z v).1 (((hp z w).2 hzw).trans ((hp w v).2 hwv))

/-- Source `lem:diagram-amalgamation`, second part. The extension is an actual
embedding on the whole monoid. The prescribed range overlaps are used to
invoke the finite-merger property; no amalgamating diagram is a premise. -/
theorem amalgamate [Infinite I] (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) {n : ℕ} (s : Fin n → Diagram M I)
    (hs : ∀ i j, i ≠ j → ExactOverlap (s i) (s j)) :
    ∃ (r : Diagram M I) (l : Fin n → M), ∀ i, sub r (l i) = s i := by
  classical
  obtain ⟨P, hP, hlabels⟩ := exists_overlap_prescription s hs
  obtain ⟨l, hl⟩ := hmerger n P hP
  let U : Set M := {m | ∃ i x, l i * x = m}
  have hreps : ∀ z : U, ∃ i x, l i * x = z.val := fun z => z.property
  choose idx arg hrep using hreps
  let f : U → I := fun z => s (idx z) (arg z)
  have hf : Function.Injective f := by
    intro z w hzw
    have hh := (hl (idx z, arg z) (idx w, arg w)).2
      ((hlabels (idx z, arg z) (idx w, arg w)).1 hzw)
    apply Subtype.ext
    simpa only [hrep] using hh
  have hfval : ∀ i x, f ⟨l i * x, ⟨i, x, rfl⟩⟩ = s i x := by
    intro i x
    let z : U := ⟨l i * x, ⟨i, x, rfl⟩⟩
    exact (hlabels (idx z, arg z) (i, x)).2
      ((hl (idx z, arg z) (i, x)).1 (hrep z))
  obtain ⟨r, hr⟩ := SmallPlacements.extend_embedding hsize ⟨f, hf⟩
  refine ⟨⟨r⟩, l, ?_⟩
  intro i
  ext x
  exact (hr ⟨l i * x, ⟨i, x, rfl⟩⟩).trans (hfval i x)

theorem common_extension [Infinite I] [DiagramOrder.IsConical M]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    {n : ℕ} (s : Fin n → Diagram M I)
    (hs : ∀ i j, i ≠ j → ExactOverlap (s i) (s j)) :
    ∃ r : Diagram M I, ∀ i, r ≤ s i := by
  obtain ⟨r, l, hl⟩ := amalgamate hsize hmerger s hs
  exact ⟨r, fun i => ⟨l i, hl i⟩⟩

end Diagram
end DiagramForcing
end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_MergerPushouts
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## MergerPresentation -/


/-! ## SimulationPushout -/

/-! The conservative simulations are also categorical pushouts among *all*
monoids. This supplies the presentation comparison, which alone is not yet
a countable-base rearrangement. -/


/-! ## PushoutPasting -/

/-! Universal-property bookkeeping for moving already selected cells before
omitted cells. These lemmas are about literal monoid pushouts; they do not
assert the existence of a selected subconstruction. -/
namespace PartitionConsistency.MonoidPushout
universe u
noncomputable section
variable {A B C D E F : Type u} [Monoid A] [Monoid B] [Monoid C]
  [Monoid D] [Monoid E] [Monoid F]

namespace IsPushout

/-- Reflection across the diagonal does not change a pushout. -/
theorem flip {f : A →* B} {g : A →* C} {i : B →* D} {j : C →* D}
    (h : IsPushout f g i j) : IsPushout g f j i where
  comm := h.comm.symm
  universal b c hc := by
    obtain ⟨t,ht,hu⟩ := h.universal c b hc.symm
    exact ⟨t,⟨ht.2,ht.1⟩,fun k hk => hu k ⟨hk.2,hk.1⟩⟩

end IsPushout
end
end PartitionConsistency.MonoidPushout

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_ConservativeHulls
attribute [-instance] _root_.OAI.PartitionConsistency.ConcreteSystem.instInfiniteCarrierT _root_.OAI.PartitionConsistency.ConservativeMonoids.Cell.instCountableGenerators _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
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

namespace PartitionConsistency.DiagramOrder
universe u
noncomputable section
open scoped Classical
variable {M : Type u} [LeftCancelMonoid M] [IsConical M]

namespace ConservativeHull

variable (hj : HasConditionalJoins (LeftDivOrder M))
variable (s : Set M) (deps : M → Set M)

def seed : Set M := insert 1 s

def submonoid : Submonoid M where
  carrier := CountableHull.carrier (seed s) (operations deps)
  one_mem' := CountableHull.subset_carrier _ _ (Set.mem_insert 1 _)
  mul_mem' hx hy := CountableHull.closed _ _ hx hy (Or.inl (Set.mem_insert _ _))

end ConservativeHull
end
end PartitionConsistency.DiagramOrder


/-! ## ConservativeCategory -/

/-! Conservative monoids without height/cost bookkeeping. The original
saturated tower forgets to this category. It is used for rearrangements:
heights are needed for scheduling ideals, but not for old-gate descent. -/

namespace PartitionConsistency.ConservativeMonoids
universe u v w
open DiagramOrder CategoryTheory CategoryTheory.Limits
noncomputable section

attribute [instance] Object.monoid Object.conical

def forgetMargins : MonoidConstruction.Object.{u} ⥤ Object.{u} where
  obj M := ⟨M,M.joins⟩
  map f := ⟨f.toMonoidHom,f.conservative⟩

end
end PartitionConsistency.ConservativeMonoids

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_ConservativeCells
attribute [-instance] _root_.OAI.PartitionConsistency.ConcreteSystem.instInfiniteCarrierT
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## ConservativeIntersections -/

/-! The intersections used when a presentation is restricted to a countable
hull. This establishes conservation at arbitrary cuts, not just selected cuts. -/


/-! ## Cell -/

/-! The actual countably presented operations, with their conservative
simulations and finite coefficient supports. These are the cells in the
original schedule, forgetting only the height/cost bookkeeping. -/
namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder DiagramForcing MonoidPushout
noncomputable section

/-- Forgetting heights takes each executed request to precisely one of the
cells above, not to an object merely satisfying the same axioms. -/
def RequestCell {M : MonoidConstruction.Object.{u}} :
    MonoidConstruction.Request M → Cell (forgetMargins.obj M)
  | .inl d => .inl ⟨d.a,d.b,M.e,d.b_ne_one,M.e_ne_one,d.path⟩
  | .inr d => .inr ⟨d.n,d.prescription,d.valid⟩

end
end PartitionConsistency.ConservativeMonoids

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_CellTowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CellRestriction -/

/-! Reflecting a scheduled operation to a conservative subobject that
contains its literal countable parameter set. -/


/-! ## CellularTower -/

/-! Cellular towers inside their actual terminal monoid. The countable hull
retains literal generators and finite old coefficients. -/

namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder DiagramOrder.ConservativeHull CategoryTheory MonoidPushout
noncomputable section
open scoped Classical

variable (T : Object.{u}) (J : Type u) [LinearOrder J] [OrderBot J] [OrderTop J]
  [SuccOrder J] [WellFoundedLT J]

namespace CellTower
variable {T J} (D : CellTower T J)

omit [WellFoundedLT J]

/-- Close under dependencies as well as factors and actual conditional
joins. This is a submonoid of the terminal monoid, not a substitute monoid. -/
def hull (s : Set T) : Subobject T where
  submonoid := ConservativeHull.submonoid (s ∪ (D.stage ⊥).submonoid) D.dependencies
  factors _ hx _ hy := CountableHull.closed _ _ hx hy
    (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  joins _ hx _ hy := CountableHull.closed _ _ hx hy
    (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

end CellTower
end
end PartitionConsistency.ConservativeMonoids

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_CellCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CellCut -/

/-! The selected subconstruction at every original cut. Closing the retained
words under their dependencies supplies actual restricted cells. -/


/-! ## CellFunctor -/

/-! Functoriality of the actual presentations. A redundant natural-number
list of generators avoids changing index types during base change. -/


/-! ## CellBaseChange -/

/-! A selected cell can be simulated over any conservative intermediate
base. Full monoid pushouts identify the presentations, while explicit cell
simulations prove that the intermediate presentation embeds conservatively. -/

namespace PartitionConsistency.ConservativeMonoids
universe u
open CategoryTheory DiagramOrder MonoidPushout
noncomputable section
open scoped Classical

namespace Subobject
variable {T : Object.{u}}

namespace Square
variable {A B C D : Subobject T} (h : Square A B C D)

include h in
theorem flip : Square A C B D := ⟨h.ac,h.ab,h.cd,h.bd,h.pushout.flip⟩

def attachment (d : Attachment A B) : Attachment C D :=
  ⟨d.cell.map (hom h.ac),h.realization d,h.realization_old d⟩

end Square
end Subobject

end
end PartitionConsistency.ConservativeMonoids

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_CellReorder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CellUnion -/

/-! Directed unions of conservative submonoids and of their presentation
pushouts. Every union here is inside the original terminal monoid. -/
namespace PartitionConsistency.ConservativeMonoids.Subobject
universe u v
open CategoryTheory DiagramOrder MonoidPushout
noncomputable section
open scoped Classical
variable {T : Object.{u}}

namespace Square
variable {A B C D E F : Subobject T}

/-- The pushout of a fixed base change with a directed union is the union
of the actual pushout stages. -/
theorem union {K : Type u} [Preorder K] [IsDirectedOrder K] [Nonempty K]
    {A C Bup Dup : Subobject T} (B D : K → Subobject T)
    (hB : Monotone (fun k => (B k).submonoid))
    (hD : Monotone (fun k => (D k).submonoid))
    (hBL : ∀ k, (B k).submonoid ≤ Bup.submonoid)
    (hDL : ∀ k, (D k).submonoid ≤ Dup.submonoid)
    (hBU : ∀ x ∈ Bup.submonoid, ∃ k, x ∈ (B k).submonoid)
    (hDU : ∀ x ∈ Dup.submonoid, ∃ k, x ∈ (D k).submonoid)
    (h : ∀ k, Square A (B k) C (D k)) : Square A Bup C Dup := by
  let k₀ : K := Classical.arbitrary K
  have hab : A.submonoid ≤ Bup.submonoid := (h k₀).ab.trans (hBL k₀)
  have hac : A.submonoid ≤ C.submonoid := (h k₀).ac
  have hbd : Bup.submonoid ≤ Dup.submonoid := by
    intro x hx
    obtain ⟨i,hi⟩ := hBU x hx
    exact hDL i ((h i).bd hi)
  have hcd : C.submonoid ≤ Dup.submonoid := (h k₀).cd.trans (hDL k₀)
  refine ⟨hab,hac,hbd,hcd,⟨by ext x; rfl,?_⟩⟩
  intro N _ b c hc
  have hi (i : K) : (b.comp (hom (hBL i)).toMonoidHom).comp (hom (h i).ab).toMonoidHom =
      c.comp (hom (h i).ac).toMonoidHom := hc
  let t (i : K) := (h i).pushout.lift (b.comp (hom (hBL i)).toMonoidHom) c (hi i)
  have ht₁ (i : K) : (t i).comp (hom (h i).bd).toMonoidHom =
      b.comp (hom (hBL i)).toMonoidHom := (h i).pushout.lift_comp_left _ _ _
  have ht₂ (i : K) : (t i).comp (hom (h i).cd).toMonoidHom = c :=
    (h i).pushout.lift_comp_right _ _ _
  have ht (i j : K) (hij : i ≤ j) :
      (t j).comp (hom (hD hij)).toMonoidHom = t i := by
    apply (h i).pushout.hom_ext
    · ext x
      have e₁ := DFunLike.congr_fun (ht₁ j) (hom (hB hij) x)
      have e₂ := DFunLike.congr_fun (ht₁ i) x
      exact e₁.trans e₂.symm
    · ext x
      exact (DFunLike.congr_fun (ht₂ j) x).trans (DFunLike.congr_fun (ht₂ i) x).symm
  let l := unionLift D hD Dup hDL hDU t ht
  have hl₁ : l.comp (hom hbd).toMonoidHom = b := by
    ext x
    obtain ⟨i,hi⟩ := hBU x.val x.property
    have e₁ := DFunLike.congr_fun (unionLift_comp D hD Dup hDL hDU t ht i)
      (hom (h i).bd ⟨x.val,hi⟩)
    have e₂ := DFunLike.congr_fun (ht₁ i) ⟨x.val,hi⟩
    exact e₁.trans e₂
  have hl₂ : l.comp (hom hcd).toMonoidHom = c := by
    ext x
    exact (DFunLike.congr_fun (unionLift_comp D hD Dup hDL hDU t ht k₀)
      (hom (h k₀).cd x)).trans (DFunLike.congr_fun (ht₂ k₀) x)
  refine ⟨l,⟨hl₁,hl₂⟩,?_⟩
  intro m hm
  have he (i : K) : m.comp (hom (hDL i)).toMonoidHom = t i := by
    apply (h i).pushout.hom_ext
    · ext x
      exact (DFunLike.congr_fun hm.1 (hom (hBL i) x)).trans
        (DFunLike.congr_fun (ht₁ i) x).symm
    · ext x
      exact (DFunLike.congr_fun hm.2 x).trans (DFunLike.congr_fun (ht₂ i) x).symm
  ext x
  obtain ⟨i,hi⟩ := hDU x.val x.property
  exact (DFunLike.congr_fun (he i) ⟨x.val,hi⟩).trans
    (DFunLike.congr_fun (unionLift_comp D hD Dup hDL hDU t ht i) ⟨x.val,hi⟩).symm

end Square
end
end PartitionConsistency.ConservativeMonoids.Subobject


/-! ## CellReorder -/

/-! Rearranging the actual tower: a countable dependency-closed submonoid
can be performed first, and every omitted cell can then be appended in its
original order. The construction uses full monoid pushouts at all cuts. -/
namespace PartitionConsistency.ConservativeMonoids.CellTower
universe u
open CategoryTheory DiagramOrder MonoidPushout _root_.OAI.PartitionConsistency.ConservativeMonoids.Subobject
noncomputable section
open scoped Classical
variable {T : Object.{u}} {J : Type u} [LinearOrder J] [OrderBot J] [OrderTop J]
  [SuccOrder J] [WellFoundedLT J] (D : CellTower T J) (S : Subobject T)

/-- Simulate the selected future cells over any original earlier cut. The
result has exactly the union presentation, not a further conservative hull. -/
theorem future_cut (hS : D.Closed S) (a b : J) (hab : a ≤ b) :
    ∃ R : Subobject T, R.submonoid = (D.stage a).submonoid ⊔ (D.restrict S b).submonoid ∧
      Square (D.restrict S a) (D.restrict S b) (D.stage a) R := by
  have base (a : J) : ∃ R : Subobject T,
      R.submonoid = (D.stage a).submonoid ⊔ (D.restrict S a).submonoid ∧
      Square (D.restrict S a) (D.restrict S a) (D.stage a) R :=
    ⟨D.stage a,(sup_eq_left.mpr (D.restrict_le S a)).symm,
      Square.identity (D.restrict_le S a)⟩
  induction b using SuccOrder.limitRecOn with
  | isMin b hb =>
    obtain rfl := hb.eq_of_le hab
    exact base a
  | succ b hb ih =>
    by_cases hab' : a ≤ b
    · obtain ⟨R,hR,hp⟩ := ih hab'
      by_cases hs : D.selected S b
      · obtain ⟨hd,hpush⟩ := D.restrict_selected S hS hs
        let hsquare : Square (D.restrict S b) (D.restrict S (Order.succ b))
            (D.stage b) (D.stage (Order.succ b)) :=
          ⟨D.restrict_mono S (Order.le_succ b),D.restrict_le S b,
            D.restrict_le S (Order.succ b),D.mono (Order.le_succ b),hpush⟩
        have hRb : R.submonoid ≤ (D.stage b).submonoid := by
          rw [hR]
          exact sup_le (D.mono hab') (D.restrict_le S b)
        obtain ⟨F,hF,hFb,hdF,hpF⟩ := hsquare.intermediate hd.some hp.bd hRb
        refine ⟨F,?_,hp.paste hpF⟩
        rw [hF,hR]
        exact (sup_comm _ _).trans (sup_assoc _ _ _ |>.trans
          (congrArg ((D.stage a).submonoid ⊔ ·)
            (sup_eq_right.mpr (D.restrict_mono S (Order.le_succ b)))))
      · have he : D.restrict S b = D.restrict S (Order.succ b) :=
          Subobject.ext (D.restrict_omitted S hs)
        exact ⟨R,by simpa only [he] using hR,by simpa only [he] using hp⟩
    · have ha : a = Order.succ b :=
        le_antisymm hab ((Order.succ_le_iff_of_not_isMax hb).mpr (lt_of_not_ge hab'))
      subst a
      exact base (Order.succ b)
  | isSuccLimit b hb ih =>
    by_cases he : a = b
    · subst a; exact base b
    have hab' : a < b := lt_of_le_of_ne hab he
    let K := {k : J // a ≤ k ∧ k < b}
    have : Nonempty K := ⟨⟨a,le_refl _,hab'⟩⟩
    have hR (k : K) : ∃ R : Subobject T,
        R.submonoid = (D.stage a).submonoid ⊔ (D.restrict S k.val).submonoid ∧
        Square (D.restrict S a) (D.restrict S k.val) (D.stage a) R :=
      ih k.val k.property.2 k.property.1
    let R (k : K) := (hR k).choose
    have hReq (k : K) := (hR k).choose_spec.1
    have hRp (k : K) := (hR k).choose_spec.2
    have hmono : Monotone (fun k => (R k).submonoid) := by
      intro i j hij
      dsimp only [R]
      rw [hReq i,hReq j]
      exact sup_le_sup_left (D.restrict_mono S hij) _
    let U := Subobject.directedSup R hmono.directed_le
    have hRL (k : K) : (R k).submonoid ≤ U.submonoid :=
      (le_iSup (fun k : K => (R k).submonoid) k)
    have hRU (x : T) (hx : x ∈ U.submonoid) : ∃ k, x ∈ (R k).submonoid :=
      (Submonoid.mem_iSup_of_directed hmono.directed_le).mp hx
    have hBL (k : K) : (D.restrict S k.val).submonoid ≤ (D.restrict S b).submonoid :=
      D.restrict_mono S k.property.2.le
    have hBU (x : T) (hx : x ∈ (D.restrict S b).submonoid) :
        ∃ k : K, x ∈ (D.restrict S k.val).submonoid := by
      obtain ⟨j,hj,hxj⟩ := D.continuous b hb x hx.2
      exact ⟨⟨max a j,le_max_left _ _,max_lt hab' hj⟩,hx.1,D.mono (le_max_right _ _) hxj⟩
    have hpu := Square.union (fun k : K => D.restrict S k.val) R
      (fun _ _ h => D.restrict_mono S h) hmono hBL hRL hBU hRU hRp
    refine ⟨U,?_,hpu⟩
    exact hpu.apex_eq_sup.trans (sup_comm _ _)

/-- The original cut, followed by all its selected future cells. -/
def future (hS : D.Closed S) (a : J) : Subobject T :=
  (D.future_cut S hS a ⊤ le_top).choose

theorem future_eq (hS : D.Closed S) (a : J) :
    (D.future S hS a).submonoid = (D.stage a).submonoid ⊔ S.submonoid := by
  have hh := (D.future_cut S hS a ⊤ le_top).choose_spec.1
  change (D.future S hS a).submonoid = (D.stage a).submonoid ⊔
    (S.submonoid ⊓ (D.stage ⊤).submonoid) at hh
  simpa only [D.terminal,inf_top_eq] using hh

theorem future_square (hS : D.Closed S) (a : J) :
    Square (D.restrict S a) S (D.stage a) (D.future S hS a) := by
  have he : D.restrict S ⊤ = S := Subobject.ext (by
    change S.submonoid ⊓ (D.stage ⊤).submonoid = S.submonoid
    rw [D.terminal,inf_top_eq])
  have hh := (D.future_cut S hS a ⊤ le_top).choose_spec.2
  exact (congrArg (fun R => Square (D.restrict S a) R (D.stage a) (D.future S hS a)) he).mp hh

theorem future_mono (hS : D.Closed S) : Monotone (fun a => (D.future S hS a).submonoid) := by
  intro a b hab
  dsimp only
  rw [D.future_eq S hS a,D.future_eq S hS b]
  exact sup_le_sup_right (D.mono hab) _

theorem future_selected (hS : D.Closed S) {a : J} (ha : D.selected S a) :
    (D.future S hS a).submonoid = (D.future S hS (Order.succ a)).submonoid := by
  obtain ⟨_,hp⟩ := D.restrict_selected S hS ha
  let h : Square (D.restrict S a) (D.restrict S (Order.succ a))
      (D.stage a) (D.stage (Order.succ a)) :=
    ⟨D.restrict_mono S (Order.le_succ a),D.restrict_le S a,
      D.restrict_le S (Order.succ a),D.mono (Order.le_succ a),hp⟩
  apply le_antisymm (D.future_mono S hS (Order.le_succ a))
  dsimp only
  rw [D.future_eq S hS (Order.succ a),D.future_eq S hS a,h.apex_eq_sup]
  apply sup_le (sup_le ?_ le_sup_left) le_sup_right
  intro x hx
  exact (show S.submonoid ≤ (D.stage a).submonoid ⊔ S.submonoid from le_sup_right) hx.1

theorem future_omitted_square (hS : D.Closed S) {a : J} (ha : ¬ D.selected S a) :
    Square (D.stage a) (D.stage (Order.succ a))
      (D.future S hS a) (D.future S hS (Order.succ a)) := by
  have he : D.restrict S a = D.restrict S (Order.succ a) :=
    Subobject.ext (D.restrict_omitted S ha)
  have h₁ := (D.future_square S hS a).flip
  have h₂ : Square (D.restrict S a) (D.stage (Order.succ a)) S
      (D.future S hS (Order.succ a)) := by
    rw [he]; exact (D.future_square S hS (Order.succ a)).flip
  exact h₁.cancel_left h₂ (D.mono (Order.le_succ a)) (D.future_mono S hS (Order.le_succ a))

/-- The reordered tower, inside the same `T`. Its initial submonoid is
`S` whenever `S` contains the original initial stage. -/
def reordered (hS : D.Closed S) : CellTower T J where
  stage := D.future S hS
  mono := D.future_mono S hS
  terminal := by rw [D.future_eq S hS ⊤,D.terminal,top_sup_eq]
  continuous := by
    intro i hi x hx
    have : Nonempty (Set.Iio i) := hi.nonempty_Iio.to_subtype
    let F (k : Set.Iio i) := D.future S hS k.val
    have hF : Monotone (fun k => (F k).submonoid) := fun _ _ h => D.future_mono S hS h
    have hle : (D.future S hS i).submonoid ≤ ⨆ k : Set.Iio i, (F k).submonoid := by
      rw [D.future_eq S hS i]
      apply sup_le
      · intro y hy
        obtain ⟨j,hj,hyj⟩ := D.continuous i hi y hy
        apply le_iSup (fun k : Set.Iio i => (F k).submonoid) ⟨j,hj⟩
        change y ∈ (D.future S hS j).submonoid
        rw [D.future_eq S hS j]
        exact (show (D.stage j).submonoid ≤ (D.stage j).submonoid ⊔ S.submonoid from le_sup_left) hyj
      · let k : Set.Iio i := Classical.arbitrary _
        apply le_trans ?_ (le_iSup (fun k : Set.Iio i => (F k).submonoid) k)
        change S.submonoid ≤ (D.future S hS k.val).submonoid
        rw [D.future_eq S hS k.val]
        exact le_sup_right
    obtain ⟨k,hk⟩ := (Submonoid.mem_iSup_of_directed hF.directed_le).mp (hle hx)
    exact ⟨k.val,k.property,hk⟩
  step := by
    intro a
    by_cases h : D.selected S a
    · exact Or.inl (D.future_selected S hS h)
    · rcases D.step a with he | hd
      · left
        rw [D.future_eq S hS a,D.future_eq S hS (Order.succ a),he]
      · exact Or.inr ⟨(D.future_omitted_square S hS h).attachment hd.some⟩

end
end PartitionConsistency.ConservativeMonoids.CellTower

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_BlockTowers
attribute [-instance] _root_.OAI.PartitionConsistency.ConcreteSystem.instInfiniteCarrierT
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## BlockIndex -/

/-! Lexicographic concatenation of the actual rounds. The extra cut at the
end of each round is retained, making passage to the next initial cut an
identity step. -/


/-! ## BlockTower -/


/-! ## RangeAttachment -/

namespace PartitionConsistency.ConservativeMonoids
universe u
open CategoryTheory DiagramOrder
noncomputable section

namespace Hom
variable {M N T : Object.{u}} (f : M ⟶ N) (g : N ⟶ T)

theorem range_comp_of_surjective (hf : Function.Surjective f) :
    Subobject.range (g.comp f) = Subobject.range g := by
  apply Subobject.ext
  apply le_antisymm
  · rintro y ⟨x,rfl⟩
    exact ⟨f x,rfl⟩
  · rintro y ⟨x,rfl⟩
    obtain ⟨z,rfl⟩ := hf x
    exact ⟨z,rfl⟩

end Hom
end
end PartitionConsistency.ConservativeMonoids


/-! ## SaturationBlock -/

namespace PartitionConsistency.ConservativeMonoids
universe u
open CategoryTheory DiagramOrder
noncomputable section

/-- The literal range of an executed request is the range attachment of
its actual probe or merger presentation. -/
theorem request_rangeAttachment {M : MonoidConstruction.Object.{u}} {T : Object.{u}}
    (d : MonoidConstruction.Request M) (f : forgetMargins.obj M ⟶ T)
    (g : forgetMargins.obj d.target ⟶ T) (h : ∀ x, g (d.inclusion x) = f x) :
    Nonempty (Attachment (Subobject.range f) (Subobject.range g)) := by
  cases d with
  | inl d => exact ⟨(RequestCell (.inl d)).rangeAttachment f g h⟩
  | inr d => exact ⟨(RequestCell (.inr d)).rangeAttachment f g h⟩

end
end PartitionConsistency.ConservativeMonoids

namespace PartitionConsistency.MonoidConstruction
universe u
open CategoryTheory DiagramOrder ConservativeMonoids
noncomputable section
open scoped Classical

namespace RoundOrdinal
instance instSuccOrder : SuccOrder RoundOrdinal.{u} := SuccOrder.ofLinearWellFoundedLT _
end RoundOrdinal

namespace Saturation
variable (M : Object.{u}) (K : Type u) [Nonempty K]

abbrev blockBase (i : RoundOrdinal.{u}) := (tower M K).obj (i : OuterIndex)
abbrev blockIndex (i : RoundOrdinal.{u}) := CompleteRound.Index (blockBase M K i) K
abbrev blockFunctor (i : RoundOrdinal.{u}) := CompleteRound.tower (blockBase M K i) K

def blockMap (i : RoundOrdinal.{u}) (j : blockIndex M K i) :
    (blockFunctor M K i).obj j ⟶ target M K :=
  (blockFunctor M K i).map (homOfLE le_top) ≫ afterRound M K i (WithTop.coe_lt_top i)

def blockStage (i : RoundOrdinal.{u}) (j : blockIndex M K i) :
    ConservativeMonoids.Subobject (forgetMargins.obj (target M K)) :=
  ConservativeMonoids.Subobject.range (forgetMargins.map (blockMap M K i j))

def outerStage (i : OuterIndex.{u}) :
    ConservativeMonoids.Subobject (forgetMargins.obj (target M K)) :=
  ConservativeMonoids.Subobject.range (forgetMargins.map (fromStage M K i))

theorem blockMap_naturality (i : RoundOrdinal.{u}) {j k : blockIndex M K i} (hjk : j ≤ k) :
    (blockFunctor M K i).map (homOfLE hjk) ≫ blockMap M K i k = blockMap M K i j := by
  unfold blockMap
  erw [← Category.assoc,← Functor.map_comp,homOfLE_comp]

theorem outerMap_naturality {i j : OuterIndex.{u}} (hij : i ≤ j) :
    (tower M K).map (homOfLE hij) ≫ fromStage M K j = fromStage M K i := by
  unfold fromStage
  erw [← Functor.map_comp,homOfLE_comp]

theorem blockStage_base (i : RoundOrdinal.{u}) : blockStage M K i ⊥ = outerStage M K i := by
  let b := blockBase M K i
  let sch := CompleteRound.schedule b K
  have he : Round.fromBase b sch ⊥ ≫ blockMap M K i ⊥ = fromStage M K i := by
    unfold blockMap
    erw [← Category.assoc,Round.fromBase_naturality]
    exact inclusion_afterRound M K i (WithTop.coe_lt_top i)
  have hf : Function.Surjective (forgetMargins.map (Round.fromBase b sch ⊥)) := by
    rw [← Round.bot_inv]
    exact (isoEquiv (Round.botIso b sch).symm).surjective
  have hh := ConservativeMonoids.Hom.range_comp_of_surjective
    (forgetMargins.map (Round.fromBase b sch ⊥)) (forgetMargins.map (blockMap M K i ⊥)) hf
  change Subobject.range (forgetMargins.map (Round.fromBase b sch ⊥ ≫ blockMap M K i ⊥)) = _ at hh
  rw [he] at hh
  exact hh.symm

theorem blockStage_top (i : RoundOrdinal.{u}) :
    blockStage M K i ⊤ = outerStage M K (Order.succ (i : OuterIndex)) := by
  have hb : blockMap M K i ⊤ = afterRound M K i (WithTop.coe_lt_top i) := by
    apply Hom.ext
    intro x
    change afterRound M K i (WithTop.coe_lt_top i)
      ((blockFunctor M K i).map (homOfLE le_top) x) = afterRound M K i _ x
    have h : (blockFunctor M K i).map (homOfLE (show (⊤ : blockIndex M K i) ≤ ⊤ from le_rfl)) = 𝟙 _ :=
      (blockFunctor M K i).map_id ⊤
    rw [h]
    rfl
  unfold blockStage
  rw [hb]
  exact ConservativeMonoids.Hom.range_comp_of_surjective
    (forgetMargins.map (succIso M K i (WithTop.coe_lt_top i)).inv)
    (forgetMargins.map (fromStage M K (Order.succ (i : OuterIndex))))
    (isoEquiv (succIso M K i (WithTop.coe_lt_top i)).symm).surjective

theorem blockStage_mono (i : RoundOrdinal.{u}) :
    Monotone (fun j => (blockStage M K i j).submonoid) := by
  intro j k hjk x hx
  obtain ⟨y,rfl⟩ := hx
  refine ⟨(blockFunctor M K i).map (homOfLE hjk) y,?_⟩
  exact congrArg (fun f : (blockFunctor M K i).obj j ⟶ target M K => f y)
    (blockMap_naturality M K i hjk)

theorem outerStage_mono : Monotone (fun i => (outerStage M K i).submonoid) := by
  intro i j hij x hx
  obtain ⟨y,rfl⟩ := hx
  refine ⟨(tower M K).map (homOfLE hij) y,?_⟩
  exact congrArg (fun f : (tower M K).obj i ⟶ target M K => f y)
    (outerMap_naturality M K hij)

theorem blockStage_limit (i : RoundOrdinal.{u}) (j : blockIndex M K i)
    (hj : Order.IsSuccLimit j) (x : target M K) (hx : x ∈ (blockStage M K i j).submonoid) :
    ∃ k < j, x ∈ (blockStage M K i k).submonoid := by
  obtain ⟨y,rfl⟩ := hx
  obtain ⟨k,hkj,z,hz⟩ := ContinuousTower.exists_rep (blockFunctor M K i) hj y
  refine ⟨k,hkj,z,?_⟩
  rw [← hz]
  exact (congrArg (fun f : (blockFunctor M K i).obj k ⟶ target M K => f z)
    (blockMap_naturality M K i hkj.le)).symm

theorem outerStage_limit (j : OuterIndex.{u}) (hj : Order.IsSuccLimit j)
    (x : target M K) (hx : x ∈ (outerStage M K j).submonoid) :
    ∃ k < j, x ∈ (outerStage M K k).submonoid := by
  obtain ⟨y,rfl⟩ := hx
  obtain ⟨k,hkj,z,hz⟩ := ContinuousTower.exists_rep (tower M K) hj y
  refine ⟨k,hkj,z,?_⟩
  rw [← hz]
  exact (congrArg (fun f : (tower M K).obj k ⟶ target M K => f z)
    (outerMap_naturality M K hkj.le)).symm

theorem blockStage_step (i : RoundOrdinal.{u}) (j : blockIndex M K i) (hj : j < ⊤) :
    Nonempty (Attachment (blockStage M K i j) (blockStage M K i (Order.succ j))) := by
  let b := blockBase M K i
  let sch := CompleteRound.schedule b K
  let d := (sch j).map (Round.fromBase b sch j)
  let e := Round.succIso b sch j (not_isMax_iff_ne_top.mpr hj.ne)
  let g := e.inv ≫ blockMap M K i (Order.succ j)
  have hc : d.inclusion ≫ g = blockMap M K i j := by
    dsimp only [g,e,d]
    rw [← Category.assoc,← Round.map_succ]
    exact blockMap_naturality M K i (Order.le_succ j)
  have h := request_rangeAttachment d (forgetMargins.map (blockMap M K i j)) (forgetMargins.map g)
    (fun x => congrArg (fun f : (blockFunctor M K i).obj j ⟶ target M K => f x) hc)
  have hg : Subobject.range (forgetMargins.map g) = blockStage M K i (Order.succ j) :=
    ConservativeMonoids.Hom.range_comp_of_surjective (forgetMargins.map e.inv)
      (forgetMargins.map (blockMap M K i (Order.succ j))) (isoEquiv e.symm).surjective
  rw [hg] at h
  exact h

/-- The executed omega-one many saturation rounds form a literal block tower
inside the very same final monoid. -/
def blocks : BlockTower (I := RoundOrdinal.{u}) (J := blockIndex M K)
    (forgetMargins.obj (target M K)) where
  stage := blockStage M K
  inner_mono := blockStage_mono M K
  outer_mono := by
    intro i j hij
    change (blockStage M K i ⊥).submonoid ≤ (blockStage M K j ⊥).submonoid
    rw [blockStage_base,blockStage_base]
    exact outerStage_mono M K (WithTop.coe_le_coe.mpr hij)
  boundary := by
    intro i
    rw [blockStage_top,blockStage_base]
    have hs : Order.succ (i : OuterIndex) = ((Order.succ i : RoundOrdinal) : OuterIndex) :=
      Order.succ_eq_of_covBy (WithTop.coe_covBy_coe.mpr (Order.covBy_succ i))
    rw [hs]
  inner_limit := blockStage_limit M K
  outer_limit := by
    intro i hi x hx
    rw [blockStage_base] at hx
    obtain ⟨k,hki,hxk⟩ := outerStage_limit M K i hi.withTopCoe x hx
    obtain ⟨k,rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt (hki.trans_le le_top))
    refine ⟨k,WithTop.coe_lt_coe.mp hki,?_⟩
    rw [blockStage_base]
    exact hxk
  covers := by
    intro x
    obtain ⟨k,hk,g,hg⟩ := countable_stage M K (fun _ : Unit => x)
    obtain ⟨k,rfl⟩ := WithTop.ne_top_iff_exists.mp hk.ne
    refine ⟨k,?_⟩
    rw [blockStage_base]
    exact ⟨g (),hg ()⟩
  step := blockStage_step M K

abbrev FlatIndex := BlockIndex.Index RoundOrdinal.{u} (blockIndex M K)
def cells : CellTower (forgetMargins.obj (target M K)) (FlatIndex M K) := (blocks M K).flatten

end Saturation
end
end PartitionConsistency.MonoidConstruction

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ForcingNames
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.SetForcingNames
universe u v


namespace ConditionAction
variable {Γ : Type v} [Group Γ] (S : ConditionAction.{u} Γ)

namespace Name
variable {S}

theorem union_HS {F : Set (Subgroup Γ)} (hF : SupportFilter.IsNormalFilter F)
    (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (hR : ∀ g p q, R (S.actCode g p) (S.actCode g q) ↔ R p q)
    {σ : S.Name} (hσ : HS F σ) : HS F (union R σ) := by
  apply hs_iff.mpr
  constructor
  · apply hF.2.1 (MulAction.stabilizer Γ σ) _ hσ.symmetric
    intro g hg
    change g • union R σ = union R σ
    rw [smul_union R hR, hg]
  · rintro τ ⟨q, hq⟩
    obtain ⟨χ, p, r, hp, hr, _, _, _⟩ := edge_unionName_iff.mp hq
    exact (hσ.child hp).subname ⟨r, hr⟩

end Name
end ConditionAction

end PartitionConsistency.SetForcingNames

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ForcingTruth
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionConsistency.ForcingQuotient.AtomicData
variable {P N : Type*} [Preorder P] (A : AtomicData P N)

theorem forceFormula_of_dense (hA : A.Regular) {n} {v : Fin n → N} {p : P}
    {φ : Formula n} (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ A.ForceFormula v r φ) :
    A.ForceFormula v p φ := A.force_of_dense hA φ.toBasic v p h

end PartitionConsistency.ForcingQuotient.AtomicData

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_SymmetricNames
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.SetForcingNames
universe u v w

namespace SymmetricSystem
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

namespace Name
variable {S}

instance instNonempty : Nonempty S.Name := ⟨empty⟩

end Name

end SymmetricSystem
end PartitionConsistency.SetForcingNames



namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem forces_snoc_congr {n} (φ : Formula (n+1)) (v : Fin n → S.Name)
    {p : P} {σ τ : S.Name} (h : S.atomic.EqF p σ τ) :
    S.Forces (Fin.snoc v σ) p φ ↔ S.Forces (Fin.snoc v τ) p φ := by
  apply S.atomic.forceFormula_tuple_congr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using h
  · simpa using S.atomic.eq_refl p (v j)

theorem edge_separate {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+1))
    (ν : S.Name) (c : P) : ZFSet.pair ν.raw (S.code c) ∈ (S.separate σ v φ).raw ↔
      ∃ i : Edges σ.raw, σ.child i.property = ν ∧ S.separationTest σ v φ i c := by
  change ZFSet.pair ν.raw (S.code c) ∈
    S.collectRaw (fun i : Edges σ.raw => σ.child i.property) (S.separationTest σ v φ) ↔ _
  rw [S.edge_collectRaw]
  constructor
  · rintro ⟨i,p,hR,hν,hp⟩
    obtain rfl := S.code_injective hp
    exact ⟨i,Name.ext hν,hR⟩
  · rintro ⟨i,hi,hR⟩
    exact ⟨i,c,hR,congrArg Name.raw hi,rfl⟩

/-- Verification of the Separation name; quantified names are unrestricted
HS names, not a rank-bounded subclass. -/
theorem mem_separate {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+1))
    (ν : S.Name) (p : P) : S.atomic.MemF p ν (S.separate σ v φ) ↔
      S.atomic.MemF p ν σ ∧ S.Forces (Fin.snoc v ν) p φ := by
  constructor
  · intro h
    have hd : ∀ q, q ≤ p → ∃ r, r ≤ q ∧
        S.atomic.MemF r ν σ ∧ S.Forces (Fin.snoc v ν) r φ := by
      intro q hqp
      obtain ⟨r,hrq,τ,c,he,hrc,heq⟩ := (S.mem_iff.mp h) q hqp
      obtain ⟨i,hi,hm,hφ⟩ := (S.edge_separate σ v φ τ c).mp he
      change S.atomic.MemF c (σ.child i.property) σ at hm
      change S.Forces (Fin.snoc v (σ.child i.property)) c φ at hφ
      rw [hi] at hm hφ
      refine ⟨r,hrq,?_,?_⟩
      · exact (S.atomic.mem_congr heq (S.atomic.eq_refl r σ)).mpr (S.atomic.mem_mono hrc hm)
      · exact (S.forces_snoc_congr φ v heq).mpr (S.atomic.forceFormula_mono hrc hφ)
    exact ⟨S.atomic_regular.2 p ν σ (fun q hq => by
      obtain ⟨r,hrq,hm,_⟩ := hd q hq
      exact ⟨r,hrq,hm⟩), S.atomic.forceFormula_of_dense S.atomic_regular (fun q hq => by
      obtain ⟨r,hrq,_,hφ⟩ := hd q hq
      exact ⟨r,hrq,hφ⟩)⟩
  · rintro ⟨hm,hφ⟩
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,τ,c,he,hrc,heq⟩ := (S.mem_iff.mp hm) q hqp
    let i : Edges σ.raw := ⟨(τ.raw, S.code c), he⟩
    have hi : σ.child i.property = τ := Name.ext rfl
    have ht : S.separationTest σ v φ i r := by
      change S.atomic.MemF r (σ.child i.property) σ ∧ _
      rw [hi]
      exact ⟨S.mem_of_edge he hrc, (S.forces_snoc_congr φ v heq).mp
        (S.atomic.forceFormula_mono (hrq.trans hqp) hφ)⟩
    exact ⟨r,hrq,τ,r,(S.edge_separate σ v φ τ r).mpr ⟨i,hi,ht⟩,le_rfl,heq⟩

end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_SymmetricSets
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The ordering on literal condition codes, false outside those codes. -/
def codeOrder (a b : ZFSet.{u}) : Prop :=
  ∃ p q : P, S.code p = a ∧ S.code q = b ∧ p ≤ q

theorem codeOrder_symmetry (g : Γ) (a b : ZFSet.{u}) :
    S.codeOrder (S.action.actCode g a) (S.action.actCode g b) ↔ S.codeOrder a b := by
  have forward (g : Γ) (a b : ZFSet.{u}) (h : S.codeOrder a b) :
      S.codeOrder (S.action.actCode g a) (S.action.actCode g b) := by
    obtain ⟨p,q,rfl,rfl,h⟩ := h
    exact ⟨S.move g p, S.move g q, (S.actCode_code g p).symm,
      (S.actCode_code g q).symm, (S.move g).monotone h⟩
  exact ⟨fun h => by simpa only [S.action.actCode_inv_actCode] using forward g⁻¹ _ _ h,
    forward g a b⟩

namespace Name
variable {S}

noncomputable def union (σ : S.Name) : S.Name :=
  ⟨ConditionAction.Name.union S.codeOrder σ.val,
    ConditionAction.Name.union_HS S.normal S.codeOrder S.codeOrder_symmetry σ.hs⟩

end Name

end PartitionConsistency.SetForcingNames.SymmetricSystem



namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

def SubsetF (p : P) (σ τ : S.Name) : Prop :=
  ∀ ν : S.Name, ∀ q, q ≤ p → S.atomic.MemF q ν σ → S.atomic.MemF q ν τ

theorem forces_subset {n} (v : Fin n → S.Name) (p : P) (a b : Fin n) :
    S.Forces v p (SetLanguage.subset a b) ↔ S.SubsetF p (v a) (v b) := by
  simp only [Forces, SetLanguage.subset, S.atomic.forceFormula_rename S.atomic_regular,
    S.atomic.forceFormula_all S.atomic_regular, S.atomic.forceFormula_imp S.atomic_regular,
    ForcingQuotient.AtomicData.forceFormula_mem]
  rfl

theorem subset_congr {p : P} {σ σ' τ τ' : S.Name}
    (hσ : S.atomic.EqF p σ σ') (hτ : S.atomic.EqF p τ τ') :
    S.SubsetF p σ τ ↔ S.SubsetF p σ' τ' := by
  constructor
  · intro h ν q hqp hν
    exact (S.atomic.mem_congr (S.atomic.eq_refl q ν) (S.atomic.eq_mono hqp hτ)).mp
      (h ν q hqp ((S.atomic.mem_congr (S.atomic.eq_refl q ν) (S.atomic.eq_mono hqp hσ)).mpr hν))
  · intro h ν q hqp hν
    exact (S.atomic.mem_congr (S.atomic.eq_refl q ν) (S.atomic.eq_mono hqp hτ)).mpr
      (h ν q hqp ((S.atomic.mem_congr (S.atomic.eq_refl q ν) (S.atomic.eq_mono hqp hσ)).mp hν))

theorem subset_symmetry (g : Γ) (p : P) (σ τ : S.Name) :
    S.SubsetF p σ τ ↔ S.SubsetF (S.move g p) (g • σ) (g • τ) := by
  have h := S.forces_symmetry g (SetLanguage.subset 0 1) ![σ,τ] p
  simpa only [S.forces_subset, Matrix.cons_val_zero, Matrix.cons_val_one] using h

instance instSmallPowerCandidate (σ : S.Name) : Small.{u} (S.PowerCandidate σ) := by
  apply small_of_injective (f := fun ν : S.PowerCandidate σ =>
    (⟨ν.val.raw,ZFSet.mem_powerset.mpr ν.property⟩ : (S.subsetBound σ).powerset))
  intro ν τ h
  exact Subtype.ext (Name.ext (congrArg Subtype.val h))

noncomputable def normalize (σ ν : S.Name) : S.Name :=
  S.separate σ ![ν] (.mem 1 0)

theorem mem_normalize (σ ν τ : S.Name) (p : P) :
    S.atomic.MemF p τ (S.normalize σ ν) ↔ S.atomic.MemF p τ σ ∧ S.atomic.MemF p τ ν :=
  S.mem_separate σ ![ν] (.mem 1 0) τ p

theorem normalize_bounded (σ ν : S.Name) : (S.normalize σ ν).raw ⊆ S.subsetBound σ := by
  intro z hz
  change z ∈ S.collectRaw (fun i : Edges σ.raw => σ.child i.property)
    (S.separationTest σ ![ν] (.mem 1 0)) at hz
  obtain ⟨i,p,_,he⟩ := (S.mem_collectRaw _ _ _).mp hz
  exact (S.mem_collectRaw _ _ _).mpr ⟨i,p,True.intro,he⟩

theorem normalize_eq {p : P} (σ ν : S.Name) (h : S.SubsetF p ν σ) :
    S.atomic.EqF p ν (S.normalize σ ν) := by
  apply S.eq_of_same_members
  intro τ q hqp
  rw [S.mem_normalize]
  exact ⟨fun hτ => ⟨h τ q hqp hτ,hτ⟩, And.right⟩

theorem powerCandidate_permute (σ : S.Name) :
    ∀ g ∈ MulAction.stabilizer Γ σ.val, ∀ (i : S.PowerCandidate σ) p,
      S.SubsetF p i.val σ → ∃ j : S.PowerCandidate σ,
        j.val = g • i.val ∧ S.SubsetF (S.move g p) j.val σ := by
  intro g hg i p hi
  have hσ : g • σ = σ := Subtype.ext hg
  have hbound : (g • i.val).raw ⊆ S.subsetBound σ := by
    rw [Name.smul_val]
    have hb := mapConditions_mono (S.action.actCode g) i.property
    simpa only [S.subsetBound_fixed σ g hσ] using hb
  refine ⟨⟨g • i.val,hbound⟩,rfl,?_⟩
  simpa only [hσ] using (S.subset_symmetry g p i.val σ).mp hi

/-- The power-set name uses every HS normalized subset candidate and the
conditions which force that candidate to be a subset. -/
noncomputable def power (σ : S.Name) : S.Name :=
  S.collect (fun i : S.PowerCandidate σ => i.val) (fun i p => S.SubsetF p i.val σ)
    (MulAction.stabilizer Γ σ.val) σ.hs.symmetric (S.powerCandidate_permute σ)

end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_SymmetricChoice
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

abbrev RelF {n} (v : Fin n → S.Name) (φ : Formula (n+2)) (p : P)
    (x y : S.Name) : Prop := S.Forces (Fin.snoc (Fin.snoc v x) y) p φ

/-- A small index set of precisely the domain-entry/condition pairs for which
there is a local symmetric witness. -/
def WitnessIndex {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2)) :=
  {i : Edges σ.raw × P // ∃ η : S.Name, S.RelF v φ i.2 (σ.child i.1.property) η}

instance instSmallWitnessIndex {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2)) :
    Small.{u} (S.WitnessIndex σ v φ) := by
  let := S.small_conditions
  unfold WitnessIndex
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

noncomputable def chosenWitness {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2))
    (i : S.WitnessIndex σ v φ) : S.Name := Classical.choose i.property

section SmallGroup
variable [Small.{u} Γ]

/-- An orbit-closed bound for one Replacement problem. Instead of a uniform
name-rank cutoff, take the whole set-group orbit of the ground-chosen local
witnesses. This set is invariant and is still small. No symmetric maximum
principle, global rank cutoff, or on-condition selection is used. -/
noncomputable def replacementBound {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+2)) : S.Name :=
  S.collect (fun z : Γ × S.WitnessIndex σ v φ => z.1 • S.chosenWitness σ v φ z.2)
    (fun _ _ => True) ⊤ S.normal.1 (by
      intro h _ z p _
      exact ⟨(h*z.1,z.2),mul_smul h z.1 _,True.intro⟩)

/-- The dense local meaning of `∃x∈σ, φ(x,y)`. -/
def ImageF {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2))
    (p : P) (ν : S.Name) : Prop :=
  ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name, S.atomic.MemF r x σ ∧ S.RelF v φ r x ν

/-- Ordinary internal single-valuedness, expressed via forcing at every
stronger condition. -/
def SingleValuedF {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2)) (p : P) : Prop :=
  ∀ x y z : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x σ →
    S.RelF v φ q x y → S.RelF v φ q x z → S.atomic.EqF q y z

/-- The image predicate, with the set-domain as one extra parameter, retaining
all quantifiers of the original formula. -/
def imageFormula {n} (φ : Formula (n+2)) : Formula (n+2) :=
  Formula.ex ((Formula.mem (Fin.last (n+2)) (Fin.last n).castSucc.castSucc).conj
    (SetLanguage.relation φ (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last (n+2)) (Fin.last (n+1)).castSucc))

noncomputable def replacementImage {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+2)) : S.Name :=
  S.separate (S.replacementBound σ v φ) (Fin.snoc v σ) (imageFormula φ)

/-- The antecedent of a Replacement instance: totality with local unique
witnesses, exactly as supplied by the existential forcing clause. -/
def TotalFunctionalF {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+2)) (p : P) : Prop :=
  ∀ x : S.Name, ∀ q, q ≤ p → S.atomic.MemF q x σ → ∀ r, r ≤ q →
    ∃ s, s ≤ r ∧ ∃ y : S.Name, S.RelF v φ s x y ∧
      ∀ z : S.Name, ∀ t, t ≤ s → S.RelF v φ t x z → S.atomic.EqF t z y

end SmallGroup
end PartitionConsistency.SetForcingNames.SymmetricSystem



end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_EquivariantMixing
attribute [-instance] _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Mixing -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)
variable {ι : Type t} [Small.{u} ι]

/-- Index the literal children of a small family, with no uniform bound on
the ranks of the family's members. -/
abbrev MixEntries (f : ι → S.Name) := Σ i, Edges (f i).raw

def mixTest (f : ι → S.Name) (a : ι → P) (i : S.MixEntries f) (p : P) : Prop :=
  p ≤ a i.1 ∧ S.atomic.MemF p ((f i.1).child i.2.property) (f i.1)

omit [Small.{u} ι] in
/-- Fixing the names and their activation conditions permutes every entry
of their union mixture, including all strengthenings of all activations. -/
theorem mixTest_permute (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ)
    (hf : ∀ g ∈ H, ∀ i, g • f i = f i)
    (ha : ∀ g ∈ H, ∀ i, S.move g (a i) = a i) :
    ∀ g ∈ H, ∀ (i : S.MixEntries f) p, S.mixTest f a i p →
      ∃ j : S.MixEntries f, (f j.1).child j.2.property = g • (f i.1).child i.2.property ∧
        S.mixTest f a j (S.move g p) := by
  intro g hg i p hp
  have he := S.entry_permute g (f i.1) i.2
  rw [hf g hg i.1] at he
  obtain ⟨j,hj⟩ := he
  refine ⟨⟨i.1,j⟩,hj,?_,?_⟩
  · change S.move g p ≤ a i.1
    rw [← ha g hg i.1]
    exact (S.move g).monotone hp.1
  · change S.atomic.MemF (S.move g p) ((f i.1).child j.property) (f i.1)
    rw [hj]
    simpa only [hf g hg i.1] using (S.mem_symmetry g p _ (f i.1)).mp hp.2

/-- A coherent or antichain mixture. Coherence is a property proved separately;
the present construction itself is just the unrestricted union of active names. -/
def mix (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hf : ∀ g ∈ H, ∀ i, g • f i = f i)
    (ha : ∀ g ∈ H, ∀ i, S.move g (a i) = a i) : S.Name :=
  S.collect (fun i : S.MixEntries f => (f i.1).child i.2.property)
    (S.mixTest f a) H hH (S.mixTest_permute f a H hf ha)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## EquivariantMix -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)
variable {ι : Type t} [Small.{u} ι]

omit [Small.{u} ι] in
/-- An equivariant family need not have each member fixed pointwise.
Permuting the names together with their activation conditions suffices. -/
theorem equivariantMixTest_permute (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ)
    (hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i)) :
    ∀ g ∈ H, ∀ (i : S.MixEntries f) p, S.mixTest f a i p →
      ∃ j : S.MixEntries f, (f j.1).child j.2.property = g • (f i.1).child i.2.property ∧
        S.mixTest f a j (S.move g p) := by
  intro g hg i p hp
  obtain ⟨j,hfj,haj⟩ := hperm g hg i.1
  have he := S.entry_permute g (f i.1) i.2
  rw [← hfj] at he
  obtain ⟨k,hk⟩ := he
  refine ⟨⟨j,k⟩,hk,?_,?_⟩
  · change S.move g p ≤ a j
    rw [haj]
    exact (S.move g).monotone hp.1
  · change S.atomic.MemF (S.move g p) ((f j).child k.property) (f j)
    rw [hk,hfj]
    exact (S.mem_symmetry g p _ (f i.1)).mp hp.2

/-- Union of an equivariant family of active arbitrary-rank names.
No choice of a common strengthening occurs in the definition. -/
def equivariantMix (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i)) : S.Name :=
  S.collect (fun i : S.MixEntries f => (f i.1).child i.2.property)
    (S.mixTest f a) H hH (S.equivariantMixTest_permute f a H hperm)

theorem equivariantMix_fixed (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i)) (g : Γ) (hg : g ∈ H) :
    g • S.equivariantMix f a H hH hperm = S.equivariantMix f a H hH hperm :=
  Subtype.ext (S.collectName_fixed _ _ H (S.equivariantMixTest_permute f a H hperm) g hg)

theorem edge_equivariantMix (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i)) (ν : S.Name) (p : P) :
    ZFSet.pair ν.raw (S.code p) ∈ (S.equivariantMix f a H hH hperm).raw ↔
      ∃ i : S.MixEntries f, (f i.1).child i.2.property = ν ∧ S.mixTest f a i p := by
  change ZFSet.pair ν.raw (S.code p) ∈
    S.collectRaw (fun i : S.MixEntries f => (f i.1).child i.2.property) (S.mixTest f a) ↔ _
  rw [S.edge_collectRaw]
  constructor
  · rintro ⟨i,c,hi,hν,hc⟩
    obtain rfl := S.code_injective hc
    exact ⟨i,Name.ext hν,hi⟩
  · rintro ⟨i,hi,hR⟩
    exact ⟨i,p,hR,congrArg Name.raw hi,rfl⟩

/-- The exact regular forcing value of membership in the union mixture. -/
theorem mem_equivariantMix (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i)) (ν : S.Name) (p : P) :
    S.atomic.MemF p ν (S.equivariantMix f a H hH hperm) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : ι, r ≤ a i ∧ S.atomic.MemF r ν (f i) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,c,he,hrc,heq⟩ := S.mem_iff.mp h q hqp
    obtain ⟨i,hi,hia,hit⟩ := (S.edge_equivariantMix f a H hH hperm τ c).mp he
    change S.atomic.MemF c ((f i.1).child i.2.property) (f i.1) at hit
    rw [hi] at hit
    exact ⟨r,hrq,i.1,hrc.trans hia,
      (S.atomic.mem_congr heq (S.atomic.eq_refl r (f i.1))).mpr (S.atomic.mem_mono hrc hit)⟩
  · intro h
    apply S.mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,i,hria,hν⟩ := h q hqp
    obtain ⟨s,hsr,τ,c,he,hsc,heq⟩ := S.mem_iff.mp hν r le_rfl
    let j : S.MixEntries f := ⟨i,⟨(τ.raw,S.code c),he⟩⟩
    have hj : (f j.1).child j.2.property = τ := Name.ext rfl
    have ht : S.mixTest f a j s := by
      change s ≤ a i ∧ S.atomic.MemF s ((f i).child he) (f i)
      exact ⟨hsr.trans hria,S.mem_of_edge he hsc⟩
    exact ⟨s,hsr.trans hrq,τ,s,(S.edge_equivariantMix f a H hH hperm τ s).mpr ⟨j,hj,ht⟩,le_rfl,heq⟩

/-- Any coherent family is equal to its mixture below its activation
condition. This applies in particular to antichains, when coherence is vacuous. -/
theorem eq_equivariantMix_at (f : ι → S.Name) (a : ι → P) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i))
    (hcoh : ∀ i j p, p ≤ a i → p ≤ a j → S.atomic.EqF p (f i) (f j)) (i : ι) :
    S.atomic.EqF (a i) (S.equivariantMix f a H hH hperm) (f i) := by
  apply S.eq_of_same_members
  intro ν q hqi
  constructor
  · intro h
    apply S.atomic_regular.2 q ν (f i)
    intro r hrq
    obtain ⟨s,hsr,j,hsj,hm⟩ := (S.mem_equivariantMix f a H hH hperm ν q).mp h r hrq
    exact ⟨s,hsr,(S.atomic.mem_congr (S.atomic.eq_refl s ν)
      (hcoh j i s hsj (hsr.trans (hrq.trans hqi)))).mp hm⟩
  · intro h
    apply (S.mem_equivariantMix f a H hH hperm ν q).mpr
    intro r hrq
    exact ⟨r,le_rfl,i,hrq.trans hqi,S.atomic.mem_mono hrq h⟩

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ProductForcing
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instIsConicalDirectLimitMonoidHom _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.MergerAlgebra.RightDivOrder.instPartialOrder _root_.OAI.PartitionConsistency.MergerAlgebra.Word.instIsConical _root_.OAI.PartitionConsistency.MonoidConstruction.Base.instIsConicalM _root_.OAI.PartitionConsistency.ProbeAlgebra.Word.instIsConical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionConsistency

namespace DiagramForcing.Diagram
universe u
variable {M I : Type u}

variable [LeftCancelMonoid M]

theorem ExactOverlap.symm {r s : Diagram M I} (h : ExactOverlap r s) : ExactOverlap s r := by
  rcases h with hd | ⟨a, b, hab, hr⟩
  · exact Or.inl hd.symm
  · exact Or.inr ⟨b, a, hab.symm, by rw [Set.inter_comm, hr, hab]⟩

/-- The binary specialization of finite diagram amalgamation. -/
theorem common_extension_two [Infinite I] [DiagramOrder.IsConical M]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    {r s : Diagram M I} (hov : ExactOverlap r s) :
    ∃ t : Diagram M I, t ≤ r ∧ t ≤ s := by
  obtain ⟨t, ht⟩ := common_extension hsize hmerger ![r, s] (by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hov
    · exact hov.symm
    · exact (hij rfl).elim)
  exact ⟨t, ht 0, ht 1⟩

end DiagramForcing.Diagram

namespace ProductForcing
universe u v
variable {M I : Type u} {κ : Type v}
open DiagramForcing

variable [LeftCancelMonoid M] [DiagramOrder.IsConical M]

/-- The independent-placement step of local decision (source
`lem:local-decision`). Compatible root restrictions suffice to place the second
product condition compatibly with the first, fixing the entire root diagram.
The monoid finite-merger property remains an explicit, unconstructed input. -/
theorem compatible_placement [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ : Diagram M I) (hs₀ : s₀ ≤ p) (hs₁ : s₁ ≤ p)
    (d₀ d₁ : CohenForcing.Condition I κ)
    (hroot : CohenForcing.Condition.Compatible (d₀.restrict p.range) (d₁.restrict p.range)) :
    ∃ π : Equiv.Perm I, (∀ j ∈ p.range, π j = j) ∧
      s₀.range ∩ (s₁.permute π).range = p.range ∧
      ∃ q : Condition M I κ, q ≤ (d₀, s₀) ∧ q ≤ permute π (d₁, s₁) := by
  let S := s₁.range ∪ d₁.support
  let T := s₀.range ∪ d₀.support
  have hμ : Cardinal.aleph0 ≤ Cardinal.mk M := Cardinal.aleph0_le_mk M
  have hS : Cardinal.mk S ≤ Cardinal.mk M := SmallPlacements.union_bound hμ
    (by simp) (d₁.cardinal_support.trans hμ)
  have hT : Cardinal.mk T ≤ Cardinal.mk M := SmallPlacements.union_bound hμ
    (by simp) (d₀.cardinal_support.trans hμ)
  obtain ⟨π, hfix, hdisj⟩ := SmallPlacements.move_off
    ((SmallPlacements.union_bound hμ (SmallPlacements.union_bound hμ hS hT)
      (by simp : Cardinal.mk p.range ≤ Cardinal.mk M)).trans_lt hsize)
  have hs₀r := Diagram.range_antitone hs₀
  have hs₁r := Diagram.range_antitone hs₁
  have hdi : Disjoint (π '' (s₁.range \ p.range)) (s₀.range ∪ p.range) := by
    apply hdisj.mono
    · exact Set.image_mono (Set.sdiff_subset_sdiff_left Set.subset_union_left)
    · exact Set.union_subset_union Set.subset_union_left Set.Subset.rfl
  have hinter : s₀.range ∩ (s₁.permute π).range = p.range := by
    rw [Diagram.range_permute]
    exact SmallPlacements.intersection_eq_root hs₁r hs₀r π hfix hdi
  have hpf : p.permute π = p := Diagram.permute_eq_of_fixes_range π p hfix
  have hs₁p : s₁.permute π ≤ p := by
    rw [← hpf]
    exact (Diagram.permuteOrderIso π).monotone hs₁
  have hov : Diagram.ExactOverlap s₀ (s₁.permute π) := by
    obtain ⟨a, ha⟩ := hs₀
    obtain ⟨b, hb⟩ := hs₁p
    exact Or.inr ⟨a, b, ha.trans hb.symm, by rwa [ha]⟩
  obtain ⟨t, ht₀, ht₁⟩ := Diagram.common_extension_two hsize hmerger hov
  have hcdisj : Disjoint (d₀.support \ p.range) ((d₁.permute π).support \ p.range) := by
    rw [Set.disjoint_left]
    rintro j ⟨hj₀, hjp⟩ ⟨hj₁, _⟩
    rw [CohenForcing.Condition.support_permute] at hj₁
    obtain ⟨k, hk, rfl⟩ := hj₁
    have hkp : k ∉ p.range := fun h => hjp (by simpa [hfix k h] using h)
    exact Set.disjoint_left.1 hdisj ⟨k, ⟨Or.inr hk, hkp⟩, rfl⟩ (Or.inl (Or.inr hj₀))
  have hcroot : CohenForcing.Condition.Compatible (d₀.restrict p.range)
      ((d₁.permute π).restrict p.range) := by
    rwa [CohenForcing.Condition.restrict_permute_of_fixes π d₁ hfix]
  have hc := CohenForcing.Condition.compatible_of_disjoint_off_root d₀ _ _ hcroot hcdisj
  obtain ⟨d, hd₀, hd₁⟩ := CohenForcing.Condition.compatible_iff.1 hc
  exact ⟨π, hfix, hinter, (d, t), ⟨hd₀, ht₀⟩, ⟨hd₁, ht₁⟩⟩

end ProductForcing

end PartitionConsistency

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ProductNames
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instIsConicalDirectLimitMonoidHom _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.MergerAlgebra.RightDivOrder.instPartialOrder _root_.OAI.PartitionConsistency.MergerAlgebra.Word.instIsConical _root_.OAI.PartitionConsistency.MonoidConstruction.Base.instIsConicalM _root_.OAI.PartitionConsistency.ProbeAlgebra.Word.instIsConical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## ProductSystem -/


/-! ## Label -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

theorem mem_labelSet (c : κ → ZFSet.{u}) (ν : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p : Poset M I κ) : (system (M := M) (I := I) (κ := κ) hμ).atomic.MemF p ν (labelSet (M := M) (I := I) hμ c) ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ j : I, (system (M := M) (I := I) (κ := κ) hμ).atomic.EqF r ν (label (M := M) hμ c j) := by
  constructor
  · intro h q hqp
    obtain ⟨r,hrq,τ,d,he,_,heq⟩ := (system (M := M) (I := I) (κ := κ) hμ).mem_iff.mp h q hqp
    rw [labelSet_raw] at he
    obtain ⟨j,_,_,hτ,_⟩ := ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mp he
    have hh : label (M := M) hμ c j = τ := Name.ext hτ
    exact ⟨r,hrq,j,hh ▸ heq⟩
  · intro h
    apply (system (M := M) (I := I) (κ := κ) hμ).mem_iff.mpr
    intro q hqp
    obtain ⟨r,hrq,j,heq⟩ := h q hqp
    exact ⟨r,hrq,label (M := M) hμ c j,⊤,
      by rw [labelSet_raw]; exact ((system (M := M) (I := I) (κ := κ) hμ).edge_collectRaw _ _ _ _).mpr ⟨j,⊤,rfl,rfl,rfl⟩,le_top,heq⟩

end
end PartitionConsistency.ProductForcing


/-! ## FunctionName -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_ChoiceFailure
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.ConstructionIteration.instHasColimitsOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instHasIterationOfShapeProd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesColimitsOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdFst_solutions _root_.OAI.PartitionConsistency.ConstructionIteration.instPreservesWellOrderContinuousOfShapeProdSnd_solutions _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instIsConicalDirectLimitMonoidHom _root_.OAI.PartitionConsistency.DiagramOrder.ConservativeLimit.instLeftCancelMonoidDirectLimitMonoidHom_solutions _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction _root_.OAI.PartitionConsistency.MergerAlgebra.RightDivOrder.instPartialOrder _root_.OAI.PartitionConsistency.MergerAlgebra.Word.instIsConical _root_.OAI.PartitionConsistency.MonoidConstruction.Base.instIsConicalM _root_.OAI.PartitionConsistency.ProbeAlgebra.Word.instIsConical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## OutsideLabel -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- The internal family P(A) minus the empty set, formed by the actual
Power Set and Separation constructions. Quantified subsets have no rank bound. -/
def choiceFailureFamily (c : κ → ZFSet.{u}) :
    (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).separate
    ((system (M := M) (I := I) (κ := κ) hμ).power (labelSet (M := M) (I := I) hμ c))
    Fin.elim0 (SetLanguage.nonempty 0)

end
end PartitionConsistency.ProductForcing


/-! ## Failure -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- The adjoined largest condition never prevents passing to a genuine
Cohen/diagram condition. -/
theorem exists_condition_below [Nonempty (Diagram M I)] (p : Poset M I κ) :
    ∃ q : Condition M I κ, (q : Poset M I κ) ≤ p := by
  induction p using WithTop.recTopCoe with
  | top => exact ⟨(⊤,Classical.choice inferInstance),le_top⟩
  | coe p => exact ⟨p,le_rfl⟩

end
end PartitionConsistency.ProductForcing


/-! ## LocalDecision -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- The direct product-forcing version of decision over a supporting
root. Any assertion forced below the root is already forced at the root,
with only the witnessing Cohen condition's root restriction retained.
All parameters are arbitrary-rank HS names. -/
theorem forces_at_supporting_root [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    {n} (φ : Formula n) (v : Fin n → (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p s : Diagram M I) (hsp : s ≤ p)
    (hsup : ∀ π ∈ SupportFilter.Fix p.range, ∀ i, π • v i = v i)
    (d : CohenForcing.Condition I κ)
    (h : (system hμ).Forces v ((d,s) : Poset M I κ) φ) :
    (system hμ).Forces v (((d.restrict p.range),p) : Poset M I κ) φ := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let : Nonempty (Diagram M I) := ⟨p⟩
  apply S.atomic.forceFormula_of_dense S.atomic_regular
  intro q hqp
  obtain ⟨q₀,hq₀⟩ := exists_condition_below q
  have hq : q₀ ≤ (d.restrict p.range,p) := WithTop.coe_le_coe.mp (hq₀.trans hqp)
  have hroot : CohenForcing.Condition.Compatible (q₀.1.restrict p.range) (d.restrict p.range) :=
    CohenForcing.Condition.compatible_iff.mpr ⟨q₀.1,q₀.1.le_restrict _,hq.1⟩
  obtain ⟨π,hπ,_,t,htq,htπ⟩ := compatible_placement hsize hmerger p q₀.2 s hq.2 hsp q₀.1 d hroot
  have hv : (fun i => π • v i) = v := funext (hsup π ((SupportFilter.mem_Fix _ _).mpr hπ))
  have ht : S.Forces v ((permute π (d,s)) : Poset M I κ) φ := by
    have hh := (S.forces_symmetry π φ v ((d,s) : Poset M I κ)).mp h
    simpa only [hv,S,move_coe] using hh
  exact ⟨t,(WithTop.coe_le_coe.mpr htq).trans hq₀,
    S.atomic.forceFormula_mono (WithTop.coe_le_coe.mpr htπ) ht⟩

/-- In particular, irrelevant Cohen coordinates can be removed from a
condition whose diagram supports its entire parameter tuple. -/
theorem forces_iff_restrict [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    {n} (φ : Formula n) (v : Fin n → (system (M := M) (I := I) (κ := κ) hμ).Name)
    (p : Diagram M I)
    (hsup : ∀ π ∈ SupportFilter.Fix p.range, ∀ i, π • v i = v i)
    (d : CohenForcing.Condition I κ) :
    (system hμ).Forces v ((d,p) : Poset M I κ) φ ↔
    (system hμ).Forces v (((d.restrict p.range),p) : Poset M I κ) φ :=
  ⟨forces_at_supporting_root hμ hsize hmerger φ v p p le_rfl hsup d,
    (system hμ).atomic.forceFormula_mono (WithTop.coe_le_coe.mpr ⟨d.le_restrict _,le_rfl⟩)⟩

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Construction_DiagramPlacements
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## ProbePlacement -/


/-! ## TriplePlacement -/

namespace PartitionConsistency.SmallPlacements
universe u
open Cardinal
noncomputable section
variable {I : Type u} [Infinite I] {μ : Cardinal.{u}}

/-- Extend a prescribed small partial placement to a permutation while
putting every unused coordinate of the larger small set outside a forbidden
small set. The prescribed part is left unchanged. -/
theorem extend_permutation_off (hμ : aleph0 ≤ μ) (hsize : μ < #I)
    {s v K : Set I} (hs : #s ≤ μ) (hv : #v ≤ μ) (hK : #K ≤ μ)
    (f : s ↪ I) :
    ∃ π : Equiv.Perm I, (∀ x : s, π x = f x) ∧ Disjoint (π '' (v \ s)) K := by
  obtain ⟨τ,hτ⟩ := extend_permutation f (hs.trans_lt hsize)
  have hfr : #(Set.range f) ≤ μ := by
    rw [← Cardinal.mk_congr (Equiv.ofInjective f f.injective)]
    exact hs
  obtain ⟨ρ,hρ,hd⟩ := move_off (s := τ '' v) (t := K) (r := Set.range f)
    ((union_bound hμ (union_bound hμ (Cardinal.mk_image_le.trans hv) hK) hfr).trans_lt hsize)
  refine ⟨ρ * τ,?_,?_⟩
  · intro x
    change ρ (τ x) = f x
    rw [hτ x,hρ _ ⟨x,rfl⟩]
  · apply hd.mono_right Set.subset_union_left |>.mono_left
    rintro _ ⟨x,⟨hx,hxs⟩,rfl⟩
    refine ⟨τ x,⟨⟨x,hx,rfl⟩,?_⟩,rfl⟩
    rintro ⟨y,hy⟩
    have hxy : x = y := τ.injective (hy.symm.trans (hτ y).symm)
    exact hxs (hxy ▸ y.property)

/-- Place the rest of a diagram after both of its independent subdiagrams
have been placed, with all leftover coordinates fresh. -/
theorem extend_two_placements (hμ : aleph0 ≤ μ) (hsize : μ < #I)
    {s₀ s₁ p v K : Set I} (hs₀ : #s₀ ≤ μ) (hs₁ : #s₁ ≤ μ) (hv : #v ≤ μ) (hK : #K ≤ μ)
    (hinter : s₀ ∩ s₁ = p) (α β : Equiv.Perm I)
    (hα : ∀ j ∈ p, α j = j) (hβ : ∀ j ∈ p, β j = j)
    (himage : (α '' s₀) ∩ (β '' s₁) = p) :
    ∃ π : Equiv.Perm I, (∀ j ∈ s₀, π j = α j) ∧ (∀ j ∈ s₁, π j = β j) ∧
      Disjoint (π '' (v \ (s₀ ∪ s₁))) K := by
  obtain ⟨f,hf₀,hf₁⟩ := paste_placements hinter α β hα hβ himage
  obtain ⟨π,hπ,hd⟩ := extend_permutation_off hμ hsize (union_bound hμ hs₀ hs₁) hv hK f
  exact ⟨π,fun j hj => (hπ ⟨j,Or.inl hj⟩).trans (hf₀ j hj),
    fun j hj => (hπ ⟨j,Or.inr hj⟩).trans (hf₁ j hj),hd⟩

/-- The simultaneous three-copy placement needed in support descent.
The two prescribed copies of `s₀` may be compared through one fresh shared
copy of `s₁`. All extra coordinates avoid the entire forbidden set, not
merely the ranges of the diagrams. -/
theorem three_copy_placement (hμ : aleph0 ≤ μ) (hsize : μ < #I)
    {s₀ s₁ p v K : Set I} (h₀ : s₀ ⊆ v) (h₁ : s₁ ⊆ v)
    (hv : #v ≤ μ) (hK : #K ≤ μ) (hinter : s₀ ∩ s₁ = p)
    (α β : Equiv.Perm I) (hα : ∀ j ∈ p, α j = j) (hβ : ∀ j ∈ p, β j = j)
    (hind : (α '' s₀) ∩ (β '' s₀) = p)
    (hαK : α '' s₀ ⊆ K) (hβK : β '' s₀ ⊆ K) :
    ∃ π ρ : Equiv.Perm I,
      (∀ j ∈ s₀, π j = α j) ∧ (∀ j ∈ s₀, ρ j = β j) ∧
      (∀ j ∈ s₁, π j = ρ j) ∧
      (π '' v) ∩ K = α '' s₀ ∧ (ρ '' v) ∩ K = β '' s₀ ∧
      (π '' v) ∩ (ρ '' v) = π '' s₁ := by
  have hs₀ : #s₀ ≤ μ := (Cardinal.mk_subtype_mono h₀).trans hv
  have hs₁ : #s₁ ≤ μ := (Cardinal.mk_subtype_mono h₁).trans hv
  have hp₀ : p ⊆ s₀ := fun _ h => (show _ ∈ s₀ ∩ s₁ from hinter.symm ▸ h).1
  have hp₁ : p ⊆ s₁ := fun _ h => (show _ ∈ s₀ ∩ s₁ from hinter.symm ▸ h).2
  have hpα : p ⊆ α '' s₀ := fun x hx => ⟨x,hp₀ hx,hα x hx⟩
  have hpβ : p ⊆ β '' s₀ := fun x hx => ⟨x,hp₀ hx,hβ x hx⟩
  have hpK : p ⊆ K := hpα.trans hαK
  have hp : #p ≤ μ := (Cardinal.mk_subtype_mono hp₀).trans hs₀
  obtain ⟨γ,hγ,hdγ⟩ := move_off (s := s₁) (t := K) (r := p)
    ((union_bound hμ (union_bound hμ hs₁ hK) hp).trans_lt hsize)
  have huK : (γ '' s₁) ∩ K = p := by
    rw [Set.inter_comm]
    exact intersection_eq_root hp₁ hpK γ hγ hdγ
  have hpγ : p ⊆ γ '' s₁ := fun x hx => ⟨x,hp₁ hx,hγ x hx⟩
  have hαγ : (α '' s₀) ∩ (γ '' s₁) = p := by
    apply Set.Subset.antisymm
    · intro x hx
      exact huK ▸ ⟨hx.2,hαK hx.1⟩
    · intro x hx
      exact ⟨hpα hx,hpγ hx⟩
  have hβγ : (β '' s₀) ∩ (γ '' s₁) = p := by
    apply Set.Subset.antisymm
    · intro x hx
      exact huK ▸ ⟨hx.2,hβK hx.1⟩
    · intro x hx
      exact ⟨hpβ hx,hpγ hx⟩
  obtain ⟨π,hπ₀,hπ₁,hdπ⟩ := extend_two_placements hμ hsize hs₀ hs₁ hv hK
    hinter α γ hα hγ hαγ
  have hπK : (π '' v) ∩ K = α '' s₀ := by
    rw [image_inter_of_fresh h₀ h₁ π hdπ,Set.image_congr hπ₀,Set.image_congr hπ₁,
      Set.union_inter_distrib_right,Set.inter_eq_left.mpr hαK,huK,Set.union_eq_left.mpr hpα]
  obtain ⟨ρ,hρ₀,hρ₁,hdρ⟩ := extend_two_placements hμ hsize hs₀ hs₁ hv
    (union_bound hμ hK (Cardinal.mk_image_le.trans hv)) hinter β γ hβ hγ hβγ
  have hρK : (ρ '' v) ∩ K = β '' s₀ := by
    rw [image_inter_of_fresh h₀ h₁ ρ (hdρ.mono_right Set.subset_union_left),
      Set.image_congr hρ₀,Set.image_congr hρ₁,
      Set.union_inter_distrib_right,Set.inter_eq_left.mpr hβK,huK,Set.union_eq_left.mpr hpβ]
  have huπ : γ '' s₁ ⊆ π '' v := by
    rw [← Set.image_congr hπ₁]
    exact Set.image_mono h₁
  have hβπ : (β '' s₀) ∩ (π '' v) = p := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxa : x ∈ α '' s₀ := hπK ▸ ⟨hx.2,hβK hx.1⟩
      exact hind ▸ ⟨hxa,hx.1⟩
    · intro x hx
      exact ⟨hpβ hx,huπ (hpγ hx)⟩
  refine ⟨π,ρ,hπ₀,hρ₀,fun j hj => (hπ₁ j hj).trans (hρ₁ j hj).symm,hπK,hρK,?_⟩
  rw [Set.inter_comm,image_inter_of_fresh h₀ h₁ ρ (hdρ.mono_right Set.subset_union_right),
    Set.image_congr hρ₀,Set.image_congr hρ₁,Set.union_inter_distrib_right,hβπ,
    Set.inter_eq_left.mpr huπ,Set.union_eq_right.mpr hpγ,Set.image_congr hπ₁]

end
end PartitionConsistency.SmallPlacements

namespace PartitionConsistency.DiagramForcing.Diagram
universe u
variable {M I : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

omit [LeftCancelMonoid M] [DiagramOrder.IsConical M] in
/-- Pointwise agreement on a diagram's range is literal agreement of the
moved diagrams, so transports of all its supported names agree as well. -/
theorem permute_eq_of_agree (s : Diagram M I) (π ρ : Equiv.Perm I)
    (h : ∀ j ∈ s.range, π j = ρ j) : s.permute π = s.permute ρ := by
  ext x
  exact h _ ⟨x,rfl⟩

theorem ExactOverlap.of_common {r s p : Diagram M I} (hr : r ≤ p) (hs : s ≤ p)
    (h : r.range ∩ s.range = p.range) : ExactOverlap r s := by
  obtain ⟨a,ha⟩ := hr
  obtain ⟨b,hb⟩ := hs
  exact Or.inr ⟨a,b,ha.trans hb.symm,by rwa [ha]⟩

theorem common_extension_three [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (r s t : Diagram M I) (hrs : ExactOverlap r s) (hrt : ExactOverlap r t)
    (hst : ExactOverlap s t) : ∃ q : Diagram M I, q ≤ r ∧ q ≤ s ∧ q ≤ t := by
  have hh : ∀ i j : Fin 3, i ≠ j → ExactOverlap (![r,s,t] i) (![r,s,t] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact False.elim (hij rfl) | exact hrs | exact hrt | exact hst |
        exact hrs.symm | exact hrt.symm | exact hst.symm
  obtain ⟨q,hq⟩ := common_extension hsize hmerger ![r,s,t] hh
  exact ⟨q,hq 0,hq 1,hq 2⟩
end PartitionConsistency.DiagramForcing.Diagram

namespace PartitionConsistency.ProductForcing
universe u
open DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

/-- The three-copy compatibility step of support descent, including the
Cohen coordinate and an arbitrary potential counterexample condition. -/
theorem descent_comparison_placement [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ v : Diagram M I) (hinter : s₀.range ∩ s₁.range = p.range)
    (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (α β : Equiv.Perm I) (hα : ∀ j ∈ p.range, α j = j) (hβ : ∀ j ∈ p.range, β j = j)
    (hind : (s₀.permute α).range ∩ (s₀.permute β).range = p.range)
    (d c : CohenForcing.Condition I κ) (hd : d.support ⊆ v.range) (t : Diagram M I)
    (htα : t ≤ s₀.permute α) (htβ : t ≤ s₀.permute β)
    (hcα : c ≤ (d.restrict s₀.range).permute α) (hcβ : c ≤ (d.restrict s₀.range).permute β) :
    ∃ π ρ : Equiv.Perm I, s₀.permute π = s₀.permute α ∧
      s₀.permute ρ = s₀.permute β ∧ s₁.permute π = s₁.permute ρ ∧
      ∃ q : Condition M I κ, q ≤ (c,t) ∧ q ≤ permute π (d,v) ∧ q ≤ permute ρ (d,v) := by
  let K : Set I := t.range ∪ c.support
  have hμ : Cardinal.aleph0 ≤ Cardinal.mk M := Cardinal.aleph0_le_mk M
  have hK : Cardinal.mk K ≤ Cardinal.mk M :=
    SmallPlacements.union_bound hμ (by simp) (c.cardinal_support.trans hμ)
  have hαK : α '' s₀.range ⊆ K :=
    (Diagram.range_permute α s₀ ▸ Diagram.range_antitone htα).trans Set.subset_union_left
  have hβK : β '' s₀.range ⊆ K :=
    (Diagram.range_permute β s₀ ▸ Diagram.range_antitone htβ).trans Set.subset_union_left
  obtain ⟨π,ρ,hπ₀,hρ₀,hπρ₁,hπK,hρK,hπρ⟩ := SmallPlacements.three_copy_placement
    hμ hsize (Diagram.range_antitone hv₀) (Diagram.range_antitone hv₁)
    (by simp) hK hinter α β hα hβ (by simpa only [Diagram.range_permute] using hind) hαK hβK
  have hsπ := Diagram.permute_eq_of_agree s₀ π α hπ₀
  have hsρ := Diagram.permute_eq_of_agree s₀ ρ β hρ₀
  have hs₁ := Diagram.permute_eq_of_agree s₁ π ρ hπρ₁
  have hvtπ : (v.permute π).range ∩ t.range = (s₀.permute α).range := by
    simp only [Diagram.range_permute]
    exact SmallPlacements.inter_eq_of_between hπK
      (Diagram.range_permute α s₀ ▸ Diagram.range_antitone htα) Set.subset_union_left
  have hvtρ : (v.permute ρ).range ∩ t.range = (s₀.permute β).range := by
    simp only [Diagram.range_permute]
    exact SmallPlacements.inter_eq_of_between hρK
      (Diagram.range_permute β s₀ ▸ Diagram.range_antitone htβ) Set.subset_union_left
  have hvπ : v.permute π ≤ s₀.permute α := hsπ ▸ (Diagram.permuteOrderIso π).monotone hv₀
  have hvρ : v.permute ρ ≤ s₀.permute β := hsρ ▸ (Diagram.permuteOrderIso ρ).monotone hv₀
  obtain ⟨w,hwt,hwπ,hwρ⟩ := Diagram.common_extension_three hsize hmerger t (v.permute π) (v.permute ρ)
    (Diagram.ExactOverlap.of_common hvπ htα hvtπ).symm
    (Diagram.ExactOverlap.of_common hvρ htβ hvtρ).symm
    (Diagram.ExactOverlap.of_common (p := s₁.permute π) ((Diagram.permuteOrderIso π).monotone hv₁)
      (by rw [hs₁]; exact (Diagram.permuteOrderIso ρ).monotone hv₁)
      (by simpa only [Diagram.range_permute] using hπρ))
  have hδπ : (d.restrict s₀.range).permute π = (d.restrict s₀.range).permute α :=
    CohenForcing.Condition.permute_eq_of_agree _ _ _
      (fun j hj => hπ₀ j ((d.support_restrict_subset _) hj))
  have hδρ : (d.restrict s₀.range).permute ρ = (d.restrict s₀.range).permute β :=
    CohenForcing.Condition.permute_eq_of_agree _ _ _
      (fun j hj => hρ₀ j ((d.support_restrict_subset _) hj))
  have hcπ := CohenForcing.Condition.compatible_permute_of_trigger d c π hd
    (show (π '' v.range) ∩ c.support ⊆ π '' s₀.range from fun j hj => by
      rw [Set.image_congr hπ₀]
      exact hπK ▸ ⟨hj.1,Or.inr hj.2⟩) (hδπ.symm ▸ hcα)
  have hcρ := CohenForcing.Condition.compatible_permute_of_trigger d c ρ hd
    (show (ρ '' v.range) ∩ c.support ⊆ ρ '' s₀.range from fun j hj => by
      rw [Set.image_congr hρ₀]
      exact hρK ▸ ⟨hj.1,Or.inr hj.2⟩) (hδρ.symm ▸ hcβ)
  have hcd := CohenForcing.Condition.compatible_permutes_of_overlap d π ρ hd
    (fun _ hj => hπρ ▸ hj) hπρ₁
  let b := c.union (d.permute π) hcπ
  let a := b.union (d.permute ρ) (hcπ.union_left hcρ hcd)
  have hab : a ≤ b := b.union_le_left _ (hcπ.union_left hcρ hcd)
  have hbc : b ≤ c := c.union_le_left _ hcπ
  have hbπ : b ≤ d.permute π := c.union_le_right _ hcπ
  have haρ : a ≤ d.permute ρ := b.union_le_right _ (hcπ.union_left hcρ hcd)
  exact ⟨π,ρ,hsπ,hsρ,hs₁,(a,w),⟨hab.trans hbc,hwt⟩,⟨hab.trans hbπ,hwπ⟩,⟨haρ,hwρ⟩⟩

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrbitNames
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## OrderedPair -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

theorem eq_opair_congr {p : P} {σ σ' τ τ' : S.Name}
    (hσ : S.atomic.EqF p σ σ') (hτ : S.atomic.EqF p τ τ') :
    S.atomic.EqF p (σ.opair τ) (σ'.opair τ') :=
  S.eq_pair_congr (S.eq_pair_congr hσ hσ) (S.eq_pair_congr hσ hτ)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## Orbit -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- Ordinary names in an orbit agree literally when their supporting diagrams
do. This does not define an action on an evaluated symmetric model. -/
theorem smul_name_eq_of_diagram_eq
    (σ : (system (M := M) (I := I) (κ := κ) hμ).Name) (p : Diagram M I)
    (hσ : ∀ g ∈ SupportFilter.Fix p.range, g • σ = σ)
    (π ρ : Equiv.Perm I) (hp : p.permute π = p.permute ρ) : π • σ = ρ • σ := by
  have hg : ρ⁻¹ * π ∈ SupportFilter.Fix p.range := by
    apply (SupportFilter.mem_Fix _ _).mpr
    rintro j ⟨x,rfl⟩
    have hh := congrArg (fun d : Diagram M I => d x) hp
    change π (p x) = ρ (p x) at hh
    change ρ.symm (π (p x)) = p x
    rw [hh,Equiv.symm_apply_apply]
  have hh := congrArg (fun ν => ρ • ν) (hσ _ hg)
  simpa only [mul_smul,smul_inv_smul] using hh

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_LocalQuotients
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Descent -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

/-- Independently placed active copies are equal, for arbitrary-rank names.
A shared third copy transports the given equality into a common extension
of each potential counterexample, using the proved three-copy placement. -/
theorem active_equal_independent [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ v : Diagram M I) (hinter : s₀.range ∩ s₁.range = p.range)
    (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (σ₀ σ₁ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hσ₀ : ∀ g ∈ SupportFilter.Fix s₀.range, g • σ₀ = σ₀)
    (hσ₁ : ∀ g ∈ SupportFilter.Fix s₁.range, g • σ₁ = σ₁)
    (d : CohenForcing.Condition I κ) (hd : d.support ⊆ v.range)
    (heq : (system hμ).atomic.EqF ((d,v) : Poset M I κ) σ₀ σ₁)
    (α β : Equiv.Perm I) (hα : ∀ j ∈ p.range, α j = j) (hβ : ∀ j ∈ p.range, β j = j)
    (hind : (s₀.permute α).range ∩ (s₀.permute β).range = p.range)
    (r : Poset M I κ)
    (hrα : r ≤ permute α (d.restrict s₀.range,s₀))
    (hrβ : r ≤ permute β (d.restrict s₀.range,s₀)) :
    (system hμ).atomic.EqF r (α • σ₀) (β • σ₀) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let : Nonempty (Diagram M I) := ⟨p⟩
  apply S.atomic_regular.1
  intro a har
  obtain ⟨q,hqa⟩ := exists_condition_below a
  have hqα : q ≤ permute α (d.restrict s₀.range,s₀) :=
    WithTop.coe_le_coe.mp (hqa.trans (har.trans hrα))
  have hqβ : q ≤ permute β (d.restrict s₀.range,s₀) :=
    WithTop.coe_le_coe.mp (hqa.trans (har.trans hrβ))
  obtain ⟨π,ρ,hπ,hρ,hπρ,t,htq,htπ,htρ⟩ := descent_comparison_placement hsize hmerger
    p s₀ s₁ v hinter hv₀ hv₁ α β hα hβ hind d q.1 hd q.2 hqα.2 hqβ.2 hqα.1 hqβ.1
  have heqπ := (S.eq_symmetry π ((d,v) : Poset M I κ) σ₀ σ₁).mp heq
  have heqρ := (S.eq_symmetry ρ ((d,v) : Poset M I κ) σ₀ σ₁).mp heq
  rw [show S.move π ((d,v) : Poset M I κ) = (permute π (d,v) : Poset M I κ) from move_coe hμ π _] at heqπ
  rw [show S.move ρ ((d,v) : Poset M I κ) = (permute ρ (d,v) : Poset M I κ) from move_coe hμ ρ _] at heqρ
  have hnameπ := smul_name_eq_of_diagram_eq hμ σ₀ s₀ hσ₀ π α hπ
  have hnameρ := smul_name_eq_of_diagram_eq hμ σ₀ s₀ hσ₀ ρ β hρ
  have hnameπρ := smul_name_eq_of_diagram_eq hμ σ₁ s₁ hσ₁ π ρ hπρ
  rw [hnameπ,hnameπρ] at heqπ
  rw [hnameρ] at heqρ
  exact ⟨t,(WithTop.coe_le_coe.mpr htq).trans hqa,
    S.atomic.eq_trans (S.atomic.eq_mono (WithTop.coe_le_coe.mpr htπ) heqπ)
      (S.atomic.eq_symm (S.atomic.eq_mono (WithTop.coe_le_coe.mpr htρ) heqρ))⟩

/-- Root-preserving translates of a diagram still extend its root. -/
theorem permute_le_root (p s : Diagram M I) (hs : s ≤ p)
    (α : Equiv.Perm I) (hα : ∀ j ∈ p.range, α j = j) : s.permute α ≤ p := by
  have hp := Diagram.permute_eq_of_fixes_range α p hα
  rw [← hp]
  exact (Diagram.permuteOrderIso α).monotone hs

/-- Coherence for arbitrary overlaps. A third independent active copy can
be placed compatibly below every proposed common extension; the independent
comparison then identifies both given copies with that third one. -/
theorem active_equal [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ v : Diagram M I) (hs₀ : s₀ ≤ p)
    (hinter : s₀.range ∩ s₁.range = p.range) (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (σ₀ σ₁ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hσ₀ : ∀ g ∈ SupportFilter.Fix s₀.range, g • σ₀ = σ₀)
    (hσ₁ : ∀ g ∈ SupportFilter.Fix s₁.range, g • σ₁ = σ₁)
    (d : CohenForcing.Condition I κ) (hd : d.support ⊆ v.range)
    (heq : (system hμ).atomic.EqF ((d,v) : Poset M I κ) σ₀ σ₁)
    (α β : Equiv.Perm I) (hα : ∀ j ∈ p.range, α j = j) (hβ : ∀ j ∈ p.range, β j = j)
    (r : Poset M I κ)
    (hrα : r ≤ permute α (d.restrict s₀.range,s₀))
    (hrβ : r ≤ permute β (d.restrict s₀.range,s₀)) :
    (system hμ).atomic.EqF r (α • σ₀) (β • σ₀) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  let : Nonempty (Diagram M I) := ⟨p⟩
  let δ := d.restrict s₀.range
  apply S.atomic_regular.1
  intro a har
  obtain ⟨q,hqa⟩ := exists_condition_below a
  have hqα : q ≤ permute α (δ,s₀) := WithTop.coe_le_coe.mp (hqa.trans (har.trans hrα))
  have hqβ : q ≤ permute β (δ,s₀) := WithTop.coe_le_coe.mp (hqa.trans (har.trans hrβ))
  have hsα : s₀.permute α ≤ p := permute_le_root p s₀ hs₀ α hα
  have hsβ : s₀.permute β ≤ p := permute_le_root p s₀ hs₀ β hβ
  have hqp : q.2 ≤ p := hqα.2.trans hsα
  have hroot : CohenForcing.Condition.Compatible (q.1.restrict p.range) (δ.restrict p.range) := by
    have hδ : (δ.permute α).restrict p.range = δ.restrict p.range :=
      CohenForcing.Condition.restrict_permute_of_fixes α δ hα
    exact CohenForcing.Condition.compatible_iff.mpr
      ⟨q.1,q.1.le_restrict _,hδ ▸ (hqα.1.trans ((δ.permute α).le_restrict _))⟩
  obtain ⟨γ,hγ,hind,t,htq,htγ⟩ := compatible_placement hsize hmerger p q.2 s₀ hqp hs₀ q.1 δ hroot
  have hsγ : s₀.permute γ ≤ p := permute_le_root p s₀ hs₀ γ hγ
  have hαγ : (s₀.permute α).range ∩ (s₀.permute γ).range = p.range := by
    apply Set.Subset.antisymm
    · intro j hj
      exact hind ▸ ⟨Diagram.range_antitone hqα.2 hj.1,hj.2⟩
    · intro j hj
      exact ⟨Diagram.range_antitone hsα hj,Diagram.range_antitone hsγ hj⟩
  have hβγ : (s₀.permute β).range ∩ (s₀.permute γ).range = p.range := by
    apply Set.Subset.antisymm
    · intro j hj
      exact hind ▸ ⟨Diagram.range_antitone hqβ.2 hj.1,hj.2⟩
    · intro j hj
      exact ⟨Diagram.range_antitone hsβ hj,Diagram.range_antitone hsγ hj⟩
  have heαγ := active_equal_independent hμ hsize hmerger p s₀ s₁ v hinter hv₀ hv₁
    σ₀ σ₁ hσ₀ hσ₁ d hd heq α γ hα hγ hαγ t
    (WithTop.coe_le_coe.mpr (htq.trans hqα)) (WithTop.coe_le_coe.mpr htγ)
  have heβγ := active_equal_independent hμ hsize hmerger p s₀ s₁ v hinter hv₀ hv₁
    σ₀ σ₁ hσ₀ hσ₁ d hd heq β γ hβ hγ hβγ t
    (WithTop.coe_le_coe.mpr (htq.trans hqβ)) (WithTop.coe_le_coe.mpr htγ)
  exact ⟨t,(WithTop.coe_le_coe.mpr htq).trans hqa,S.atomic.eq_trans heαγ (S.atomic.eq_symm heβγ)⟩

/-- The unrestricted-rank support intersection lemma, in direct product
forcing form. Both root equalities hold under the respective restrictions
of the original Cohen witness, not under an extra compatibility hypothesis. -/
theorem support_descent [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ v : Diagram M I) (hs₀ : s₀ ≤ p) (hs₁ : s₁ ≤ p)
    (hinter : s₀.range ∩ s₁.range = p.range) (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (σ₀ σ₁ : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hσ₀ : ∀ g ∈ SupportFilter.Fix s₀.range, g • σ₀ = σ₀)
    (hσ₁ : ∀ g ∈ SupportFilter.Fix s₁.range, g • σ₁ = σ₁)
    (d : CohenForcing.Condition I κ)
    (heq : (system hμ).atomic.EqF ((d,v) : Poset M I κ) σ₀ σ₁) :
    ∃ σ : (system (M := M) (I := I) (κ := κ) hμ).Name,
      (∀ g ∈ SupportFilter.Fix p.range, g • σ = σ) ∧
      (system hμ).atomic.EqF ((d.restrict s₀.range,s₀) : Poset M I κ) σ σ₀ ∧
      (system hμ).atomic.EqF ((d.restrict s₁.range,s₁) : Poset M I κ) σ σ₁ := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hv : ∀ π ∈ SupportFilter.Fix v.range, ∀ i : Fin 2,
      π • (![σ₀,σ₁] : Fin 2 → S.Name) i = ![σ₀,σ₁] i := by
    intro π hπ i
    fin_cases i
    · exact supported_mono hμ hv₀ σ₀ hσ₀ π hπ
    · exact supported_mono hμ hv₁ σ₁ hσ₁ π hπ
  have heq' : S.atomic.EqF ((d.restrict v.range,v) : Poset M I κ) σ₀ σ₁ := by
    have hh := forces_iff_restrict hμ hsize hmerger (.equal 0 1) ![σ₀,σ₁] v hv d
    simpa only [Forces,ForcingQuotient.AtomicData.forceFormula_equal,Matrix.cons_val_zero,
      Matrix.cons_val_one] using hh.mp (by
        simpa only [Forces,ForcingQuotient.AtomicData.forceFormula_equal,Matrix.cons_val_zero,
          Matrix.cons_val_one] using heq)
  let H := SupportFilter.Fix p.range
  let f : H → S.Name := fun g => g.val • σ₀
  let a : H → Poset M I κ := fun g =>
    (permute g.val ((d.restrict v.range).restrict s₀.range,s₀) : Poset M I κ)
  have hH : H ∈ S.filter := ⟨p.range,(Diagram.cardinal_range p).trans_le hcard,le_rfl⟩
  have hperm : ∀ g ∈ H, ∀ i, ∃ j, f j = g • f i ∧ a j = S.move g (a i) := by
    intro g hg i
    refine ⟨⟨g * i.val,H.mul_mem hg i.property⟩,?_,?_⟩
    · exact mul_smul g i.val σ₀
    · change (permute (g * i.val) ((d.restrict v.range).restrict s₀.range,s₀) : Poset M I κ) =
        S.move g (permute i.val ((d.restrict v.range).restrict s₀.range,s₀))
      rw [move_coe,permute_mul]
  have hc : ∀ i j q, q ≤ a i → q ≤ a j → S.atomic.EqF q (f i) (f j) := by
    intro i j q hi hj
    exact active_equal hμ hsize hmerger p s₀ s₁ v hs₀ hinter hv₀ hv₁ σ₀ σ₁ hσ₀ hσ₁
      (d.restrict v.range) (d.support_restrict_subset _) heq' i.val j.val
      ((SupportFilter.mem_Fix _ _).mp i.property) ((SupportFilter.mem_Fix _ _).mp j.property)
      q hi hj
  let σ := S.equivariantMix f a H hH hperm
  have hσ : ∀ g ∈ SupportFilter.Fix p.range, g • σ = σ :=
    S.equivariantMix_fixed f a H hH hperm
  have hres (s : Diagram M I) (hvs : v ≤ s) :
      (d.restrict v.range).restrict s.range = d.restrict s.range := by
    ext z
    simp only [CohenForcing.Condition.mem_restrict]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,Diagram.range_antitone hvs h.2⟩,h.2⟩⟩
  have hσ₀' : S.atomic.EqF ((d.restrict s₀.range,s₀) : Poset M I κ) σ σ₀ := by
    have hh := S.eq_equivariantMix_at f a H hH hperm hc 1
    change S.atomic.EqF (a 1) σ (f 1) at hh
    simpa only [a,f,Subgroup.coe_one,permute_one,one_smul,hres s₀ hv₀] using hh
  have heq' : S.atomic.EqF ((d,v) : Poset M I κ) σ σ₁ :=
    S.atomic.eq_trans (S.atomic.eq_mono (WithTop.coe_le_coe.mpr ⟨d.le_restrict _,hv₀⟩) hσ₀') heq
  have hv' : ∀ π ∈ SupportFilter.Fix s₁.range, ∀ i : Fin 2,
      π • (![σ,σ₁] : Fin 2 → S.Name) i = ![σ,σ₁] i := by
    intro π hπ i
    fin_cases i
    · exact supported_mono hμ hs₁ σ hσ π hπ
    · exact hσ₁ π hπ
  refine ⟨σ,hσ,hσ₀',?_⟩
  have hh := forces_at_supporting_root hμ hsize hmerger (.equal 0 1)
    ![σ,σ₁] s₁ v hv₁ hv' d (by
      simpa only [Forces,ForcingQuotient.AtomicData.forceFormula_equal,Matrix.cons_val_zero,
        Matrix.cons_val_one] using heq')
  simpa only [Forces,ForcingQuotient.AtomicData.forceFormula_equal,Matrix.cons_val_zero,
    Matrix.cons_val_one] using hh

end
end PartitionConsistency.ProductForcing


/-! ## LocalName -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Separation retains the literal common support of the bounding name and
all of its parameters. -/
theorem separate_fixed {n} (σ : S.Name) (v : Fin n → S.Name)
    (φ : Formula (n+1)) (g : Γ) (hσ : g • σ = σ) (hv : ∀ i, g • v i = v i) :
    g • S.separate σ v φ = S.separate σ v φ := by
  apply Subtype.ext
  exact S.collectName_fixed _ _ _ (S.separationTest_permute σ v φ) g
    ⟨congrArg Subtype.val hσ,(S.mem_tupleStabilizer v g).mpr hv⟩

/-- Normalizing a subset name does not enlarge its support. -/
theorem normalize_fixed (σ ν : S.Name) (g : Γ)
    (hσ : g • σ = σ) (hν : g • ν = ν) :
    g • S.normalize σ ν = S.normalize σ ν := by
  apply S.separate_fixed σ ![ν] (.mem 1 0) g hσ
  intro i
  fin_cases i
  exact hν

end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable (c : κ → ZFSet.{u})

/-- The normalization bound is the actual set of all pairs of individual
label names with condition codes; there is no bound on the ranks of the
original subsets being represented. -/
theorem labelSet_subsetBound :
    (system (M := M) (I := I) (κ := κ) hμ).subsetBound (labelSet hμ c) =
      (system (M := M) (I := I) (κ := κ) hμ).collectRaw
        (label hμ c) (fun _ _ => True) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨i,p,_,rfl⟩ := (S.mem_collectRaw _ _ z).mp hz
    have hi := i.property
    simp only [labelSet_raw] at hi
    obtain ⟨j,q,_,hj,_⟩ := (S.edge_collectRaw _ _ _ _).mp hi
    exact (S.mem_collectRaw _ _ _).mpr ⟨j,p,True.intro,by rw [hj]; rfl⟩
  · intro hz
    obtain ⟨j,p,_,rfl⟩ := (S.mem_collectRaw _ _ z).mp hz
    have he : ZFSet.pair (label (M := M) hμ c j).raw (S.code ⊤) ∈ (labelSet (M := M) (I := I) hμ c).raw := by
      rw [labelSet_raw]
      exact (S.edge_collectRaw _ _ _ _).mpr ⟨j,⊤,rfl,rfl,rfl⟩
    exact (S.mem_collectRaw _ _ _).mpr
      ⟨⟨((label (M := M) hμ c j).raw,S.code ⊤),he⟩,p,True.intro,rfl⟩

/-- Every normalized candidate is forced to be a subset of the label set,
not just those candidates which happen to be classes for a particular E. -/
theorem normalized_subset_labelSet
    (ν : (system (M := M) (I := I) (κ := κ) hμ).PowerCandidate (labelSet hμ c))
    (p : Poset M I κ) :
    (system hμ).SubsetF p ν.val (labelSet hμ c) := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  intro τ q _ hm
  apply (mem_labelSet hμ c τ q).mpr
  intro s hsq
  obtain ⟨t,hts,ρ,d,he,_,heq⟩ := S.mem_iff.mp hm s hsq
  have hb := ν.property he
  rw [labelSet_subsetBound hμ c] at hb
  obtain ⟨j,_,_,hj,_⟩ := (S.edge_collectRaw _ _ _ _).mp hb
  have hh : label (M := M) hμ c j = ρ := Name.ext hj
  exact ⟨t,hts,j,hh ▸ heq⟩

instance instSmallLocalName (r : Diagram M I) : Small.{u} (LocalName hμ c r) := inferInstanceAs
  (Small.{u} {ν : (system (M := M) (I := I) (κ := κ) hμ).PowerCandidate (labelSet hμ c) //
    ∀ π ∈ SupportFilter.Fix r.range, π • ν.val = ν.val})

/-- Canonical normalization into X(r), for any supported name at any rank. -/
def localNormalize (r : Diagram M I)
    (ν : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hν : ∀ π ∈ SupportFilter.Fix r.range, π • ν = ν) : LocalName hμ c r :=
  ⟨⟨(system hμ).normalize (labelSet hμ c) ν,(system hμ).normalize_bounded _ _⟩,
    fun π hπ => (system hμ).normalize_fixed _ _ π (smul_labelSet hμ c π) (hν π hπ)⟩

theorem localNormalize_eq (r : Diagram M I)
    (ν : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hν : ∀ π ∈ SupportFilter.Fix r.range, π • ν = ν)
    (p : Poset M I κ) (hsub : (system hμ).SubsetF p ν (labelSet hμ c)) :
    (system hμ).atomic.EqF p ν (localNormalize hμ c r ν hν).name :=
  (system hμ).normalize_eq _ _ hsub

/-- Support descent followed by normalization supplies a member of the
*ground set* X(p), with the equalities at the two original supporting roots.
No statement that the descended name is a class is postulated here. -/
theorem localName_descent [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ v : Diagram M I) (hs₀ : s₀ ≤ p) (hs₁ : s₁ ≤ p)
    (hinter : s₀.range ∩ s₁.range = p.range) (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (σ₀ : LocalName hμ c s₀) (σ₁ : LocalName hμ c s₁)
    (d : CohenForcing.Condition I κ)
    (heq : (system hμ).atomic.EqF ((d,v) : Poset M I κ) σ₀.name σ₁.name) :
    ∃ σ : LocalName hμ c p,
      (system hμ).atomic.EqF ((d.restrict s₀.range,s₀) : Poset M I κ) σ.name σ₀.name ∧
      (system hμ).atomic.EqF ((d.restrict s₁.range,s₁) : Poset M I κ) σ.name σ₁.name := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  obtain ⟨ν,hν,hν₀,hν₁⟩ := support_descent hμ hcard hsize hmerger p s₀ s₁ v hs₀ hs₁
    hinter hv₀ hv₁ σ₀.name σ₁.name σ₀.fixed σ₁.fixed d heq
  have hn (i : Poset M I κ) (σ : S.PowerCandidate (labelSet hμ c))
      (hi : S.atomic.EqF i ν σ.val) :
      S.atomic.EqF i (localNormalize hμ c p ν hν).name σ.val := by
    have hsub : S.SubsetF i ν (labelSet hμ c) :=
      (S.subset_congr hi (S.atomic.eq_refl i (labelSet hμ c))).mpr
        (normalized_subset_labelSet hμ c σ i)
    exact S.atomic.eq_trans (S.atomic.eq_symm (localNormalize_eq hμ c p ν hν i hsub)) hi
  exact ⟨localNormalize hμ c p ν hν,hn _ σ₀.val hν₀,hn _ σ₁.val hν₁⟩

end
end PartitionConsistency.ProductForcing


/-! ## LocalQuotient -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable {c : κ → ZFSet.{u}}

instance instSmallLocalQuotient (F : GenericFilter (CohenForcing.Condition I κ)) (r : Diagram M I) :
    Small.{u} (LocalQuotient (c := c) hμ F r) :=
  small_of_surjective (Quotient.mk'_surjective (s := localSetoid (c := c) hμ F r))

namespace LocalQuotient
variable {hμ}
variable (F : GenericFilter (CohenForcing.Condition I κ))

theorem ofName_eq {r : Diagram M I} (σ τ : LocalName hμ c r) :
    ofName F σ = ofName F τ ↔ (localAtomic hμ r).EqG F σ.name τ.name :=
  Quotient.eq

/-- Local decision prevents a stronger diagram from identifying distinct
local classes. No genericity hypothesis on F is needed for this direction. -/
theorem restrict_injective [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    {r s : Diagram M I} (hsr : s ≤ r) :
    Function.Injective (restrict (c := c) (hμ := hμ) F hsr) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h σ =>
    induction y using Quotient.inductionOn with
    | h τ =>
      intro h
      obtain ⟨d,hd,heq⟩ := (ofName_eq F (σ.restrict hsr) (τ.restrict hsr)).mp h
      apply (ofName_eq F σ τ).mpr
      refine ⟨d.restrict r.range,F.lower (d.le_restrict _) hd,?_⟩
      have hfix : ∀ π ∈ SupportFilter.Fix r.range, ∀ i : Fin 2,
          π • (![σ.name,τ.name] : Fin 2 → (system hμ).Name) i = ![σ.name,τ.name] i := by
        intro π hπ i
        fin_cases i
        · exact σ.fixed π hπ
        · exact τ.fixed π hπ
      have hh := forces_at_supporting_root hμ hsize hmerger (.equal 0 1)
        ![σ.name,τ.name] r s hsr hfix d (by exact heq)
      exact hh

/-- The intersection property of local symbolic subsets. This is the
quotient-level consequence of the proved arbitrary-rank support descent. -/
theorem intersection [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (p s₀ s₁ v : Diagram M I) (hs₀ : s₀ ≤ p) (hs₁ : s₁ ≤ p)
    (hinter : s₀.range ∩ s₁.range = p.range) (hv₀ : v ≤ s₀) (hv₁ : v ≤ s₁)
    (x₀ : LocalQuotient (c := c) hμ F s₀) (x₁ : LocalQuotient (c := c) hμ F s₁)
    (heq : restrict F hv₀ x₀ = restrict F hv₁ x₁) :
    ∃ x : LocalQuotient (c := c) hμ F p,
      restrict F hs₀ x = x₀ ∧ restrict F hs₁ x = x₁ := by
  induction x₀ using Quotient.inductionOn with
  | h σ₀ =>
    induction x₁ using Quotient.inductionOn with
    | h σ₁ =>
      obtain ⟨d,hd,heq⟩ := (ofName_eq F (σ₀.restrict hv₀) (σ₁.restrict hv₁)).mp heq
      obtain ⟨σ,hσ₀,hσ₁⟩ := localName_descent hμ c hcard hsize hmerger p s₀ s₁ v hs₀ hs₁
        hinter hv₀ hv₁ σ₀ σ₁ d heq
      exact ⟨ofName F σ,(ofName_eq F _ _).mpr
        ⟨d.restrict s₀.range,F.lower (d.le_restrict _) hd,hσ₀⟩,
        (ofName_eq F _ _).mpr ⟨d.restrict s₁.range,F.lower (d.le_restrict _) hd,hσ₁⟩⟩

end LocalQuotient

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_LocalRecords
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Record -/


/-! The ground record calculation for local quotients. These results count
literal witnesses of local representation by a covariant family of names.
They do not assume that every normalized subset is such a class, or assert
that every local E-class has a witness without the forcing argument. -/


/-! ## Class -/


namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- Every separation name is a normalization over the bounding name. -/
theorem separate_bounded {n} (σ : S.Name) (v : Fin n → S.Name) (φ : Formula (n+1)) :
    (S.separate σ v φ).raw ⊆ S.subsetBound σ := by
  intro z hz
  change z ∈ S.collectRaw (fun i : Edges σ.raw => σ.child i.property)
    (S.separationTest σ v φ) at hz
  obtain ⟨i,p,_,he⟩ := (S.mem_collectRaw _ _ _).mp hz
  exact (S.mem_collectRaw (fun i : Edges σ.raw => σ.child i.property)
    (fun _ _ => True) _).mpr ⟨i,p,True.intro,he⟩

theorem relationClass_bounded (A E x : S.Name) :
    (S.relationClass A E x).raw ⊆ S.subsetBound A :=
  S.separate_bounded A ![E,x] (SetLanguage.edge 0 1 2)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

def localLabelClass (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix r.range, π • E = E) (j : I) (hj : j ∈ r.range) :
    LocalName hμ c r :=
  ⟨⟨labelClass hμ c E j,(system hμ).relationClass_bounded _ _ _⟩,by
    intro π hπ
    rw [labelClass_move,hE π hπ,(SupportFilter.mem_Fix _ _).mp hπ j hj]⟩

end
end PartitionConsistency.ProductForcing


/-! ## Availability -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable {c : κ → ZFSet.{u}}

/-- The normalized names and the proved support descent instantiate the
intersection calculus. Eligibility as an E-class is a later subcollection. -/
def allLocalSystem [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (F : GenericFilter (CohenForcing.Condition I κ)) :
    LocalDiagramSystem.System.{u,u+1} M I where
  Obj := LocalQuotient (c := c) hμ F
  restrict := LocalQuotient.restrict F
  restrict_refl := LocalQuotient.restrict_refl F
  restrict_comp := LocalQuotient.restrict_restrict F
  injective := LocalQuotient.restrict_injective F hsize hmerger
  intersection := LocalQuotient.intersection F hcard hsize hmerger

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_AvailableRecords
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.Arrow.instSubsingleton _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Eligible -/


namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

theorem eligible_restrict (F : GenericFilter (CohenForcing.Condition I κ))
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) {r s : Diagram M I} (hsr : s ≤ r)
    (x : LocalQuotient (c := c) hμ F r) (hx : Eligible hμ c F r E x) :
    Eligible hμ c F s E (LocalQuotient.restrict F hsr x) := by
  induction x using Quotient.inductionOn with
  | h τ =>
    obtain ⟨d,hd,he⟩ := hx
    exact ⟨d,hd,(system hμ).atomic.forceFormula_mono
      (p := ((d,r) : Poset M I κ)) (q := ((d,s) : Poset M I κ))
      (WithTop.coe_le_coe.mpr ⟨le_rfl,hsr⟩) he⟩

/-- Decision of the class test at its supporting root reflects eligibility
from every stronger diagram. No assertion of E being an equivalence relation
or of nonwellorderability is needed for this logical step. -/
theorem eligible_restrict_iff [Infinite M] [Infinite I]
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (F : GenericFilter (CohenForcing.Condition I κ)) (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    {r s : Diagram M I} (hsr : s ≤ r)
    (hE : ∀ π ∈ SupportFilter.Fix r.range, π • E = E)
    (x : LocalQuotient (c := c) hμ F r) :
    Eligible hμ c F s E (LocalQuotient.restrict F hsr x) ↔ Eligible hμ c F r E x := by
  constructor
  · induction x using Quotient.inductionOn with
    | h τ =>
      rintro ⟨d,hd,hf⟩
      refine ⟨d.restrict r.range,F.lower (d.le_restrict _) hd,?_⟩
      apply forces_at_supporting_root hμ hsize hmerger (SetLanguage.isClass 0 1 2)
        ![τ.name,labelSet hμ c,E] r s hsr ?_ d hf
      intro π hπ i
      fin_cases i
      · exact τ.fixed π hπ
      · exact smul_labelSet hμ c π
      · exact hE π hπ
  · exact eligible_restrict hμ c F E hsr x

/-- A genuinely dense set of Cohen conditions giving literal local records.
The diagram may be strengthened and the condition's support put in it. -/
def classRepresentationSet (r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (τ : LocalName hμ c r) : Set (CohenForcing.Condition I κ) :=
  {d | ∃ t : Diagram M I, t ≤ r ∧ d.support ⊆ t.range ∧ ∃ j ∈ t.range,
    (system hμ).atomic.EqF ((d,t) : Poset M I κ) τ.name (labelClass hμ c E j)}

end
end PartitionConsistency.ProductForcing


/-! ## ActualAvailability -/

namespace PartitionConsistency.DiagramForcing.Diagram
universe u
variable {M I : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]

/-- Among two subdiagrams of the same larger diagram, range containment
reflects the diagram order. Common embeddability is essential here. -/
theorem le_of_common_and_range {t r s : Diagram M I} (htr : t ≤ r) (hts : t ≤ s)
    (hrs : s.range ⊆ r.range) : r ≤ s := by
  obtain ⟨a,rfl⟩ := htr
  obtain ⟨b,rfl⟩ := hts
  obtain ⟨c,hc⟩ := hrs (show t b ∈ (t.sub b).range by exact ⟨1,by simp⟩)
  have hab : a*c = b := t.injective hc
  exact ⟨c,by rw [sub_sub,hab]⟩

/-- An exact intersection of two roots which both extend q still extends q. -/
theorem intersection_le_root {p s₀ s₁ q : Diagram M I}
    (hs₀ : s₀ ≤ p) (h₀q : s₀ ≤ q) (h₁q : s₁ ≤ q)
    (hinter : s₀.range ∩ s₁.range = p.range) : p ≤ q := by
  apply le_of_common_and_range hs₀ h₀q
  rw [← hinter]
  exact fun _ h => ⟨range_antitone h₀q h,range_antitone h₁q h⟩

end PartitionConsistency.DiagramForcing.Diagram

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- The actual symbolic class system below q. Outside the cone below q the
object type is empty, so no meaningless eligibility assertions are needed.
All maps retain representative names and all axioms are proved. -/
def eligibleSystem [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ)
    (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
    (F : GenericFilter (CohenForcing.Condition I κ)) (q : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E) :
    LocalDiagramSystem.System.{u,u+1} M I where
  Obj r := {x : LocalQuotient (c := c) hμ F r // r ≤ q ∧ Eligible hμ c F r E x}
  restrict hsr x := ⟨LocalQuotient.restrict F hsr x.val,
    hsr.trans x.property.1,eligible_restrict hμ c F E hsr x.val x.property.2⟩
  restrict_refl x := Subtype.ext (LocalQuotient.restrict_refl F x.val)
  restrict_comp hsr hts x := Subtype.ext (LocalQuotient.restrict_restrict F hsr hts x.val)
  injective := by
    intro r s hsr x y h
    exact Subtype.ext (LocalQuotient.restrict_injective F hsize hmerger hsr
      (congrArg Subtype.val h))
  intersection p s₀ s₁ t hs₀ hs₁ hinter ht₀ ht₁ x₀ x₁ heq := by
    have hpq := Diagram.intersection_le_root hs₀ x₀.property.1 x₁.property.1 hinter
    obtain ⟨x,hx₀,hx₁⟩ := LocalQuotient.intersection F hcard hsize hmerger
      p s₀ s₁ t hs₀ hs₁ hinter ht₀ ht₁ x₀.val x₁.val (congrArg Subtype.val heq)
    have hel : Eligible hμ c F p E x := by
      apply (eligible_restrict_iff hμ c hsize hmerger F E hs₀
        (supported_mono hμ hpq E hE) x).mp
      rw [hx₀]
      exact x₀.property.2
    exact ⟨⟨x,hpq,hel⟩,Subtype.ext hx₀,Subtype.ext hx₁⟩

end
end PartitionConsistency.ProductForcing


/-! ## Contraction -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_ComponentGluing
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.instMulActionSubtypePermMemSubgroupRootGroup _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Component -/

namespace PartitionConsistency.LocalDiagramSystem
universe u v
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]

namespace Vertex
variable {q : Diagram M I}

namespace Arrow
variable {v w z : Vertex q}

/-- There is no nontrivial identity-index contraction. -/
theorem eq_of_index_one (f : Arrow v w) (h : f.index = 1) : v = w := by
  rcases v with ⟨r,a,hr,U⟩
  rcases w with ⟨s,b,hs,V⟩
  have hrs : r = s := by simpa only [h,Diagram.sub_one] using f.diagram
  subst s
  have hab : a = b := Diagram.index_unique (hr.trans hs.symm)
  subst b
  have hUV : U = V := by
    apply ConeIdeal.ext
    ext x
    have hh := f.ideal x
    rw [h] at hh
    exact (iff_of_eq (congrArg (fun y : LeftDivOrder M => y ∈ U.carrier)
      (one_mul x).symm)).trans hh.symm
  subst V
  rfl

end Arrow

namespace Common

theorem of_arrow {v w : Vertex q} (f : Arrow v w) : Common v w :=
  ⟨w,⟨f⟩,⟨Arrow.id w⟩⟩

end Common

/-- A countable cofinal sequence in the bounded ideal yields a countable
cofinal chain in the *entire* component. The target is not limited to the
successors of the one initially selected vertex. -/
theorem component_cofinal_chain (hj : HasConditionalJoins (LeftDivOrder M))
    (H : HeightCost (LeftDivOrder M)) (v : Vertex q) :
    ∃ f : ℕ → Vertex q, f 0 = v ∧
      (∀ i j, i ≤ j → Nonempty (Arrow (f i) (f j))) ∧
      (∀ i, Common v (f i)) ∧
      ∀ w, Common v w → ∃ i, Nonempty (Arrow w (f i)) := by
  classical
  obtain ⟨n,hn₀,hnU,hnmono,hncof⟩ := v.ideal.countable_cofinal_sequence H hj
  choose f g hg using fun i => v.exists_contraction (n i) (hnU i)
  refine ⟨f,(g 0).eq_of_index_one ((hg 0).trans hn₀) |>.symm,?_,?_,?_⟩
  · intro i j hij
    exact (g i).between (g j) (by rw [hg i,hg j]; exact hnmono hij)
  · intro i
    exact Common.of_arrow (g i)
  · intro w hw
    obtain ⟨t,⟨a⟩,⟨b⟩⟩ := hw
    obtain ⟨i,hi⟩ := hncof a.index a.mem
    obtain ⟨c⟩ := a.between (g i) (by rw [hg i]; exact hi)
    exact ⟨i,⟨b.comp c⟩⟩

end Vertex
end PartitionConsistency.LocalDiagramSystem


/-! ## FiberMap -/


/-! ## Gluing -/

namespace PartitionConsistency.LocalDiagramSystem.System
universe u v
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable (D : System.{u,v} M I) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}

/-- The canonical fiber identifications commute with the gluing maps. -/
theorem toGlued_arrow (root w z : Vertex q) (hw : Vertex.Common root w)
    (hz : Vertex.Common root z) (f : w.Arrow z) (x : D.vertexFiber z) :
    D.toGlued hj root w hw (D.arrowMap hj f x) = D.toGlued hj root z hz x := by
  apply Quotient.sound
  exact ⟨z,f,Vertex.Arrow.id z,x,rfl,D.arrowMap_id hj _ _⟩

end PartitionConsistency.LocalDiagramSystem.System

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_ConcreteSystem
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CardinalParameters -/


/-! ## Instance -/


/-! ## LabelFiber -/

namespace PartitionConsistency.LocalDiagramSystem
universe u
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
noncomputable section

/-- Label availability is literal membership in the subdiagram range. -/
theorem label_available_iff (r : Diagram M I) (j : r.range) (n : M) :
    (labelSystem (M := M) (I := I)).Available r j n ↔ j.val ∈ (r.sub n).range := by
  constructor
  · rintro ⟨k,hk⟩
    exact (congrArg Subtype.val hk) ▸ k.property
  · intro hj
    exact ⟨⟨j.val,hj⟩,rfl⟩

/-- The availability test at a center is precisely left divisibility. -/
theorem label_available_center (r : Diagram M I) (k n : M) :
    (labelSystem (M := M) (I := I)).Available r ⟨r k,⟨k,rfl⟩⟩ n ↔ n ∣ k := by
  rw [label_available_iff]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,(r.injective hx).symm⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,congrArg r hx.symm⟩

/-- A probe profile supplies a genuine exact-fiber label, rather than merely
an element of the ambient label range. -/
def labelFiberEmbedding {q : Diagram M I} (w : Vertex q) {K : Type u}
    (m : K → M) (hinj : Function.Injective m)
    (hprofile : ∀ i (x : M), x ∣ w.index ∧ x ∣ m i ↔ x ∈ w.ideal.carrier) :
    K ↪ (labelSystem (M := M) (I := I)).vertexFiber w where
  toFun i := ⟨⟨w.diagram (m i),⟨m i,rfl⟩⟩,by
    apply ConeIdeal.ext
    ext n
    change n ≤ w.index ∧ (labelSystem (M := M) (I := I)).Available
      w.diagram ⟨w.diagram (m i),⟨m i,rfl⟩⟩ n ↔ _
    erw [label_available_center,LeftDivOrder.le_iff_dvd]
    exact hprofile i n⟩
  inj' := by
    intro i j h
    apply hinj
    apply w.diagram.injective
    exact congrArg (fun z : (labelSystem (M := M) (I := I)).vertexFiber w => z.val.val) h

theorem labelFiberSet_subset {q : Diagram M I} (w : Vertex q) :
    labelFiberSet w ⊆ w.diagram.range := by
  rintro _ ⟨x,rfl⟩
  exact x.val.property

end
end PartitionConsistency.LocalDiagramSystem


/-! ## Stabilizer -/

namespace PartitionConsistency.LocalDiagramSystem.Vertex
universe u
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {q : Diagram M I}
noncomputable section

theorem common_moved (hj : HasConditionalJoins (LeftDivOrder M)) (v : Vertex q)
    (π : componentStabilizer hj v) {w : Vertex q} (hw : Common v w) :
    Common v (π.val • w) := π.property.trans hj (hw.move π.val)

/-- Chains are constructed from the height-cost theorem, not postulated
when they are used with the saturated monoid. -/
theorem exists_chain (hj : HasConditionalJoins (LeftDivOrder M))
    (H : HeightCost (LeftDivOrder M)) (v : Vertex q) : Nonempty (Chain v) := by
  obtain ⟨f,hf,hm,_,hc⟩ := component_cofinal_chain hj H v
  exact ⟨⟨f,hf,hm,hc⟩⟩

namespace Chain
variable {v : Vertex q} (C : Chain v)

theorem common (i : ℕ) : Common v (C.vertex i) := by
  have h := Common.of_arrow (C.increasing 0 i (Nat.zero_le i)).some
  rwa [C.first] at h

theorem ranges_antitone : Antitone (fun i => (C.vertex i).diagram.range) := by
  intro i j hij
  obtain ⟨f⟩ := C.increasing i j hij
  exact Diagram.range_antitone (show (C.vertex i).diagram ≤ (C.vertex j).diagram from
    ⟨f.index,f.diagram⟩)

/-- The increasing union of pointwise tail fixers, regarded inside the actual
component stabilizer. -/
def tailFixer (hj : HasConditionalJoins (LeftDivOrder M)) :
    Subgroup (componentStabilizer hj v) where
  carrier := {π | ∃ i, ∀ j ∈ (C.vertex i).diagram.range, π.val.val j = j}
  one_mem' := ⟨0,fun _ _ => rfl⟩
  mul_mem' := by
    rintro π σ ⟨i,hi⟩ ⟨k,hk⟩
    refine ⟨max i k,?_⟩
    intro j hj
    change π.val.val (σ.val.val j) = j
    rw [hk j (C.ranges_antitone (le_max_right _ _) hj),hi j (C.ranges_antitone (le_max_left _ _) hj)]
  inv_mem' := by
    rintro π ⟨i,hi⟩
    refine ⟨i,?_⟩
    intro j hj
    change π.val.val.symm j = j
    exact π.val.val.symm_apply_eq.mpr (hi j hj).symm

/-- Membership is eventual pointwise fixation, not a condition on an assigned
bijection or on the result of the quotient construction. -/
theorem mem_tailFixer (hj : HasConditionalJoins (LeftDivOrder M))
    (π : componentStabilizer hj v) : π ∈ C.tailFixer hj ↔
      ∃ i, ∀ j ∈ (C.vertex i).diagram.range, π.val.val j = j := Iff.rfl

/-- A permutation fixing a chain diagram belongs to the component stabilizer.
This justifies viewing the displayed union of full fixers inside that group. -/
theorem fixes_mem_stabilizer (hj : HasConditionalJoins (LeftDivOrder M))
    (π : RootGroup q) (i : ℕ)
    (h : ∀ j ∈ (C.vertex i).diagram.range, π.val j = j) :
    π ∈ componentStabilizer hj v := by
  have hf : π • C.vertex i = C.vertex i := by
    have he := Diagram.permute_eq_of_fixes_range π.val (C.vertex i).diagram h
    have hperm : ∀ (w : Vertex q), w.diagram.permute π.val = w.diagram → π • w = w := by
      rintro ⟨r,a,hr,U⟩ he
      change ({diagram := r.permute π.val,index := a,root := _,ideal := U} : Vertex q) = _
      simp only [he]
    exact hperm _ he
  exact (C.common i).trans hj (by simpa only [hf] using ((C.common i).move π).symm)

/-- Cofinality of the chain makes the union of its tail fixers normal. The
conjugating permutation is allowed to move the entire chain. -/
instance tailFixer_normal (hj : HasConditionalJoins (LeftDivOrder M)) :
    (C.tailFixer hj).Normal where
  conj_mem := by
    rintro k ⟨i,hi⟩ σ
    obtain ⟨j,⟨f⟩⟩ := C.cofinal (σ.val • C.vertex i) (common_moved hj v σ (C.common i))
    refine ⟨j,?_⟩
    intro x hx
    have himage : x ∈ ((C.vertex i).diagram.permute σ.val.val).range :=
      Diagram.range_antitone (show (σ.val • C.vertex i).diagram ≤ (C.vertex j).diagram from
        ⟨f.index,f.diagram⟩) hx
    rw [Diagram.range_permute] at himage
    obtain ⟨y,hy,rfl⟩ := himage
    change σ.val.val (k.val.val (σ.val.val.symm (σ.val.val y))) = σ.val.val y
    rw [Equiv.symm_apply_apply,hi y hy]

end Chain
end
end PartitionConsistency.LocalDiagramSystem.Vertex

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_QuotientTransport
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Transport -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- Literal name transport is a bijection of the whole ground collection,
including the support and normalization requirements. -/
def LocalName.transportEquiv (π : Equiv.Perm I) (r : Diagram M I) :
    LocalName hμ c r ≃ LocalName hμ c (r.permute π) where
  toFun := LocalName.transport hμ π
  invFun σ := (σ.transport hμ π⁻¹).rebase hμ c (r.permute_inv_permute π)
  left_inv σ := by
    apply LocalName.ext
    change π⁻¹ • (π • σ.name) = σ.name
    exact inv_smul_smul π σ.name
  right_inv σ := by
    apply LocalName.ext
    change π • (π⁻¹ • σ.name) = σ.name
    exact smul_inv_smul π σ.name

variable {c hμ}

/-- Equality of local names is preserved and reflected between the original
filter and the moved filter. Only actual product-forcing symmetry is used. -/
theorem local_eq_transport_iff (F : GenericFilter (CohenForcing.Condition I κ))
    (π : Equiv.Perm I) (r : Diagram M I) (σ τ : LocalName hμ c r) :
    (localAtomic hμ (r.permute π)).EqG
        (F.move (CohenForcing.Condition.permuteOrderIso π))
        (σ.transport hμ π).name (τ.transport hμ π).name ↔
      (localAtomic hμ r).EqG F σ.name τ.name := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  constructor
  · rintro ⟨d,hd,he⟩
    change S.atomic.EqF ((OrderDual.ofDual d,r.permute π) : Poset M I κ) (π • σ.name) (π • τ.name) at he
    refine ⟨(OrderDual.ofDual d).permute π⁻¹,hd,?_⟩
    apply (S.eq_symmetry π (((OrderDual.ofDual d).permute π⁻¹,r) : Poset M I κ) σ.name τ.name).mpr
    simpa only [S,move_coe,permute,CohenForcing.Condition.permute_permute_inv] using he
  · rintro ⟨d,hd,he⟩
    change S.atomic.EqF ((OrderDual.ofDual d,r) : Poset M I κ) σ.name τ.name at he
    change ∃ d, d ∈ F.move (CohenForcing.Condition.permuteOrderIso π) ∧
      S.atomic.EqF ((OrderDual.ofDual d,r.permute π) : Poset M I κ) (π • σ.name) (π • τ.name)
    refine ⟨(OrderDual.ofDual d).permute π,(GenericFilter.mem_move F _ d).mpr hd,?_⟩
    change S.atomic.EqF (((OrderDual.ofDual d).permute π,r.permute π) : Poset M I κ) (π • σ.name) (π • τ.name)
    simpa only [S,move_coe,permute] using
      (S.eq_symmetry π ((OrderDual.ofDual d,r) : Poset M I κ) σ.name τ.name).mp he

namespace LocalQuotient
variable (F : GenericFilter (CohenForcing.Condition I κ))

theorem transport_injective (π : Equiv.Perm I) (r : Diagram M I) :
    Function.Injective (transport (c := c) hμ F π (r := r)) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h σ =>
    induction y using Quotient.inductionOn with
    | h τ =>
      intro h
      apply (ofName_eq F σ τ).mpr
      exact (local_eq_transport_iff F π r σ τ).mp (Quotient.exact h)

theorem transport_surjective (π : Equiv.Perm I) (r : Diagram M I) :
    Function.Surjective (transport (c := c) hμ F π (r := r)) := by
  intro x
  induction x using Quotient.inductionOn with
  | h τ =>
    obtain ⟨σ,rfl⟩ := (LocalName.transportEquiv hμ c π r).surjective τ
    exact ⟨ofName F σ,rfl⟩

/-- Source (symbolic-transport) is a genuine equivalence, not only a map.
It does not assert an automorphism of one fixed interpreted model. -/
def transportEquiv (π : Equiv.Perm I) (r : Diagram M I) :
    LocalQuotient (c := c) hμ F r ≃
      LocalQuotient (c := c) hμ (F.move (CohenForcing.Condition.permuteOrderIso π)) (r.permute π) :=
  Equiv.ofBijective (transport hμ F π) ⟨transport_injective F π r,transport_surjective F π r⟩

end LocalQuotient

/-- Eligibility uses the moved equivalence-relation name and the moved
filter; the set of Cohen labels itself is fixed by coordinate permutations. -/
theorem eligibleName_coordinate_transport (F : GenericFilter (CohenForcing.Condition I κ))
    (π : Equiv.Perm I) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (τ : LocalName hμ c r) :
    EligibleName hμ c (F.move (CohenForcing.Condition.permuteOrderIso π))
        (r.permute π) (π • E) (τ.transport hμ π) ↔
      EligibleName hμ c F r E τ := by
  let S := system (M := M) (I := I) (κ := κ) hμ
  have hv : (fun i => π • (![τ.name,labelSet hμ c,E] : Fin 3 → S.Name) i) =
      ![π • τ.name,labelSet hμ c,π • E] := by
    apply funext
    intro i
    fin_cases i
    · rfl
    · exact smul_labelSet (M := M) (I := I) hμ c π
    · rfl
  constructor
  · rintro ⟨d,hd,hf⟩
    refine ⟨d.permute π⁻¹,hd,?_⟩
    apply (S.forces_symmetry π (SetLanguage.isClass 0 1 2)
      ![τ.name,labelSet hμ c,E] ((d.permute π⁻¹,r) : Poset M I κ)).mpr
    simpa only [hv,S,move_coe,permute,CohenForcing.Condition.permute_permute_inv,LocalName.transport_name] using hf
  · rintro ⟨d,hd,hf⟩
    refine ⟨d.permute π,(GenericFilter.mem_move F _ d).mpr hd,?_⟩
    simpa only [hv,S,move_coe,permute,LocalName.transport_name] using
      (S.forces_symmetry π (SetLanguage.isClass 0 1 2)
        ![τ.name,labelSet hμ c,E] ((d,r) : Poset M I κ)).mp hf

theorem eligible_coordinate_transport (F : GenericFilter (CohenForcing.Condition I κ))
    (π : Equiv.Perm I) (r : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) (x : LocalQuotient (c := c) hμ F r) :
    Eligible hμ c (F.move (CohenForcing.Condition.permuteOrderIso π))
        (r.permute π) (π • E) (LocalQuotient.transport hμ F π x) ↔
      Eligible hμ c F r E x := by
  induction x using Quotient.inductionOn with
  | h τ => exact eligibleName_coordinate_transport F π r E τ

end
end PartitionConsistency.ProductForcing


/-! ## SystemTransport -/

/-!
Naturality of the exact fibers and the glued component under relabeling.
These are assertions about the genuine local quotient systems, not choices
of fiber bijections. In the application the source and target generics differ.
-/
namespace PartitionConsistency.LocalDiagramSystem
universe u v w
open DiagramForcing DiagramOrder
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]

namespace ReindexIso
variable {D : System.{u,v} M I} {E : System.{u,w} M I} {π : Equiv.Perm I}
variable (T : ReindexIso D E π)

variable {q : Diagram M I} (g : Vertex.RootGroup q)
variable (T : ReindexIso D E g.val)

/-- Every contraction and its transported contraction give the same map
on symbolic elements after transport. -/
theorem fiberEquiv_arrow (hj : HasConditionalJoins (LeftDivOrder M))
    {a b : Vertex q} (f : a.Arrow b) (x : D.vertexFiber b) :
    T.fiberEquiv g a (D.arrowMap hj f x) =
      E.arrowMap hj (f.move g) (T.fiberEquiv g b x) := by
  apply Subtype.ext
  exact T.natural (show a.diagram ≤ b.diagram from ⟨f.index,f.diagram⟩) x.val

/-- Naturality on the *whole* component. In particular the root-fiber
construction of `gluedEquiv` does not make independent choices at vertices. -/
theorem gluedEquiv_toGlued (hj : HasConditionalJoins (LeftDivOrder M))
    (a b : Vertex q) (hb : Vertex.Common a b) (x : D.vertexFiber b) :
    T.gluedEquiv g hj a (D.toGlued hj a b hb x) =
      E.toGlued hj (g • a) (g • b) (hb.move g) (T.fiberEquiv g b x) := by
  obtain ⟨t,⟨f⟩,⟨h⟩⟩ := (show Vertex.Common a b from hb)
  obtain ⟨z,rfl⟩ := (D.arrowMap_bijective hj h).2 x
  have hat : Vertex.Common a t := Vertex.Common.of_arrow f
  have hleft : D.toGlued hj a b hb (D.arrowMap hj h z) =
      D.toGlued hj a a (Vertex.Common.refl a) (D.arrowMap hj f z) :=
    (D.toGlued_arrow hj a b t hb hat h z).trans
      (D.toGlued_arrow hj a a t (Vertex.Common.refl a) hat f z).symm
  rw [hleft,T.gluedEquiv_root,T.fiberEquiv_arrow,T.fiberEquiv_arrow]
  exact (E.toGlued_arrow hj (g • a) (g • a) (g • t)
    (Vertex.Common.refl (g • a)) (hat.move g) (f.move g) (T.fiberEquiv g t z)).trans
      (E.toGlued_arrow hj (g • a) (g • b) (g • t)
        (hb.move g) (hat.move g) (h.move g) (T.fiberEquiv g t z)).symm

end ReindexIso
end PartitionConsistency.LocalDiagramSystem

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- The source and target here are the actual systems of eligible classes.
Transport of the filter, names and diagrams supplies every axiom of the
reindexing isomorphism. Since the permutation fixes q, it fixes E literally. -/
def eligibleSystemTransport [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (F : GenericFilter (CohenForcing.Condition I κ))
    (q : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E) (π : Vertex.RootGroup q) :
    ReindexIso (eligibleSystem hμ c hcard hsize hmerger F q E hE)
      (eligibleSystem hμ c hcard hsize hmerger
        (F.move (CohenForcing.Condition.permuteOrderIso π.val)) q E hE) π.val where
  app r := (LocalQuotient.transportEquiv (c := c) (hμ := hμ) F π.val r).subtypeEquiv
    (fun x => by
      have hq : q.permute π.val = q :=
        Diagram.permute_eq_of_fixes_range _ _ ((SupportFilter.mem_Fix _ _).mp π.property)
      have hle : r ≤ q ↔ r.permute π.val ≤ q := by
        constructor
        · intro hr
          have hr' : r.permute π.val ≤ q.permute π.val :=
            (Diagram.permuteOrderIso π.val).monotone hr
          simpa only [hq] using hr' 
        · intro hr
          apply (Diagram.permuteOrderIso π.val).le_iff_le.mp
          change r.permute π.val ≤ q.permute π.val
          simpa only [hq] using hr
      have hel := eligible_coordinate_transport F π.val r E x
      rw [hE π.val π.property] at hel
      exact and_congr hle hel.symm)
  natural hsr x := Subtype.ext (LocalQuotient.transport_restrict F π.val hsr x.val)

end
end PartitionConsistency.ProductForcing


/-! ## ComponentRebase -/

/-! Canonical change of the chosen root of a glued component.  These maps
retain each representative literally and have no auxiliary choices. -/

namespace PartitionConsistency.LocalDiagramSystem.ReindexIso
universe u v w
open DiagramForcing DiagramOrder
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {D : System.{u,v} M I} {E : System.{u,w} M I}
variable {q : Diagram M I} (g : Vertex.RootGroup q) (T : ReindexIso D E g.val)
variable (hj : HasConditionalJoins (LeftDivOrder M))
noncomputable section

/-- If g stabilizes the component, transport is an equivalence to the
symbolic component at the original chosen root of the *moved* system. -/
def componentEquiv (a : Vertex q) (ha : Vertex.Common a (g • a)) :
    D.Glued hj a ≃ E.Glued hj a :=
  (T.gluedEquiv g hj a).trans (E.rebaseGlued hj ha.symm)

theorem componentEquiv_toGlued (a b : Vertex q) (ha : Vertex.Common a (g • a))
    (hb : Vertex.Common a b) (x : D.vertexFiber b) :
    T.componentEquiv g hj a ha (D.toGlued hj a b hb x) =
      E.toGlued hj a (g • b) (ha.trans hj (hb.move g)) (T.fiberEquiv g b x) := by
  change E.rebaseGlued hj ha.symm (T.gluedEquiv g hj a (D.toGlued hj a b hb x)) = _
  rw [T.gluedEquiv_toGlued,System.rebaseGlued_toGlued]

end
end PartitionConsistency.LocalDiagramSystem.ReindexIso

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_TailGraphs
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## TailCode -/

/-! Codes for actual symbolic classes along a component chain.  The
representing relation ignores a finite prefix and is covariant under each
eventual pointwise fixer, with the *same* code at the moved Cohen filter. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- The ground code set in the paper: at position i a literal local
normalized name supported on the i-th chain diagram. -/
def ChainCode {q : Diagram M I} {v : Vertex q} (C : Vertex.Chain v) :=
  ∀ i, LocalName hμ c (C.vertex i).diagram

instance instSmallChainCode {q : Diagram M I} {v : Vertex q} (C : Vertex.Chain v) :
    Small.{u} (ChainCode hμ c C) := inferInstanceAs
  (Small.{u} (∀ i, LocalName hμ c (C.vertex i).diagram))

namespace ChainCode
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : DiagramOrder.HasConditionalJoins (DiagramOrder.LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

/-- A literal HS name represents a point of the glued component at w.  The
name, rather than its check-name code, is used in this predicate. -/
def At (F : GenericFilter (CohenForcing.Condition I κ)) (w : Vertex q)
    (τ : (system (M := M) (I := I) (κ := κ) hμ).Name) (b : (D[F]).Glued hj v) : Prop :=
  ∃ (hw : Vertex.Common v w) (x : (D[F]).vertexFiber w)
    (σ : LocalName hμ c w.diagram), σ.name = τ ∧
      LocalQuotient.ofName F σ = x.val.val ∧ (D[F]).toGlued hj v w hw x = b

/-- Eventual representation is explicitly insensitive to all entries in a
finite initial segment. -/
def Represents (F : GenericFilter (CohenForcing.Condition I κ))
    (a : ChainCode hμ c C) (b : (D[F]).Glued hj v) : Prop :=
  ∃ N, ∀ i, N ≤ i → At hμ c hcard hsize hmerger hj E hE F (C.vertex i) (a i).name b

variable {hμ c hcard hsize hmerger hj E hE C}

variable (hμ c hcard hsize hmerger hj E hE)

/-- Transport of the glued component to the moved Cohen filter, retaining
its original chosen root. -/
def transport (F : GenericFilter (CohenForcing.Condition I κ))
    (g : Vertex.componentStabilizer hj v) :
    (D[F]).Glued hj v ≃
      (D[F.move (CohenForcing.Condition.permuteOrderIso g.val.val)]).Glued hj v :=
  (eligibleSystemTransport hμ c hcard hsize hmerger F q E hE g.val).componentEquiv
    g.val hj v g.property

/-- This equality is about the actual transported name. In particular it
does not identify movement of a check-name with movement of its code. -/
theorem at_transport_iff (F : GenericFilter (CohenForcing.Condition I κ))
    (g : Vertex.componentStabilizer hj v) (w : Vertex q)
    (τ : (system (M := M) (I := I) (κ := κ) hμ).Name) (b : (D[F]).Glued hj v) :
    At hμ c hcard hsize hmerger hj E hE
      (F.move (CohenForcing.Condition.permuteOrderIso g.val.val)) (g.val • w) (g.val.val • τ)
      (transport hμ c hcard hsize hmerger hj E hE F g b) ↔
    At hμ c hcard hsize hmerger hj E hE F w τ b := by
  let F' := F.move (CohenForcing.Condition.permuteOrderIso g.val.val)
  let T := eligibleSystemTransport hμ c hcard hsize hmerger F q E hE g.val
  have hnat {hw : Vertex.Common v w} (x : (D[F]).vertexFiber w) :
      transport hμ c hcard hsize hmerger hj E hE F g ((D[F]).toGlued hj v w hw x) =
        (D[F']).toGlued hj v (g.val • w) (g.property.trans hj (hw.move g.val))
          (T.fiberEquiv g.val w x) := T.componentEquiv_toGlued g.val hj v w g.property hw x
  constructor
  · rintro ⟨hw,y,σ,hσ,hy,hb⟩
    have hw' : Vertex.Common v w := by
      have h := (g.property.symm.trans hj hw).move g.val⁻¹
      simpa only [inv_smul_smul] using h
    obtain ⟨x,hx⟩ := (T.fiberEquiv g.val w).surjective y
    obtain ⟨ρ,hρ⟩ := (LocalName.transportEquiv hμ c g.val.val w.diagram).surjective σ
    have hname : ρ.name = τ := by
      have hh : g.val.val • ρ.name = g.val.val • τ := by
        calc
          g.val.val • ρ.name = (LocalName.transportEquiv hμ c g.val.val w.diagram ρ).name := rfl
          _ = σ.name := congrArg LocalName.name hρ
          _ = g.val.val • τ := hσ
      exact (MulAction.injective g.val.val) hh
    refine ⟨hw',x,ρ,hname,?_,?_⟩
    · apply LocalQuotient.transport_injective F g.val.val w.diagram
      change LocalQuotient.ofName F' (ρ.transport hμ g.val.val) =
        (T.fiberEquiv g.val w x).val.val
      rw [hx]
      exact (congrArg (LocalQuotient.ofName F') hρ).trans hy
    · apply (transport hμ c hcard hsize hmerger hj E hE F g).injective
      rw [hnat,hx]
      exact hb
  · rintro ⟨hw,x,σ,hσ,hx,hb⟩
    refine ⟨g.property.trans hj (hw.move g.val),T.fiberEquiv g.val w x,
      σ.transport hμ g.val.val,?_,?_,?_⟩
    · change g.val.val • σ.name = g.val.val • τ
      rw [hσ]
    · exact congrArg (LocalQuotient.transport hμ F g.val.val) hx
    · exact (hnat x).symm.trans (congrArg (transport hμ c hcard hsize hmerger hj E hE F g) hb)

variable (C)

omit [Infinite M] [Infinite I] in
/-- Eventual literal fixation of every entry of every individual code. The
bound concerns the chain, not an invariance of its ground code wellorder. -/
theorem tail_fixed (k : C.tailFixer hj) : ∃ N, ∀ i, N ≤ i →
    k.val.val • C.vertex i = C.vertex i ∧
      ∀ τ : LocalName hμ c (C.vertex i).diagram, k.val.val.val • τ.name = τ.name := by
  obtain ⟨N,hN⟩ := k.property
  refine ⟨N,fun i hi => ?_⟩
  have hfix : ∀ j ∈ (C.vertex i).diagram.range, k.val.val.val j = j :=
    fun j hj => hN j (C.ranges_antitone hi hj)
  have hdiag := Diagram.permute_eq_of_fixes_range k.val.val.val (C.vertex i).diagram hfix
  have hvert : k.val.val • C.vertex i = C.vertex i := by
    generalize C.vertex i = w at hdiag ⊢
    obtain ⟨r,a,hr,U⟩ := w
    change ({diagram := r.permute k.val.val.val,index := a,root := _,ideal := U} : Vertex q) = _
    simp only [hdiag]
  exact ⟨hvert,fun τ => τ.fixed k.val.val.val ((SupportFilter.mem_Fix _ _).mpr hfix)⟩

/-- Source lemma `least-code-covariance`, at the level of functioning codes:
the very same code represents the transported point at the moved filter.
Only a finite prefix may cease working. -/
theorem represents_same_code (F : GenericFilter (CohenForcing.Condition I κ))
    (k : C.tailFixer hj) (a : ChainCode hμ c C) (b : (D[F]).Glued hj v) :
    Represents hμ c hcard hsize hmerger hj E hE C
      (F.move (CohenForcing.Condition.permuteOrderIso k.val.val.val)) a
      (transport hμ c hcard hsize hmerger hj E hE F k.val b) ↔
    Represents hμ c hcard hsize hmerger hj E hE C F a b := by
  obtain ⟨N,hN⟩ := tail_fixed hμ c hj C k
  have htail (i : ℕ) (hi : N ≤ i) :
      At hμ c hcard hsize hmerger hj E hE
        (F.move (CohenForcing.Condition.permuteOrderIso k.val.val.val)) (C.vertex i) (a i).name
        (transport hμ c hcard hsize hmerger hj E hE F k.val b) ↔
      At hμ c hcard hsize hmerger hj E hE F (C.vertex i) (a i).name b := by
    have hh := at_transport_iff hμ c hcard hsize hmerger hj E hE F k.val (C.vertex i) (a i).name b
    simpa only [(hN i hi).1,(hN i hi).2 (a i)] using hh
  constructor
  · rintro ⟨L,hL⟩
    exact ⟨max N L,fun i hi => (htail i ((le_max_left _ _).trans hi)).mp
      (hL i ((le_max_right _ _).trans hi))⟩
  · rintro ⟨L,hL⟩
    exact ⟨max N L,fun i hi => (htail i ((le_max_left _ _).trans hi)).mpr
      (hL i ((le_max_right _ _).trans hi))⟩

end ChainCode
end
end PartitionConsistency.ProductForcing


/-! ## Graph -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

def productSupport (X Y : S.Name) : Subgroup Γ :=
  MulAction.stabilizer Γ X.val ⊓ MulAction.stabilizer Γ Y.val

omit [OrderTop P] in
theorem productSupport_mem (X Y : S.Name) : S.productSupport X Y ∈ S.filter :=
  S.normal.2.2.1 _ _ X.hs.symmetric Y.hs.symmetric

theorem product_permute (X Y : S.Name) :
    ∀ g ∈ S.productSupport X Y, ∀ i p, S.productTest X Y i p →
      ∃ j, S.productEntry X Y j = g • S.productEntry X Y i ∧
        S.productTest X Y j (S.move g p) := by
  intro g hg i p hp
  have hx : g • X = X := Subtype.ext hg.1
  have hy : g • Y = Y := Subtype.ext hg.2
  have hex := S.entry_permute g X i.1
  have hey := S.entry_permute g Y i.2
  rw [hx] at hex
  rw [hy] at hey
  obtain ⟨j,hj⟩ := hex
  obtain ⟨k,hk⟩ := hey
  refine ⟨(j,k),?_,?_,?_⟩
  · simp only [productEntry,Name.smul_opair,hj,hk]
  · change S.atomic.MemF (S.move g p) (X.child j.property) X
    rw [hj]
    simpa only [hx] using (S.mem_symmetry g p _ X).mp hp.1

  · change S.atomic.MemF (S.move g p) (Y.child k.property) Y
    rw [hk]
    simpa only [hy] using (S.mem_symmetry g p _ Y).mp hp.2


def cartesianName (X Y : S.Name) : S.Name :=
  S.collect (S.productEntry X Y) (S.productTest X Y) (S.productSupport X Y)
    (S.productSupport_mem X Y) (S.product_permute X Y)

theorem cartesianName_fixed (X Y : S.Name) (g : Γ) (hx : g • X = X) (hy : g • Y = Y) :
    g • S.cartesianName X Y = S.cartesianName X Y :=
  Subtype.ext (S.collectName_fixed _ _ (S.productSupport X Y) (S.product_permute X Y)
    g ⟨congrArg Subtype.val hx,congrArg Subtype.val hy⟩)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_GraphFusion
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## IndexedGraph -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The canonical internal graph of a small ground-indexed name family.
Uniform support is used only to prove that this actual set name is HS. -/
def indexedGraph (X : ZFSet.{u}) (f : X → S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
    (hfix : ∀ g ∈ H, ∀ x, g • f x = f x) : S.Name :=
  S.collect (fun x : X => (Name.check x.val).opair (f x)) (fun _ _ => True) H hH (by
    intro g hg x p _
    exact ⟨x,by simp only [Name.smul_opair,Name.smul_check,hfix g hg],trivial⟩)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## CheckGraph -/

/-! Literal ground graphs and their check names.  These lemmas keep the
internal set-function formula, including its no-junk-entries conjunct. -/


/-! ## Fusion -/

/-! Countable ground-sequence preservation by fusion at a fixed supporting
root. The diagram forcing is not asserted to be countably closed. -/


/-! ## StableIdeal -/

/-! Dense stabilization of the actual availability ideals. This is a
condition-by-condition form of the countable-closure argument: it involves
no filter asserted to meet an unbounded collection of ambient dense sets. -/


/-! ## StableAvailability -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ)
variable (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)

/-- Availability when only equality forced by d is used. Each witness is an
actual normalized name on the required subdiagram. -/
def ForcedAvailable (d : CohenForcing.Condition I κ) (r : Diagram M I)
    (τ : LocalName hμ c r) (n : M) : Prop :=
  ∃ σ : LocalName hμ c (r.sub n),
    (system hμ).atomic.EqF ((d,r) : Poset M I κ) σ.name τ.name

/-- The availability ideal of a specified local name with respect to any
directed filter. No dense-set meeting assumptions are required for this
purely algebraic ideal assertion. -/
def localAvailability (F : GenericFilter (CohenForcing.Condition I κ))
    (r : Diagram M I) (a : M) (τ : LocalName hμ c r) : ConeIdeal (show LeftDivOrder M from a) :=
  (allLocalSystem (c := c) hμ hcard hsize hmerger F).availability r a
    (LocalQuotient.ofName F τ)

/-- The principal-filter availability ideal, built from the already proved
intersection/descent calculus. Its definition assumes no stability. -/
def forcedAvailability (d : CohenForcing.Condition I κ) (r : Diagram M I)
    (a : M) (τ : LocalName hμ c r) : ConeIdeal (show LeftDivOrder M from a) :=
  localAvailability hμ c hcard hsize hmerger (principalFilter d) r a τ

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_PersistentCodes
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CodeSelection -/

/-! Least-code selection at the level of forcing conditions. No generic
filter, regular ultrafilter, or selection of values in another universe is
assumed. The equivalence relation has a monotone truth value, and working
codes persist under refinement. -/


/-! ## PrincipalCode -/

/-! The least-code construction without an ambient fully generic filter.
The names and glued quotient values are the actual ones from the local
symbolic system. The principal filter at a condition is used only as a
convenient quotient notation for equality forced by that condition. -/

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : DiagramOrder.HasConditionalJoins (DiagramOrder.LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

/-- A code keeps representing a genuine exact-fiber value at every stronger
Cohen condition. This is a predicate on the already defined name collection,
not an extra mathematical hypothesis about that collection. -/
def Works (d : CohenForcing.Condition I κ) (a : ChainCode hμ c C) : Prop :=
  ∀ e, e ≤ d → ∃ b : (D[principalFilter e]).Glued hj v,
    Represents hμ c hcard hsize hmerger hj E hE C (principalFilter e) a b

/-- Eventual equality forced by one Cohen condition. Every comparison is of
actual names at their chain diagrams. -/
def Same (d : CohenForcing.Condition I κ) (a b : ChainCode hμ c C) : Prop :=
  ∃ N, ∀ i, N ≤ i → (localAtomic hμ (C.vertex i).diagram).EqF d (a i).name (b i).name

variable {hμ c hcard hsize hmerger hj E hE C}

variable (hμ c hcard hsize hmerger hj E hE C)

/-- Persistent least codes, defined over the fixed ground wellordering. -/
abbrev Selected (a : ChainCode hμ c C) (d : CohenForcing.Condition I κ) : Prop :=
  ConditionCodeSelection.Selected (Works hμ c hcard hsize hmerger hj E hE C)
    (Same hμ c C) a d

/-- The working-code predicate is invariant under a tail fixer acting on the
condition. The code itself, and its prescribed ground ordering, do not move. -/
theorem works_covariance (k : C.tailFixer hj) (d : CohenForcing.Condition I κ)
    (a : ChainCode hμ c C) :
    Works hμ c hcard hsize hmerger hj E hE C (d.permute k.val.val.val) a ↔
    Works hμ c hcard hsize hmerger hj E hE C d a := by
  let e := CohenForcing.Condition.permuteOrderIso (κ := κ) k.val.val.val
  have hf (f : CohenForcing.Condition I κ) :
      (∃ x : (D[principalFilter (e f)]).Glued hj v,
        Represents hμ c hcard hsize hmerger hj E hE C (principalFilter (e f)) a x) ↔
      ∃ x : (D[principalFilter f]).Glued hj v,
        Represents hμ c hcard hsize hmerger hj E hE C (principalFilter f) a x := by
    rw [← principalFilter_move f e]
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨y,rfl⟩ := (transport hμ c hcard hsize hmerger hj E hE (principalFilter f) k.val).surjective x
      exact ⟨y,(represents_same_code hμ c hcard hsize hmerger hj E hE C _ k a y).mp hx⟩
    · rintro ⟨y,hy⟩
      exact ⟨transport hμ c hcard hsize hmerger hj E hE (principalFilter f) k.val y,
        (represents_same_code hμ c hcard hsize hmerger hj E hE C _ k a y).mpr hy⟩
  constructor
  · intro h f hfd
    exact (hf f).mp (h (e f) (e.monotone hfd))
  · intro h f hfd
    change f ≤ e d at hfd
    have hfd' : e.symm f ≤ d := by
      simpa only [e.symm_apply_apply] using e.symm.monotone hfd
    have hh := (hf (e.symm f)).mpr (h (e.symm f) hfd')
    exact (show e (e.symm f) = f from e.apply_symm_apply f) ▸ hh

omit [Infinite M] [Infinite I] in
/-- Eventual equality has the same covariance, again for the unchanged
codes. This uses literal fixation on a tail, not invariance of the code set's
wellordering under coordinatewise transport. -/
theorem same_covariance (k : C.tailFixer hj) (d : CohenForcing.Condition I κ)
    (a b : ChainCode hμ c C) :
    Same hμ c C (d.permute k.val.val.val) a b ↔ Same hμ c C d a b := by
  obtain ⟨N,hN⟩ := tail_fixed hμ c hj C k
  have he (i : ℕ) (hi : N ≤ i) :
      (localAtomic hμ (C.vertex i).diagram).EqF (d.permute k.val.val.val) (a i).name (b i).name ↔
      (localAtomic hμ (C.vertex i).diagram).EqF d (a i).name (b i).name := by
    have hdg : (C.vertex i).diagram.permute k.val.val.val = (C.vertex i).diagram :=
      congrArg Vertex.diagram (hN i hi).1
    have hh := (system hμ).eq_symmetry k.val.val.val
      ((d,(C.vertex i).diagram) : Poset M I κ) (a i).name (b i).name
    simpa only [localAtomic,move_coe,permute,hdg,(hN i hi).2 (a i),(hN i hi).2 (b i)] using hh.symm
  constructor
  · rintro ⟨L,hL⟩
    exact ⟨max N L,fun i hi => (he i ((le_max_left _ _).trans hi)).mp
      (hL i ((le_max_right _ _).trans hi))⟩
  · rintro ⟨L,hL⟩
    exact ⟨max N L,fun i hi => (he i ((le_max_left _ _).trans hi)).mpr
      (hL i ((le_max_right _ _).trans hi))⟩

/-- Condition-level covariance of least-code selection. All auxiliary
wellorders remain fixed. -/
theorem selected_covariance (k : C.tailFixer hj) (d : CohenForcing.Condition I κ)
    (a : ChainCode hμ c C) :
    Selected hμ c hcard hsize hmerger hj E hE C a (d.permute k.val.val.val) ↔
      Selected hμ c hcard hsize hmerger hj E hE C a d :=
  ConditionCodeSelection.selected_covariance _ _
    (CohenForcing.Condition.permuteOrderIso k.val.val.val)
    (works_covariance hμ c hcard hsize hmerger hj E hE C k)
    (same_covariance hμ c hj C k) a d

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## PersistentCode -/

/-! Stable availability gives actual working ground codes, persistently at
every refinement. This supplies the density input for least-code ranks,
without a countable family of external fully generic filters. -/


/-! ## OrdinalName -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [Preorder P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The semantic transitivity clause, with unrestricted HS names. -/
def TransF (p : P) (σ : S.Name) : Prop :=
  ∀ (τ ν : S.Name) (q : P), q ≤ p →
    S.atomic.MemF q τ σ → S.atomic.MemF q ν τ → S.atomic.MemF q ν σ

/-- A transitive set of transitive sets; used to prove ordinal preservation,
not as a replacement for the ordinal formula in the statement of ACwo. -/
def OrdF (p : P) (σ : S.Name) : Prop :=
  S.TransF p σ ∧ ∀ (τ : S.Name) (q : P), q ≤ p → S.atomic.MemF q τ σ → S.TransF q τ

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrdinalCodes
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
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
namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)
variable {X : Type u} [LinearOrder X] [IsWellOrder X (· < ·)]
variable (R : X → P → Prop) (H : Subgroup Γ) (hH : H ∈ S.filter)
variable (hR : ∀ g ∈ H, ∀ x p, R x p → R x (S.move g p))

/-- Names literally fixed by one specified subgroup. -/
def FixedName (H : Subgroup Γ) := {σ : S.Name // ∀ g ∈ H, g • σ = σ}

namespace FixedName
variable {S H}

def collect {A : Type u} (f : A → S.FixedName H) (Q : A → P → Prop)
    (hQ : ∀ g ∈ H, ∀ a p, Q a p → Q a (S.move g p)) : S.FixedName H :=
  ⟨S.collect (fun a => (f a).val) Q H hH
      (fun g hg a p ha => ⟨a,((f a).property g hg).symm,hQ g hg a p ha⟩),
    fun g hg => Subtype.ext
      (S.collectName_fixed (fun a => (f a).val) Q H
        (fun g hg a p ha => ⟨a,((f a).property g hg).symm,hQ g hg a p ha⟩) g hg)⟩

end FixedName

/-- Rank in the selected suborder: recurse only along the fixed ground
wellordering. The predecessor set is small, with no bound on name ranks. -/
def selectedRankFixed (a : X) : S.FixedName H :=
  (IsWellFounded.wf (r := (· < ·))).fix
    (fun a f => FixedName.collect hH (fun b : {b : X // b < a} => f b.val b.property)
      (fun b p => R b.val p) (fun g hg b p => hR g hg b.val p)) a

def selectedRank (a : X) : S.Name := (S.selectedRankFixed R H hH hR a).val

/-- The ordinal consisting of the ranks of all selected elements. -/
def selectionType : S.Name :=
  (FixedName.collect hH (fun a => S.selectedRankFixed R H hH hR a) R hR).val

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## SelectedRank -/


/-! ## CohenSelection -/

/-! The ordinal coding of a condition-defined wellorder can be carried out
inside the product symmetric system itself. Its rank names have the given
tail support. Reflection to a supporting diagram permits all ordinal
decisions to be made by strengthening just the Cohen coordinate. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
variable [Infinite M] [Infinite I]
variable (hsize : Cardinal.mk M < Cardinal.mk I) (hmerger : HasFiniteMergers M)
include hsize hmerger

omit hsize hmerger

namespace CohenSelection
variable {X : Type u} [LinearOrder X] [IsWellOrder X (· < ·)]
variable (R : X → CohenForcing.Condition I κ → Prop)
variable (H : Subgroup (Equiv.Perm I)) (hH : H ∈ (system (M := M) (I := I) (κ := κ) hμ).filter)
variable (hR : ∀ π ∈ H, ∀ a d, R a d → R a (d.permute π))

include hR in
omit [Infinite M] [Infinite I] [IsWellOrder X (· < ·)] [LinearOrder X] in
theorem lift_covariance (π : Equiv.Perm I) (hπ : π ∈ H) (a : X) (p : Poset M I κ)
    (ha : lift (M := M) R a p) : lift (M := M) R a ((system (M := M) (I := I) (κ := κ) hμ).move π p) := by
  obtain ⟨d,r,rfl,ha⟩ := ha
  rw [move_coe]
  exact ⟨d.permute π,r.permute π,rfl,hR π hπ a d ha⟩

/-- The literal names used for the ordinal ranks and order type. -/
def rank (a : X) : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).selectedRank (lift (M := M) R) H hH (lift_covariance (M := M) hμ R H hR) a

def orderType : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).selectionType (lift (M := M) R) H hH (lift_covariance (M := M) hμ R H hR)

end CohenSelection
end
end PartitionConsistency.ProductForcing


/-! ## CodeRoot -/

/-! Connecting the persistent ground codes to literal root-supported names.
The comparison of two codes is equivalent to forced equality of any of their
root representatives. No generic evaluator is presumed in this step. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)

/-- A code represents a particular root name from some index onward. -/
def Rooted (a : ChainCode hμ c C) (d : CohenForcing.Condition I κ)
    (τ : LocalName hμ c v.diagram) : Prop :=
  ∃ N, ∀ i, N ≤ i → (system hμ).atomic.EqF ((d,v.diagram) : Poset M I κ) (a i).name τ.name

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## OrderAssignment -/

/-! Enumeration using one fixed, bounded table of bijections with ordinals.
This is the order-theoretic part of the preliminary component assignment.
The table is chosen once and never depends on the wellordered set being
enumerated. -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_CodeLinks
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CodeOrdinal -/

/-! Actual ordinal names for the persistent least-code ordering on a single
component. All names have the initial diagram as a support. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
section IndexCoding
variable {q : Diagram M I} {v : Vertex q} (C : Vertex.Chain v)

/-- Small carrier for the prescribed ground wellordering; no rearrangement
of code order occurs when conditions or components move. -/
def Index := Shrink.{u} (ChainCode hμ c C)

def code : Index hμ c C ≃ ChainCode hμ c C := (equivShrink (ChainCode hμ c C)).symm

instance instLinearOrderIndex : LinearOrder (Index hμ c C) :=
  show LinearOrder (Shrink.{u} (ChainCode hμ c C)) from
  IsWellOrder.linearOrder (OrderAssignment.smallRel (@WellOrderingRel (ChainCode hμ c C)))

instance instIsWellOrderIndexLt : IsWellOrder (Index hμ c C) (· < ·) :=
  inferInstanceAs (IsWellOrder (Shrink.{u} (ChainCode hμ c C))
    (OrderAssignment.smallRel (@WellOrderingRel (ChainCode hμ c C))))

end IndexCoding

variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)

/-- The old tail fixer viewed faithfully as coordinate permutations. -/
def tailGroup : Subgroup (Equiv.Perm I) :=
  (C.tailFixer hj).map ((Vertex.RootGroup q).subtype.comp (Vertex.componentStabilizer hj v).subtype)

omit [Infinite M] [Infinite I] in
theorem tailGroup_mem (π : Equiv.Perm I) : π ∈ tailGroup hj C ↔
    ∃ k : C.tailFixer hj, k.val.val.val = π := by
  change (∃ k ∈ C.tailFixer hj, k.val.val = π) ↔ _
  constructor
  · rintro ⟨k,hk,he⟩; exact ⟨⟨k,hk⟩,he⟩
  · rintro ⟨k,he⟩; exact ⟨k.val,k.property,he⟩

omit [Infinite M] [Infinite I] in
theorem root_le_tailGroup : SupportFilter.Fix v.diagram.range ≤ tailGroup hj C := by
  intro π hπ
  have hr : v.diagram ≤ q := ⟨v.index,v.root⟩
  have hπq : π ∈ Vertex.RootGroup q := by
    apply (SupportFilter.mem_Fix _ _).mpr
    intro j hj
    exact (SupportFilter.mem_Fix _ _).mp hπ j (Diagram.range_antitone hr hj)
  let g : Vertex.RootGroup q := ⟨π,hπq⟩
  have hg (j : I) (hj : j ∈ (C.vertex 0).diagram.range) : g.val j = j := by
    rw [C.first] at hj
    exact (SupportFilter.mem_Fix _ _).mp hπ j hj
  let k : Vertex.componentStabilizer hj v := ⟨g,C.fixes_mem_stabilizer hj g 0 hg⟩
  exact (tailGroup_mem hj C π).mpr ⟨⟨k,0,hg⟩,rfl⟩

include hcard in
omit [Infinite M] [Infinite I] in
theorem tailGroup_supported : tailGroup hj C ∈ (system (M := M) (I := I) (κ := κ) hμ).filter :=
  ⟨v.diagram.range,(Diagram.cardinal_range v.diagram).trans_le hcard,root_le_tailGroup hj C⟩

/-- A small index is selected precisely when its actual ground name code is
persistently least in its eventual-equality class. -/
def IsSelected (a : Index hμ c C) (d : CohenForcing.Condition I κ) : Prop :=
  Selected hμ c hcard hsize hmerger hj E hE C (code hμ c C a) d

theorem isSelected_covariance (π : Equiv.Perm I) (hπ : π ∈ tailGroup hj C)
    (a : Index hμ c C) (d : CohenForcing.Condition I κ)
    (ha : IsSelected hμ c hcard hsize hmerger hj E hE C a d) :
    IsSelected hμ c hcard hsize hmerger hj E hE C a (d.permute π) := by
  obtain ⟨k,rfl⟩ := (tailGroup_mem hj C π).mp hπ
  exact (selected_covariance hμ c hcard hsize hmerger hj E hE C k d (code hμ c C a)).mpr ha

/-- The von Neumann rank of a selected code, not a check-name for its
predetermined ground index. -/
def ordinalRank (a : Index hμ c C) : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  CohenSelection.rank hμ (IsSelected hμ c hcard hsize hmerger hj E hE C)
    (tailGroup hj C) (tailGroup_supported hμ hcard hj C)
    (isSelected_covariance hμ c hcard hsize hmerger hj E hE C) a

/-- The similarly supported total order-type name. -/
def ordinalType : (system (M := M) (I := I) (κ := κ) hμ).Name :=
  CohenSelection.orderType hμ (IsSelected hμ c hcard hsize hmerger hj E hE C)
    (tailGroup hj C) (tailGroup_supported hμ hcard hj C)
    (isSelected_covariance hμ c hcard hsize hmerger hj E hE C)

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## CodeLink -/

/-! Eventual code links at arbitrary vertices, rather than only at the
chosen first vertex. This is the local forcing form of the canonical
identifications in one component. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

/-- At every sufficiently late chain vertex a code entry equals the given
name at w, and that vertex actually is a successor of w. -/
def Links (d : CohenForcing.Condition I κ) (w : Vertex q)
    (τ : (system (M := M) (I := I) (κ := κ) hμ).Name) (a : ChainCode hμ c C) : Prop :=
  ∃ N, ∀ i, N ≤ i → Nonempty (w.Arrow (C.vertex i)) ∧
    (system hμ).atomic.EqF ((d,w.diagram) : Poset M I κ) (a i).name τ

variable {hμ c C}

omit [Infinite M] [Infinite I] in
theorem links_common {d : CohenForcing.Condition I κ} {w : Vertex q}
    {τ : (system (M := M) (I := I) (κ := κ) hμ).Name} {a : ChainCode hμ c C}
    (h : Links hμ c C d w τ a) : Vertex.Common v w := by
  obtain ⟨N,hN⟩ := h
  obtain ⟨f⟩ := (hN N le_rfl).1
  obtain ⟨g⟩ := C.increasing 0 N (Nat.zero_le _)
  exact ⟨C.vertex N,by simpa only [C.first] using (show Nonempty ((C.vertex 0).Arrow (C.vertex N)) from ⟨g⟩),⟨f⟩⟩

end
end PartitionConsistency.ProductForcing.ChainCode

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_UniformNames
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## UniformFamily -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w t
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The range of a small ground family all of whose entries have the same
literal support. This is an actual HS name, not an external evaluated set. -/
def uniformRange {ι : Type t} [Small.{u} ι] (f : ι → S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i) : S.Name :=
  S.collect f (fun _ _ => True) H hH (fun g hg i _ _ => ⟨i,(hfix g hg i).symm,trivial⟩)

namespace UniformInverse
variable {S}
variable (X : ZFSet.{u}) (f : X → S.Name)

/-- The index is the least possible index of this value. Negative equality
with every earlier entry is forced, not merely unforced at this condition. -/
def LeastValue (p : P) (x : S.Name) (i : X) : Prop :=
  S.atomic.EqF p x (f i) ∧ ∀ j, WellOrderingRel j i → ∀ q, q ≤ p → ¬ S.atomic.EqF q x (f j)

omit [OrderTop P] in
theorem least_congr {p : P} {x y : S.Name} {i : X}
    (he : S.atomic.EqF p x y) : LeastValue X f p x i ↔ LeastValue X f p y i := by
  have step {x y : S.Name} (he : S.atomic.EqF p x y) (h : LeastValue X f p x i) :
      LeastValue X f p y i := by
    refine ⟨S.atomic.eq_trans (S.atomic.eq_symm he) h.1,?_⟩
    intro j hj q hqp hy
    exact h.2 j hj q hqp (S.atomic.eq_trans (S.atomic.eq_mono hqp he) hy)
  exact ⟨step he,step (S.atomic.eq_symm he)⟩

/-- Regularization of the indexed least-value relation. -/
def Holds (p : P) (x y : S.Name) : Prop :=
  ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : X,
    S.atomic.EqF r y (Name.check i.val) ∧ LeastValue X f r x i

def relation : S.BinaryRelation where
  holds := Holds X f
  mono h hx q hqp := hx q (hqp.trans h)
  regular h q hqp := by
    obtain ⟨r,hrq,hh⟩ := h q hqp
    obtain ⟨s,hsr,hi⟩ := hh r le_rfl
    exact ⟨s,hsr.trans hrq,hi⟩
  congr := by
    intro p x x' y y' hx hy
    have step {x x' y y' : S.Name} (hx : S.atomic.EqF p x x') (hy : S.atomic.EqF p y y')
        (h : Holds X f p x y) : Holds X f p x' y' := by
      intro q hqp
      obtain ⟨r,hrq,i,he,hl⟩ := h q hqp
      exact ⟨r,hrq,i,S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono (hrq.trans hqp) hy)) he,
        (least_congr X f (S.atomic.eq_mono (hrq.trans hqp) hx)).mp hl⟩
    exact ⟨step hx hy,step (S.atomic.eq_symm hx) (S.atomic.eq_symm hy)⟩

omit [OrderTop P] in
/-- The least-value test is covariant under each automorphism fixing all
entries of the family. Its negative conjunct is transported at every stronger
condition by the inverse order isomorphism. -/
theorem least_move (H : Subgroup Γ)
    (hfix : ∀ g ∈ H, ∀ i, g • f i = f i) (g : Γ) (hg : g ∈ H)
    {p : P} {x : S.Name} {i : X} (hi : LeastValue X f p x i) :
    LeastValue X f (S.move g p) (g • x) i := by
  refine ⟨?_,?_⟩
  · simpa only [hfix g hg i] using (S.eq_symmetry g p x (f i)).mp hi.1
  · intro j hj q hqp he
    have hq : (S.move g).symm q ≤ p := (S.move g).symm_apply_le.mpr hqp
    apply hi.2 j hj ((S.move g).symm q) hq
    apply (S.eq_symmetry g ((S.move g).symm q) x (f j)).mpr
    simpa only [OrderIso.apply_symm_apply,hfix g hg j] using he

theorem relation_move (H : Subgroup Γ)
    (hfix : ∀ g ∈ H, ∀ i, g • f i = f i) (g : Γ) (hg : g ∈ H)
    (p : P) (x y : S.Name) (h : (relation X f).holds p x y) :
    (relation X f).holds (S.move g p) (g • x) (g • y) := by
  intro q hqp
  obtain ⟨r,hrq,i,he,hi⟩ := h ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hqp)
  refine ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,i,?_,least_move X f H hfix g hg hi⟩
  simpa only [Name.smul_check] using (S.eq_symmetry g r y (Name.check i.val)).mp he

end UniformInverse

/-- The same least-index graph restricted to an arbitrary supported set.
The set need not have a literal representative among the indexed entries. -/
def uniformSubsetInverse (X : ZFSet.{u}) (f : X → S.Name) (Y : S.Name)
    (H : Subgroup Γ) (hH : H ∈ S.filter) (hfix : ∀ g ∈ H, ∀ i, g • f i = f i)
    (hY : ∀ g ∈ H, g • Y = Y) : S.Name :=
  (UniformInverse.relation X f).graph Y (Name.check X) H hH hY
    (fun g _ => Name.smul_check S g X) (UniformInverse.relation_move X f H hfix)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## CheckOrdinal -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Forcing_RelationCalculus
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## RelationTools -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- An equality-invariant regular forcing predicate, used only to produce
bounded HS subnames by literal collection. -/
structure UnaryRelation where
  holds : P → S.Name → Prop
  mono : ∀ {p q x}, q ≤ p → holds p x → holds q x
  regular : ∀ {p x}, (∀ q, q ≤ p → ∃ r, r ≤ q ∧ holds r x) → holds p x
  congr : ∀ {p x y}, S.atomic.EqF p x y → (holds p x ↔ holds p y)

namespace UnaryRelation
variable {S} (R : S.UnaryRelation)
variable (X : S.Name) (H : Subgroup Γ) (hH : H ∈ S.filter)
variable (hX : ∀ g ∈ H, g • X = X)
variable (hR : ∀ g ∈ H, ∀ p x, R.holds p x → R.holds (S.move g p) (g • x))

def test (i : Edges X.raw) (p : P) :=
  S.atomic.MemF p (X.child i.property) X ∧ R.holds p (X.child i.property)

omit [OrderTop P] in
include hX hR in
theorem test_permute : ∀ g ∈ H, ∀ i p, R.test X i p →
    ∃ j : Edges X.raw, X.child j.property = g • X.child i.property ∧
      R.test X j (S.move g p) := by
  intro g hg i p hi
  have hh := S.entry_permute g X i
  rw [hX g hg] at hh
  obtain ⟨j,hj⟩ := hh
  refine ⟨j,hj,?_,?_⟩
  · change S.atomic.MemF (S.move g p) (X.child j.property) X
    rw [hj]
    simpa only [hX g hg] using (S.mem_symmetry g p _ X).mp hi.1
  · change R.holds (S.move g p) (X.child j.property)
    rw [hj]
    exact hR g hg p _ hi.2

/-- The subset is formed from literal children of the bounding name. -/
def select : S.Name :=
  S.collect (fun i : Edges X.raw => X.child i.property) (R.test X) H hH
    (R.test_permute X H hX hR)

omit [OrderTop P] in
theorem select_fixed (g : Γ) (hg : g ∈ H) :
    g • R.select X H hH hX hR = R.select X H hH hX hR :=
  Subtype.ext (S.collectName_fixed _ _ H (R.test_permute X H hX hR) g hg)

end UnaryRelation

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## MapCalculus -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

def compositionRelation (f g X Y Z : S.Name) : S.BinaryRelation :=
  (S.boundedApp f X Y).comp (S.boundedApp g Y Z)

theorem compositionRelation_move (f g X Y Z : S.Name) (π : Γ)
    (hf : π • f = f) (hg : π • g = g) (hX : π • X = X)
    (hY : π • Y = Y) (hZ : π • Z = Z)
    (p : P) (x z : S.Name) (h : (S.compositionRelation f g X Y Z).holds p x z) :
    (S.compositionRelation f g X Y Z).holds (S.move π p) (π • x) (π • z) := by
  intro q hq
  obtain ⟨r,hrq,y,hh,hh'⟩ := h ((S.move π).symm q) ((S.move π).symm_apply_le.mpr hq)
  exact ⟨S.move π r,(S.move π).le_symm_apply.mp hrq,π • y,
    S.boundedApp_move f X Y π hf hX hY r x y hh,
    S.boundedApp_move g Y Z π hg hY hZ r y z hh'⟩

def compositionGraph (f g X Y Z : S.Name) : S.Name :=
  (S.compositionRelation f g X Y Z).graph X Z (S.tupleStabilizer ![f,g,X,Y,Z])
    (S.tupleStabilizer_mem _) (fun π hπ => (S.mem_tupleStabilizer _ π).mp hπ 2)
    (fun π hπ => (S.mem_tupleStabilizer _ π).mp hπ 4)
    (fun π hπ => S.compositionRelation_move f g X Y Z π
      ((S.mem_tupleStabilizer _ π).mp hπ 0) ((S.mem_tupleStabilizer _ π).mp hπ 1)
      ((S.mem_tupleStabilizer _ π).mp hπ 2) ((S.mem_tupleStabilizer _ π).mp hπ 3)
      ((S.mem_tupleStabilizer _ π).mp hπ 4))

def inverseGraph (f X Y : S.Name) : S.Name :=
  (S.boundedApp f X Y).inverse.graph Y X (S.tupleStabilizer ![f,X,Y])
    (S.tupleStabilizer_mem _) (fun π hπ => (S.mem_tupleStabilizer _ π).mp hπ 2)
    (fun π hπ => (S.mem_tupleStabilizer _ π).mp hπ 1)
    (fun π hπ p x y h => S.boundedApp_move f X Y π
      ((S.mem_tupleStabilizer _ π).mp hπ 0) ((S.mem_tupleStabilizer _ π).mp hπ 1)
      ((S.mem_tupleStabilizer _ π).mp hπ 2) p y x h)

/-- Restriction is a bounded application graph, not a change of interpretation
of an old function name. -/
def restrictionGraph (f X Y : S.Name) : S.Name :=
  (S.boundedApp f X Y).graph X Y (S.tupleStabilizer ![f,X,Y])
    (S.tupleStabilizer_mem _) (fun π hπ => (S.mem_tupleStabilizer _ π).mp hπ 1)
    (fun π hπ => (S.mem_tupleStabilizer _ π).mp hπ 2)
    (fun π hπ => S.boundedApp_move f X Y π
      ((S.mem_tupleStabilizer _ π).mp hπ 0) ((S.mem_tupleStabilizer _ π).mp hπ 1)
      ((S.mem_tupleStabilizer _ π).mp hπ 2))

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrdinalPresentation
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Completion -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

namespace BinaryRelation
/-- Any fixed formula with two distinguished free variables gives a regular
binary forcing relation. Its other free variables remain actual parameters. -/
def ofFormula {n} (v : Fin n → S.Name) (φ : Formula (n+2)) : S.BinaryRelation where
  holds p x y := S.Forces (Fin.snoc (Fin.snoc v x) y) p φ
  mono h hp := S.atomic.forceFormula_mono h hp
  regular h := S.atomic.forceFormula_of_dense S.atomic_regular h
  congr hx hy := by
    apply S.atomic.forceFormula_tuple_congr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hy
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [Fin.snoc_castSucc,Fin.snoc_last] using hx
      · simpa only [Fin.snoc_castSucc] using S.atomic.eq_refl _ (v j)

omit [OrderTop P] in
theorem ofFormula_symmetry {n} (v : Fin n → S.Name) (φ : Formula (n+2))
    (g : Γ) (hv : ∀ i, g • v i = v i) (p : P) (x y : S.Name) :
    (ofFormula S v φ).holds p x y ↔
      (ofFormula S v φ).holds (S.move g p) (g • x) (g • y) := by
  have hh := S.forces_symmetry g φ (Fin.snoc (Fin.snoc v x) y) p
  have he : (fun i => g • Fin.snoc (Fin.snoc v x) y i) =
      Fin.snoc (Fin.snoc v (g • x)) (g • y) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.snoc_castSucc,Fin.snoc_last]
      · simp only [Fin.snoc_castSucc,hv]
  change S.Forces _ _ _ ↔ S.Forces _ _ _
  simpa only [he] using hh
end BinaryRelation

/-- Use a partial graph's value when it belongs to the codomain, and otherwise
use the specified default. The variables are `f,X,x₀,a,y`, respectively. -/
def defaultFormula : Formula 5 :=
  ((SetLanguage.edge 0 3 4).conj (.mem 4 1)).disj
    ((Formula.ex ((SetLanguage.edge 0 3 5).conj (.mem 5 1))).neg.conj (.equal 4 2))

def defaultRelation (f X x₀ : S.Name) : S.BinaryRelation :=
  BinaryRelation.ofFormula S ![f,X,x₀] defaultFormula

def NoValue (f X : S.Name) (p : P) (a : S.Name) : Prop :=
  ∀ q, q ≤ p → ∀ y : S.Name, S.App q f a y → S.atomic.MemF q y X → False

omit [OrderTop P] in
theorem defaultRelation_symmetry (f X x₀ : S.Name) (g : Γ)
    (hf : g • f = f) (hX : g • X = X) (hx₀ : g • x₀ = x₀)
    (p : P) (a y : S.Name) :
    (S.defaultRelation f X x₀).holds p a y ↔
      (S.defaultRelation f X x₀).holds (S.move g p) (g • a) (g • y) := by
  apply BinaryRelation.ofFormula_symmetry
  intro i
  fin_cases i <;> assumption

/-- A ground-indexed family of completed partial maps, with an actual ordered
pair as input. Local witnesses are regularized, as in existential forcing. -/
def completionRelation (O : ZFSet.{u}) (f : O → S.Name) (X x₀ : S.Name) : S.BinaryRelation where
  holds p x y := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : O, ∃ a : S.Name,
    S.atomic.EqF r x (a.opair (Name.check i.val)) ∧
      (S.defaultRelation (f i) X x₀).holds r a y
  mono h hh q hq := hh q (hq.trans h)
  regular hh q hq := by
    obtain ⟨r,hrq,hr⟩ := hh q hq
    obtain ⟨s,hsr,i,a,ha,hR⟩ := hr r le_rfl
    exact ⟨s,hsr.trans hrq,i,a,ha,hR⟩
  congr hxx' hyy' := by
    constructor
    · intro h q hqp
      obtain ⟨r,hrq,i,a,ha,hR⟩ := h q hqp
      have hrp := hrq.trans hqp
      exact ⟨r,hrq,i,a,S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono hrp hxx')) ha,
        ((S.defaultRelation (f i) X x₀).congr (S.atomic.eq_refl r a)
          (S.atomic.eq_mono hrp hyy')).mp hR⟩
    · intro h q hqp
      obtain ⟨r,hrq,i,a,ha,hR⟩ := h q hqp
      have hrp := hrq.trans hqp
      exact ⟨r,hrq,i,a,S.atomic.eq_trans (S.atomic.eq_mono hrp hxx') ha,
        ((S.defaultRelation (f i) X x₀).congr (S.atomic.eq_refl r a)
          (S.atomic.eq_mono hrp hyy')).mpr hR⟩

theorem completionRelation_symmetry (O : ZFSet.{u}) (f : O → S.Name) (X x₀ : S.Name)
    (g : Γ) (hf : ∀ i, g • f i = f i) (hX : g • X = X) (hx₀ : g • x₀ = x₀)
    (p : P) (x y : S.Name) (h : (S.completionRelation O f X x₀).holds p x y) :
    (S.completionRelation O f X x₀).holds (S.move g p) (g • x) (g • y) := by
  intro q hqp
  have hqp' : (S.move g).symm q ≤ p := (S.move g).symm_apply_le.mpr hqp
  obtain ⟨r,hrq,i,a,ha,hR⟩ := h _ hqp'
  refine ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,i,g • a,?_,?_⟩
  · simpa only [Name.smul_opair,Name.smul_check] using (S.eq_symmetry g r x _).mp ha
  · exact (S.defaultRelation_symmetry (f i) X x₀ g (hf i) hX hx₀ r a y).mp hR

/-- Auxiliary graph construction for a family of invariant partial orbit maps.
The support is precisely a common support for the three displayed set names. -/
def completionGraph (O : ZFSet.{u}) (f : O → S.Name) (A X x₀ : S.Name)
    (hf : ∀ g : Γ, ∀ i, g • f i = f i) : S.Name :=
  let H := S.productSupport A X ⊓ MulAction.stabilizer Γ x₀.val
  (S.completionRelation O f X x₀).graph (S.cartesianName A (Name.check O)) X H
    (S.normal.2.2.1 _ _ (S.productSupport_mem A X) x₀.hs.symmetric)
    (fun g hg => S.cartesianName_fixed A (Name.check O) g (Subtype.ext hg.1.1) (Name.smul_check S g O))
    (fun _ hg => Subtype.ext hg.1.2)
    (fun g hg p x y h => S.completionRelation_symmetry O f X x₀ g (hf g)
      (Subtype.ext hg.1.2) (Subtype.ext hg.2) p x y h)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## Presentation -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)

instance instSmallPresentationIndex (X : (system (M := M) (I := I) (κ := κ) hμ).Name) :
    Small.{u} (PresentationIndex hμ X) := by
  unfold PresentationIndex
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_ClassFibers
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions _root_.OAI.PartitionConsistency.ForcingQuotient.instMulActionPermGenericFilterCondition _root_.OAI.PartitionConsistency.LocalDiagramSystem.Vertex.labelFiberAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## LocalList -/

namespace PartitionConsistency.SetLanguage

/-- A set is wellorderable exactly when it embeds in some ordinal. Both
quantified witnesses are internal sets; the injection is an internal graph. -/
def wellorderableFormula : Formula 1 :=
  .ex ((ordinal 1).conj (.ex (injection 2 0 1)))

def wellorderable {n} (a : Fin n) : Formula n :=
  Formula.rename ![a] wellorderableFormula

end PartitionConsistency.SetLanguage

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- A ground ordinal enumerating the entire normalized local-name set. -/
def localListOrdinal (r : Diagram M I) : Ordinal.{u} :=
  (exists_ordinal_equiv (LocalName hμ c r)).choose

def localListEquiv (r : Diagram M I) :
    (localListOrdinal hμ c r).toZFSet ≃ LocalName hμ c r :=
  (exists_ordinal_equiv (LocalName hμ c r)).choose_spec.some

def localListEntry (r : Diagram M I) (i : (localListOrdinal hμ c r).toZFSet) :
    (system (M := M) (I := I) (κ := κ) hμ).Name := (localListEquiv hμ c r i).name

theorem localListEntry_fixed (r : Diagram M I) (π : Equiv.Perm I)
    (hπ : π ∈ SupportFilter.Fix r.range) (i : (localListOrdinal hμ c r).toZFSet) :
    π • localListEntry hμ c r i = localListEntry hμ c r i :=
  (localListEquiv hμ c r i).fixed π hπ

theorem localList_support (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I) :
    SupportFilter.Fix r.range ∈ (system (M := M) (I := I) (κ := κ) hμ).filter :=
  ⟨r.range,(Diagram.cardinal_range r).trans_le hcard,le_rfl⟩

/-- The canonical evaluation list range, formed as a genuine HS name
with support D_r; its domain has been enumerated by a ground ordinal. -/
def localList (hcard : Cardinal.mk M ≤ μ) (r : Diagram M I) :
    (system (M := M) (I := I) (κ := κ) hμ).Name :=
  (system (M := M) (I := I) (κ := κ) hμ).uniformRange
    (ι := (localListOrdinal hμ c r).toZFSet) (localListEntry hμ c r)
    (SupportFilter.Fix r.range)
    (localList_support (κ := κ) hμ hcard r)
    (by
      intro π hπ i
      exact localListEntry_fixed hμ c r π hπ i)

end
end PartitionConsistency.ProductForcing


/-! ## OutsideClass -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- A class outside the *entire* local-name evaluation list, decided in a
literal stronger diagram that also contains all the condition coordinates.
The right factor of the root is recorded and is necessarily nontrivial. -/
def outsideClassSet (hcard : Cardinal.mk M ≤ μ) (p : Diagram M I)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name) :
    Set (CohenForcing.Condition I κ) :=
  {d | ∃ (t : Diagram M I) (b : M), t.sub b = p ∧ b ≠ 1 ∧
    d.support ⊆ t.range ∧ ∃ j ∈ t.range,
      ∀ s : Poset M I κ, s ≤ (d,t) →
        ¬ (system hμ).atomic.MemF s (labelClass hμ c E j) (localList hμ c hcard p)}

end
end PartitionConsistency.ProductForcing


/-! ## ClassFiber -/

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

/-- Persistent exclusion from the evaluation list of *all* local names at
p. This statement is expressed in the actual symmetric forcing relation. -/
def OutsideLocal (hcard : Cardinal.mk M ≤ μ) (p s : Diagram M I)
    (d : CohenForcing.Condition I κ) (σ : LocalName hμ c s) : Prop :=
  ∀ z : Poset M I κ, z ≤ (d,s) →
    ¬ (system hμ).atomic.MemF z σ.name (localList hμ c hcard p)

/-- A supported eligible class at any subdiagram gives a genuine element
of D_F(r), even when that subdiagram is not itself below q. -/
def classFromLocal [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (F : GenericFilter (CohenForcing.Condition I κ))
    (q r s : Diagram M I) (hrq : r ≤ q) (hrs : r ≤ s)
    (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
    (σ : LocalName hμ c s) (hσ : EligibleName hμ c F s E σ) :
    (eligibleSystem hμ c hcard hsize hmerger F q E hE).Obj r :=
  ⟨LocalQuotient.restrict F hrs (LocalQuotient.ofName F σ),hrq,
    eligible_restrict hμ c F E hrs (LocalQuotient.ofName F σ) hσ⟩

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrdinalChoice
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## Antichain -/


/-! ## Maximum -/


/-! ## ChoiceFamily -/

namespace PartitionConsistency.SetLanguage

/-- Auxiliary formula for a value selected from the set `F(i)`.
Its variables are the family graph, the index, and the selected value. -/
def familyMember : Formula 3 :=
  .ex ((edge 0 1 3).conj (.mem 2 3))

end PartitionConsistency.SetLanguage


/-! ## ACwo -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_QuotientActions
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## SaturatedFibers -/

namespace PartitionConsistency.LocalDiagramSystem.System
universe u v w
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable (D : System.{u,v} M I)

instance fiberSmall (r : Diagram M I) (a : M) (U : ConeIdeal (show LeftDivOrder M from a))
    [Small.{w} (D.Obj r)] : Small.{w} (D.Fiber r a U) :=
  inferInstanceAs (Small.{w} {x : D.Obj r // D.availability r a x = U})

end PartitionConsistency.LocalDiagramSystem.System

namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem MonoidConstruction
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})

instance eligibleSystem_obj_small [Infinite M] [Infinite I]
    (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
    (hmerger : HasFiniteMergers M) (F : GenericFilter (CohenForcing.Condition I κ))
    (q r : Diagram M I) (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
    (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E) :
    Small.{u} ((eligibleSystem hμ c hcard hsize hmerger F q E hE).Obj r) :=
  inferInstanceAs (Small.{u} {x : LocalQuotient (c := c) hμ F r //
    r ≤ q ∧ Eligible hμ c F r E x})

end
end PartitionConsistency.ProductForcing


/-! ## Preliminary -/

/-! A preliminary assignment on the genuine symbolic component with tail
covariance. Exact cardinality at an intermediate filter is an explicit
input here; the issued dense requirements needed to obtain it are in
`SaturatedFibersWork`. No existence of a filter generic over every ambient
set is assumed or asserted. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
variable (hj : DiagramOrder.HasConditionalJoins (DiagramOrder.LeftDivOrder M))
variable {q : Diagram M I} (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "D[" F "]" => eligibleSystem hμ c hcard hsize hmerger F q E hE

instance eligibleSystem_glued_small (F : GenericFilter (CohenForcing.Condition I κ)) :
    Small.{u} ((D[F]).Glued hj v) :=
  small_of_surjective ((D[F]).toGlued_surjective hj v v (Vertex.Common.refl v))

end
end PartitionConsistency.ProductForcing


/-! ## ComponentAction -/

/-! The actual symbolic fibers carry transport between moved Cohen filters.
On the total space this is a genuine group action. The individual interpreted
universes are not being treated as if they carried this action internally. -/


/-! ## CodeCovariance -/

/-! Covariance on actual forcing conditions. The code order is held fixed,
whereas both the Cohen condition and the local supporting vertex move. -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_GermSelectors
attribute [-instance] _root_.OAI.PartitionConsistency.CohenForcing.Condition.coordinateAction _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
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
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [DiagramOrder.IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "ordT" => ordinalType hμ c hcard hsize hmerger hj E hE C
local notation "ordR" => ordinalRank hμ c hcard hsize hmerger hj E hE C
local notation "Sel" => IsSelected hμ c hcard hsize hmerger hj E hE C
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

/-- The bounded ground table depends on the component's fixed coding data,
never on a condition or a moved generic computation. -/
def ordinalTable : OrderAssignment.Table (labelFiberSet v) (ordT).raw.rank :=
  OrderAssignment.chooseTable _ _

/-- `j` is assigned to the class named by `τ` at the local vertex `w`.
Both ordinal values in this definition are forced values of actual names. -/
def Preliminary (d : CohenForcing.Condition I κ) (w : Vertex q)
    (j : labelFiberSet v) (τ : (S).Name) : Prop :=
  ∃ (θ : Ordinal.{u}) (hb : θ ≤ (ordT).raw.rank)
    (hc : θ.card = Cardinal.mk (labelFiberSet v)) (a : Index hμ c C),
    Sel a d ∧ (S).atomic.EqF ((d,v.diagram) : Poset M I κ) ordT (Name.check θ.toZFSet) ∧
    (S).atomic.EqF ((d,v.diagram) : Poset M I κ) (ordR a)
      (Name.check (OrderAssignment.indices (ordinalTable hμ c hcard hsize hmerger hj E hE C)
        θ hb hc j).val.toZFSet) ∧ Links hμ c C d w τ (code hμ c C a)

variable {hμ c hcard hsize hmerger hj E hE C}

theorem preliminary_common {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : (S).Name}
    (h : Preliminary hμ c hcard hsize hmerger hj E hE C d w j τ) : Vertex.Common v w := by
  obtain ⟨_,_,_,_,_,_,_,hl⟩ := h
  exact links_common hl

variable (hμ c hcard hsize hmerger hj E hE C)

/-- The exact cardinal-count hypothesis used by the two density proofs.
It is a theorem for the concrete system (not a construction premise). -/
def OrdinalCount (d : CohenForcing.Condition I κ) : Prop :=
  ∀ e, e ≤ d → ∀ θ : Ordinal.{u},
    (S).atomic.EqF ((e,v.diagram) : Poset M I κ) ordT (Name.check θ.toZFSet) →
      θ.card = Cardinal.mk (labelFiberSet v)

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## Germ -/

namespace PartitionConsistency.LocalDiagramSystem.Vertex.Chain
universe u t
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {q : Diagram M I} {v : Vertex q}
noncomputable section
variable (C : Chain v)

/-- These are the literal alignments of the moved chain with contractions
of its initial vertex. There is no replacement relation assumed here. -/
def Alignments (hj : HasConditionalJoins (LeftDivOrder M))
    (π : componentStabilizer hj v) : Set (ℕ × M) :=
  {p | ∃ f : Arrow v (π.val • C.vertex p.1), f.index = p.2}

end
end PartitionConsistency.LocalDiagramSystem.Vertex.Chain


/-! ## Selector -/

/-! A combinatorial coset-selector argument. The existence of a countable-base
tower and symmetric names for its assignments are established separately. -/

namespace PartitionConsistency.LocalDiagramSystem.Vertex.Chain
universe u
open DiagramOrder DiagramForcing TailSelector
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {q : Diagram M I} {v : Vertex q}
noncomputable section

/-- The abstract tail data are supplied by the actual component stabilizer
and the union of its pointwise tail fixers previously constructed. -/
def tailData (C : Chain v) (hj : HasConditionalJoins (LeftDivOrder M)) :
    TailData (componentStabilizer hj v) I where
  tail := fun i => (C.vertex i).diagram.range
  antitone := C.ranges_antitone
  K := C.tailFixer hj
  normal := inferInstance
  mem_iff := C.mem_tailFixer hj

end
end PartitionConsistency.LocalDiagramSystem.Vertex.Chain

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_StableSelectors
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
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
open CohenForcing
variable {G I κ : Type u} [Group G] [MulAction G I] (D : TailData G I)
variable [LinearOrder κ]

/-- Every bounded detector row is completely assigned after a finite initial
segment. The quantifier over all representatives makes covariance literal. -/
def Complete (p : Condition I κ) (α : κ) : Prop :=
  ∀ g : G, ∀ δ : D.Nonidentity, ∃ N, ∀ n, N ≤ n →
    ∀ b : Set.Iio α, (g • D.detector δ n,b.val) ∈ p.dom

/-- A good condition actually decides a distinguishing pattern; arbitrary
unassigned row values are never used for a stable selection. -/
def Good (p : Condition I κ) : Prop :=
  ∃ α : κ, D.Complete p α ∧ Function.Injective (D.pattern p.rows α)

variable [WellFoundedLT κ]

/-- This candidate does not yet mention a generic filter. -/
def conditionSelector (p : Condition I κ) (h : D.Good p) : D.Cosets :=
  D.selector p.rows ⟨h.choose,h.choose_spec.2⟩

/-- The downward-persistent relation that can be used as a name recipe. -/
def Selected (p : Condition I κ) (c : D.Cosets) : Prop :=
  ∃ h : D.Good p, D.conditionSelector p h = c

end
end PartitionConsistency.TailSelector.TailData


/-! ## CosetPredicate -/

/-! Coset transport for predicates on the total space of computations.
The inverse moves every argument, in particular the actual Cohen condition. -/


/-! ## Corrected -/

/-! A component assignment on actual conditions: select a residual coset,
compute at the inverse-moved condition, then transport every argument back.
The quotient operation uses proved tail invariance, not an arbitrary choice
of a bijection. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ
local notation "G" => Vertex.componentStabilizer hj v
local notation "K" => C.tailFixer hj

abbrev AssignmentPoint := CohenForcing.Condition I κ × Vertex q × labelFiberSet v × (S).Name

def preliminaryPoint (x : AssignmentPoint (κ := κ) hμ (v := v)) : Prop :=
  Preliminary hμ c hcard hsize hmerger hj E hE C x.1 x.2.1 x.2.2.1 x.2.2.2

variable [LinearOrder κ] [WellFoundedLT κ]

/-- The persistent selected-coset version of the assignment predicate. -/
def Corrected (d : CohenForcing.Condition I κ) (w : Vertex q)
    (j : labelFiberSet v) (τ : (S).Name) : Prop :=
  ∃ g : G, (C.tailData hj).Selected d (g : G ⧸ K) ∧
    CosetPredicate.shift g (preliminaryPoint hμ c hcard hsize hmerger hj E hE C) (d,w,j,τ)

variable {hμ c hcard hsize hmerger hj E hE C}

theorem corrected_common {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : labelFiberSet v} {τ : (S).Name}
    (h : Corrected hμ c hcard hsize hmerger hj E hE C d w j τ) : Vertex.Common v w := by
  obtain ⟨g,_,h⟩ := h
  have hc := Vertex.common_moved hj v g (preliminary_common h)
  change Vertex.Common v (g • (g⁻¹ • w)) at hc
  simpa only [smul_inv_smul] using hc

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## StableTransport -/

/-! Coordinate transport for the permanently decided availability ideal.
This is used both for coset correction and for moving between component
orbits. -/
namespace PartitionConsistency.ProductForcing
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

variable {q : Diagram M I}

/-- An actual local class whose availability has become permanent. Keeping
the literal name as an argument avoids any chosen representative under
transport between vertices. -/
def StableAt (E : (S).Name) (d : CohenForcing.Condition I κ) (w : Vertex q)
    (τ : (S).Name) : Prop :=
  ∃ ρ : LocalName hμ c w.diagram, ρ.name = τ ∧
    (S).Forces ![τ,labelSet hμ c,E] ((d,w.diagram) : Poset M I κ)
      (SetLanguage.isClass 0 1 2) ∧
    ∀ e, e ≤ d → forcedAvailability hμ c hcard hsize hmerger e w.diagram w.index ρ = w.ideal

end
end PartitionConsistency.ProductForcing

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrbitAssignments
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## CorrectedDensity -/

/-! Exactness and the two density directions for the coset-corrected
assignment. Selector density and ordinal counts are discharged for the
concrete system in the following construction. -/


/-! ## ComponentOrbit -/

/-! Orbits of actual contraction components, under the group fixing the
root diagram. Representatives and chains are chosen only once per orbit. -/
namespace PartitionConsistency.LocalDiagramSystem.Vertex
universe u
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
variable {q : Diagram M I}
noncomputable section
variable (hj : HasConditionalJoins (LeftDivOrder M))

def OrbitRel (_hj : HasConditionalJoins (LeftDivOrder M)) (v w : Vertex q) : Prop := ∃ g : RootGroup q, Common v (g • w)

namespace OrbitRel
variable {hj}
theorem refl (v : Vertex q) : OrbitRel hj v v := ⟨1,by simpa using Common.refl v⟩
theorem symm {v w : Vertex q} (h : OrbitRel hj v w) : OrbitRel hj w v := by
  obtain ⟨g,hg⟩ := h
  exact ⟨g⁻¹,by simpa only [inv_smul_smul] using (hg.move g⁻¹).symm⟩
theorem trans {v w z : Vertex q} (h : OrbitRel hj v w) (h' : OrbitRel hj w z) :
    OrbitRel hj v z := by
  obtain ⟨g,hg⟩ := h
  obtain ⟨s,hs⟩ := h'
  exact ⟨g*s,by simpa only [mul_smul] using hg.trans hj (hs.move g)⟩
end OrbitRel

def orbitSetoid : Setoid (Vertex q) where
  r := OrbitRel hj
  iseqv := ⟨OrbitRel.refl,OrbitRel.symm,OrbitRel.trans⟩

abbrev ComponentOrbit := Quotient (orbitSetoid (q := q) hj)

def orbit (v : Vertex q) : ComponentOrbit (q := q) hj := Quotient.mk _ v

def orbitRep (a : ComponentOrbit (q := q) hj) : Vertex q := a.out

def orbitChain (H : HeightCost (LeftDivOrder M)) (a : ComponentOrbit (q := q) hj) :
    Chain (orbitRep hj a) := Classical.choice (exists_chain hj H _)

end
end PartitionConsistency.LocalDiagramSystem.Vertex


/-! ## AllComponent -/

/-! Transport of the corrected assignment to an entire orbit of components.
The only ambiguity is the actual component stabilizer, whose covariance has
already been proved with the inverse-moved Cohen condition. -/
namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
variable {v : Vertex q} (C : Vertex.Chain v)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ
local notation "G" => Vertex.RootGroup q

def OrbitAssignment (d : CohenForcing.Condition I κ) (w : Vertex q) (j : I) (τ : (S).Name) : Prop :=
  ∃ (g : G) (k : labelFiberSet v), g • k.val = j ∧
    Corrected hμ c hcard hsize hmerger hj E hE C (g⁻¹ • d) (g⁻¹ • w) k (g⁻¹ • τ)

variable {hμ c hcard hsize hmerger hj E hE C}

theorem orbitAssignment_label {d : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ : (S).Name}
    (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ) : j ∈ labelFiberSet w := by
  obtain ⟨g,k,rfl,h⟩ := h
  have hk : k.val ∈ labelFiberSet (g⁻¹ • w) := by
    rw [← labelFiberSet_common hj (corrected_common h)]
    exact k.property
  have hh := (labelFiberSet_permute g (g⁻¹ • w) k.val).mp hk
  change g.val k.val ∈ labelFiberSet w
  simpa only [smul_inv_smul] using hh

variable (hμ c hcard hsize hmerger hj E hE C)

theorem orbitAssignment_permute (s : G) {d : CohenForcing.Condition I κ} {w : Vertex q}
    {j : I} {τ : (S).Name} (h : OrbitAssignment hμ c hcard hsize hmerger hj E hE C d w j τ) :
    OrbitAssignment hμ c hcard hsize hmerger hj E hE C (s • d) (s • w) (s • j) (s • τ) := by
  obtain ⟨g,k,hk,h⟩ := h
  refine ⟨s*g,k,?_,?_⟩
  · rw [mul_smul,hk]
  · simpa only [mul_inv_rev,mul_smul,inv_smul_smul] using h

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## OrbitDensity -/


/-! ## GlobalAssignment -/

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable (H : HeightCost (LeftDivOrder M)) {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

/-- The assignment on all vertices, choosing a single chain per orbit of
actual components. Its witnesses are local names and literal label indices. -/
def Assigned (d : CohenForcing.Condition I κ) (w : Vertex q) (j : I) (τ : (S).Name) : Prop :=
  ∃ a : Vertex.ComponentOrbit (q := q) hj,
    OrbitAssignment hμ c hcard hsize hmerger hj E hE (Vertex.orbitChain hj H a) d w j τ

variable {hμ c hcard hsize hmerger hj H E hE}

theorem assigned_label {d : CohenForcing.Condition I κ} {w : Vertex q} {j : I} {τ : (S).Name}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ) : j ∈ labelFiberSet w := by
  obtain ⟨a,ha⟩ := h
  exact orbitAssignment_label ha

variable (hμ c hcard hsize hmerger hj H E hE)

theorem assigned_permute (g : Vertex.RootGroup q) {d : CohenForcing.Condition I κ}
    {w : Vertex q} {j : I} {τ : (S).Name}
    (h : Assigned hμ c hcard hsize hmerger hj H E hE d w j τ) :
    Assigned hμ c hcard hsize hmerger hj H E hE (g • d) (g • w) (g • j) (g • τ) := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a,orbitAssignment_permute hμ c hcard hsize hmerger hj E hE _ g ha⟩

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## AssignmentCompatibility -/

namespace PartitionConsistency.LocalDiagramSystem
universe u
open DiagramOrder DiagramForcing
variable {M I : Type u} [LeftCancelMonoid M] [IsConical M]
noncomputable section

/-- The vertex associated to a literal available label at an extension of q. -/
def labelVertex {q : Diagram M I} (r : Diagram M I) (a : M) (ha : r.sub a = q)
    (j : I) (hj : j ∈ r.range) : Vertex q :=
  ⟨r,a,ha,(labelSystem (M := M)).availability r a ⟨j,hj⟩⟩

end
end PartitionConsistency.LocalDiagramSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_AssignedGraphs
attribute [-instance] _root_.OAI.PartitionConsistency.DiagramOrder.instIsConicalSubtypeMemSubmonoid _root_.OAI.PartitionConsistency.DiagramOrder.instLeftCancelMonoidSubtypeMemSubmonoid_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## AssignedGraph -/

namespace PartitionConsistency.ProductForcing.ChainCode
universe u
open SetForcingNames SetForcingNames.SymmetricSystem DiagramForcing ForcingQuotient
open DiagramOrder LocalDiagramSystem
noncomputable section
variable {M I κ : Type u} [LeftCancelMonoid M] [IsConical M]
variable {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ) (c : κ → ZFSet.{u})
variable [Infinite M] [Infinite I] [LinearOrder κ] [WellFoundedLT κ]
variable (hcard : Cardinal.mk M ≤ μ) (hsize : Cardinal.mk M < Cardinal.mk I)
variable (hmerger : HasFiniteMergers M) (hj : HasConditionalJoins (LeftDivOrder M))
variable (H : HeightCost (LeftDivOrder M)) {q : Diagram M I}
variable (E : (system (M := M) (I := I) (κ := κ) hμ).Name)
variable (hE : ∀ π ∈ SupportFilter.Fix q.range, π • E = E)
local notation "S" => system (M := M) (I := I) (κ := κ) hμ

/-- A bounded graph entry is witnessed by a genuine local assignment, with
forced equality to its literal label and its normalized class name. -/
def GraphWitness (p : Poset M I κ) (x y : (S).Name) : Prop :=
  ∃ (d : CohenForcing.Condition I κ) (w : Vertex q) (j : I)
    (τ : LocalName hμ c w.diagram),
    p ≤ (d,w.diagram) ∧ Assigned hμ c hcard hsize hmerger hj H E hE d w j τ.name ∧
    (S).atomic.EqF p x (label hμ c j) ∧ (S).atomic.EqF p y τ.name

/-- Density closure of the literal entry relation. -/
def GraphHolds (p : Poset M I κ) (x y : (S).Name) : Prop :=
  ∀ r, r ≤ p → ∃ s, s ≤ r ∧ GraphWitness hμ c hcard hsize hmerger hj H E hE s x y

def graphRelation : (S).BinaryRelation where
  holds := GraphHolds hμ c hcard hsize hmerger hj H E hE
  mono h hh r hr := hh r (hr.trans h)
  regular h r hr := by
    obtain ⟨s,hs,hh⟩ := h r hr
    obtain ⟨t,ht,hw⟩ := hh s le_rfl
    exact ⟨t,ht.trans hs,hw⟩
  congr := by
    intro p x x' y y' hx hy
    have step {x x' y y' : (S).Name} (hx : (S).atomic.EqF p x x')
        (hy : (S).atomic.EqF p y y')
        (h : GraphHolds hμ c hcard hsize hmerger hj H E hE p x y) :
        GraphHolds hμ c hcard hsize hmerger hj H E hE p x' y' := by
      intro r hr
      obtain ⟨s,hs,d,w,j,τ,hp,ha,hxj,hyτ⟩ := h r hr
      exact ⟨s,hs,d,w,j,τ,hp,ha,
        (S).atomic.eq_trans ((S).atomic.eq_symm ((S).atomic.eq_mono (hs.trans hr) hx)) hxj,
        (S).atomic.eq_trans ((S).atomic.eq_symm ((S).atomic.eq_mono (hs.trans hr) hy)) hyτ⟩
    exact ⟨step hx hy,step ((S).atomic.eq_symm hx) ((S).atomic.eq_symm hy)⟩

/-- Moving the condition, diagram, name and label together preserves the
literal graph predicate. The change of Cohen computation is essential. -/
theorem graphWitness_move (g : Vertex.RootGroup q) {p : Poset M I κ} {x y : (S).Name}
    (h : GraphWitness hμ c hcard hsize hmerger hj H E hE p x y) :
    GraphWitness hμ c hcard hsize hmerger hj H E hE ((S).move g.val p) (g • x) (g • y) := by
  obtain ⟨d,w,j,τ,hp,ha,hx,hy⟩ := h
  refine ⟨g • d,g • w,g • j,τ.transport hμ g.val,?_,
    assigned_permute hμ c hcard hsize hmerger hj H E hE g ha,?_,?_⟩
  · change (S).move g.val p ≤ ((d.permute g.val,w.diagram.permute g.val) : Poset M I κ)
    simpa only [move_coe,permute] using ((S).move g.val).monotone hp
  · change (S).atomic.EqF ((S).move g.val p) (g.val • x) (label hμ c (g.val j))
    simpa only [smul_label] using ((S).eq_symmetry g.val p x (label hμ c j)).mp hx
  · exact ((S).eq_symmetry g.val p y τ.name).mp hy

theorem graphRelation_move (g : Equiv.Perm I) (hg : g ∈ SupportFilter.Fix q.range)
    (p : Poset M I κ) (x y : (S).Name)
    (h : (graphRelation hμ c hcard hsize hmerger hj H E hE).holds p x y) :
    (graphRelation hμ c hcard hsize hmerger hj H E hE).holds ((S).move g p) (g • x) (g • y) := by
  intro r hr
  obtain ⟨s,hs,hw⟩ := h (((S).move g).symm r) (((S).move g).symm_apply_le.mpr hr)
  exact ⟨(S).move g s,((S).move g).le_symm_apply.mp hs,
    graphWitness_move hμ c hcard hsize hmerger hj H E hE ⟨g,hg⟩ hw⟩

/-- The collected graph is a set-sized HS name with the single support D_q. -/
def assignmentGraph : (S).Name :=
  (graphRelation hμ c hcard hsize hmerger hj H E hE).graph
    (labelSet hμ c) (quotientName hμ c E) (SupportFilter.Fix q.range)
    (localList_support hμ hcard q) (fun g _ => smul_labelSet hμ c g)
    (fun g hg => quotientName_fixed hμ c E g (hE g hg))
    (graphRelation_move hμ c hcard hsize hmerger hj H E hE)

end
end PartitionConsistency.ProductForcing.ChainCode


/-! ## GraphDensity -/


/-! ## CountableHull -/

/-! Small hulls for countably-ary operations, used for the chain condition of
countable Cohen forcing. The construction is a genuine well-founded term
algebra; no elementary-submodel or large-cardinal assumption is needed. -/


/-! ## CohenChain -/

/-! Chain condition for the actual countable Cohen conditions. The small
hull is a well-founded term algebra, so this proof adds no hypothesis about
an elementary submodel or a delta-system. -/
namespace PartitionConsistency.CohenForcing.Condition
universe u
noncomputable section
open scoped Classical
variable {I κ : Type u}

theorem exists_code (d : Condition I κ) :
    ∃ f : ℕ → Option ((I × κ) × Bool),
      Set.range f = Set.insert none (Option.some '' d.graph) := by
  obtain ⟨f,hf⟩ := ((d.countable_graph.image Option.some).insert none).exists_eq_range
    (Set.insert_nonempty _ _)
  exact ⟨f,hf.symm⟩

def code (d : Condition I κ) : ℕ → Option ((I × κ) × Bool) :=
  (exists_code d).choose

def decode (f : ℕ → Option ((I × κ) × Bool)) : Condition I κ :=
  if h : ∃ d : Condition I κ, Set.range f = Set.insert none (Option.some '' d.graph)
    then h.choose else ⊤

def compatibleChoice (A : Set (Condition I κ)) (d : Condition I κ) : Condition I κ :=
  if h : ∃ e ∈ A, Compatible d e then h.choose else ⊤

def restrictedGraph (p : Condition I κ) (S : Set (Option ((I × κ) × Bool))) :
    Condition I κ where
  graph := {z | z ∈ p.graph ∧ some z ∈ S}
  functional a b c hb hc := p.functional a b c hb.1 hc.1
  countable_graph := p.countable_graph.mono (fun _ h => h.1)

end
end PartitionConsistency.CohenForcing.Condition


/-! ## ChainPreservation -/

/-! Cardinal preservation from the actual chain condition. The statements
below concern the internal set-graph surjection sentence and arbitrary name
ranks. No existence of an ambient fully generic filter is used. -/

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_OrderedSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## LeastOccurrence -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable {S : SymmetricSystem.{u} P Γ}

namespace LeastOccurrence
variable (X : ZFSet.{u}) (R : X → S.UnaryRelation)

/-- Occurrence at this index and forced nonoccurrence at every smaller
index in the fixed ground wellordering. -/
def At (p : P) (x : S.Name) (i : X) : Prop :=
  (R i).holds p x ∧ ∀ j, WellOrderingRel j i → ∀ q, q ≤ p → ¬ (R j).holds q x

omit [OrderTop P] in
theorem mono {p q : P} {x : S.Name} {i : X} (h : q ≤ p) (hi : At X R p x i) : At X R q x i :=
  ⟨(R i).mono h hi.1,fun j hj r hr => hi.2 j hj r (hr.trans h)⟩

omit [OrderTop P] in
theorem congr {p : P} {x y : S.Name} {i : X} (he : S.atomic.EqF p x y) :
    At X R p x i ↔ At X R p y i := by
  have step {x y : S.Name} (he : S.atomic.EqF p x y) (h : At X R p x i) : At X R p y i := by
    refine ⟨((R i).congr he).mp h.1,?_⟩
    intro j hj q hq hy
    exact h.2 j hj q hq (((R j).congr (S.atomic.eq_mono hq he)).mpr hy)
  exact ⟨step he,step (S.atomic.eq_symm he)⟩

def predicate (i : X) : S.UnaryRelation where
  holds p x := At X R p x i
  mono := mono X R
  regular := by
    intro p x h
    refine ⟨(R i).regular (fun q hq => (h q hq).imp (fun r hr => ⟨hr.1,hr.2.1⟩)),?_⟩
    intro j hj q hq hi
    obtain ⟨r,hrq,hr⟩ := h q hq
    exact hr.2 j hj r le_rfl ((R j).mono hrq hi)
  congr := congr X R

omit [OrderTop P] in
theorem move (H : Subgroup Γ)
    (hR : ∀ g ∈ H, ∀ i p x, (R i).holds p x → (R i).holds (S.move g p) (g • x))
    (g : Γ) (hg : g ∈ H) {p : P} {x : S.Name} {i : X} (hi : At X R p x i) :
    At X R (S.move g p) (g • x) i := by
  refine ⟨hR g hg i p x hi.1,?_⟩
  intro j hj q hq hh
  have hback := hR g⁻¹ (H.inv_mem hg) j q (g • x) hh
  have heq : S.move g⁻¹ q = (S.move g).symm q := by
    change S.codeEquiv.symm (S.action.perm g⁻¹ (S.codeEquiv q)) =
      S.codeEquiv.symm ((S.action.perm g).symm (S.codeEquiv q))
    rw [map_inv]
    rfl
  simp only [inv_smul_smul,heq] at hback
  exact hi.2 j hj ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq) hback

/-- The least-index graph, regularized in both the value and index names. -/
def relation : S.BinaryRelation where
  holds p x y := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : X,
    S.atomic.EqF r y (Name.check i.val) ∧ At X R r x i
  mono h hh q hq := hh q (hq.trans h)
  regular h q hq := by
    obtain ⟨r,hrq,hr⟩ := h q hq
    obtain ⟨s,hsr,i,hi⟩ := hr r le_rfl
    exact ⟨s,hsr.trans hrq,i,hi⟩
  congr := by
    intro p x x' y y' hx hy
    have step {x x' y y' : S.Name} (hx : S.atomic.EqF p x x') (hy : S.atomic.EqF p y y')
        (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : X,
          S.atomic.EqF r y (Name.check i.val) ∧ At X R r x i) :
        ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i : X,
          S.atomic.EqF r y' (Name.check i.val) ∧ At X R r x' i := by
      intro q hq
      obtain ⟨r,hrq,i,hi,hr⟩ := h q hq
      exact ⟨r,hrq,i,S.atomic.eq_trans (S.atomic.eq_symm (S.atomic.eq_mono (hrq.trans hq) hy)) hi,
        (congr X R (S.atomic.eq_mono (hrq.trans hq) hx)).mp hr⟩
    exact ⟨step hx hy,step (S.atomic.eq_symm hx) (S.atomic.eq_symm hy)⟩

end LeastOccurrence
end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## WellorderedImage -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The value of a function at the (at most one) point of a given ordinal
index in an injection of its domain. -/
def indexedImage (f J X Y : S.Name) (Ξ : ZFSet.{u}) (i : Ξ) : S.UnaryRelation where
  holds p y := ((S.boundedApp J X (Name.check Ξ)).inverse.comp
    (S.boundedApp f X Y)).holds p (Name.check i.val) y
  mono := BinaryRelation.mono _
  regular := BinaryRelation.regular _
  congr hx := BinaryRelation.congr _ (S.atomic.eq_refl _ _) hx

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## RelationFamily -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w i
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable {S : SymmetricSystem.{u} P Γ}

namespace BinaryRelation
/-- Regular union of an arbitrary indexed family of binary relations. The
bounded graph constructor subsequently makes this relation an actual set. -/
def familyUnion {ι : Sort i} (R : ι → S.BinaryRelation) : S.BinaryRelation where
  holds p x y := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i, (R i).holds r x y
  mono h hh q hq := hh q (hq.trans h)
  regular h q hq := by
    obtain ⟨r,hrq,hr⟩ := h q hq
    obtain ⟨s,hsr,i,hi⟩ := hr r le_rfl
    exact ⟨s,hsr.trans hrq,i,hi⟩
  congr := by
    intro p x x' y y' hx hy
    have step {x x' y y' : S.Name} (hx : S.atomic.EqF p x x') (hy : S.atomic.EqF p y y')
        (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i, (R i).holds r x y) :
        ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ i, (R i).holds r x' y' := by
      intro q hq
      obtain ⟨r,hrq,i,hi⟩ := h q hq
      exact ⟨r,hrq,i,((R i).congr (S.atomic.eq_mono (hrq.trans hq) hx)
        (S.atomic.eq_mono (hrq.trans hq) hy)).mp hi⟩
    exact ⟨step hx hy,step (S.atomic.eq_symm hx) (S.atomic.eq_symm hy)⟩

end BinaryRelation

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## WellorderedSection -/

namespace PartitionConsistency.SetLanguage
/-- A preimage for the (possibly absent) value at one ordinal index. -/
def indexedSection : Formula 6 :=
  .all ((Formula.mem 6 2).imp ((edge 3 6 4).imp ((Formula.mem 5 1).conj (edge 0 5 6))))
end PartitionConsistency.SetLanguage

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

def sectionPart (J Y i x : S.Name) : S.BinaryRelation where
  holds p y z := S.atomic.MemF p y Y ∧ S.App p J y i ∧ S.atomic.EqF p z x
  mono h hh := ⟨S.atomic.mem_mono h hh.1,S.app_mono h hh.2.1,S.atomic.eq_mono h hh.2.2⟩
  regular h := ⟨S.atomic_regular.2 _ _ _ (fun q hq => (h q hq).imp
    (fun _ hr => ⟨hr.1,hr.2.1⟩)),(S.appRelation J).regular (fun q hq => (h q hq).imp
    (fun _ hr => ⟨hr.1,hr.2.2.1⟩)),S.atomic_regular.1 _ _ _ (fun q hq => (h q hq).imp
    (fun _ hr => ⟨hr.1,hr.2.2.2⟩))⟩
  congr hy hz := and_congr (S.atomic.mem_congr hy (S.atomic.eq_refl _ _))
    (and_congr (S.app_congr (S.atomic.eq_refl _ _) hy (S.atomic.eq_refl _ _))
      ⟨fun h => S.atomic.eq_trans (S.atomic.eq_symm hz) h,fun h => S.atomic.eq_trans hz h⟩)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_SliceGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## SubsetImage -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

def subsetImageGraph (f A D d : S.Name) : S.Name :=
  ((S.defaultRelation f D d).bounded A D).graph A D (S.tupleStabilizer ![f,A,D,d])
    (S.tupleStabilizer_mem _) (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 1)
    (fun g hg => (S.mem_tupleStabilizer _ g).mp hg 2) (by
      intro g hg p a y h
      have hf : g • f = f := (S.mem_tupleStabilizer _ g).mp hg 0
      have hA : g • A = A := (S.mem_tupleStabilizer _ g).mp hg 1
      have hD : g • D = D := (S.mem_tupleStabilizer _ g).mp hg 2
      have hd : g • d = d := (S.mem_tupleStabilizer _ g).mp hg 3
      refine ⟨?_,?_,(S.defaultRelation_symmetry f D d g hf hD hd p a y).mp h.2.2⟩
      · simpa only [hA] using (S.mem_symmetry g p a A).mp h.1
      · simpa only [hD] using (S.mem_symmetry g p y D).mp h.2.1)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## SliceRelations -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable {S : SymmetricSystem.{u} P Γ}

namespace BinaryRelation
/-- Existential projection, with the regular forcing meaning of existence. -/
def image (R : S.BinaryRelation) : S.UnaryRelation where
  holds p y := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name, R.holds r x y
  mono h hh q hq := hh q (hq.trans h)
  regular h q hq := by
    obtain ⟨r,hrq,hr⟩ := h q hq
    obtain ⟨s,hsr,x,hx⟩ := hr r le_rfl
    exact ⟨s,hsr.trans hrq,x,hx⟩
  congr := by
    intro p y z he
    have step {y z : S.Name} (he : S.atomic.EqF p y z)
        (h : ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name, R.holds r x y) :
        ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ x : S.Name, R.holds r x z := by
      intro q hq
      obtain ⟨r,hrq,x,hx⟩ := h q hq
      exact ⟨r,hrq,x,(R.congr (S.atomic.eq_refl r x) (S.atomic.eq_mono (hrq.trans hq) he)).mp hx⟩
    exact ⟨step he,step (S.atomic.eq_symm he)⟩

omit [OrderTop P] in
theorem image_move (R : S.BinaryRelation) (g : Γ)
    (hR : ∀ p x y, R.holds p x y → R.holds (S.move g p) (g • x) (g • y))
    (p : P) (y : S.Name) (h : R.image.holds p y) :
    R.image.holds (S.move g p) (g • y) := by
  intro q hq
  obtain ⟨r,hrq,x,hx⟩ := h ((S.move g).symm q) ((S.move g).symm_apply_le.mpr hq)
  exact ⟨S.move g r,(S.move g).le_symm_apply.mp hrq,g • x,hR r x y hx⟩

end BinaryRelation

/-- Parameters of the ordinal slicing of a presentation and a surjection.
There are no correctness assumptions in this structure. -/
structure SliceData (S : SymmetricSystem.{u} P Γ) where
  s : S.Name
  f : S.Name
  A : S.Name
  X : S.Name
  Y : S.Name
  O : ZFSet.{u}

namespace SliceData
variable (D : SliceData S)

def support : Subgroup Γ := S.tupleStabilizer ![D.s,D.f,D.A,D.X,D.Y]
omit [OrderTop P] in
theorem support_mem : D.support ∈ S.filter := S.tupleStabilizer_mem _
omit [OrderTop P] in
theorem fix_s {g : Γ} (hg : g ∈ D.support) : g • D.s = D.s := (S.mem_tupleStabilizer _ g).mp hg 0
omit [OrderTop P] in
theorem fix_f {g : Γ} (hg : g ∈ D.support) : g • D.f = D.f := (S.mem_tupleStabilizer _ g).mp hg 1
omit [OrderTop P] in
theorem fix_A {g : Γ} (hg : g ∈ D.support) : g • D.A = D.A := (S.mem_tupleStabilizer _ g).mp hg 2
omit [OrderTop P] in
theorem fix_X {g : Γ} (hg : g ∈ D.support) : g • D.X = D.X := (S.mem_tupleStabilizer _ g).mp hg 3
omit [OrderTop P] in
theorem fix_Y {g : Γ} (hg : g ∈ D.support) : g • D.Y = D.Y := (S.mem_tupleStabilizer _ g).mp hg 4

/-- The restriction of the presentation to the i-th Cartesian slice. -/
def slice (i : D.O) : S.BinaryRelation where
  holds p a x := S.atomic.MemF p a D.A ∧ S.atomic.MemF p x D.X ∧
    S.App p D.s (a.opair (Name.check i.val)) x
  mono h hh := ⟨S.atomic.mem_mono h hh.1,S.atomic.mem_mono h hh.2.1,S.app_mono h hh.2.2⟩
  regular h := ⟨S.atomic_regular.2 _ _ _ (fun q hq => (h q hq).imp
    (fun _ hr => ⟨hr.1,hr.2.1⟩)),S.atomic_regular.2 _ _ _ (fun q hq => (h q hq).imp
    (fun _ hr => ⟨hr.1,hr.2.2.1⟩)),(S.appRelation D.s).regular (fun q hq => (h q hq).imp
    (fun _ hr => ⟨hr.1,hr.2.2.2⟩))⟩
  congr ha hx := and_congr (S.atomic.mem_congr ha (S.atomic.eq_refl _ _))
    (and_congr (S.atomic.mem_congr hx (S.atomic.eq_refl _ _))
      (S.app_congr (S.atomic.eq_refl _ _) (S.eq_opair_congr ha (S.atomic.eq_refl _ _)) hx))

theorem slice_move (g : Γ) (hg : g ∈ D.support) (i : D.O) (p : P) (a x : S.Name)
    (h : (D.slice i).holds p a x) : (D.slice i).holds (S.move g p) (g • a) (g • x) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [D.fix_A hg] using (S.mem_symmetry g p a D.A).mp h.1
  · simpa only [D.fix_X hg] using (S.mem_symmetry g p x D.X).mp h.2.1
  · simpa only [D.fix_s hg,Name.smul_opair,Name.smul_check] using
      (S.app_symmetry g p D.s (a.opair (Name.check i.val)) x).mp h.2.2

def B (i : D.O) : S.Name :=
  (D.slice i).image.select D.X D.support D.support_mem (fun _ hg => D.fix_X hg)
    (fun g hg => BinaryRelation.image_move _ g (D.slice_move g hg i))

theorem fix_B (g : Γ) (hg : g ∈ D.support) (i : D.O) : g • D.B i = D.B i :=
  UnaryRelation.select_fixed _ _ _ _ _ _ g hg

/-- An occurrence of a target value in f[B_i]. -/
def occurrence (i : D.O) : S.UnaryRelation := (S.boundedApp D.f (D.B i) D.Y).image

theorem occurrence_move (g : Γ) (hg : g ∈ D.support) (i : D.O) (p : P) (y : S.Name)
    (h : (D.occurrence i).holds p y) : (D.occurrence i).holds (S.move g p) (g • y) :=
  BinaryRelation.image_move _ g (S.boundedApp_move D.f (D.B i) D.Y g
    (D.fix_f hg) (D.fix_B g hg i) (D.fix_Y hg)) p y h

/-- The target pieces are occurrences at their least index in the fixed
wellordering of the ground ordinal. -/
def Ypart (i : D.O) : S.Name :=
  (LeastOccurrence.predicate D.O D.occurrence i).select D.Y D.support D.support_mem
    (fun _ hg => D.fix_Y hg)
    (fun g hg _ _ h => LeastOccurrence.move D.O D.occurrence D.support D.occurrence_move g hg h)

theorem fix_Ypart (g : Γ) (hg : g ∈ D.support) (i : D.O) : g • D.Ypart i = D.Ypart i :=
  UnaryRelation.select_fixed _ _ _ _ _ _ g hg

def preimage (i : D.O) : S.UnaryRelation := (S.boundedApp D.f (D.B i) (D.Ypart i)).inverse.image

theorem preimage_move (g : Γ) (hg : g ∈ D.support) (i : D.O) (p : P) (x : S.Name)
    (h : (D.preimage i).holds p x) : (D.preimage i).holds (S.move g p) (g • x) :=
  BinaryRelation.image_move _ g (fun p y x h => S.boundedApp_move D.f (D.B i) (D.Ypart i) g
    (D.fix_f hg) (D.fix_B g hg i) (D.fix_Ypart g hg i) p x y h) p x h

/-- The source pieces are B_i intersected with the preimages of Y_i. -/
def Spart (i : D.O) : S.Name :=
  (D.preimage i).select (D.B i) D.support D.support_mem (fun g hg => D.fix_B g hg i)
    (fun g hg => D.preimage_move g hg i)

end SliceData
end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## SliceGeometry -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable {S : SymmetricSystem.{u} P Γ}

namespace SliceData
variable (D : SliceData S)

def sliceGraph (i : D.O) : S.Name :=
  (D.slice i).graph D.A (D.B i) D.support D.support_mem (fun _ hg => D.fix_A hg)
    (fun g hg => D.fix_B g hg i) (fun g hg => D.slice_move g hg i)

/-- Restrict f to the disjoint source and target pieces. -/
def partGraph (i : D.O) : S.Name := S.restrictionGraph D.f (D.Spart i) (D.Ypart i)

end SliceData
end
end PartitionConsistency.SetForcingNames.SymmetricSystem

end OAI
end

section
-- module Solutions.OAIQ5_T1.PartitionConsistency_Models_SliceAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ## SliceAssembly -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

/-- The empty binary relation, with its regular interpretation. -/
def falseRelation : S.BinaryRelation where
  holds _ _ _ := False
  mono _ h := h
  regular h := by obtain ⟨_,_,h⟩ := h _ le_rfl; exact h
  congr _ _ := Iff.rfl

end
end PartitionConsistency.SetForcingNames.SymmetricSystem


/-! ## SliceCandidates -/

end OAI
end


