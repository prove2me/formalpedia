-- Prove2me | Definitions.Def_OAI_BinPackingGap_Part08
-- name    : OAI_BinPackingGap_Part08
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T18:51:03.704981+00:00
-- url     : https://prove2.me/theorems/ab81d597-06e8-4753-9e46-9ef9330f4733
-- title:
--   Structural additive gap for bin packing, part 8 of 10 (port of OpenAI's formalization)
-- statement:
--   Part 8 of 10 of a port of OpenAI's Lean formalization of the structural additive gap from the manuscript *Additive hardness and unbounded configuration gaps in bin packing* (OpenAI, September 24, 2026). For every $c$, it constructs an instance with $5B$ items of sizes in $(1/6,1)$ whose individual and type configuration LPs both equal $B$, while the optimum exceeds $B+c$. This part contains the modules `Trees/InventoryFromTrees`, `Inventory/LocalCompletionCoverage`, `Inventory/PackingExclusions`, `Trees/InventoryRowGeometry`, `Machines/PackingJobCoverage`, `Configurations/CoverageSoundness`, `Trees/TreeAvoidance`, `Packing/PhaseIteration`, `Trees/CompetingTrees`, `Packing/ExtractedCover`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/BinPacking`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `BinPackingGap`, which matches upstream `Model.lean` up to two private lemmas and a section wrapper. This part sets `maxHeartbeats` to 1000000, because the platform compiler exceeded the default heartbeat limit on a `simp` call that stays far below it locally.
--
--   The development is split into 10 parts only so that each compiles within the platform's time limit. The final part proves `OAI.BinPackingGap.structural_additive_gap`, the first clause of `OAI.BinPackingGap.main_results`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/BinPacking: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Trees/InventoryFromTrees.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Inventory/LocalCompletionCoverage.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Inventory/PackingExclusions.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Trees/InventoryRowGeometry.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/PackingJobCoverage.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Configurations/CoverageSoundness.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Trees/TreeAvoidance.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/PhaseIteration.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Trees/CompetingTrees.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/ExtractedCover.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf

/-
Structural additive gap for bin packing (port of OpenAI's formalization), part 8 of 10.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/BinPacking/: Trees/InventoryFromTrees.lean, Inventory/LocalCompletionCoverage.lean, Inventory/PackingExclusions.lean, Trees/InventoryRowGeometry.lean, Machines/PackingJobCoverage.lean, Configurations/CoverageSoundness.lean, Trees/TreeAvoidance.lean, Packing/PhaseIteration.lean, Trees/CompetingTrees.lean, Packing/ExtractedCover.lean
These files formalize part of the manuscript "Additive hardness and unbounded configuration gaps in
bin packing" (OpenAI, September 24, 2026). Copyright OpenAI. Licensed under the Apache License,
Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same
license, on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Model.lean) come from the platform definition `BinPackingGap`, to which upstream Model.lean
is identical up to two private lemmas and a section wrapper; `set_option maxHeartbeats 1000000` is set for this part (the platform compiler exceeded the default heartbeat limit on a `simp` call that stays far below it locally).
-/
import Mathlib
import Definitions.Def_OAI_BinPackingGap_Part07

set_option autoImplicit false
set_option maxHeartbeats 1000000

-- ===== Adapted from lean/OAI/Computability/BinPacking/Trees/InventoryFromTrees.lean =====
namespace OAI

namespace BinPackingGap.InventoryData

def ofCompetingTrees (G : GraphInput) {d : ℕ} (T : CompetingTrees d) (R k : ℕ) :
    InventoryData where
  graph := G
  plus := T.plus
  minus := T.minus
  d := d
  R := R
  L := T.height
  quota := T.quota
  k := k

@[simp] theorem ofCompetingTrees_P (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) :
    (ofCompetingTrees G T R k).P = T.quotaTotal := rfl

theorem ofCompetingTrees_plus_height (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) :
    (ofCompetingTrees G T R k).plus.height = (ofCompetingTrees G T R k).L :=
  T.plus_height

theorem ofCompetingTrees_minus_height (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) :
    (ofCompetingTrees G T R k).minus.height = (ofCompetingTrees G T R k).L :=
  T.minus_height

theorem ofCompetingTrees_height_pos (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) : 0 < (ofCompetingTrees G T R k).L :=
  T.height_pos

end BinPackingGap.InventoryData

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Inventory/LocalCompletionCoverage.lean =====
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

theorem exists_equiv_extending_injections
    {I J S : Type*} [Fintype I] [Fintype J]
    (f : S → I) (g : S → J) (hf : Function.Injective f) (hg : Function.Injective g)
    (hcard : Fintype.card I = Fintype.card J) :
    ∃ e : I ≃ J, ∀ s, e (f s) = g s :=
  exists_equiv_extending_embeddings ⟨f, hf⟩ ⟨g, hg⟩ hcard

end BinPackingGap.PartialAllocation

namespace BinPackingGap.InventoryData

open IntervalCoverage

variable (D : InventoryData)

theorem designated_injective (v : D.Vertex) :
    Function.Injective (D.designated (v := v)) := by
  rintro ⟨(p | p | j), a⟩ ⟨(q | q | k), b⟩ h <;>
    simp_all [designated, Subtype.val_inj]

theorem deadline_undesignated {v : D.Vertex} (i : D.MBase v)
    (hi : ∀ q : D.TestAt v × Fin D.d, D.designated q ≠ i) :
    D.deadline i = D.mainBaseline i := by
  rcases i with (⟨node, j⟩ | ⟨node, j⟩ | padding) | job
  · have hn : node.val ∉ D.plus.leaves := by
      intro hn
      exact hi (.inl ⟨node, hn⟩, j) rfl
    simp only [deadline, treeDeadline, hn, ite_false, mainBaseline, treeBaseline]
  · have hn : node.val ∉ D.minus.leaves := by
      intro hn
      exact hi (.inr (.inl ⟨node, hn⟩), j) rfl
    simp only [deadline, treeDeadline, hn, ite_false, mainBaseline, treeBaseline]
  · rfl
  · exact False.elim (hi (.inr (.inr job.1), job.2) rfl)

def deadlineShiftData (v : D.Vertex) :
    ShiftData (D.MBase v) (D.TestAt v) D.d ℚ where
  baseline := D.mainBaseline
  left := D.testLeft
  right := D.testRight
  designated := ⟨D.designated, D.designated_injective v⟩
  baseline_designated := D.mainBaseline_designated
  left_le_right := fun t => (D.testLeft_lt_testRight t).le

private theorem deadline_prefix_active (v : D.Vertex) (a : ℚ) :
    prefixCount (D.deadline (v := v)) a =
      prefixCount (D.mainBaseline (v := v)) a +
        D.d * ((D.deadlineShiftData v).activeTests a).card := by
  exact (D.deadlineShiftData v).deadline_prefix_of_agrees
    (D.deadline (v := v)) D.deadline_designated D.deadline_undesignated a

private theorem deadline_active_card (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    (v : D.Vertex) (a : ℚ) :
    ((D.deadlineShiftData v).activeTests a).card =
      @ite ℕ (∃ t : D.TestAt v, a ∈ D.testInterval t)
        (Classical.propDecidable _) 1 0 := by
  classical
  have hdisjoint : ∀ s t : D.TestAt v, s ≠ t →
      Disjoint (Set.Ico ((D.deadlineShiftData v).left s)
        ((D.deadlineShiftData v).right s))
        (Set.Ico ((D.deadlineShiftData v).left t)
        ((D.deadlineShiftData v).right t)) := by
    intro s t hst
    exact D.testInterval_disjoint hplusheight hminusheight hL hst
  have hc := (D.deadlineShiftData v).activeTests_card hdisjoint a
  by_cases ht : ∃ t : D.TestAt v, a ∈ D.testInterval t
  · rw [ite_eq_left ht]
    have ht' : ∃ t : D.TestAt v,
        (D.deadlineShiftData v).left t ≤ a ∧
          a < (D.deadlineShiftData v).right t := ht
    rw [ite_eq_left ht'] at hc
    exact hc
  · rw [ite_eq_right ht]
    have ht' : ¬ ∃ t : D.TestAt v,
        (D.deadlineShiftData v).left t ≤ a ∧
          a < (D.deadlineShiftData v).right t := ht
    rw [ite_eq_right ht'] at hc
    exact hc

theorem deadline_prefix (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    (v : D.Vertex) (a : ℚ) :
    prefixCount (D.deadline (v := v)) a =
      prefixCount (D.mainBaseline (v := v)) a +
        D.d * (@ite ℕ (∃ t : D.TestAt v, a ∈ D.testInterval t)
          (Classical.propDecidable _) 1 0) := by
  rw [D.deadline_prefix_active, D.deadline_active_card hplusheight hminusheight hL]

theorem deadline_prefix_at_test (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    (v : D.Vertex) (t : D.TestAt v) (a : ℚ) (ha : a ∈ D.testInterval t) :
    ((Finset.univ : Finset (D.MBase v)).filter (fun z => D.deadline z ≤ a)).card =
      ((Finset.univ : Finset (D.MBase v)).filter
        (fun z => D.mainBaseline z ≤ a)).card + D.d := by
  classical
  have hex : ∃ t : D.TestAt v, a ∈ D.testInterval t := ⟨t, ha⟩
  simpa only [prefixCount, prefixSet, ite_eq_left hex, Nat.mul_one] using
    D.deadline_prefix hplusheight hminusheight hL v a

theorem exists_deadline_matching (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    (v : D.Vertex) (h : D.MBase v → ℚ)
    (hle : ∀ b, h b ≤ D.mainBaseline b)
    (hcover : ∀ (t : D.TestAt v) (a : ℚ), a ∈ D.testInterval t →
      D.d ≤ coverageCount h D.mainBaseline a) :
    ∃ e : D.MBase v ≃ D.MBase v, ∀ b, h b ≤ D.deadline (e b) := by
  classical
  apply exists_equiv_of_prefix_dominance h D.deadline rfl
  intro a
  rw [D.deadline_prefix hplusheight hminusheight hL,
    completion_prefix_identity h D.mainBaseline hle]
  by_cases ht : ∃ t : D.TestAt v, a ∈ D.testInterval t
  · rw [ite_eq_left ht, Nat.mul_one]
    obtain ⟨t, ht⟩ := ht
    exact Nat.add_le_add_left (hcover t a ht) _
  · rw [ite_eq_right ht, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_add_right _ _

end BinPackingGap.InventoryData

namespace BinPackingGap.LocalResourceAllocation

open UniformTree

def oppositeTree {d : ℕ} (T : CompetingTrees d) : Bool → UniformTree
  | false => T.plus
  | true => T.minus

def oppositeMarking {d : ℕ} (T : CompetingTrees d) :
    (selected : Bool) → Finset (oppositeTree T selected).Node
  | false => T.markingPlus
  | true => T.markingMinus

abbrev OppositeMarked {d : ℕ} (T : CompetingTrees d) (selected : Bool) :=
  ↥(oppositeMarking T selected)

theorem opposite_height {d : ℕ} (T : CompetingTrees d) (selected : Bool) :
    (oppositeTree T selected).height = T.height := by
  cases selected
  · exact T.plus_height
  · exact T.minus_height

theorem opposite_depth_pos {d : ℕ} (T : CompetingTrees d) (selected : Bool)
    (a : OppositeMarked T selected) : 0 < depth a.val := by
  cases selected
  · exact T.markingPlus_depth_pos a.val a.property
  · exact T.markingMinus_depth_pos a.val a.property

theorem opposite_quota {d : ℕ} (T : CompetingTrees d) (selected : Bool)
    (ell : ℕ) (hlo : 1 ≤ ell) (hhi : ell ≤ T.height) :
    ((oppositeMarking T selected).filter (fun node => depth node = ell)).card ≤
      T.quota ell := by
  cases selected
  · exact T.plus_quota ell hlo hhi
  · exact T.minus_quota ell hlo hhi

variable (G : GraphInput) {d : ℕ} (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ)

local notation "D" => InventoryData.ofCompetingTrees G T R k

def markedDepth (selected : Bool) (a : OppositeMarked T selected) : (D).Depth :=
  ⟨depth a.val, Finset.mem_Icc.mpr
    ⟨opposite_depth_pos T selected a,
      (depth_le_height a.val).trans_eq (opposite_height T selected)⟩⟩

def markedByDepth (selected : Bool) : OppositeMarked T selected ↪
    Σ ell : (D).Depth,
      ↥((oppositeMarking T selected).filter (fun node => depth node = ell.val)) := by
  classical
  refine ⟨fun a => ⟨markedDepth G T R k selected a,
    ⟨a.val, Finset.mem_filter.mpr ⟨a.property, rfl⟩⟩⟩, ?_⟩
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun z => z.2.val) hab

def markedResource (selected : Bool) : OppositeMarked T selected ↪ (D).PositiveLocal := by
  classical
  exact (markedByDepth G T R k selected).trans
    (Function.Embedding.sigmaMap (Function.Embedding.refl (D).Depth) (fun ell =>
      (Finset.equivFin
        ((oppositeMarking T selected).filter (fun node => depth node = ell.val))).toEmbedding.trans
        (Fin.castLEEmb (opposite_quota T selected ell.val
          (Finset.mem_Icc.mp ell.property).1 (Finset.mem_Icc.mp ell.property).2))))

@[simp] theorem markedResource_depth (selected : Bool) (a : OppositeMarked T selected) :
    (markedResource G T R k selected a).1.val = depth a.val := rfl

def markedRow (v : G.Vertex) :
    (selected : Bool) → OppositeMarked T selected → (D).MBase v
  | false, a => .inl (.inl (a.val, ⟨0, hd⟩))
  | true, a => .inl (.inr (.inl (a.val, ⟨0, hd⟩)))

theorem markedRow_injective (v : G.Vertex) (selected : Bool) :
    Function.Injective (markedRow G T hd R k v selected) := by
  cases selected
  · intro a b hab
    apply Subtype.ext
    exact congrArg Prod.fst (Sum.inl.inj (Sum.inl.inj hab))
  · intro a b hab
    apply Subtype.ext
    exact congrArg Prod.fst (Sum.inl.inj (Sum.inr.inj (Sum.inl.inj hab)))

theorem fundedRoot_ne_markedRow (v : G.Vertex) (selected : Bool) (j : Fin d)
    (a : OppositeMarked T selected) :
    (D).fundedRoot selected j ≠ markedRow G T hd R k v selected a := by
  cases selected <;> intro h <;> cases Sum.inl.inj h

def zeroResource (v : G.Vertex) : Fin d ↪ (D).DMAt v := by
  clear hd
  have hstock : d ≤ (D).t - (D).P := by
    have h := (D).two_mul_d_le_t_sub_P
    change 2 * d ≤ (D).t - (D).P at h
    omega
  refine ⟨fun j => .inr (.inl (Fin.castLE hstock j)), ?_⟩
  intro a b hab
  exact Fin.castLE_injective hstock (Sum.inl.inj (Sum.inr.inj hab))

@[simp] theorem zeroResource_local_length (v : G.Vertex) (j : Fin d) :
    (D).localLength (.inl (zeroResource G T R k v j)) = 0 := rfl

def seedRows (v : G.Vertex) (selected : Bool) :
    (Fin d ⊕ OppositeMarked T selected) ↪ (D).MBase v := by
  refine ⟨Sum.elim ((D).fundedRoot selected) (markedRow G T hd R k v selected), ?_⟩
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl ((D).fundedRoot_injective v selected hab)
  · exact False.elim (fundedRoot_ne_markedRow G T hd R k v selected a b hab)
  · exact False.elim (fundedRoot_ne_markedRow G T hd R k v selected b a hab.symm)
  · exact congrArg Sum.inr (markedRow_injective G T hd R k v selected hab)

def seedResources (v : G.Vertex) (selected : Bool) :
    (Fin d ⊕ OppositeMarked T selected) ↪ (D).DMAt v := by
  refine ⟨Sum.elim (zeroResource G T R k v)
    (fun a => .inl (markedResource G T R k selected a)), ?_⟩
  intro a b hab
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl ((zeroResource G T R k v).injective hab)
  · have hbad : Sum.inr _ = Sum.inl _ := hab
    cases hbad
  · have hbad : Sum.inl _ = Sum.inr _ := hab
    cases hbad
  · exact congrArg Sum.inr ((markedResource G T R k selected).injective (Sum.inl.inj hab))

theorem exists_localEquiv (v : G.Vertex) (selected : Bool) :
    ∃ e : (D).MBase v ≃ (D).DMAt v,
      ∀ s : Fin d ⊕ OppositeMarked T selected,
        e (seedRows G T hd R k v selected s) = seedResources G T R k v selected s := by
  let : Fintype ((D).MBase v) := by
    dsimp [InventoryData.MBase, InventoryData.TreeRow, InventoryData.JobCopy,
      InventoryData.ofCompetingTrees]
    infer_instance
  let : Fintype ((D).DMAt v) := by
    dsimp [InventoryData.DMAt, InventoryData.PositiveLocal, InventoryData.ZeroLocalAt,
      InventoryData.Depth, InventoryData.JobCopy, InventoryData.ofCompetingTrees]
    infer_instance
  apply PartialAllocation.exists_equiv_extending_embeddings
    (seedRows G T hd R k v selected) (seedResources G T R k v selected)
  exact ((D).card_mBase v).trans ((D).card_dmAt v).symm

def localEquiv (v : G.Vertex) (selected : Bool) : (D).MBase v ≃ (D).DMAt v :=
  Classical.choose (exists_localEquiv G T hd R k v selected)

theorem localEquiv_seed (v : G.Vertex) (selected : Bool)
    (s : Fin d ⊕ OppositeMarked T selected) :
    localEquiv G T hd R k v selected (seedRows G T hd R k v selected s) =
      seedResources G T R k v selected s :=
  Classical.choose_spec (exists_localEquiv G T hd R k v selected) s

theorem localEquiv_fundedRoot (v : G.Vertex) (selected : Bool) (j : Fin d) :
    localEquiv G T hd R k v selected ((D).fundedRoot selected j) =
      zeroResource G T R k v j :=
  localEquiv_seed G T hd R k v selected (.inl j)

theorem localEquiv_markedRow (v : G.Vertex) (selected : Bool)
    (a : OppositeMarked T selected) :
    localEquiv G T hd R k v selected (markedRow G T hd R k v selected a) =
      .inl (markedResource G T R k selected a) :=
  localEquiv_seed G T hd R k v selected (.inr a)

theorem fundedRoot_local_zero (v : G.Vertex) (selected : Bool) (j : Fin d) :
    (D).localLength (.inl (localEquiv G T hd R k v selected ((D).fundedRoot selected j))) =
      0 := by
  rw [localEquiv_fundedRoot, zeroResource_local_length]

theorem markedRow_local_length (v : G.Vertex) (selected : Bool)
    (a : OppositeMarked T selected) :
    (D).localLength (.inl (localEquiv G T hd R k v selected
      (markedRow G T hd R k v selected a))) =
      Geometry.lambda G.edges.length R (D).geometryBound (depth a.val) := by
  rw [localEquiv_markedRow]
  change Geometry.lambda G.edges.length R (D).geometryBound
    (markedResource G T R k selected a).1.val = _
  rw [markedResource_depth]

theorem plusMarked_local_length (v : G.Vertex) (node : T.plus.Node)
    (hnode : node ∈ T.markingPlus) :
    (D).localLength (.inl (localEquiv G T hd R k v false
      (.inl (.inl (node, ⟨0, hd⟩))))) =
      Geometry.lambda G.edges.length R (D).geometryBound (depth node) :=
  markedRow_local_length G T hd R k v false ⟨node, hnode⟩

theorem minusMarked_local_length (v : G.Vertex) (node : T.minus.Node)
    (hnode : node ∈ T.markingMinus) :
    (D).localLength (.inl (localEquiv G T hd R k v true
      (.inl (.inr (.inl (node, ⟨0, hd⟩)))))) =
      Geometry.lambda G.edges.length R (D).geometryBound (depth node) :=
  markedRow_local_length G T hd R k v true ⟨node, hnode⟩

end BinPackingGap.LocalResourceAllocation

namespace BinPackingGap.LocalCompletionCoverage

open InventoryData IntervalCoverage

private theorem card_le_coverage {ι κ : Type*} [Fintype ι]
    (h baseline : ι → ℚ) (a : ℚ) (s : Finset κ) (f : κ → ι)
    (hf : Function.Injective f)
    (hc : ∀ x ∈ s, h (f x) ≤ a ∧ a < baseline (f x)) :
    s.card ≤ coverageCount h baseline a := by
  classical
  exact Finset.card_le_card_of_injOn f
    (fun x hx => (mem_coverageSet h baseline a (f x)).mpr (hc x hx))
    (fun _ _ _ _ hxy => hf hxy)

private theorem nodeInterval_subset_root {U : UniformTree} (node : U.Node)
    (m R B : ℕ) (side : TreeGeometry.Side) (hB : U.branchBound ≤ B)
    {a : ℚ}
    (ha : a ∈ Set.Ico (TreeGeometry.left m R B side node.val)
      (TreeGeometry.right m R B side node.val)) :
    a ∈ Set.Ico (TreeGeometry.rootOffset side) (TreeGeometry.rootOffset side + 1) := by
  have he := TreeGeometry.prefix_endpoints m R B side
    (u := []) (v := node.val) List.nil_prefix (TreeGeometry.boundedAddress_node node hB)
  simp only [TreeGeometry.left_nil, TreeGeometry.right_nil] at he
  exact ⟨he.1.trans ha.1, ha.2.trans_le he.2⟩

variable (G : GraphInput) {d : ℕ} (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ)

local notation "D" => InventoryData.ofCompetingTrees G T R k

local instance mainFintype (v : G.Vertex) : Fintype ((D).MBase v) := by
  dsimp [InventoryData.MBase, InventoryData.TreeRow, InventoryData.JobCopy,
    InventoryData.ofCompetingTrees]
  infer_instance

def localCompletion (v : G.Vertex) (selected : Bool) (b : (D).MBase v) : ℚ :=
  (D).rowCoordinate ((D).stateMainRow v selected b) - (D).stateMainLength selected b -
    (D).localLength (.inl (LocalResourceAllocation.localEquiv G T hd R k v selected b))

theorem localCompletion_le_baseline (v : G.Vertex) (selected : Bool) (b : (D).MBase v) :
    localCompletion G T hd R k v selected b ≤ (D).mainBaseline b := by
  have hg := (D).stateMainLength_nonneg selected b
  have hl := (D).localLength_nonneg
    (.inl (LocalResourceAllocation.localEquiv G T hd R k v selected b))
  have hdelta := Geometry.delta_nonneg G.edges.length R (D).geometryBound (D).L
  have hshort : (0 : ℚ) ≤
      if (D).rowShort ((D).stateMainRow v selected b) then
        Geometry.delta G.edges.length R (D).geometryBound (D).L else 0 := by
    split_ifs
    · exact hdelta
    · exact le_rfl
  have hbase := (D).stateMainRow_baseline v selected b
  unfold localCompletion rowCoordinate
  dsimp only [InventoryData.ofCompetingTrees] at *
  rw [hbase]
  linarith

private theorem fundedRoot_covers (v : G.Vertex) (selected : Bool) (j : Fin d)
    {a : ℚ} (ha : a ∈ Set.Ico (if selected then 0 else 4) (if selected then 1 else 5)) :
    localCompletion G T hd R k v selected ((D).fundedRoot selected j) ≤ a ∧
      a < (D).mainBaseline ((D).fundedRoot (v := v) selected j) := by
  have hzero := LocalResourceAllocation.fundedRoot_local_zero G T hd R k v selected j
  have hglobal := (D).stateMainLength_fundedRoot (v := v) selected j
  unfold localCompletion
  rw [hzero, hglobal]
  cases selected <;>
    norm_num [fundedRoot, stateMainRow, stateRowEquiv, rowCoordinate, rowBaseline,
      rowShort, mainBaseline, treeBaseline, UniformTree.root, TreeGeometry.right_nil,
      TreeGeometry.rootOffset] at ha ⊢ <;> exact ha

private theorem fundedRoot_coverage (v : G.Vertex) (selected : Bool) {a : ℚ}
    (ha : a ∈ Set.Ico (if selected then 0 else 4) (if selected then 1 else 5)) :
    d ≤ coverageCount (localCompletion G T hd R k v selected) (D).mainBaseline a := by
  classical
  have hc := card_le_coverage (localCompletion G T hd R k v selected)
    (D).mainBaseline a (Finset.univ : Finset (Fin d)) ((D).fundedRoot selected)
    ((D).fundedRoot_injective v selected)
    (fun j _ => fundedRoot_covers G T hd R k v selected j ha)
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

private theorem plusMarked_completion_le (v : G.Vertex) (node : T.plus.Node)
    (hnode : node ∈ T.markingPlus) :
    localCompletion G T hd R k v false (.inl (.inl (node, ⟨0, hd⟩))) ≤
      TreeGeometry.left G.edges.length R (D).geometryBound .plus node.val := by
  have hlocal := LocalResourceAllocation.plusMarked_local_length G T hd R k v node hnode
  have hglobal := (D).stateMainLength_nonneg false
    (.inl (.inl (node, ⟨0, hd⟩))) (v := v)
  have hn : node.val ≠ [] := by
    intro hn
    have hp := T.markingPlus_depth_pos node hnode
    simp [UniformTree.depth, hn] at hp
  have hcoord : (D).rowCoordinate
      ((D).stateMainRow v false (.inl (.inl (node, ⟨0, hd⟩)))) =
      TreeGeometry.right G.edges.length R (D).geometryBound .plus node.val := by
    change TreeGeometry.right G.edges.length R (D).geometryBound .plus node.val - 0 = _
    exact sub_zero _
  have hwidth : TreeGeometry.right G.edges.length R (D).geometryBound .plus node.val =
      TreeGeometry.left G.edges.length R (D).geometryBound .plus node.val +
        Geometry.lambda G.edges.length R (D).geometryBound (UniformTree.depth node) := by
    rw [TreeGeometry.right, TreeGeometry.width_of_ne_nil _ _ _ hn]
    rfl
  unfold localCompletion
  dsimp only [InventoryData.ofCompetingTrees] at *
  rw [hcoord, hlocal, hwidth]
  linarith

private theorem minusMarked_completion_le (v : G.Vertex) (node : T.minus.Node)
    (hnode : node ∈ T.markingMinus) :
    localCompletion G T hd R k v true (.inl (.inr (.inl (node, ⟨0, hd⟩)))) ≤
      TreeGeometry.left G.edges.length R (D).geometryBound .minus node.val := by
  have hlocal := LocalResourceAllocation.minusMarked_local_length G T hd R k v node hnode
  have hglobal := (D).stateMainLength_nonneg true
    (.inl (.inr (.inl (node, ⟨0, hd⟩)))) (v := v)
  have hn : node.val ≠ [] := by
    intro hn
    have hp := T.markingMinus_depth_pos node hnode
    simp [UniformTree.depth, hn] at hp
  have hcoord : (D).rowCoordinate
      ((D).stateMainRow v true (.inl (.inr (.inl (node, ⟨0, hd⟩))))) =
      TreeGeometry.right G.edges.length R (D).geometryBound .minus node.val := by
    change TreeGeometry.right G.edges.length R (D).geometryBound .minus node.val - 0 = _
    exact sub_zero _
  have hwidth : TreeGeometry.right G.edges.length R (D).geometryBound .minus node.val =
      TreeGeometry.left G.edges.length R (D).geometryBound .minus node.val +
        Geometry.lambda G.edges.length R (D).geometryBound (UniformTree.depth node) := by
    rw [TreeGeometry.right, TreeGeometry.width_of_ne_nil _ _ _ hn]
    rfl
  unfold localCompletion
  dsimp only [InventoryData.ofCompetingTrees] at *
  rw [hcoord, hlocal, hwidth]
  linarith

private theorem plusMarked_coverage (v : G.Vertex) (leaf : (D).PlusLeaf) {a : ℚ}
    (ha : a ∈ (D).testInterval (.inl leaf : (D).TestAt v)) :
    d ≤ coverageCount (localCompletion G T hd R k v false) (D).mainBaseline a := by
  classical
  apply (T.plus_rich leaf.val leaf.property).trans
  apply card_le_coverage (localCompletion G T hd R k v false) (D).mainBaseline a
    (T.markingPlus.filter (fun node => UniformTree.ancestor node leaf.val))
    (fun node => .inl (.inl (node, ⟨0, hd⟩)))
  · intro x y hxy
    exact congrArg Prod.fst (Sum.inl.inj (Sum.inl.inj hxy))
  · intro node hnode
    obtain ⟨hmark, hancestor⟩ := Finset.mem_filter.mp hnode
    have he := TreeGeometry.prefix_endpoints G.edges.length R (D).geometryBound .plus
      hancestor (TreeGeometry.boundedAddress_node leaf.val (D).plus_branch_le_geometryBound)
    exact ⟨(plusMarked_completion_le G T hd R k v node hmark).trans (he.1.trans ha.1),
      ha.2.trans_le he.2⟩

private theorem minusMarked_coverage (v : G.Vertex) (leaf : (D).MinusLeaf) {a : ℚ}
    (ha : a ∈ (D).testInterval (.inr (.inl leaf) : (D).TestAt v)) :
    d ≤ coverageCount (localCompletion G T hd R k v true) (D).mainBaseline a := by
  classical
  apply (T.minus_rich leaf.val leaf.property).trans
  apply card_le_coverage (localCompletion G T hd R k v true) (D).mainBaseline a
    (T.markingMinus.filter (fun node => UniformTree.ancestor node leaf.val))
    (fun node => .inl (.inr (.inl (node, ⟨0, hd⟩))))
  · intro x y hxy
    exact congrArg Prod.fst (Sum.inl.inj (Sum.inr.inj (Sum.inl.inj hxy)))
  · intro node hnode
    obtain ⟨hmark, hancestor⟩ := Finset.mem_filter.mp hnode
    have he := TreeGeometry.prefix_endpoints G.edges.length R (D).geometryBound .minus
      hancestor (TreeGeometry.boundedAddress_node leaf.val (D).minus_branch_le_geometryBound)
    exact ⟨(minusMarked_completion_le G T hd R k v node hmark).trans (he.1.trans ha.1),
      ha.2.trans_le he.2⟩

private theorem shortJob_coverage (v : G.Vertex) (job : (D).IncidencePosition v) {a : ℚ}
    (ha : a ∈ (D).testInterval (.inr (.inr job) : (D).TestAt v)) :
    d ≤ coverageCount (localCompletion G T hd R k v false) (D).mainBaseline a := by
  classical
  have hc := card_le_coverage (localCompletion G T hd R k v false)
    (D).mainBaseline a (Finset.univ : Finset (Fin d))
    (fun j => .inr (job, j))
    (by intro i j hij; exact congrArg Prod.snd (Sum.inr.inj hij)) (by
      intro j _
      have hl := (D).localLength_nonneg
        (.inl (LocalResourceAllocation.localEquiv G T hd R k v false (.inr (job, j))))
      change Geometry.baseline G.edges.length R ((D).incidencePosition job) -
        Geometry.delta G.edges.length R (D).geometryBound (D).L - 0 -
        (D).localLength (.inl (LocalResourceAllocation.localEquiv G T hd R k v false
          (.inr (job, j)))) ≤ a ∧
        a < Geometry.baseline G.edges.length R ((D).incidencePosition job)
      change Geometry.baseline G.edges.length R ((D).incidencePosition job) -
          Geometry.delta G.edges.length R (D).geometryBound (D).L ≤ a ∧
        a < Geometry.baseline G.edges.length R ((D).incidencePosition job) at ha
      exact ⟨by linarith [ha.1], ha.2⟩)
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

theorem localCompletion_coverage (v : G.Vertex) (selected : Bool)
    (test : (D).TestAt v) (a : ℚ) (ha : a ∈ (D).testInterval test) :
    d ≤ coverageCount (localCompletion G T hd R k v selected) (D).mainBaseline a := by
  cases selected
  · rcases test with leaf | leaf | job
    · exact plusMarked_coverage G T hd R k v leaf ha
    · apply fundedRoot_coverage G T hd R k v false
      have hroot := nodeInterval_subset_root leaf.val G.edges.length R (D).geometryBound .minus
        (D).minus_branch_le_geometryBound ha
      norm_num [TreeGeometry.rootOffset] at hroot ⊢
      exact hroot
    · exact shortJob_coverage G T hd R k v job ha
  · rcases test with leaf | leaf | job
    · apply fundedRoot_coverage G T hd R k v true
      have hroot := nodeInterval_subset_root leaf.val G.edges.length R (D).geometryBound .plus
        (D).plus_branch_le_geometryBound ha
      norm_num [TreeGeometry.rootOffset] at hroot ⊢
      exact hroot
    · exact minusMarked_coverage G T hd R k v leaf ha
    · apply fundedRoot_coverage G T hd R k v true
      have hj := Geometry.closedJobCell_bounds
        (Geometry.jobTestInterval_subset_closedJobCell G.edges.length R (D).geometryBound
          (D).L ((D).incidencePosition job) ha)
      exact ⟨by dsimp; linarith [hj.1], hj.2⟩

theorem exists_anchorEquiv (v : G.Vertex) (selected : Bool) :
    ∃ e : (D).MBase v ≃ (D).MBase v, ∀ b,
      (D).rowCoordinate ((D).stateMainRow v selected b) - (D).stateMainLength selected b -
        (D).localLength (.inl (LocalResourceAllocation.localEquiv G T hd R k v selected b)) ≤
          (D).deadline (e b) := by
  exact (D).exists_deadline_matching T.plus_height T.minus_height T.height_pos v
    (localCompletion G T hd R k v selected)
    (localCompletion_le_baseline G T hd R k v selected)
    (localCompletion_coverage G T hd R k v selected)

end BinPackingGap.LocalCompletionCoverage

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Inventory/PackingExclusions.lean =====
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

theorem excludedPositions_card_le {T Pos : Type*} [Fintype Pos]
    (selected : Finset T) (I : T → Pos → Prop)
    (hunique : ∀ t ∈ selected, ∀ r s, I t r → I t s → r = s) :
    (excludedPositions selected I).card ≤ selected.card := by
  classical
  have witness (r : ↥(excludedPositions selected I)) : ∃ t ∈ selected, I t r :=
    (mem_excludedPositions selected I).mp r.property
  let f : ↥(excludedPositions selected I) → ↥selected := fun r =>
    ⟨(witness r).choose, (witness r).choose_spec.1⟩
  have hf (r : ↥(excludedPositions selected I)) : I (f r) r :=
    (witness r).choose_spec.2
  have hinj : Function.Injective f := by
    intro r s hrs
    have ht : (f r : T) = (f s : T) := congrArg (fun t : ↥selected => (t : T)) hrs
    apply Subtype.ext
    apply hunique (f r) (f r).property r s (hf r)
    rw [ht]
    exact hf s
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

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

theorem excludedRepetitions_card_le {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) :
    (excludedRepetitions bad e).card ≤ bad.card := by
  classical
  let f : ↥(excludedRepetitions bad e) → ↥bad := fun j =>
    ⟨(e, j), (mem_excludedRepetitions bad e).mp j.property⟩
  have hinj : Function.Injective f := by
    intro j k hjk
    apply Subtype.ext
    exact congrArg Prod.snd (congrArg (fun x : ↥bad => (x : E × Fin R)) hjk)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

theorem excluded_nonexcluded_card {E : Type*} {R : ℕ}
    (bad : Finset (E × Fin R)) (e : E) :
    (excludedRepetitions bad e).card + (nonexcludedRepetitions bad e).card = R := by
  classical
  have hdis : Disjoint (excludedRepetitions bad e) (nonexcludedRepetitions bad e) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact ((mem_nonexcludedRepetitions bad e).mp hk)
      ((mem_excludedRepetitions bad e).mp hj)
  have hunion : excludedRepetitions bad e ∪ nonexcludedRepetitions bad e = Finset.univ := by
    ext j
    by_cases hj : (e, j) ∈ bad <;> simp [hj]
  calc
    _ = (excludedRepetitions bad e ∪ nonexcludedRepetitions bad e).card :=
      (Finset.card_union_of_disjoint hdis).symm
    _ = R := by rw [hunion]; simp

theorem nonexcludedRepetitions_add_card_bound {E : Type*} {R P : ℕ}
    (bad : Finset (E × Fin R)) (e : E) (hbad : bad.card ≤ P) :
    R ≤ P + (nonexcludedRepetitions bad e).card := by
  calc
    R = (excludedRepetitions bad e).card + (nonexcludedRepetitions bad e).card :=
      (excluded_nonexcluded_card bad e).symm
    _ ≤ P + (nonexcludedRepetitions bad e).card :=
      Nat.add_le_add_right ((excludedRepetitions_card_le bad e).trans hbad) _

theorem nonexcludedRepetitions_card_ge {E : Type*} {R P : ℕ}
    (bad : Finset (E × Fin R)) (e : E) (hbad : bad.card ≤ P) :
    R - P ≤ (nonexcludedRepetitions bad e).card := by
  apply Nat.sub_le_iff_le_add.mpr
  simpa only [Nat.add_comm] using nonexcludedRepetitions_add_card_bound bad e hbad

theorem nonexcludedRepetitions_card_ge_real {E : Type*} {R P : ℕ}
    (bad : Finset (E × Fin R)) (e : E) (hbad : bad.card ≤ P) :
    (R : ℝ) - P ≤ ((nonexcludedRepetitions bad e).card : ℝ) := by
  have h : (R : ℝ) ≤ (P : ℝ) + ((nonexcludedRepetitions bad e).card : ℝ) := by
    exact_mod_cast nonexcludedRepetitions_add_card_bound bad e hbad
  apply sub_le_iff_le_add.mpr
  simpa only [add_comm] using h

theorem nonexcludedRepetitions_card_ge_of_unique_hits {T E : Type*} [Fintype E]
    {R P : ℕ} (selected : Finset T) (I : T → E × Fin R → Prop)
    (hunique : ∀ t ∈ selected, ∀ r s, I t r → I t s → r = s)
    (hselected : selected.card ≤ P) (e : E) :
    R - P ≤ (nonexcludedRepetitions (excludedPositions selected I) e).card :=
  nonexcludedRepetitions_card_ge _ e ((excludedPositions_card_le selected I hunique).trans hselected)

theorem nonexcludedRepetitions_card_ge_real_of_unique_hits {T E : Type*} [Fintype E]
    {R P : ℕ} (selected : Finset T) (I : T → E × Fin R → Prop)
    (hunique : ∀ t ∈ selected, ∀ r s, I t r → I t s → r = s)
    (hselected : selected.card ≤ P) (e : E) :
    (R : ℝ) - P ≤ ((nonexcludedRepetitions (excludedPositions selected I) e).card : ℝ) :=
  nonexcludedRepetitions_card_ge_real _ e
    ((excludedPositions_card_le selected I hunique).trans hselected)

namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def tupleHitsJob (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : D.Position) : Prop :=
  (tupleClosedInterval p e t ∩
    Geometry.closedJobCell D.graph.edges.length D.R D.geometryBound D.L r).Nonempty

def excludedAt (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) :
    Finset D.Position :=
  excludedPositions (zeroPositiveTuples p e v) (tupleHitsJob p e)

theorem selected_hits_job_unique (p : Packing I b) (e : D.Item ≃ I.Item)
    (hL : 1 ≤ D.L) (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) {r s : D.Position}
    (hr : tupleHitsJob p e t r) (hs : tupleHitsJob p e t s) : r = s :=
  Geometry.closedJobCell_unique_of_short_interval hL
    (selected_interval_length_first p e v t ht) hr hs

theorem excludedAt_card_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (hL : 1 ≤ D.L) (v : D.Vertex) : (excludedAt p e v).card ≤ D.P := by
  apply (excludedPositions_card_le (zeroPositiveTuples p e v) (tupleHitsJob p e) ?_).trans
    (zeroPositiveTuples_card_le p e v)
  intro t ht r s hr hs
  exact selected_hits_job_unique p e hL v t ht hr hs

def goodRepetitions (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (edge : D.Edge) : Finset (Fin D.R) :=
  nonexcludedRepetitions (excludedAt p e v) edge

theorem goodRepetitions_card_ge (p : Packing I b) (e : D.Item ≃ I.Item)
    (hL : 1 ≤ D.L) (v : D.Vertex) (edge : D.Edge) :
    D.R - D.P ≤ (goodRepetitions p e v edge).card :=
  nonexcludedRepetitions_card_ge _ edge (excludedAt_card_le p e hL v)

theorem goodRepetitions_card_ge_real (p : Packing I b) (e : D.Item ≃ I.Item)
    (hL : 1 ≤ D.L) (v : D.Vertex) (edge : D.Edge) :
    (D.R : ℝ) - D.P ≤ ((goodRepetitions p e v edge).card : ℝ) :=
  nonexcludedRepetitions_card_ge_real _ edge (excludedAt_card_le p e hL v)

theorem covering_not_selected_of_nonexcluded (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (hr : r ∉ excludedAt p e v)
    (t : p.TableBin (subclass e))
    (ht : t ∈ tupleCovering p e v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r)) :
    t ∉ zeroPositiveTuples p e v := by
  intro hselected
  apply hr
  apply (mem_excludedPositions _ _).mpr
  refine ⟨t, hselected, ?_⟩
  obtain ⟨_, hlo, hhi⟩ := (mem_tupleCovering p e v _ t).mp ht
  refine ⟨Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r,
    ⟨hlo, hhi.le⟩, ?_⟩
  exact Geometry.jobInterior_mem_closedJobCell _ _ _ _ _

end PackingCounts
end BinPackingGap

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Trees/InventoryRowGeometry.lean =====
namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

private theorem node_right_in_root {T : UniformTree} (v : T.Node)
    (s : TreeGeometry.Side) (hT : T.branchBound ≤ D.geometryBound) :
    TreeGeometry.rootOffset s ≤
        TreeGeometry.right D.graph.edges.length D.R D.geometryBound s v.val ∧
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound s v.val ≤
        TreeGeometry.rootOffset s + 1 := by
  apply TreeGeometry.nodeCell_subset_root D.graph.edges.length D.R D.geometryBound s hT v
  exact ⟨(TreeGeometry.left_lt_right _ _ _ _ _).le, le_rfl⟩

theorem rowBaseline_le_one_of_not_tm {v : D.Vertex} (r : D.RowAt v)
    (hclass : D.rowSubclass r ≠ .tm) : D.rowBaseline r ≤ 1 := by
  rcases r with t | ⟨short, j⟩
  · rcases t with ⟨node, i⟩ | ⟨node, i⟩ | i
    · have h := D.node_right_in_root node .plus D.plus_branch_le_geometryBound
      simpa only [rowBaseline, treeBaseline, TreeGeometry.rootOffset, zero_add] using h.2
    · exact (hclass rfl).elim
    · exact le_rfl
  · exact (Geometry.job_baseline_lt_one _ _ _).le

theorem rowBaseline_ge_four_of_tm {v : D.Vertex} (r : D.RowAt v)
    (hclass : D.rowSubclass r = .tm) : 4 ≤ D.rowBaseline r := by
  rcases r with t | ⟨short, j⟩
  · rcases t with ⟨node, i⟩ | ⟨node, i⟩ | i
    · cases hclass
    · exact (D.node_right_in_root node .minus D.minus_branch_le_geometryBound).1
    · cases hclass
  · cases hclass

theorem rowShort_eq_false_of_tm {v : D.Vertex} (r : D.RowAt v)
    (hclass : D.rowSubclass r = .tm) : D.rowShort r = false := by
  rcases r with t | ⟨short, j⟩
  · rfl
  · cases hclass

theorem exists_jobCopy_of_rowShort {v : D.Vertex} (r : D.RowAt v)
    (hshort : D.rowShort r = true) : ∃ j : D.JobCopy v, r = .inr (true, j) := by
  rcases r with t | ⟨short, j⟩
  · cases hshort
  · change short = true at hshort
    subst short
    exact ⟨j, rfl⟩

theorem row_zero_resources_empty {v : D.Vertex} (r : D.RowAt v)
    (hshort : D.rowShort r = false) :
    completionInterval (D.rowBaseline r) (D.rowShort r) 0 0
      (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) = ∅ := by
  rw [hshort]
  exact completionInterval_long_zero_lengths _ _

theorem row_zero_resources_job {v : D.Vertex} (r : D.RowAt v)
    (hshort : D.rowShort r = true) :
    ∃ j : D.JobCopy v, r = .inr (true, j) ∧
      D.rowPosition r = some (D.jobPosition j) ∧
      completionInterval (D.rowBaseline r) (D.rowShort r) 0 0
        (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) =
        Geometry.jobTestInterval D.graph.edges.length D.R D.geometryBound D.L
          (D.jobPosition j) := by
  obtain ⟨j, rfl⟩ := D.exists_jobCopy_of_rowShort r hshort
  refine ⟨j, rfl, rfl, ?_⟩
  exact completion_job_interval _ _ _ _ _

theorem minus_row_completion_gt_one {v w : D.Vertex} (r : D.RowAt v)
    (u : D.GlobalCopy) (l : D.LocalAt w) (hclass : D.rowSubclass r = .tm) :
    1 < completion (D.rowBaseline r) (D.rowShort r) (D.globalLength u)
      (D.localLength l) (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
  apply completion_minus_geometry_gt_one
    D.graph.edges.length D.R D.geometryBound D.L
  · exact D.rowBaseline_ge_four_of_tm r hclass
  · exact D.rowShort_eq_false_of_tm r hclass
  · exact D.globalLength_le_one u
  · exact D.localLength_le_lambda_one l

theorem minus_row_not_cover_jobInterior {v w : D.Vertex} (r : D.RowAt v)
    (u : D.GlobalCopy) (l : D.LocalAt w) (hclass : D.rowSubclass r = .tm)
    (job : D.Position) :
    Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L job ∉
      completionInterval (D.rowBaseline r) (D.rowShort r) (D.globalLength u)
        (D.localLength l) (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
  intro hmem
  have hh := D.minus_row_completion_gt_one r u l hclass
  have hj := (Geometry.closedJobCell_bounds
    (Geometry.jobInterior_mem_closedJobCell D.graph.edges.length D.R
      D.geometryBound D.L job)).2
  exact (not_le_of_gt (hj.trans hh)) hmem.1

theorem plus_row_not_cover_minus_side {v w : D.Vertex} (r : D.RowAt v)
    (u : D.GlobalCopy) (l : D.LocalAt w) (hclass : D.rowSubclass r ≠ .tm)
    {a : ℚ} (ha : 4 ≤ a) :
    a ∉ completionInterval (D.rowBaseline r) (D.rowShort r) (D.globalLength u)
      (D.localLength l) (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
  apply not_mem_plus_completionInterval
  · exact D.rowBaseline_le_one_of_not_tm r hclass
  · linarith

end BinPackingGap.InventoryData

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Machines/PackingJobCoverage.lean =====
namespace OAI

noncomputable section

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def shortMainAt (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) : Finset (p.TableBin (subclass e)) := by
  classical
  exact (Coverage.mainTuplesAt p (subclass e) (label e) v).filter fun t =>
    tupleBaseline p e t = Geometry.baseline D.graph.edges.length D.R r ∧
      tupleShort p e t = true

theorem main_unit_species (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (hu : D.globalUnit (globalCopy p e t) = true) :
    (globalCopy p e t).1 = .up true ∨ (globalCopy p e t).1 = .um true := by
  rcases hcopy : globalCopy p e t with ⟨s, i⟩
  rw [hcopy] at hu
  change s = .up true ∨ s = .um true
  cases s with
  | up one =>
      change one = true at hu
      exact Or.inl (congrArg GlobalSpecies.up hu)
  | um one =>
      change one = true at hu
      exact Or.inr (congrArg GlobalSpecies.um hu)
  | edge edge permit =>
      have hglobal := roleCopy_subclass p e t .«global»
      change D.itemSubclass ⟨.«global», globalCopy p e t⟩ = _ at hglobal
      rw [hcopy] at hglobal
      have hmain := ((Coverage.mem_mainTuplesAt p (subclass e) (label e) v t).mp ht).2.2
      exfalso
      apply hmain
      cases hpattern : p.tablePattern (subclass e) t <;>
        rw [hpattern] at hglobal <;> cases hglobal

theorem row_minus_of_global_um (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hu : (globalCopy p e t).1 = .um true) :
    D.rowSubclass (rowCopy p e t).2 = .tm := by
  have hg := roleCopy_subclass p e t .«global»
  have hx := roleCopy_subclass p e t .x
  have hclass : D.itemSubclass ⟨.«global», globalCopy p e t⟩ = .um := by
    rcases hcopy : globalCopy p e t with ⟨s, i⟩
    have hs : s = .um true := by simpa only [hcopy] using hu
    subst s
    rfl
  have hpat : p.tablePattern (subclass e) t = .minusTree := by
    rw [hclass] at hg
    cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]
  rw [hpat] at hx
  change D.itemSubclass ⟨.x, rowCopy p e t⟩ = .tm at hx
  rcases hc : rowCopy p e t with ⟨w, r⟩
  rw [hc] at hx
  exact hx

theorem job_covering_global_not_um (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (t : p.TableBin (subclass e))
    (ht : t ∈ tupleCovering p e v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r)) :
    (globalCopy p e t).1 ≠ .um true := by
  intro hu
  have hrow := row_minus_of_global_um p e t hu
  apply D.minus_row_not_cover_jobInterior (rowCopy p e t).2 (globalCopy p e t)
    (localCopy p e t).2 hrow r
  exact ((mem_tupleCovering p e v _ t).mp ht).2

theorem zero_resources_job_cover (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (t : p.TableBin (subclass e))
    (ht : t ∈ tupleCovering p e v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r))
    (hg : tupleGlobalLength p e t = 0) (hl : tupleLocalLength p e t = 0) :
    tupleBaseline p e t = Geometry.baseline D.graph.edges.length D.R r ∧
      tupleShort p e t = true := by
  have hmem := ((mem_tupleCovering p e v _ t).mp ht).2
  have hshort : tupleShort p e t = true := by
    cases hs : tupleShort p e t with
    | false =>
        have hfinish : tupleFinish p e t = tupleBaseline p e t := by
          simp [tupleFinish, hs, hg, hl]
        rw [hfinish] at hmem
        exact (not_lt_of_ge hmem.1 hmem.2).elim
    | true => rfl
  obtain ⟨j, hj, _, hinter⟩ := D.row_zero_resources_job (rowCopy p e t).2 hshort
  have hmem' : Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r ∈
      completionInterval (D.rowBaseline (rowCopy p e t).2)
        (D.rowShort (rowCopy p e t).2) 0 0
        (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
    change completion _ _ 0 0 _ ≤ _ ∧ _ < _
    simpa only [tupleFinish, hg, hl, tupleBaseline, tupleShort] using hmem
  rw [hinter] at hmem'
  have hpos : D.jobPosition j = r :=
    (Geometry.jobInterior_mem_jobTestInterval_iff D.geometryBound D.L).mp hmem'
  refine ⟨?_, hshort⟩
  simp only [tupleBaseline, hj, InventoryData.rowBaseline, hpos]

theorem nonexcluded_covering_subset (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (hr : r ∉ excludedAt p e v) :
    tupleCovering p e v (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r) ⊆
      fundedTuples p e (.up true) v ∪ shortMainAt p e v r := by
  classical
  intro t ht
  have hM := ((mem_tupleCovering p e v _ t).mp ht).1
  by_cases hu : D.globalUnit (globalCopy p e t) = true
  · have hspec := main_unit_species p e v t hM hu
    rcases hspec with hp | hm
    · exact Finset.mem_union_left _ ((mem_fundedTuples p e (.up true) v t).mpr
        ⟨hM, (selected_global_resource_iff p e t (.up true)).mpr hp⟩)
    · exact (job_covering_global_not_um p e v r t ht hm).elim
  · have hfalse : D.globalUnit (globalCopy p e t) = false := Bool.eq_false_of_not_eq_true hu
    have hnot := covering_not_selected_of_nonexcluded p e v r hr t ht
    have hnotpos : p.itemAtRole (subclass e) t .«local» ∉ positiveLocalResources e v := by
      intro hp
      exact hnot ((mem_zeroPositiveTuples p e v t).mpr ⟨hM, hfalse, hp⟩)
    have hlocal := tupleLocalLength_eq_zero_of_not_positive p e v t
      (Coverage.mainTuplesAt_subset_good p (subclass e) (label e) v hM) hnotpos
    have hz := zero_resources_job_cover p e v r t ht
      (tupleGlobalLength_eq_of_unit_false p e t hfalse) hlocal
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hM, hz⟩)

theorem nonexcluded_coverage_upper (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (hr : r ∉ excludedAt p e v) :
    (tupleCovering p e v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r)).card ≤
      xplus p e v + (shortMainAt p e v r).card := by
  calc
    _ ≤ (fundedTuples p e (.up true) v ∪ shortMainAt p e v r).card :=
      Finset.card_le_card (nonexcluded_covering_subset p e v r hr)
    _ ≤ _ := Finset.card_union_le _ _

end PackingCounts
end BinPackingGap

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Configurations/CoverageSoundness.lean =====
namespace OAI

noncomputable section

namespace BinPackingGap

namespace InventoryCoverage

variable {D : InventoryData} {I : Instance} {b : ℕ}

theorem coveringTuplesAt_eq (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (a : ℚ) :
    Coverage.coveringTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (PackingCounts.tupleFinish p e) a =
      PackingCounts.tupleCovering p e v a := by
  unfold Coverage.coveringTuplesAt PackingCounts.tupleCovering
  apply Finset.filter_congr
  intro t _
  rw [rowBaseline_selected p e t]
  rfl

theorem shortMainAt_eq (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) :
    Coverage.currentShortMainAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (rowShort e) (Geometry.baseline D.graph.edges.length D.R r) =
      PackingCounts.shortMainAt p e v r := by
  unfold Coverage.currentShortMainAt PackingCounts.shortMainAt
  apply Finset.filter_congr
  intro t _
  rw [rowBaseline_selected p e t, rowShort_selected p e t]
  rfl

end InventoryCoverage

namespace InventoryData

variable (D : InventoryData)

theorem test_coverage {b c : ℕ}
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (v : D.Vertex) (t : D.TestAt v) (a : ℚ) (ha : a ∈ D.testInterval t) :
    D.d ≤ (PackingCounts.tupleCovering p D.itemEquiv v a).card + 6 * lossAllowance c := by
  classical
  have hbad := D.badAnchorsAt_card_le hk p hb v
  have horder := PackingCounts.edge_selected_baseline_le p D.itemEquiv
    D.packingInstance_size_eq v
  have hle : ∀ u ∈ Coverage.mainTuplesAt p (PackingCounts.subclass D.itemEquiv) (PackingCounts.label D.itemEquiv) v,
      PackingCounts.tupleFinish p D.itemEquiv u ≤
        InventoryCoverage.rowBaseline D.itemEquiv (p.itemAtRole (PackingCounts.subclass D.itemEquiv) u .x) := by
    intro u _
    simpa only [InventoryCoverage.rowBaseline_selected, PackingCounts.tupleBaseline] using
      PackingCounts.tupleFinish_le_baseline p D.itemEquiv u
  have hfeasible := PackingCounts.main_completion_le_selected_deadline p D.itemEquiv
    D.packingInstance_size_eq v
  have hdeficit := InventoryCoverage.actual_deadline_deficit_bound p D.itemEquiv v a
    (lossAllowance c) (PackingCounts.tupleFinish p D.itemEquiv) hbad horder hle hfeasible
  rw [D.deadline_prefix_at_test hplusheight hminusheight hL v t a ha,
    InventoryCoverage.coveringTuplesAt_eq] at hdeficit
  change (InventoryCoverage.originalBaselinePrefix D v a).card + D.d ≤
    (InventoryCoverage.originalBaselinePrefix D v a).card +
      (PackingCounts.tupleCovering p D.itemEquiv v a).card + 6 * lossAllowance c at hdeficit
  omega

def longMatchesAt {b : ℕ} (p : Packing D.packingInstance b)
    (v : D.Vertex) (r : D.IncidencePosition v) : ℕ :=
  (Coverage.currentLongEdgeAt p D.encodedSubclass D.encodedLabel v
    (InventoryCoverage.rowBaseline D.itemEquiv) (InventoryCoverage.keyBaseline D.itemEquiv)
    (InventoryCoverage.rowShort D.itemEquiv)
    (Geometry.baseline D.graph.edges.length D.R (D.incidencePosition r))).card

theorem long_matches_at_nonexcluded {b c : ℕ}
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (v : D.Vertex) (r : D.IncidencePosition v)
    (hr : D.incidencePosition r ∉ PackingCounts.excludedAt p D.itemEquiv v) :
    D.d ≤ D.longMatchesAt p v r + PackingCounts.xplus p D.itemEquiv v + 9 * lossAllowance c := by
  classical
  let a := Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L (D.incidencePosition r)
  let finish := PackingCounts.tupleFinish p D.itemEquiv
  have hbad := D.badAnchorsAt_card_le hk p hb v
  have horder := PackingCounts.edge_selected_baseline_le p D.itemEquiv
    D.packingInstance_size_eq v
  have hle : ∀ u ∈ Coverage.mainTuplesAt p (PackingCounts.subclass D.itemEquiv) (PackingCounts.label D.itemEquiv) v,
      finish u ≤ InventoryCoverage.rowBaseline D.itemEquiv
        (p.itemAtRole (PackingCounts.subclass D.itemEquiv) u .x) := by
    intro u _
    simpa only [finish, InventoryCoverage.rowBaseline_selected, PackingCounts.tupleBaseline] using
      PackingCounts.tupleFinish_le_baseline p D.itemEquiv u
  have hfeasible := PackingCounts.main_completion_le_selected_deadline p D.itemEquiv
    D.packingInstance_size_eq v
  have hpartition := Coverage.completion_prefix_decomposition p (PackingCounts.subclass D.itemEquiv)
    (PackingCounts.label D.itemEquiv) v (InventoryCoverage.rowBaseline D.itemEquiv) finish hle a
  have hdeadline := Coverage.deadline_prefix_le_completion_add_loss p (PackingCounts.subclass D.itemEquiv)
    (PackingCounts.label D.itemEquiv) v (InventoryCoverage.anchorDeadline D.itemEquiv) finish a
    (lossAllowance c) hbad hfeasible
  have ha : a ∈ D.testInterval (.inr (.inr r) : D.TestAt v) :=
    Geometry.jobInterior_mem_jobTestInterval D.graph.edges.length D.R D.geometryBound D.L
      (D.incidencePosition r)
  rw [InventoryCoverage.deadlinePrefix_card,
    D.deadline_prefix_at_test hplusheight hminusheight hL v (.inr (.inr r)) a ha] at hdeadline
  have hbase := InventoryCoverage.actual_displaced_job_prefix_le p D.itemEquiv v r
    (lossAllowance c) hbad horder
  have hupper : (Coverage.coveringTuplesAt p (PackingCounts.subclass D.itemEquiv) (PackingCounts.label D.itemEquiv) v
      (InventoryCoverage.rowBaseline D.itemEquiv) finish a).card ≤
      PackingCounts.xplus p D.itemEquiv v +
      (Coverage.currentShortMainAt p (PackingCounts.subclass D.itemEquiv) (PackingCounts.label D.itemEquiv) v
        (InventoryCoverage.rowBaseline D.itemEquiv) (InventoryCoverage.rowShort D.itemEquiv)
        (Geometry.baseline D.graph.edges.length D.R (D.incidencePosition r))).card := by
    simpa only [finish, a, InventoryCoverage.coveringTuplesAt_eq,
      InventoryCoverage.shortMainAt_eq] using
      PackingCounts.nonexcluded_coverage_upper p D.itemEquiv v (D.incidencePosition r) hr
  have hcorrection := CoverageCounts.displaced_short_correction hpartition hdeadline hbase hupper
  exact InventoryCoverage.actual_current_long_matches_from_correction p D.itemEquiv v r
    (lossAllowance c) (PackingCounts.xplus p D.itemEquiv v) hbad horder hcorrection

end InventoryData
end BinPackingGap

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Trees/TreeAvoidance.lean =====
namespace OAI

namespace BinPackingGap

def pullMarks (stem : List ℕ) (marks : Finset (List ℕ)) : Finset (List ℕ) :=
  (marks.filter (fun w => stem.IsPrefix w)).image (fun w => w.drop stem.length)

@[simp] theorem mem_pullMarks (stem word : List ℕ) (marks : Finset (List ℕ)) :
    word ∈ pullMarks stem marks ↔ stem ++ word ∈ marks := by
  constructor
  · intro hw
    obtain ⟨v, hv, hdrop⟩ := Finset.mem_image.mp hw
    obtain ⟨hvA, hpref⟩ := Finset.mem_filter.mp hv
    have heq : stem ++ word = v := by
      calc
        stem ++ word = stem ++ v.drop stem.length :=
          congrArg (fun t => stem ++ t) hdrop.symm
        _ = v.take stem.length ++ v.drop stem.length :=
          congrArg (fun t => t ++ v.drop stem.length) (List.prefix_iff_eq_take.mp hpref)
        _ = v := List.take_append_drop stem.length v
    exact heq.symm ▸ hvA
  · intro hw
    exact Finset.mem_image.mpr
      ⟨stem ++ word, Finset.mem_filter.mpr ⟨hw, List.prefix_append stem word⟩,
        by simp⟩

@[simp] theorem nil_mem_pullMarks (stem : List ℕ) (marks : Finset (List ℕ)) :
    [] ∈ pullMarks stem marks ↔ stem ∈ marks := by
  simpa only [List.append_nil] using mem_pullMarks stem [] marks

theorem levelCount_pullMarks_le (stem : List ℕ) (marks : Finset (List ℕ)) (j : ℕ) :
    levelCount (pullMarks stem marks) j ≤ levelCount marks (stem.length + j) := by
  have hsub : (pullMarks stem marks).filter (fun w => w.length = j) ⊆
      (marks.filter (fun w => w.length = stem.length + j)).image
        (fun w => w.drop stem.length) := by
    intro w hw
    obtain ⟨hw, hlen⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_image.mpr ⟨stem ++ w, ?_, by simp⟩
    exact Finset.mem_filter.mpr
      ⟨(mem_pullMarks stem w marks).mp hw, by simp only [List.length_append, hlen]⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

theorem disjoint_prefixes_append_of_pull (stem word : List ℕ)
    (marks : Finset (List ℕ))
    (hold : Disjoint marks (UniformTree.prefixes stem))
    (hnew : Disjoint (pullMarks stem marks) (UniformTree.prefixes word)) :
    Disjoint marks (UniformTree.prefixes (stem ++ word)) := by
  apply Finset.disjoint_left.mpr
  intro v hv hprefix
  rw [prefixes_append_eq] at hprefix
  rcases Finset.mem_union.mp hprefix with hprefix | hprefix
  · exact Finset.disjoint_left.mp hold hv hprefix
  · obtain ⟨w, _, hw, heq⟩ := mem_prefixesAfter_iff.mp hprefix
    apply Finset.disjoint_left.mp hnew
    · exact (mem_pullMarks stem w marks).mpr (heq.symm ▸ hv)
    · exact UniformTree.mem_prefixes_iff.mpr hw

def extendPhaseQuota (height : ℕ) (old : ℕ → ℕ) (depth : ℕ) : ℕ :=
  if depth ≤ height then old depth else phaseQuota (depth - height)

theorem extendPhaseQuota_old (height : ℕ) (old : ℕ → ℕ) {depth : ℕ}
    (hdepth : depth ≤ height) : extendPhaseQuota height old depth = old depth := by
  simp only [extendPhaseQuota, ite_eq_left hdepth]

theorem extendPhaseQuota_new (height : ℕ) (old : ℕ → ℕ) {j : ℕ}
    (hj : 0 < j) : extendPhaseQuota height old (height + j) = phaseQuota j := by
  have hnot : ¬ height + j ≤ height := by omega
  simp only [extendPhaseQuota, ite_eq_right hnot, Nat.add_sub_cancel_left]

theorem graft_avoids {n : ℕ} (old : AuxiliaryTree n)
    (G : old.tree.leaves → AuxiliaryTree 1) (N : ℕ)
    (hG : ∀ l, (G l).tree.height = N)
    (hquota : ∀ l, (G l).quota = phaseQuota)
    (marks : Finset (List ℕ))
    (hmarks : RespectsTreeQuota
      (UniformTree.graft old.tree (fun l => (G l).tree) N hG)
      (extendPhaseQuota old.tree.height old.quota) marks) :
    ∃ leaf ∈ (UniformTree.graft old.tree (fun l => (G l).tree) N hG).leaves,
      Disjoint marks (UniformTree.prefixes leaf) := by
  have hold : RespectsTreeQuota old.tree old.quota marks := by
    refine ⟨hmarks.1, ?_⟩
    intro j hj hbound
    have hglobal := hmarks.2 j hj (by
      change j ≤ old.tree.height + N
      omega)
    simpa only [extendPhaseQuota_old old.tree.height old.quota hbound] using hglobal
  obtain ⟨l, hl, havoidOld⟩ := old.avoids marks hold
  let oldLeaf : old.tree.leaves := ⟨l, hl⟩
  have hlocal : RespectsTreeQuota (G oldLeaf).tree (G oldLeaf).quota
      (pullMarks l marks) := by
    constructor
    · rw [nil_mem_pullMarks]
      intro hmarked
      exact Finset.disjoint_left.mp havoidOld hmarked
        (UniformTree.mem_prefixes_iff.mpr (List.prefix_refl l))
    · intro j hj hbound
      have hjpos : 0 < j := by omega
      have hlocalBound : j ≤ N := by simpa only [hG oldLeaf] using hbound
      have hglobal := hmarks.2 (old.tree.height + j) (by omega) (by
        change old.tree.height + j ≤ old.tree.height + N
        omega)
      have hpull := levelCount_pullMarks_le l marks j
      rw [old.tree.length_leaf l hl] at hpull
      rw [hquota oldLeaf]
      exact hpull.trans (by
        simpa only [extendPhaseQuota_new old.tree.height old.quota hjpos] using hglobal)
  obtain ⟨w, hw, havoidNew⟩ := (G oldLeaf).avoids (pullMarks l marks) hlocal
  refine ⟨l ++ w, ?_, disjoint_prefixes_append_of_pull l w marks havoidOld havoidNew⟩
  exact (UniformTree.mem_graft_leaves old.tree (fun l => (G l).tree) N hG).mpr
    ⟨oldLeaf, w, hw, rfl⟩

end BinPackingGap

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/PhaseIteration.lean =====
namespace OAI

namespace BinPackingGap

namespace UniformTree

def leafRank (T : UniformTree) (l : T.leaves) : ℕ :=
  ((T.leaves.orderIsoOfFin rfl).symm l).val + 1

theorem leafRank_pos (T : UniformTree) (l : T.leaves) : 0 < T.leafRank l := by
  unfold leafRank
  omega

theorem one_le_leafRank (T : UniformTree) (l : T.leaves) : 1 ≤ T.leafRank l :=
  T.leafRank_pos l

theorem leafRank_le (T : UniformTree) (l : T.leaves) : T.leafRank l ≤ T.leaves.card := by
  have h := ((T.leaves.orderIsoOfFin rfl).symm l).isLt
  unfold leafRank
  omega

theorem leafRank_injective (T : UniformTree) : Function.Injective T.leafRank := by
  intro l m h
  apply (T.leaves.orderIsoOfFin rfl).symm.injective
  apply Fin.ext
  exact Nat.add_right_cancel h

theorem leaf_card_pos (T : UniformTree) : 0 < T.leaves.card :=
  Finset.card_pos.mpr T.leaves_nonempty

def rankedGadget (T : UniformTree) (l : T.leaves) : AuxiliaryTree 1 :=
  ForkGadget.auxiliary T.leaves.card (T.leafRank l)
    (T.one_le_leafRank l) (T.leafRank_le l)

@[simp] theorem rankedGadget_height (T : UniformTree) (l : T.leaves) :
    (T.rankedGadget l).tree.height = T.leaves.card := rfl

@[simp] theorem rankedGadget_quota (T : UniformTree) (l : T.leaves) :
    (T.rankedGadget l).quota = phaseQuota := rfl

theorem rankedGadget_red_depth (T : UniformTree) (l : T.leaves)
    {w : List ℕ} (hw : w ∈ (T.rankedGadget l).red) : w.length = T.leafRank l :=
  ForkGadget.auxiliary_red_depth _ _ _ _ hw

theorem rankedGadget_blue_depth (T : UniformTree) (l : T.leaves)
    {w : List ℕ} (hw : w ∈ (T.rankedGadget l).blue) : w.length = T.leafRank l :=
  ForkGadget.auxiliary_blue_depth _ _ _ _ hw

@[simp] theorem rankedGadget_card_red (T : UniformTree) (l : T.leaves) :
    (T.rankedGadget l).red.card = phaseQuota (T.leafRank l) :=
  ForkGadget.auxiliary_card_red _ _ _ _

@[simp] theorem rankedGadget_card_blue (T : UniformTree) (l : T.leaves) :
    (T.rankedGadget l).blue.card = phaseQuota (T.leafRank l) :=
  ForkGadget.auxiliary_card_blue _ _ _ _

def nextPhase (T : UniformTree) : UniformTree :=
  T.graft (fun l => (T.rankedGadget l).tree) T.leaves.card
    (fun l => T.rankedGadget_height l)

@[simp] theorem nextPhase_height (T : UniformTree) :
    T.nextPhase.height = T.height + T.leaves.card := rfl

theorem height_lt_nextPhase (T : UniformTree) : T.height < T.nextPhase.height := by
  rw [nextPhase_height]
  exact Nat.lt_add_of_pos_right T.leaf_card_pos

theorem mem_nextPhase_leaves (T : UniformTree) {x : List ℕ} :
    x ∈ T.nextPhase.leaves ↔
      ∃ l : T.leaves, ∃ w ∈ (T.rankedGadget l).tree.leaves, x = l.val ++ w :=
  T.mem_graft_leaves _ _ _

def singletonRoot : UniformTree where
  height := 0
  leaves := {[]}
  leaves_nonempty := ⟨[], Finset.mem_singleton_self []⟩
  length_leaf := by
    intro l hl
    have hl' : l = [] := Finset.mem_singleton.mp hl
    simp only [hl', List.length_nil]
  positive_labels := by
    intro l hl a ha
    have hl' : l = [] := Finset.mem_singleton.mp hl
    simp only [hl', List.not_mem_nil] at ha

end UniformTree

namespace AuxiliaryTree

def initial : AuxiliaryTree 0 where
  tree := UniformTree.singletonRoot
  quota := fun _ => 0
  quota_pos := by
    intro depth hpos hle
    change depth ≤ 0 at hle
    omega
  red := ∅
  blue := ∅
  red_subset := Finset.empty_subset _
  blue_subset := Finset.empty_subset _
  root_not_red := by simp
  root_not_blue := by simp
  red_blue_disjoint := by simp
  red_level := by simp [levelCount]
  blue_level := by simp [levelCount]
  total_count := by simp [colorCount]
  red_witness := ⟨[], Finset.mem_singleton_self [], by simp [colorCount]⟩
  blue_witness := ⟨[], Finset.mem_singleton_self [], by simp [colorCount]⟩
  avoids := by
    intro marks hmarks
    refine ⟨[], Finset.mem_singleton_self [], ?_⟩
    apply Finset.disjoint_left.mpr
    intro w hw hp
    have heq : w = [] := by
      simpa only [UniformTree.mem_prefixes_iff, List.prefix_nil] using hp
    exact hmarks.1 (heq ▸ hw)

def step {n : ℕ} (old : AuxiliaryTree n) : AuxiliaryTree (n + 1) where
  tree := old.tree.nextPhase
  quota := extendPhaseQuota old.tree.height old.quota
  quota_pos := by
    intro depth hpos _
    unfold extendPhaseQuota
    split_ifs with hdepth
    · exact old.quota_pos depth hpos hdepth
    · exact phaseQuota_pos _
  red := old.red ∪ old.tree.liftMarks (fun l => (old.tree.rankedGadget l).red)
  blue := old.blue ∪ old.tree.liftMarks (fun l => (old.tree.rankedGadget l).blue)
  red_subset := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact old.tree.vertices_subset_graft _ _ _ (old.red_subset hw)
    · exact old.tree.liftMarks_subset_graft_vertices _ _ _ _
        (fun l => (old.tree.rankedGadget l).red_subset) hw
  blue_subset := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact old.tree.vertices_subset_graft _ _ _ (old.blue_subset hw)
    · exact old.tree.liftMarks_subset_graft_vertices _ _ _ _
        (fun l => (old.tree.rankedGadget l).blue_subset) hw
  root_not_red := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact old.root_not_red h
    · exact old.tree.root_not_mem_lift _
        (fun l => (old.tree.rankedGadget l).root_not_red) h
  root_not_blue := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact old.root_not_blue h
    · exact old.tree.root_not_mem_lift _
        (fun l => (old.tree.rankedGadget l).root_not_blue) h
  red_blue_disjoint := by
    apply Finset.disjoint_left.mpr
    intro w hr hb
    rcases Finset.mem_union.mp hr with hr | hr <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact Finset.disjoint_left.mp old.red_blue_disjoint hr hb
    · exact Finset.disjoint_left.mp
        (old.tree.old_marks_disjoint_lift old.red _ old.red_subset
          (fun l => (old.tree.rankedGadget l).root_not_blue)) hr hb
    · exact Finset.disjoint_left.mp
        (old.tree.old_marks_disjoint_lift old.blue _ old.blue_subset
          (fun l => (old.tree.rankedGadget l).root_not_red)) hb hr
    · exact Finset.disjoint_left.mp
        (old.tree.liftMarks_disjoint _ _
          (fun l => (old.tree.rankedGadget l).red_blue_disjoint)) hr hb
  red_level := by
    intro depth hpos _
    simpa only [extendPhaseQuota] using
      old.tree.levelCount_union_liftMarks_le old.red
        (fun l => (old.tree.rankedGadget l).red)
        old.red_subset (fun l => (old.tree.rankedGadget l).root_not_red)
        old.tree.leafRank old.tree.leafRank_injective
        (fun l _ hw => old.tree.rankedGadget_red_depth l hw)
        (fun l => (old.tree.rankedGadget_card_red l).le)
        old.quota old.red_level depth hpos
  blue_level := by
    intro depth hpos _
    simpa only [extendPhaseQuota] using
      old.tree.levelCount_union_liftMarks_le old.blue
        (fun l => (old.tree.rankedGadget l).blue)
        old.blue_subset (fun l => (old.tree.rankedGadget l).root_not_blue)
        old.tree.leafRank old.tree.leafRank_injective
        (fun l _ hw => old.tree.rankedGadget_blue_depth l hw)
        (fun l => (old.tree.rankedGadget_card_blue l).le)
        old.quota old.blue_level depth hpos
  total_count := by
    intro leaf hleaf
    obtain ⟨l, w, hw, rfl⟩ := old.tree.mem_nextPhase_leaves.mp hleaf
    rw [old.tree.colorCount_union_liftMarks old.red _ old.red_subset
        (fun l => (old.tree.rankedGadget l).root_not_red),
      old.tree.colorCount_union_liftMarks old.blue _ old.blue_subset
        (fun l => (old.tree.rankedGadget l).root_not_blue)]
    have hold := old.total_count l.val l.property
    have hnew := (old.tree.rankedGadget l).total_count w hw
    omega
  red_witness := by
    obtain ⟨l, hl, hold⟩ := old.red_witness
    let leaf : old.tree.leaves := ⟨l, hl⟩
    obtain ⟨w, hw, hnew⟩ := (old.tree.rankedGadget leaf).red_witness
    refine ⟨l ++ w, old.tree.mem_nextPhase_leaves.mpr ⟨leaf, w, hw, rfl⟩, ?_⟩
    change colorCount (old.red ∪ old.tree.liftMarks
      (fun l => (old.tree.rankedGadget l).red)) (leaf.val ++ w) = n + 1
    rw [old.tree.colorCount_union_liftMarks old.red _ old.red_subset
      (fun l => (old.tree.rankedGadget l).root_not_red) leaf w]
    exact congrArg₂ (· + ·) hold hnew
  blue_witness := by
    obtain ⟨l, hl, hold⟩ := old.blue_witness
    let leaf : old.tree.leaves := ⟨l, hl⟩
    obtain ⟨w, hw, hnew⟩ := (old.tree.rankedGadget leaf).blue_witness
    refine ⟨l ++ w, old.tree.mem_nextPhase_leaves.mpr ⟨leaf, w, hw, rfl⟩, ?_⟩
    change colorCount (old.blue ∪ old.tree.liftMarks
      (fun l => (old.tree.rankedGadget l).blue)) (leaf.val ++ w) = n + 1
    rw [old.tree.colorCount_union_liftMarks old.blue _ old.blue_subset
      (fun l => (old.tree.rankedGadget l).root_not_blue) leaf w]
    exact congrArg₂ (· + ·) hold hnew
  avoids := graft_avoids old old.tree.rankedGadget old.tree.leaves.card
    old.tree.rankedGadget_height old.tree.rankedGadget_quota

@[simp] theorem step_height {n : ℕ} (old : AuxiliaryTree n) :
    old.step.tree.height = old.tree.height + old.tree.leaves.card := rfl

theorem height_lt_step {n : ℕ} (old : AuxiliaryTree n) :
    old.tree.height < old.step.tree.height := old.tree.height_lt_nextPhase

end AuxiliaryTree

def buildAuxiliary : (n : ℕ) → AuxiliaryTree n
  | 0 => AuxiliaryTree.initial
  | n + 1 => (buildAuxiliary n).step

@[simp] theorem buildAuxiliary_zero : buildAuxiliary 0 = AuxiliaryTree.initial := rfl

@[simp] theorem buildAuxiliary_succ (n : ℕ) :
    buildAuxiliary (n + 1) = (buildAuxiliary n).step := rfl

theorem phases_le_buildAuxiliary_height (n : ℕ) : n ≤ (buildAuxiliary n).tree.height := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have h := (buildAuxiliary n).height_lt_step
      change n + 1 ≤ (buildAuxiliary n).step.tree.height
      omega

theorem buildAuxiliary_height_pos {n : ℕ} (hn : 0 < n) :
    0 < (buildAuxiliary n).tree.height :=
  lt_of_lt_of_le hn (phases_le_buildAuxiliary_height n)

end BinPackingGap

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Trees/CompetingTrees.lean =====
namespace OAI

namespace BinPackingGap

def competingTrees (d : ℕ) (hd : 0 < d) : CompetingTrees d :=
  CompetingTrees.ofAuxiliary d hd (buildAuxiliary (2 * d - 1))

theorem exists_competingTrees (d : ℕ) (hd : 0 < d) : Nonempty (CompetingTrees d) :=
  ⟨competingTrees d hd⟩

end BinPackingGap

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/ExtractedCover.lean =====
namespace OAI

noncomputable section

namespace BinPackingGap.SideChoice

open UniformTree

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
theorem card_le_of_unique_hit [DecidableEq α] [DecidableEq β]
    (tuples : Finset α) (nodes : Finset β)
    (hits : α → β → Prop)
    (hcover : ∀ v ∈ nodes, ∃ t ∈ tuples, hits t v)
    (hunique : ∀ t ∈ tuples, ∀ v w, hits t v → hits t w → v = w) :
    nodes.card ≤ tuples.card := by
  classical
  let f : nodes → tuples := fun v =>
    ⟨Classical.choose (hcover v.val v.property),
      (Classical.choose_spec (hcover v.val v.property)).1⟩
  have hf : ∀ v : nodes, hits (f v).val v.val := fun v =>
    (Classical.choose_spec (hcover v.val v.property)).2
  apply Finset.card_le_card_of_injective (f := f)
  intro v w hvw
  apply Subtype.ext
  have ht : (f v).val = (f w).val := congrArg Subtype.val hvw
  apply hunique (f v).val (f v).property v.val w.val (hf v)
  rw [ht]
  exact hf w

omit [DecidableEq α] [DecidableEq β] in
theorem level_card_le_resources [DecidableEq α] [DecidableEq β]
    (selected : Finset α) (level : α → ℕ)
    (resource : α → β) (stock : Finset β) (ℓ q : ℕ)
    (hmap : ∀ t ∈ selected, level t = ℓ → resource t ∈ stock)
    (hinj : Set.InjOn resource (selected.filter fun t => level t = ℓ))
    (hstock : stock.card ≤ q) :
    (selected.filter fun t => level t = ℓ).card ≤ q := by
  apply (Finset.card_le_card_of_injOn resource ?_ hinj).trans hstock
  intro t ht
  exact hmap t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2

variable {d : ℕ} (T : CompetingTrees d)

def taggedDepth : T.plus.Node ⊕ T.minus.Node → ℕ := Sum.elim depth depth

def marksPlus (selected : Finset α)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop) : Finset T.plus.Node := by
  classical
  exact Finset.univ.filter fun v => ∃ t ∈ selected, hits t (.inl v)

def marksMinus (selected : Finset α)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop) : Finset T.minus.Node := by
  classical
  exact Finset.univ.filter fun v => ∃ t ∈ selected, hits t (.inr v)

omit [DecidableEq α] in
@[simp] theorem mem_marksPlus [DecidableEq α] (selected : Finset α)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop) (v : T.plus.Node) :
    v ∈ marksPlus T selected hits ↔ ∃ t ∈ selected, hits t (.inl v) := by
  classical
  simp [marksPlus]

omit [DecidableEq α] in
@[simp] theorem mem_marksMinus [DecidableEq α] (selected : Finset α)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop) (v : T.minus.Node) :
    v ∈ marksMinus T selected hits ↔ ∃ t ∈ selected, hits t (.inr v) := by
  classical
  simp [marksMinus]

theorem roots_not_marked (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (hpositive : ∀ t ∈ selected, 0 < level t)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t) :
    T.plus.root ∉ marksPlus T selected hits ∧
      T.minus.root ∉ marksMinus T selected hits := by
  constructor
  · intro hroot
    obtain ⟨t, ht, hhit⟩ := (mem_marksPlus T selected hits _).mp hroot
    have hh : 0 = level t := hdepth t ht (.inl T.plus.root) hhit
    have hp := hpositive t ht
    omega
  · intro hroot
    obtain ⟨t, ht, hhit⟩ := (mem_marksMinus T selected hits _).mp hroot
    have hh : 0 = level t := hdepth t ht (.inr T.minus.root) hhit
    have hp := hpositive t ht
    omega

theorem marked_level_card_le (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t)
    (hunique : ∀ t ∈ selected, ∀ v w, hits t v → hits t w → v = w)
    (ℓ : ℕ) :
    ((marksPlus T selected hits).filter fun v => depth v = ℓ).card +
      ((marksMinus T selected hits).filter fun v => depth v = ℓ).card ≤
      (selected.filter fun t => level t = ℓ).card := by
  classical
  rw [← Finset.card_disjSum]
  apply card_le_of_unique_hit _ _ hits
  · intro v hv
    cases v with
    | inl v =>
      have hv' := Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp hv)
      obtain ⟨t, ht, hhit⟩ := (mem_marksPlus T selected hits v).mp hv'.1
      refine ⟨t, Finset.mem_filter.mpr ⟨ht, ?_⟩, hhit⟩
      have hh : depth v = level t := hdepth t ht (.inl v) hhit
      exact hh.symm.trans hv'.2
    | inr v =>
      have hv' := Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hv)
      obtain ⟨t, ht, hhit⟩ := (mem_marksMinus T selected hits v).mp hv'.1
      refine ⟨t, Finset.mem_filter.mpr ⟨ht, ?_⟩, hhit⟩
      have hh : depth v = level t := hdepth t ht (.inr v) hhit
      exact hh.symm.trans hv'.2
  · intro t ht v w hv hw
    exact hunique t (Finset.mem_filter.mp ht).1 v w hv hw

theorem exists_unhit_leaf (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (hpositive : ∀ t ∈ selected, 0 < level t)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t)
    (hunique : ∀ t ∈ selected, ∀ v w, hits t v → hits t w → v = w)
    (hstock : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ T.height →
      (selected.filter fun t => level t = ℓ).card ≤ T.quota ℓ) :
    (∃ l : T.plus.Node, leaf l ∧
      ∀ t ∈ selected, ∀ v, hits t (.inl v) → ¬ ancestor v l) ∨
    (∃ l : T.minus.Node, leaf l ∧
      ∀ t ∈ selected, ∀ v, hits t (.inr v) → ¬ ancestor v l) := by
  have hroots := roots_not_marked T selected level hits hpositive hdepth
  have hquota : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ T.height →
      ((marksPlus T selected hits).filter fun v => depth v = ℓ).card +
        ((marksMinus T selected hits).filter fun v => depth v = ℓ).card ≤ T.quota ℓ := by
    intro ℓ hlo hhi
    exact (marked_level_card_le T selected level hits hdepth hunique ℓ).trans
      (hstock ℓ hlo hhi)
  rcases T.shared_obstruction (marksPlus T selected hits) (marksMinus T selected hits)
    hroots.1 hroots.2 hquota with ⟨l, hl, havoid⟩ | ⟨l, hl, havoid⟩
  · left
    refine ⟨l, hl, ?_⟩
    intro t ht v hhit
    exact havoid v ((mem_marksPlus T selected hits v).mpr ⟨t, ht, hhit⟩)
  · right
    refine ⟨l, hl, ?_⟩
    intro t ht v hhit
    exact havoid v ((mem_marksMinus T selected hits v).mpr ⟨t, ht, hhit⟩)

theorem exists_leaf_coverage_le_funded (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (fundPlus fundMinus : Finset α)
    (coverPlus : T.plus.Node → Finset α) (coverMinus : T.minus.Node → Finset α)
    (hpositive : ∀ t ∈ selected, 0 < level t)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t)
    (hunique : ∀ t ∈ selected, ∀ v w, hits t v → hits t w → v = w)
    (hstock : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ T.height →
      (selected.filter fun t => level t = ℓ).card ≤ T.quota ℓ)
    (hcoverPlus : ∀ l, leaf l → ∀ t ∈ coverPlus l,
      t ∈ fundPlus ∨ t ∈ selected ∧ ∃ v, hits t (.inl v) ∧ ancestor v l)
    (hcoverMinus : ∀ l, leaf l → ∀ t ∈ coverMinus l,
      t ∈ fundMinus ∨ t ∈ selected ∧ ∃ v, hits t (.inr v) ∧ ancestor v l) :
    (∃ l : T.plus.Node, leaf l ∧ (coverPlus l).card ≤ fundPlus.card) ∨
    (∃ l : T.minus.Node, leaf l ∧ (coverMinus l).card ≤ fundMinus.card) := by
  rcases exists_unhit_leaf T selected level hits hpositive hdepth hunique hstock with
    ⟨l, hl, havoid⟩ | ⟨l, hl, havoid⟩
  · left
    refine ⟨l, hl, Finset.card_le_card ?_⟩
    intro t ht
    rcases hcoverPlus l hl t ht with hfund | ⟨hselected, v, hhit, hancestor⟩
    · exact hfund
    · exact (havoid t hselected v hhit hancestor).elim
  · right
    refine ⟨l, hl, Finset.card_le_card ?_⟩
    intro t ht
    rcases hcoverMinus l hl t ht with hfund | ⟨hselected, v, hhit, hancestor⟩
    · exact hfund
    · exact (havoid t hselected v hhit hancestor).elim

theorem side_choice (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (fundPlus fundMinus : Finset α)
    (coverPlus : T.plus.Node → Finset α) (coverMinus : T.minus.Node → Finset α)
    (K : ℕ)
    (hpositive : ∀ t ∈ selected, 0 < level t)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t)
    (hunique : ∀ t ∈ selected, ∀ v w, hits t v → hits t w → v = w)
    (hstock : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ T.height →
      (selected.filter fun t => level t = ℓ).card ≤ T.quota ℓ)
    (hcoverPlus : ∀ l, leaf l → ∀ t ∈ coverPlus l,
      t ∈ fundPlus ∨ t ∈ selected ∧ ∃ v, hits t (.inl v) ∧ ancestor v l)
    (hcoverMinus : ∀ l, leaf l → ∀ t ∈ coverMinus l,
      t ∈ fundMinus ∨ t ∈ selected ∧ ∃ v, hits t (.inr v) ∧ ancestor v l)
    (hlowerPlus : ∀ l, leaf l → d ≤ (coverPlus l).card + 6 * K)
    (hlowerMinus : ∀ l, leaf l → d ≤ (coverMinus l).card + 6 * K) :
    d ≤ fundPlus.card + 6 * K ∨ d ≤ fundMinus.card + 6 * K := by
  rcases exists_leaf_coverage_le_funded T selected level hits fundPlus fundMinus
    coverPlus coverMinus hpositive hdepth hunique hstock hcoverPlus hcoverMinus with
    ⟨l, hl, hle⟩ | ⟨l, hl, hle⟩
  · exact Or.inl ((hlowerPlus l hl).trans (Nat.add_le_add_right hle _))
  · exact Or.inr ((hlowerMinus l hl).trans (Nat.add_le_add_right hle _))

end BinPackingGap.SideChoice

namespace BinPackingGap

section

def reductionTrees (c : ℕ) (ρ : ℝ) : CompetingTrees (depthDemand c ρ) :=
  competingTrees (depthDemand c ρ) (depthDemand_pos c ρ)

def reductionInventory (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) : InventoryData :=
  InventoryData.ofCompetingTrees G (reductionTrees c ρ)
    (repetitions (reductionTrees c ρ).quotaTotal G.n (lossAllowance c)) k

def reductionInstance (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) : Instance :=
  (reductionInventory c ρ G k).packingInstance

def reductionBinBound (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) : ℕ :=
  (reductionInventory c ρ G k).B

@[simp] theorem reductionInventory_graph (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).graph = G := rfl

@[simp] theorem reductionInventory_d (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).d = depthDemand c ρ := rfl

@[simp] theorem reductionInventory_k (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).k = k := rfl

@[simp] theorem reductionInventory_P (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).P = (reductionTrees c ρ).quotaTotal := rfl

theorem reductionInventory_R (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).R =
      repetitions (reductionInventory c ρ G k).P G.n (lossAllowance c) := rfl

theorem reductionInventory_R_pos (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    0 < (reductionInventory c ρ G k).R := repetitions_pos _ _ _

theorem reductionInventory_height_pos (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    0 < (reductionInventory c ρ G k).L := (reductionTrees c ρ).height_pos

theorem reductionInventory_plus_height (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).plus.height = (reductionInventory c ρ G k).L :=
  (reductionTrees c ρ).plus_height

theorem reductionInventory_minus_height (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).minus.height = (reductionInventory c ρ G k).L :=
  (reductionTrees c ρ).minus_height

theorem reductionInstance_count (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ)
    (hk : k ≤ G.n) :
    (reductionInstance c ρ G k).n = 5 * reductionBinBound c ρ G k :=
  (reductionInventory c ρ G k).packingInstance_n hk

theorem reductionInstance_size_bounds (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ)
    (i : (reductionInstance c ρ G k).Item) :
    (1 / 6 : ℚ) < (reductionInstance c ρ G k).size i ∧
      (reductionInstance c ρ G k).size i < 1 :=
  (reductionInventory c ρ G k).packingInstance_size_mem_interval i

namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

private theorem selected_inventory_subclass (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    D.itemSubclass ⟨r, roleCopy p e t r⟩ =
      patternSubclass (p.tablePattern (subclass e) t) r := by
  have h := p.itemAtRole_subclass (subclass e) t r
  rw [← roleCopy_item p e t r] at h
  simpa only [subclass, Function.comp_apply, Equiv.symm_apply_apply] using h

private theorem selected_row_subclass (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    D.rowSubclass (rowCopy p e t).2 =
      patternSubclass (p.tablePattern (subclass e) t) .x := by
  have h := selected_inventory_subclass p e t .x
  change D.itemSubclass ⟨.x, rowCopy p e t⟩ = _ at h
  rcases hc : rowCopy p e t with ⟨v, r⟩
  simpa only [hc, InventoryData.itemSubclass] using h

private theorem unit_global_species (u : D.GlobalCopy) (hu : D.globalUnit u = true) :
    u.1 = .up true ∨ u.1 = .um true := by
  rcases u with ⟨s, i⟩
  cases s with
  | up one => cases one <;> simp_all [InventoryData.globalUnit]
  | um one => cases one <;> simp_all [InventoryData.globalUnit]
  | edge edge permit => simp [InventoryData.globalUnit] at hu

private theorem selected_row_tm_of_um (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) {one : Bool}
    (hs : (globalCopy p e t).1 = .um one) :
    D.rowSubclass (rowCopy p e t).2 = .tm := by
  have hg := selected_inventory_subclass p e t .«global»
  have hclass : D.itemSubclass ⟨.«global», globalCopy p e t⟩ = .um := by
    rcases hc : globalCopy p e t with ⟨s, i⟩
    have hs' : s = .um one := by simpa only [hc] using hs
    subst s
    rfl
  rw [hclass] at hg
  have hx := selected_row_subclass p e t
  cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]

private theorem selected_row_not_tm_of_up (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) {one : Bool}
    (hs : (globalCopy p e t).1 = .up one) :
    D.rowSubclass (rowCopy p e t).2 ≠ .tm := by
  have hg := selected_inventory_subclass p e t .«global»
  have hclass : D.itemSubclass ⟨.«global», globalCopy p e t⟩ = .up := by
    rcases hc : globalCopy p e t with ⟨s, i⟩
    have hs' : s = .up one := by simpa only [hc] using hs
    subst s
    rfl
  rw [hclass] at hg
  have hx := selected_row_subclass p e t
  cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]

private theorem selected_global_resource (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    p.itemAtRole (subclass e) t .«global» ∈
      globalResources e (globalCopy p e t).1 := by
  apply (mem_globalResources e _ _).mpr
  refine ⟨(globalCopy p e t).2, ?_⟩
  exact roleCopy_item p e t .«global»

private theorem funded_of_species (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    {s : GlobalSpecies D.graph} (hs : (globalCopy p e t).1 = s) :
    t ∈ fundedTuples p e s v := by
  apply (mem_fundedTuples p e s v t).mpr
  refine ⟨ht, ?_⟩
  have hr := selected_global_resource p e t
  rwa [hs] at hr

theorem covering_plus_unit_funded (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (leaf : D.PlusLeaf) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus leaf.val)
    (hu : D.globalUnit (globalCopy p e t) = true)
    (hc : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    t ∈ fundedTuples p e (.up true) v := by
  rcases unit_global_species (globalCopy p e t) hu with hup | hum
  · exact funded_of_species p e v t ht hup
  · have hrow := selected_row_tm_of_um p e t hum
    have hfinish : 1 < tupleFinish p e t :=
      D.minus_row_completion_gt_one (rowCopy p e t).2 (globalCopy p e t)
        (localCopy p e t).2 hrow
    have hroot := TreeGeometry.nodeCell_subset_root D.graph.edges.length D.R
      D.geometryBound .plus D.plus_branch_le_geometryBound leaf.val ha
    have ha1 : a ≤ 1 := by
      simpa only [TreeGeometry.rootOffset, zero_add] using hroot.2
    exact False.elim (by linarith only [hfinish, ha1, hc.1])

theorem covering_minus_unit_funded (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (leaf : D.MinusLeaf) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus leaf.val)
    (hu : D.globalUnit (globalCopy p e t) = true)
    (hc : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    t ∈ fundedTuples p e (.um true) v := by
  rcases unit_global_species (globalCopy p e t) hu with hup | hum
  · have hrow := selected_row_not_tm_of_up p e t hup
    have hbase : tupleBaseline p e t ≤ 1 :=
      D.rowBaseline_le_one_of_not_tm (rowCopy p e t).2 hrow
    have hroot := TreeGeometry.nodeCell_subset_root D.graph.edges.length D.R
      D.geometryBound .minus D.minus_branch_le_geometryBound leaf.val ha
    have ha4 : 4 ≤ a := hroot.1
    exact False.elim (by linarith only [hbase, ha4, hc.2])
  · exact funded_of_species p e v t ht hum

theorem zero_lengths_cover_jobCell (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) {a : ℚ}
    (hu : D.globalUnit (globalCopy p e t) = false)
    (hl : tupleLocalLength p e t = 0)
    (hc : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    ∃ j : D.JobCopy (rowCopy p e t).1,
      a ∈ D.testCell (.inr (.inr j.1) : D.TestAt (rowCopy p e t).1) := by
  have hg := tupleGlobalLength_eq_of_unit_false p e t hu
  have hmem : a ∈ completionInterval (tupleBaseline p e t) (tupleShort p e t) 0 0
      (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
    change completion (tupleBaseline p e t) (tupleShort p e t) 0 0 _ ≤ a ∧
      a < tupleBaseline p e t
    simpa only [tupleFinish, hg, hl] using hc
  change a ∈ completionInterval (D.rowBaseline (rowCopy p e t).2)
    (D.rowShort (rowCopy p e t).2) 0 0
    (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) at hmem
  by_cases hs : D.rowShort (rowCopy p e t).2 = true
  · obtain ⟨j, _, _, hj⟩ := D.row_zero_resources_job (rowCopy p e t).2 hs
    rw [hj] at hmem
    refine ⟨j, ?_⟩
    change a ∈ Geometry.closedJobCell D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j)
    exact ⟨hmem.1, hmem.2.le⟩
  · have hsfalse : D.rowShort (rowCopy p e t).2 = false := by
      cases hh : D.rowShort (rowCopy p e t).2 <;> simp_all
    rw [D.row_zero_resources_empty (rowCopy p e t).2 hsfalse] at hmem
    cases hmem

theorem zero_lengths_not_cover_plus_leaf (p : Packing I b) (e : D.Item ≃ I.Item)
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (t : p.TableBin (subclass e)) (leaf : D.PlusLeaf) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus leaf.val)
    (hu : D.globalUnit (globalCopy p e t) = false)
    (hl : tupleLocalLength p e t = 0) :
    ¬ (tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) := by
  intro hc
  obtain ⟨j, hj⟩ := zero_lengths_cover_jobCell p e t hu hl hc
  have hleaf : a ∈ D.testCell (.inl leaf : D.TestAt (rowCopy p e t).1) := ha
  have hdis := D.testCell_disjoint hplusheight hminusheight hL
    (show (.inl leaf : D.TestAt (rowCopy p e t).1) ≠ .inr (.inr j.1) by
      intro h; cases h)
  exact Set.disjoint_left.mp hdis hleaf hj

theorem zero_lengths_not_cover_minus_leaf (p : Packing I b) (e : D.Item ≃ I.Item)
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (t : p.TableBin (subclass e)) (leaf : D.MinusLeaf) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus leaf.val)
    (hu : D.globalUnit (globalCopy p e t) = false)
    (hl : tupleLocalLength p e t = 0) :
    ¬ (tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) := by
  intro hc
  obtain ⟨j, hj⟩ := zero_lengths_cover_jobCell p e t hu hl hc
  have hleaf : a ∈ D.testCell (.inr (.inl leaf) : D.TestAt (rowCopy p e t).1) := ha
  have hdis := D.testCell_disjoint hplusheight hminusheight hL
    (show (.inr (.inl leaf) : D.TestAt (rowCopy p e t).1) ≠ .inr (.inr j.1) by
      intro h; cases h)
  exact Set.disjoint_left.mp hdis hleaf hj

end PackingCounts

open UniformTree

namespace InventoryData

variable (D : InventoryData)

def plusPoint (v : D.plus.Node) : ℚ :=
  (TreeGeometry.left D.graph.edges.length D.R D.geometryBound .plus v.val +
    TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus v.val) / 2

def minusPoint (v : D.minus.Node) : ℚ :=
  (TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus v.val +
    TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus v.val) / 2

theorem plusPoint_mem_Ico (v : D.plus.Node) :
    D.plusPoint v ∈ Set.Ico
      (TreeGeometry.left D.graph.edges.length D.R D.geometryBound .plus v.val)
      (TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus v.val) := by
  have h := TreeGeometry.left_lt_right D.graph.edges.length D.R D.geometryBound .plus v.val
  dsimp only [plusPoint, Set.mem_Ico]
  constructor <;> linarith

theorem minusPoint_mem_Ico (v : D.minus.Node) :
    D.minusPoint v ∈ Set.Ico
      (TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus v.val)
      (TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus v.val) := by
  have h := TreeGeometry.left_lt_right D.graph.edges.length D.R D.geometryBound .minus v.val
  dsimp only [minusPoint, Set.mem_Ico]
  constructor <;> linarith

theorem plusPoint_mem_cell (v : D.plus.Node) :
    D.plusPoint v ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus v :=
  ⟨(D.plusPoint_mem_Ico v).1, (D.plusPoint_mem_Ico v).2.le⟩

theorem minusPoint_mem_cell (v : D.minus.Node) :
    D.minusPoint v ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus v :=
  ⟨(D.minusPoint_mem_Ico v).1, (D.minusPoint_mem_Ico v).2.le⟩

def taggedAddress : D.plus.Node ⊕ D.minus.Node → TreeGeometry.Side × List ℕ
  | .inl v => (.plus, v.val)
  | .inr v => (.minus, v.val)

theorem taggedAddress_injective : Function.Injective D.taggedAddress := by
  intro u v h
  cases u with
  | inl u =>
    cases v with
    | inl v => exact congrArg Sum.inl (Subtype.ext (congrArg Prod.snd h))
    | inr v => have hs := congrArg Prod.fst h; cases hs
  | inr u =>
    cases v with
    | inl v => have hs := congrArg Prod.fst h; cases hs
    | inr v => exact congrArg Sum.inr (Subtype.ext (congrArg Prod.snd h))

def taggedNodeDepth (v : D.plus.Node ⊕ D.minus.Node) : ℕ :=
  (D.taggedAddress v).2.length

def taggedNodeCell (v : D.plus.Node ⊕ D.minus.Node) : Set ℚ :=
  TreeGeometry.cell D.graph.edges.length D.R D.geometryBound
    (D.taggedAddress v).1 (D.taggedAddress v).2

theorem taggedAddress_bounded (v : D.plus.Node ⊕ D.minus.Node) :
    TreeGeometry.BoundedAddress D.geometryBound (D.taggedAddress v).2 := by
  cases v with
  | inl v => exact TreeGeometry.boundedAddress_node v D.plus_branch_le_geometryBound
  | inr v => exact TreeGeometry.boundedAddress_node v D.minus_branch_le_geometryBound

end InventoryData

namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def tupleHits (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (v : D.plus.Node ⊕ D.minus.Node) : Prop :=
  D.taggedNodeDepth v = tupleLocalDepth p e t ∧
    (tupleClosedInterval p e t ∩ D.taggedNodeCell v).Nonempty

theorem selected_hits_unique (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v)
    (u w : D.plus.Node ⊕ D.minus.Node)
    (hu : tupleHits p e t u) (hw : tupleHits p e t w) : u = w := by
  apply D.taggedAddress_injective
  exact TreeGeometry.eq_of_short_intersections D.graph.edges.length D.R D.geometryBound
    (Finset.mem_Icc.mp (selected_depth_mem p e v t ht)).2
    hu.1 hw.1 (D.taggedAddress_bounded u) (D.taggedAddress_bounded w)
    (selected_interval_length p e v t ht) hu.2 hw.2

theorem main_local_nonzero_positive (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (hlocal : tupleLocalLength p e t ≠ 0) :
    p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v := by
  have hlabel := good_local_vertex p e v t
    (Coverage.mainTuplesAt_subset_good p (subclass e) (label e) v ht)
  cases hcopy : localCopy p e t with
  | mk w l =>
    have hwv : w = v := by simpa only [hcopy] using hlabel
    subst w
    rcases l with ((i | z) | j)
    · apply (mem_positiveLocalResources e v _).mpr
      refine ⟨i, ?_⟩
      rw [← roleCopy_item p e t .«local»]
      exact congrArg (fun x : (Σ w : D.Vertex, D.LocalAt w) => e ⟨.«local», x⟩)
        hcopy.symm
    · exact (hlocal (congrArg
        (fun x : (Σ w : D.Vertex, D.LocalAt w) => D.localLength x.2) hcopy)).elim
    · exact (hlocal (congrArg
        (fun x : (Σ w : D.Vertex, D.LocalAt w) => D.localLength x.2) hcopy)).elim

theorem selected_hits_plus_ancestor (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) (hheight : D.plus.height = D.L)
    (l : D.plus.Node) (hl : leaf l) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus l)
    (hcover : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    ∃ u : D.plus.Node, tupleHits p e t (.inl u) ∧ ancestor u l := by
  let ell := tupleLocalDepth p e t
  have hell : ell ≤ depth l := by
    rw [(leaf_iff_depth_eq_height l).mp hl, hheight]
    exact (Finset.mem_Icc.mp (selected_depth_mem p e v t ht)).2
  refine ⟨ancestorAt l ell, ⟨depth_ancestorAt l hell, ?_⟩, ancestorAt_ancestor l ell⟩
  refine ⟨a, ⟨hcover.1, hcover.2.le⟩, ?_⟩
  exact TreeGeometry.mem_ancestor_cell D.graph.edges.length D.R D.geometryBound .plus
    D.plus_branch_le_geometryBound l ell ha

theorem selected_hits_minus_ancestor (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) (hheight : D.minus.height = D.L)
    (l : D.minus.Node) (hl : leaf l) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus l)
    (hcover : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    ∃ u : D.minus.Node, tupleHits p e t (.inr u) ∧ ancestor u l := by
  let ell := tupleLocalDepth p e t
  have hell : ell ≤ depth l := by
    rw [(leaf_iff_depth_eq_height l).mp hl, hheight]
    exact (Finset.mem_Icc.mp (selected_depth_mem p e v t ht)).2
  refine ⟨ancestorAt l ell, ⟨depth_ancestorAt l hell, ?_⟩, ancestorAt_ancestor l ell⟩
  refine ⟨a, ⟨hcover.1, hcover.2.le⟩, ?_⟩
  exact TreeGeometry.mem_ancestor_cell D.graph.edges.length D.R D.geometryBound .minus
    D.minus_branch_le_geometryBound l ell ha

theorem covering_plus_classification (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (l : D.plus.Node) (hl : leaf l) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus l)
    (ht : t ∈ tupleCovering p e v a) :
    t ∈ fundedTuples p e (.up true) v ∨
      t ∈ zeroPositiveTuples p e v ∧
        ∃ u : D.plus.Node, tupleHits p e t (.inl u) ∧ ancestor u l := by
  obtain ⟨hmain, hcover⟩ := (mem_tupleCovering p e v a t).mp ht
  cases hu : D.globalUnit (globalCopy p e t) with
  | false =>
    have hlocal : tupleLocalLength p e t ≠ 0 := by
      intro hz
      exact zero_lengths_not_cover_plus_leaf p e hplusheight hminusheight hL t
        ⟨l, hl⟩ ha hu hz hcover
    have hselected : t ∈ zeroPositiveTuples p e v :=
      (mem_zeroPositiveTuples p e v t).mpr
        ⟨hmain, hu, main_local_nonzero_positive p e v t hmain hlocal⟩
    exact Or.inr ⟨hselected,
      selected_hits_plus_ancestor p e v t hselected hplusheight l hl ha hcover⟩
  | true =>
    exact Or.inl (covering_plus_unit_funded p e v t hmain ⟨l, hl⟩ ha hu hcover)

theorem covering_minus_classification (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (l : D.minus.Node) (hl : leaf l) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus l)
    (ht : t ∈ tupleCovering p e v a) :
    t ∈ fundedTuples p e (.um true) v ∨
      t ∈ zeroPositiveTuples p e v ∧
        ∃ u : D.minus.Node, tupleHits p e t (.inr u) ∧ ancestor u l := by
  obtain ⟨hmain, hcover⟩ := (mem_tupleCovering p e v a t).mp ht
  cases hu : D.globalUnit (globalCopy p e t) with
  | false =>
    have hlocal : tupleLocalLength p e t ≠ 0 := by
      intro hz
      exact zero_lengths_not_cover_minus_leaf p e hplusheight hminusheight hL t
        ⟨l, hl⟩ ha hu hz hcover
    have hselected : t ∈ zeroPositiveTuples p e v :=
      (mem_zeroPositiveTuples p e v t).mpr
        ⟨hmain, hu, main_local_nonzero_positive p e v t hmain hlocal⟩
    exact Or.inr ⟨hselected,
      selected_hits_minus_ancestor p e v t hselected hminusheight l hl ha hcover⟩
  | true =>
    exact Or.inl (covering_minus_unit_funded p e v t hmain ⟨l, hl⟩ ha hu hcover)

theorem side_choice_of_competingTrees (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) (p : Packing I b)
    (e : (InventoryData.ofCompetingTrees G T R k).Item ≃ I.Item)
    (v : G.Vertex) (K : ℕ)
    (hlowerPlus : ∀ l : T.plus.Node, leaf l →
      d ≤ (tupleCovering p e v ((InventoryData.ofCompetingTrees G T R k).plusPoint l)).card +
        6 * K)
    (hlowerMinus : ∀ l : T.minus.Node, leaf l →
      d ≤ (tupleCovering p e v ((InventoryData.ofCompetingTrees G T R k).minusPoint l)).card +
        6 * K) :
    d ≤ xplus p e v + 6 * K ∨ d ≤ xminus p e v + 6 * K := by
  classical
  let D := InventoryData.ofCompetingTrees G T R k
  change d ≤ (fundedTuples p e (.up true) v).card + 6 * K ∨
    d ≤ (fundedTuples p e (.um true) v).card + 6 * K
  apply SideChoice.side_choice T (zeroPositiveTuples p e v) (tupleLocalDepth p e)
    (tupleHits p e) (fundedTuples p e (.up true) v) (fundedTuples p e (.um true) v)
    (fun l => tupleCovering p e v (D.plusPoint l))
    (fun l => tupleCovering p e v (D.minusPoint l)) K
  · intro t ht
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (selected_depth_mem p e v t ht)).1
  · intro t _ w hhit
    cases w <;> exact hhit.1
  · intro t ht u w hu hw
    exact selected_hits_unique p e v t ht u w hu hw
  · intro ell hlo hhi
    exact zeroPositiveTuples_depth_card_le p e v
      ⟨ell, Finset.mem_Icc.mpr ⟨hlo, hhi⟩⟩
  · intro l hl t ht
    exact covering_plus_classification p e v t T.plus_height T.minus_height
      (Nat.succ_le_of_lt T.height_pos) l hl (D.plusPoint_mem_cell l) ht
  · intro l hl t ht
    exact covering_minus_classification p e v t T.plus_height T.minus_height
      (Nat.succ_le_of_lt T.height_pos) l hl (D.minusPoint_mem_cell l) ht
  · exact hlowerPlus
  · exact hlowerMinus

theorem side_choice_of_test_coverage (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) (p : Packing I b)
    (e : (InventoryData.ofCompetingTrees G T R k).Item ≃ I.Item)
    (v : G.Vertex) (K : ℕ)
    (hcoverage : ∀ q : (InventoryData.ofCompetingTrees G T R k).TestAt v, ∀ a : ℚ,
      a ∈ (InventoryData.ofCompetingTrees G T R k).testInterval q →
        d ≤ (tupleCovering p e v a).card + 6 * K) :
    d ≤ xplus p e v + 6 * K ∨ d ≤ xminus p e v + 6 * K := by
  apply side_choice_of_competingTrees G T R k p e v K
  · intro l hl
    exact hcoverage (.inl ⟨l, hl⟩) _
      ((InventoryData.ofCompetingTrees G T R k).plusPoint_mem_Ico l)
  · intro l hl
    exact hcoverage (.inr (.inl ⟨l, hl⟩)) _
      ((InventoryData.ofCompetingTrees G T R k).minusPoint_mem_Ico l)

end PackingCounts

end

def extractedCover (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) {b : ℕ}
    (p : Packing (reductionInstance c ρ G k) b) : Finset G.Vertex :=
  thresholdCover (depthDemand c ρ)
    (PackingCounts.xplus p (reductionInventory c ρ G k).itemEquiv)

theorem reduction_side_choice (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ)
    (hk : k ≤ G.n) {b : ℕ} (p : Packing (reductionInstance c ρ G k) b)
    (hb : b ≤ reductionBinBound c ρ G k + c) (v : G.Vertex) :
    depthDemand c ρ ≤ PackingCounts.xplus p (reductionInventory c ρ G k).itemEquiv v +
      6 * lossAllowance c ∨
    depthDemand c ρ ≤ PackingCounts.xminus p (reductionInventory c ρ G k).itemEquiv v +
      6 * lossAllowance c := by
  let D := reductionInventory c ρ G k
  apply PackingCounts.side_choice_of_test_coverage G (reductionTrees c ρ)
    D.R k p D.itemEquiv v (lossAllowance c)
  intro q a ha
  exact D.test_coverage (reductionInventory_plus_height c ρ G k)
    (reductionInventory_minus_height c ρ G k)
    (Nat.succ_le_of_lt (reductionInventory_height_pos c ρ G k)) hk p hb v q a ha

theorem extractedCover_card_le (c : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (G : GraphInput) (k : ℕ) (hk : k ≤ G.n) {b : ℕ}
    (p : Packing (reductionInstance c ρ G k) b)
    (hb : b ≤ reductionBinBound c ρ G k + c) :
    ((extractedCover c ρ G k p).card : ℝ) ≤ (k : ℝ) + ρ * G.n := by
  let D := reductionInventory c ρ G k
  apply thresholdCover_card_le_graph G
    (PackingCounts.xplus p D.itemEquiv) (PackingCounts.xminus p D.itemEquiv)
    (depthDemand_pos c ρ) (depthDemand_ge_72 c ρ) hk hρ (depthDemand_ge_120_div c ρ)
  · exact PackingCounts.xplus_budget p D.itemEquiv
  · exact PackingCounts.total_budget p D.itemEquiv hk
  · exact reduction_side_choice c ρ G k hk p hb

end BinPackingGap

end

end OAI


