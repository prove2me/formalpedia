-- Prove2me | Definitions.Def_OAI_BinPackingGap_Part06
-- name    : OAI_BinPackingGap_Part06
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T18:42:46.202995+00:00
-- url     : https://prove2.me/theorems/5a7e1b5e-6690-4590-b2e1-f5607b781373
-- title:
--   Structural additive gap for bin packing, part 6 of 10 (port of OpenAI's formalization)
-- statement:
--   Part 6 of 10 of a port of OpenAI's Lean formalization of the structural additive gap from the manuscript *Additive hardness and unbounded configuration gaps in bin packing* (OpenAI, September 24, 2026). For every $c$, it constructs an instance with $5B$ items of sizes in $(1/6,1)$ whose individual and type configuration LPs both equal $B$, while the optimum exceeds $B+c$. This part contains the modules `Inventory/InventoryCoverage`, `Trees/KeyGeometry`, `Packing/PackingFeasibility`, `Inventory/EdgeLongConsumption`, `Trees/TreeAttachment`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/BinPacking`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `BinPackingGap`, which matches upstream `Model.lean` up to two private lemmas and a section wrapper. This part sets `maxHeartbeats` to 1000000, because the platform compiler exceeded the default heartbeat limit on a `simp` call that stays far below it locally.
--
--   The development is split into 10 parts only so that each compiles within the platform's time limit. The final part proves `OAI.BinPackingGap.structural_additive_gap`, the first clause of `OAI.BinPackingGap.main_results`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/BinPacking: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Inventory/InventoryCoverage.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Trees/KeyGeometry.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/PackingFeasibility.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Inventory/EdgeLongConsumption.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Trees/TreeAttachment.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf

/-
Structural additive gap for bin packing (port of OpenAI's formalization), part 6 of 10.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/BinPacking/: Inventory/InventoryCoverage.lean, Trees/KeyGeometry.lean, Packing/PackingFeasibility.lean, Inventory/EdgeLongConsumption.lean, Trees/TreeAttachment.lean
These files formalize part of the manuscript "Additive hardness and unbounded configuration gaps in
bin packing" (OpenAI, September 24, 2026). Copyright OpenAI. Licensed under the Apache License,
Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same
license, on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Model.lean) come from the platform definition `BinPackingGap`, to which upstream Model.lean
is identical up to two private lemmas and a section wrapper; `set_option maxHeartbeats 1000000` is set for this part (the platform compiler exceeded the default heartbeat limit on a `simp` call that stays far below it locally).
-/
import Mathlib
import Definitions.Def_OAI_BinPackingGap_Part05

set_option autoImplicit false
set_option maxHeartbeats 1000000

-- ===== Adapted from lean/OAI/Computability/BinPacking/Inventory/InventoryCoverage.lean =====
namespace OAI

noncomputable section
open scoped BigOperators

namespace BinPackingGap
namespace InventoryCoverage

variable {D : InventoryData} {I : Instance} {b : ℕ}

def itemRowBaseline (D : InventoryData) : D.Item → ℚ
  | ⟨.x, ⟨_, r⟩⟩ => D.rowBaseline r
  | _ => 0

def itemRowShort (D : InventoryData) : D.Item → Bool
  | ⟨.x, ⟨_, r⟩⟩ => D.rowShort r
  | _ => false

def itemKeyBaseline (D : InventoryData) : D.Item → ℚ
  | ⟨.anchor, ⟨_, .inr j⟩⟩ => Geometry.baseline D.graph.edges.length D.R (D.jobPosition j)
  | _ => 0

def itemDeadline (D : InventoryData) : D.Item → ℚ
  | ⟨.anchor, ⟨_, .inl z⟩⟩ => D.deadline z
  | _ => 0

def rowBaseline (e : D.Item ≃ I.Item) : I.Item → ℚ := itemRowBaseline D ∘ e.symm

def rowShort (e : D.Item ≃ I.Item) : I.Item → Bool := itemRowShort D ∘ e.symm

def keyBaseline (e : D.Item ≃ I.Item) : I.Item → ℚ := itemKeyBaseline D ∘ e.symm

def anchorDeadline (e : D.Item ≃ I.Item) : I.Item → ℚ := itemDeadline D ∘ e.symm

@[simp] theorem rowBaseline_selected (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) :
    rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) =
      D.rowBaseline (PackingCounts.rowCopy p e t).2 := by
  rw [← PackingCounts.roleCopy_item p e t .x]
  change itemRowBaseline D (e.symm (e ⟨.x, PackingCounts.rowCopy p e t⟩)) = _
  rw [e.symm_apply_apply]
  rfl

@[simp] theorem rowShort_selected (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) :
    rowShort e (p.itemAtRole (PackingCounts.subclass e) t .x) =
      D.rowShort (PackingCounts.rowCopy p e t).2 := by
  rw [← PackingCounts.roleCopy_item p e t .x]
  change itemRowShort D (e.symm (e ⟨.x, PackingCounts.rowCopy p e t⟩)) = _
  rw [e.symm_apply_apply]
  rfl

theorem keyBaseline_selected_of_key (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) (v : D.Vertex) (j : D.JobCopy v)
    (hcopy : PackingCounts.anchorCopy p e t = ⟨v, .inr j⟩) :
    keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor) =
      Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) := by
  rw [← PackingCounts.roleCopy_item p e t .anchor]
  change itemKeyBaseline D (e.symm (e ⟨.anchor, PackingCounts.anchorCopy p e t⟩)) = _
  rw [e.symm_apply_apply, hcopy]
  rfl

theorem anchorDeadline_selected_of_deadline (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) (v : D.Vertex) (z : D.MBase v)
    (hcopy : PackingCounts.anchorCopy p e t = ⟨v, .inl z⟩) :
    anchorDeadline e (p.itemAtRole (PackingCounts.subclass e) t .anchor) = D.deadline z := by
  rw [← PackingCounts.roleCopy_item p e t .anchor]
  change itemDeadline D (e.symm (e ⟨.anchor, PackingCounts.anchorCopy p e t⟩)) = _
  rw [e.symm_apply_apply, hcopy]
  rfl

theorem rowShort_implies_job (e : D.Item ≃ I.Item) (i : I.Item)
    (h : rowShort e i = true) : PackingCounts.subclass e i = .s := by
  let x := e.symm i
  change itemRowShort D x = true at h
  change D.itemSubclass x = .s
  rcases x with ⟨role, copy⟩
  cases role with
  | x =>
      rcases copy with ⟨v, tree | ⟨short, job⟩⟩
      · cases h
      · rfl
  | anchor => cases h
  | «global» => cases h
  | «local» => cases h
  | flag => cases h

private theorem treeSubclass_ne_s (t : D.TreeRow) : D.treeSubclass t ≠ .s := by
  rcases t with p | (m | pad) <;> simp [InventoryData.treeSubclass]

private theorem treeSubclass_tree (t : D.TreeRow) :
    D.treeSubclass t = .tp ∨ D.treeSubclass t = .tm := by
  rcases t with p | (m | pad)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

def treePrefix (D : InventoryData) (a : ℚ) : Finset D.TreeRow :=
  Finset.univ.filter fun r => D.treeBaseline r ≤ a

def jobPrefix (D : InventoryData) (v : D.Vertex) (a : ℚ) : Finset (D.JobCopy v) :=
  Finset.univ.filter fun j => Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) ≤ a

def originalBaselinePrefix (D : InventoryData) (v : D.Vertex) (a : ℚ) :
    Finset (D.MBase v) := Finset.univ.filter fun z => D.mainBaseline z ≤ a

def jobsAt (D : InventoryData) (v : D.Vertex) (current : ℚ) : Finset (D.JobCopy v) :=
  Finset.univ.filter fun j =>
    Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) = current

private theorem card_filter_transport {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (P : β → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter fun x => P (e x)).card := by
  exact (Finset.card_bijective (s := Finset.univ.filter fun x => P (e x))
    (t := Finset.univ.filter P) e e.bijective (fun _ => by simp)).symm

theorem jobRowPrefix_card (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    (Coverage.jobRowPrefixAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) a).card = 2 * (jobPrefix D v a).card := by
  classical
  unfold Coverage.jobRowPrefixAt
  rw [card_filter_transport e]
  simp only [jobPrefix, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, rowBaseline, itemRowBaseline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.rowBaseline, treeSubclass_ne_s,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type, two_mul]

theorem treeRowPrefix_card (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    (Coverage.treeRowPrefixAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) a).card = (treePrefix D a).card := by
  classical
  unfold Coverage.treeRowPrefixAt
  rw [card_filter_transport e]
  simp only [treePrefix, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, rowBaseline, itemRowBaseline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.rowBaseline, treeSubclass_tree,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem keyPrefix_card (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    (Coverage.keyPrefixAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (keyBaseline e) a).card = (jobPrefix D v a).card := by
  classical
  unfold Coverage.keyPrefixAt
  rw [card_filter_transport e]
  simp only [jobPrefix, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, keyBaseline, itemKeyBaseline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.treeSubclass, InventoryData.TreeRow,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem deadlinePrefix_card (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    (Coverage.deadlinePrefixAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (anchorDeadline e) a).card =
      (Finset.univ.filter fun z : D.MBase v => D.deadline z ≤ a).card := by
  classical
  unfold Coverage.deadlinePrefixAt
  rw [card_filter_transport e]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, anchorDeadline, itemDeadline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.treeSubclass, InventoryData.TreeRow,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem originalBaselinePrefix_card (D : InventoryData) (v : D.Vertex) (a : ℚ) :
    (originalBaselinePrefix D v a).card = (treePrefix D a).card + (jobPrefix D v a).card := by
  classical
  have hsplit : originalBaselinePrefix D v a =
      (treePrefix D a).disjSum (jobPrefix D v a) := by
    ext z
    cases z <;>
      simp only [originalBaselinePrefix, treePrefix, jobPrefix, Finset.mem_filter,
        Finset.mem_univ, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, true_and] <;>
      rfl
  rw [hsplit, Finset.card_disjSum]

theorem currentKeyItems_card (e : D.Item ≃ I.Item) (v : D.Vertex) (current : ℚ) :
    (Coverage.currentKeyItemsAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (keyBaseline e) current).card = (jobsAt D v current).card := by
  classical
  unfold Coverage.currentKeyItemsAt
  rw [card_filter_transport e]
  simp only [jobsAt, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, keyBaseline, itemKeyBaseline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.treeSubclass, InventoryData.TreeRow,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem currentShortItems_card (e : D.Item ≃ I.Item) (v : D.Vertex) (current : ℚ) :
    (Coverage.currentShortItemsAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (rowShort e) current).card = (jobsAt D v current).card := by
  classical
  unfold Coverage.currentShortItemsAt
  rw [card_filter_transport e]
  simp only [jobsAt, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, rowBaseline, rowShort,
    itemRowBaseline, itemRowShort, InventoryData.itemSubclass, InventoryData.itemLabel,
    InventoryData.RoleCopies, InventoryData.rowSubclass, InventoryData.rowBaseline,
    InventoryData.rowShort, treeSubclass_ne_s,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

def positionOf (D : InventoryData) {v : D.Vertex} (r : D.IncidencePosition v) : D.Position :=
  D.incidencePosition r

theorem positionOf_injective (D : InventoryData) (v : D.Vertex) :
    Function.Injective (positionOf D (v := v)) :=
  D.incidencePosition_injective v

theorem job_baseline_eq_iff (D : InventoryData) (v : D.Vertex)
    (j : D.JobCopy v) (r : D.IncidencePosition v) :
    Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) =
      Geometry.baseline D.graph.edges.length D.R (positionOf D r) ↔ j.1 = r := by
  rw [Geometry.baseline_eq_iff]
  change positionOf D j.1 = positionOf D r ↔ j.1 = r
  exact (positionOf_injective D v).eq_iff

theorem jobsAt_position_card (D : InventoryData) (v : D.Vertex)
    (r : D.IncidencePosition v) :
    (jobsAt D v (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card = D.d := by
  classical
  have heq : jobsAt D v (Geometry.baseline D.graph.edges.length D.R (positionOf D r)) =
      ({r} : Finset (D.IncidencePosition v)).product (Finset.univ : Finset (Fin D.d)) := by
    ext ⟨s, j⟩
    simp only [jobsAt, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.product_eq_sprod, Finset.mem_product, Finset.mem_singleton, and_true]
    exact job_baseline_eq_iff D v (s, j) r
  rw [heq]
  simp

theorem actual_displaced_baseline_prefix_le
    (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ)
    (extra : Finset (p.TableBin (PackingCounts.subclass e))) (K : ℕ)
    (hbad : (Coverage.badAnchorsAt p (PackingCounts.subclass e) (PackingCounts.label e) v).card ≤ 3 * K)
    (horder : ∀ t ∈ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤
        keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor))
    (hextra : extra ⊆ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v)
    (hextraRows : ∀ t ∈ extra, rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤ a)
    (hextraDis : Disjoint
      (Coverage.edgePrefixAt p (PackingCounts.subclass e) (PackingCounts.label e) v
        (keyBaseline e) a) extra) :
    (Coverage.baselinePrefixAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) a).card + extra.card ≤ (originalBaselinePrefix D v a).card + 3 * K := by
  apply Coverage.displaced_baseline_prefix_le p (PackingCounts.subclass e) (PackingCounts.label e) v
    (rowBaseline e) (keyBaseline e) a extra (originalBaselinePrefix D v a).card
    (jobPrefix D v a).card K hbad horder hextra hextraRows hextraDis
  · exact jobRowPrefix_card e v a
  · exact keyPrefix_card e v a
  · rw [treeRowPrefix_card, originalBaselinePrefix_card]

private theorem exists_job_of_subclass_s (D : InventoryData) (i : D.Item)
    (h : D.itemSubclass i = .s) :
    ∃ v : D.Vertex, ∃ short : Bool, ∃ j : D.JobCopy v,
      i = ⟨.x, ⟨v, .inr (short, j)⟩⟩ := by
  have hr : i.1 = .x := by
    change D.itemRole i = .x
    rw [← D.itemSubclass_role, h]
    rfl
  rcases i with ⟨role, copy⟩
  dsimp at hr
  subst role
  rcases copy with ⟨v, tree | ⟨short, job⟩⟩
  · exact False.elim (treeSubclass_ne_s tree h)
  · exact ⟨v, short, job, rfl⟩

theorem row_before_current_le_interior (e : D.Item ≃ I.Item) (i : I.Item)
    (hcls : PackingCounts.subclass e i = .s) {v : D.Vertex}
    (r : D.IncidencePosition v)
    (hearlier : rowBaseline e i <
      Geometry.baseline D.graph.edges.length D.R (positionOf D r)) :
    rowBaseline e i ≤
      Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L (positionOf D r) := by
  obtain ⟨w, short, j, hj⟩ := exists_job_of_subclass_s D (e.symm i) hcls
  have hbase : rowBaseline e i =
      Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) := by
    change itemRowBaseline D (e.symm i) = _
    rw [hj]
    rfl
  rw [hbase] at hearlier ⊢
  exact (Geometry.baseline_le_jobInterior D.geometryBound D.L).mpr
    (Geometry.baseline_lt_iff.mp hearlier)

theorem actual_displaced_job_prefix_le
    (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex)
    (r : D.IncidencePosition v) (K : ℕ)
    (hbad : (Coverage.badAnchorsAt p (PackingCounts.subclass e) (PackingCounts.label e) v).card ≤ 3 * K)
    (horder : ∀ t ∈ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤
        keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor)) :
    (Coverage.baselinePrefixAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e)
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L (positionOf D r))).card +
    (Coverage.displacedTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (keyBaseline e)
      (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card ≤
    (originalBaselinePrefix D v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L (positionOf D r))).card +
      3 * K := by
  classical
  apply actual_displaced_baseline_prefix_le p e v _ _ K hbad horder
  · intro t ht
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  · intro t ht
    obtain ⟨ht, hbefore⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht, _⟩ := Finset.mem_filter.mp ht
    have hpat := ((Coverage.mem_edgeTuplesAt p (PackingCounts.subclass e)
      (PackingCounts.label e) v t).mp ht).2.2
    apply row_before_current_le_interior e _ _ r hbefore
    rw [p.itemAtRole_subclass (PackingCounts.subclass e) t .x, hpat]
    rfl
  · apply Finset.disjoint_left.mpr
    intro t hearly hcurrent
    have hle := (Finset.mem_filter.mp hearly).2
    have heq := (Finset.mem_filter.mp (Finset.mem_filter.mp hcurrent).1).2
    rw [heq] at hle
    have hcut := (Geometry.jobInterior_mem_jobTestInterval D.graph.edges.length D.R
      D.geometryBound D.L (positionOf D r)).2
    exact (not_lt_of_ge hle) hcut

theorem actual_deadline_deficit_bound
    (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) (K : ℕ)
    (finish : p.TableBin (PackingCounts.subclass e) → ℚ)
    (hbad : (Coverage.badAnchorsAt p (PackingCounts.subclass e) (PackingCounts.label e) v).card ≤ 3 * K)
    (horder : ∀ t ∈ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤
        keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor))
    (hle : ∀ t ∈ Coverage.mainTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      finish t ≤ rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x))
    (hfeasible : ∀ t ∈ Coverage.mainTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      finish t ≤ anchorDeadline e (p.itemAtRole (PackingCounts.subclass e) t .anchor)) :
    (Finset.univ.filter fun z : D.MBase v => D.deadline z ≤ a).card ≤
      (originalBaselinePrefix D v a).card +
      (Coverage.coveringTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v
        (rowBaseline e) finish a).card + 6 * K := by
  classical
  have hbase := actual_displaced_baseline_prefix_le p e v a ∅ K hbad horder
    (Finset.empty_subset _) (by simp) (by simp)
  simp only [Finset.card_empty, Nat.add_zero] at hbase
  have hdeadline := Coverage.deadline_prefix_le_completion_add_loss p
    (PackingCounts.subclass e) (PackingCounts.label e) v (anchorDeadline e) finish a K
    hbad hfeasible
  rw [deadlinePrefix_card] at hdeadline
  have hsplit := Coverage.completion_prefix_decomposition p (PackingCounts.subclass e)
    (PackingCounts.label e) v (rowBaseline e) finish hle a
  omega

theorem actual_current_long_matches_from_correction
    (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex)
    (r : D.IncidencePosition v) (K xplus : ℕ)
    (hbad : (Coverage.badAnchorsAt p (PackingCounts.subclass e) (PackingCounts.label e) v).card ≤ 3 * K)
    (horder : ∀ t ∈ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤
        keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor))
    (hcorrection : D.d + (Coverage.displacedTuplesAt p (PackingCounts.subclass e)
        (PackingCounts.label e) v (rowBaseline e) (keyBaseline e)
        (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card ≤
      xplus + (Coverage.currentShortMainAt p (PackingCounts.subclass e)
        (PackingCounts.label e) v (rowBaseline e) (rowShort e)
        (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card + 6 * K) :
    D.d ≤ (Coverage.currentLongEdgeAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (keyBaseline e) (rowShort e)
      (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card + xplus + 9 * K := by
  apply Coverage.current_long_matches_from_correction p (PackingCounts.subclass e)
    (PackingCounts.label e) v (rowBaseline e) (keyBaseline e) (rowShort e)
    (Geometry.baseline D.graph.edges.length D.R (positionOf D r)) D.d K xplus
    hbad horder (rowShort_implies_job e) _ _ hcorrection
  · rw [currentKeyItems_card, jobsAt_position_card]
  · rw [currentShortItems_card, jobsAt_position_card]

end InventoryCoverage
end BinPackingGap

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Trees/KeyGeometry.lean =====
namespace OAI

namespace BinPackingGap.Geometry

def keyExpression (m R D L : ℕ) (row key : Position m R) (edge : Fin m)
    (nonpermit short : Bool) : ℚ :=
  baseline m R row - baseline m R key + beta m R edge - beta m R key.1 +
    delta m R D L * ((if nonpermit then 1 else 0) - (if short then 1 else 0))

theorem keyExpression_eq_coordinates (m R D L : ℕ) (row key : Position m R)
    (edge : Fin m) (nonpermit short : Bool) :
    keyExpression m R D L row key edge nonpermit short =
      (baseline m R row - if short then delta m R D L else 0) +
      (-baseline m R key - beta m R key.1) +
      (beta m R edge + if nonpermit then delta m R D L else 0) + 0 + 0 := by
  cases nonpermit <;> cases short <;> simp [keyExpression] <;> ring

theorem key_perturbation_lower (m R D L : ℕ) (nonpermit short : Bool) :
    -delta m R D L ≤
      delta m R D L * ((if nonpermit then 1 else 0) - (if short then 1 else 0)) := by
  have hd := delta_nonneg m R D L
  cases nonpermit <;> cases short <;> simp_all

theorem keyExpression_pos_of_later_row {m R D L : ℕ}
    {row key : Position m R} (edge : Fin m) (nonpermit short : Bool)
    (hlater : posLT key row) :
    0 < keyExpression m R D L row key edge nonpermit short := by
  have hg := gap_pos m R
  have hd := delta_lt_gap m R D L
  have hjump := mul_le_mul_of_nonneg_left (heightCode_jump hlater) (le_of_lt hg)
  have hedge := mul_nonneg (le_of_lt hg) (theta_nonneg R edge)
  have hpert := key_perturbation_lower m R D L nonpermit short
  dsimp [keyExpression, baseline, beta]
  nlinarith

theorem keyExpression_pos_of_later_edge {m R D L : ℕ}
    (row key : Position m R) {edge : Fin m} (nonpermit short : Bool)
    (hlater : key.1 < edge) :
    0 < keyExpression m R D L row key edge nonpermit short := by
  have hg := gap_pos m R
  have hd := delta_lt_gap m R D L
  have hjump := mul_le_mul_of_nonneg_left
    (theta_jump_ge_heightCode (R := R) hlater) (le_of_lt hg)
  have hrow := mul_nonneg (le_of_lt hg) (heightCode_nonneg R row)
  have hpert := key_perturbation_lower m R D L nonpermit short
  dsimp [keyExpression, baseline, beta]
  nlinarith

theorem row_order_of_key_feasible {m R D L : ℕ}
    {row key : Position m R} {edge : Fin m} {nonpermit short : Bool}
    (h : keyExpression m R D L row key edge nonpermit short ≤ 0) :
    posLE row key := by
  apply posLE_iff_not_posLT.mpr
  intro hlater
  exact (not_lt_of_ge h) (keyExpression_pos_of_later_row edge nonpermit short hlater)

theorem edge_order_of_key_feasible {m R D L : ℕ}
    {row key : Position m R} {edge : Fin m} {nonpermit short : Bool}
    (h : keyExpression m R D L row key edge nonpermit short ≤ 0) :
    edge ≤ key.1 := by
  by_contra hnot
  exact (not_lt_of_ge h)
    (keyExpression_pos_of_later_edge row key nonpermit short (lt_of_not_ge hnot))

theorem keyExpression_exact_position_edge (m R D L : ℕ)
    (key : Position m R) (nonpermit short : Bool) :
    keyExpression m R D L key key key.1 nonpermit short =
      delta m R D L * ((if nonpermit then 1 else 0) - (if short then 1 else 0)) := by
  simp [keyExpression]

theorem short_exact_key_feasible (m R D L : ℕ) (key : Position m R)
    (nonpermit : Bool) :
    keyExpression m R D L key key key.1 nonpermit true ≤ 0 := by
  rw [keyExpression_exact_position_edge]
  have hd := delta_nonneg m R D L
  cases nonpermit <;> simp_all

theorem long_exact_key_feasible_iff (m R D L : ℕ) (key : Position m R)
    (nonpermit : Bool) :
    keyExpression m R D L key key key.1 nonpermit false ≤ 0 ↔ nonpermit = false := by
  rw [keyExpression_exact_position_edge]
  have hd := delta_pos m R D L
  cases nonpermit <;> simp_all

theorem exact_long_key_resource {m R D L : ℕ}
    (key : Position m R) (edge : Fin m) (nonpermit : Bool)
    (h : keyExpression m R D L key key edge nonpermit false ≤ 0) :
    edge < key.1 ∨ (edge = key.1 ∧ nonpermit = false) := by
  have he := edge_order_of_key_feasible h
  rcases lt_or_eq_of_le he with hlt | heq
  · exact Or.inl hlt
  · right
    refine ⟨heq, ?_⟩
    subst edge
    exact (long_exact_key_feasible_iff m R D L key nonpermit).mp h

end BinPackingGap.Geometry

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/PackingFeasibility.lean =====
namespace OAI

noncomputable section

namespace BinPackingGap
namespace PackingCounts

open scoped BigOperators

variable {D : InventoryData} {I : Instance} {b : ℕ}

theorem good_selected_labels (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) (r : Role) :
    label e (p.itemAtRole (subclass e) t r) = tableRoleLabel v v v r := by
  cases r with
  | x =>
      simpa only [selected_row_label, tableRoleLabel] using
        congrArg some (good_row_vertex p e v t ht)
  | anchor =>
      simpa only [selected_anchor_label, tableRoleLabel] using
        congrArg some (good_anchor_vertex p e v t ht)
  | «global» =>
      change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .«global»)) = none
      rw [← roleCopy_item p e t .«global», e.symm_apply_apply]
      rfl
  | «local» =>
      simpa only [selected_local_label, tableRoleLabel] using
        congrArg some (good_local_vertex p e v t ht)
  | flag =>
      change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .flag)) = none
      rw [← roleCopy_item p e t .flag, e.symm_apply_apply]
      rfl

@[simp] theorem selected_itemCoordinate (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    D.itemCoordinate (e.symm (p.itemAtRole (subclass e) t r)) =
      D.itemCoordinate ⟨r, roleCopy p e t r⟩ := by
  rw [← roleCopy_item p e t r]
  simp only [Equiv.symm_apply_apply]

theorem good_coordinate_nonpos (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    D.rowCoordinate (rowCopy p e t).2 + D.anchorCoordinate (anchorCopy p e t).2 +
      D.globalCoordinate (globalCopy p e t) + D.localCoordinate (localCopy p e t).2 ≤ 0 := by
  have h := p.table_coordinate_nonpos_of_same_label (subclass e) (label e)
    (fun i => D.itemCoordinate (e.symm i)) hsize t v (good_selected_labels p e v t ht)
  simp only [selected_itemCoordinate] at h
  rw [Role.sum_univ] at h
  have hx (x : Σ v : D.Vertex, D.RowAt v) :
      D.itemCoordinate ⟨.x, x⟩ = D.rowCoordinate x.2 := by
    cases x
    rfl
  have ha (a : Σ v : D.Vertex, D.AnchorAt v) :
      D.itemCoordinate ⟨.anchor, a⟩ = D.anchorCoordinate a.2 := by
    cases a
    rfl
  have hl (l : Σ v : D.Vertex, D.LocalAt v) :
      D.itemCoordinate ⟨.«local», l⟩ = D.localCoordinate l.2 := by
    cases l
    rfl
  rw [hx (rowCopy p e t), ha (anchorCopy p e t), hl (localCopy p e t)] at h
  simpa only [InventoryData.itemCoordinate, add_zero] using h

private theorem main_anchor_of_subclass (a : Σ v : D.Vertex, D.AnchorAt v)
    (h : D.itemSubclass ⟨.anchor, a⟩ = .z) :
    ∃ z : D.MBase a.1, a.2 = .inl z := by
  rcases a with ⟨v, z | j⟩
  · exact ⟨z, rfl⟩
  · simp [InventoryData.itemSubclass] at h

private theorem globalCoordinate_of_not_w (u : D.GlobalCopy)
    (h : D.itemSubclass ⟨.«global», u⟩ ≠ .w) :
    D.globalCoordinate u = -D.globalLength u := by
  rcases u with ⟨species, i⟩
  cases species with
  | up one => rfl
  | um one => rfl
  | edge edge permit => exact (h rfl).elim

theorem main_anchor_copy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hpat : p.tablePattern (subclass e) t ≠ .edgeJob) :
    ∃ z : D.MBase (anchorCopy p e t).1, (anchorCopy p e t).2 = .inl z := by
  apply main_anchor_of_subclass
  have h := roleCopy_subclass p e t .anchor
  cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]

theorem main_globalCoordinate (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hpat : p.tablePattern (subclass e) t ≠ .edgeJob) :
    D.globalCoordinate (globalCopy p e t) = -D.globalLength (globalCopy p e t) := by
  apply globalCoordinate_of_not_w
  have h := roleCopy_subclass p e t .«global»
  cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]

theorem main_completion_le_deadline (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v) :
    ∃ z : D.MBase (anchorCopy p e t).1,
      (anchorCopy p e t).2 = .inl z ∧ tupleFinish p e t ≤ D.deadline z := by
  have hpat := ((Coverage.mem_mainTuplesAt p (subclass e) (label e) v t).mp ht).2.2
  have hgood := Coverage.mainTuplesAt_subset_good p (subclass e) (label e) v ht
  have h := good_coordinate_nonpos p e hsize v t hgood
  obtain ⟨z, hz⟩ := main_anchor_copy p e t hpat
  refine ⟨z, hz, ?_⟩
  have ha : D.anchorCoordinate (anchorCopy p e t).2 = -D.deadline z := by
    rw [hz]
    rfl
  rw [ha, main_globalCoordinate p e t hpat] at h
  change D.rowCoordinate (rowCopy p e t).2 + -D.deadline z +
    -D.globalLength (globalCopy p e t) + -D.localLength (localCopy p e t).2 ≤ 0 at h
  have rearrange (x deadline globalLen localLen : ℚ)
      (hh : x + -deadline + -globalLen + -localLen ≤ 0) :
      x - globalLen - localLen ≤ deadline := by linarith
  exact rearrange (D.rowCoordinate (rowCopy p e t).2) (D.deadline z)
    (D.globalLength (globalCopy p e t)) (D.localLength (localCopy p e t).2) h

theorem main_completion_le_selected_deadline (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v) :
    tupleFinish p e t ≤
      InventoryCoverage.anchorDeadline e (p.itemAtRole (subclass e) t .anchor) := by
  obtain ⟨z, hz, hfinish⟩ := main_completion_le_deadline p e hsize v t ht
  have hcopy : anchorCopy p e t = ⟨(anchorCopy p e t).1, .inl z⟩ := by
    conv_lhs => rw [← Sigma.eta (anchorCopy p e t)]
    rw [hz]
  rw [InventoryCoverage.anchorDeadline_selected_of_deadline p e t _ z hcopy]
  exact hfinish

private theorem job_row_of_subclass (a : Σ v : D.Vertex, D.RowAt v)
    (h : D.itemSubclass ⟨.x, a⟩ = .s) :
    ∃ short : Bool, ∃ j : D.JobCopy a.1, a.2 = .inr (short, j) := by
  rcases a with ⟨v, row | ⟨short, j⟩⟩
  · rcases row with plus | (minus | padding) <;>
      simp [InventoryData.itemSubclass, InventoryData.rowSubclass,
        InventoryData.treeSubclass] at h
  · exact ⟨short, j, rfl⟩

private theorem key_anchor_of_subclass (a : Σ v : D.Vertex, D.AnchorAt v)
    (h : D.itemSubclass ⟨.anchor, a⟩ = .y) :
    ∃ j : D.JobCopy a.1, a.2 = .inr j := by
  rcases a with ⟨v, z | j⟩
  · simp [InventoryData.itemSubclass] at h
  · exact ⟨j, rfl⟩

private theorem edge_global_of_subclass (u : D.GlobalCopy)
    (h : D.itemSubclass ⟨.«global», u⟩ = .w) :
    ∃ edge : D.Edge, ∃ permit : Bool, ∃ i : Fin (D.globalStock (.edge edge permit)),
      u = ⟨.edge edge permit, i⟩ := by
  rcases u with ⟨species, i⟩
  cases species with
  | up one => simp [InventoryData.itemSubclass] at h
  | um one => simp [InventoryData.itemSubclass] at h
  | edge edge permit => exact ⟨edge, permit, i, rfl⟩

private theorem edge_local_of_subclass (a : Σ v : D.Vertex, D.LocalAt v)
    (h : D.itemSubclass ⟨.«local», a⟩ = .dg) :
    ∃ j : D.JobCopy a.1, a.2 = .inr j := by
  rcases a with ⟨v, main | j⟩
  · simp [InventoryData.itemSubclass] at h
  · exact ⟨j, rfl⟩

structure EdgeTupleData (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) where
  short : Bool
  row : D.JobCopy (rowCopy p e t).1
  key : D.JobCopy (anchorCopy p e t).1
  localJob : D.JobCopy (localCopy p e t).1
  edge : D.Edge
  permit : Bool
  globalIndex : Fin (D.globalStock (.edge edge permit))
  row_eq : (rowCopy p e t).2 = .inr (short, row)
  anchor_eq : (anchorCopy p e t).2 = .inr key
  local_eq : (localCopy p e t).2 = .inr localJob
  global_eq : globalCopy p e t = ⟨.edge edge permit, globalIndex⟩

theorem edgeTupleData_nonempty (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hpat : p.tablePattern (subclass e) t = .edgeJob) :
    Nonempty (EdgeTupleData p e t) := by
  have hx : D.itemSubclass ⟨.x, rowCopy p e t⟩ = .s := by
    simpa only [hpat, patternSubclass] using roleCopy_subclass p e t .x
  have ha : D.itemSubclass ⟨.anchor, anchorCopy p e t⟩ = .y := by
    simpa only [hpat, patternSubclass] using roleCopy_subclass p e t .anchor
  have hu : D.itemSubclass ⟨.«global», globalCopy p e t⟩ = .w := by
    simpa only [hpat, patternSubclass] using roleCopy_subclass p e t .«global»
  have hl : D.itemSubclass ⟨.«local», localCopy p e t⟩ = .dg := by
    simpa only [hpat, patternSubclass] using roleCopy_subclass p e t .«local»
  obtain ⟨short, row, hrow⟩ := job_row_of_subclass _ hx
  obtain ⟨key, hkey⟩ := key_anchor_of_subclass _ ha
  obtain ⟨edge, permit, i, hglobal⟩ := edge_global_of_subclass _ hu
  obtain ⟨localJob, hlocal⟩ := edge_local_of_subclass _ hl
  exact ⟨⟨short, row, key, localJob, edge, permit, i, hrow, hkey, hlocal, hglobal⟩⟩

namespace EdgeTupleData

variable {p : Packing I b} {e : D.Item ≃ I.Item} {t : p.TableBin (subclass e)}

def expression (w : EdgeTupleData p e t) : ℚ :=
  Geometry.keyExpression D.graph.edges.length D.R D.geometryBound D.L
    (D.jobPosition w.row) (D.jobPosition w.key) w.edge (!w.permit) w.short

theorem expression_eq_coordinates (w : EdgeTupleData p e t) :
    w.expression =
      D.rowCoordinate (rowCopy p e t).2 + D.anchorCoordinate (anchorCopy p e t).2 +
        D.globalCoordinate (globalCopy p e t) + D.localCoordinate (localCopy p e t).2 := by
  rw [w.row_eq, w.anchor_eq, w.global_eq, w.local_eq]
  unfold expression
  rw [Geometry.keyExpression_eq_coordinates]
  simp only [InventoryData.rowCoordinate, InventoryData.rowBaseline, InventoryData.rowShort,
    InventoryData.anchorCoordinate, InventoryData.globalCoordinate,
    InventoryData.localCoordinate, InventoryData.localLength, neg_zero, add_zero]
  cases w.permit <;> cases w.short <;> simp

theorem feasible (w : EdgeTupleData p e t)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    w.expression ≤ 0 := by
  rw [w.expression_eq_coordinates]
  exact good_coordinate_nonpos p e hsize v t ht

theorem row_order (w : EdgeTupleData p e t) (h : w.expression ≤ 0) :
    Geometry.posLE (D.jobPosition w.row) (D.jobPosition w.key) :=
  Geometry.row_order_of_key_feasible h

theorem edge_order (w : EdgeTupleData p e t) (h : w.expression ≤ 0) :
    w.edge ≤ (D.jobPosition w.key).1 :=
  Geometry.edge_order_of_key_feasible h

theorem exact_long_resource (w : EdgeTupleData p e t) (h : w.expression ≤ 0)
    (hpos : D.jobPosition w.row = D.jobPosition w.key) (hlong : w.short = false) :
    w.edge < (D.jobPosition w.key).1 ∨
      (w.edge = (D.jobPosition w.key).1 ∧ w.permit = true) := by
  have h' : Geometry.keyExpression D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition w.key) (D.jobPosition w.key) w.edge (!w.permit) false ≤ 0 := by
    simpa only [expression, hpos, hlong] using h
  have hresource := Geometry.exact_long_key_resource (D.jobPosition w.key) w.edge
    (!w.permit) h'
  cases hp : w.permit <;> simpa [hp] using hresource

end EdgeTupleData

theorem edge_tuple_feasible (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.edgeTuplesAt p (subclass e) (label e) v) :
    ∃ w : EdgeTupleData p e t, w.expression ≤ 0 ∧
      Geometry.posLE (D.jobPosition w.row) (D.jobPosition w.key) ∧
        w.edge ≤ (D.jobPosition w.key).1 := by
  have hpat := ((Coverage.mem_edgeTuplesAt p (subclass e) (label e) v t).mp ht).2.2
  obtain ⟨w⟩ := edgeTupleData_nonempty p e t hpat
  have hf := w.feasible hsize v
    (Coverage.edgeTuplesAt_subset_good p (subclass e) (label e) v ht)
  exact ⟨w, hf, w.row_order hf, w.edge_order hf⟩

theorem edge_selected_baseline_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.edgeTuplesAt p (subclass e) (label e) v) :
    InventoryCoverage.rowBaseline e (p.itemAtRole (subclass e) t .x) ≤
      InventoryCoverage.keyBaseline e (p.itemAtRole (subclass e) t .anchor) := by
  obtain ⟨w, _, hrow, _⟩ := edge_tuple_feasible p e hsize v t ht
  have hcopy : anchorCopy p e t = ⟨(anchorCopy p e t).1, .inr w.key⟩ := by
    conv_lhs => rw [← Sigma.eta (anchorCopy p e t)]
    rw [w.anchor_eq]
  rw [InventoryCoverage.rowBaseline_selected,
    InventoryCoverage.keyBaseline_selected_of_key p e t _ w.key hcopy, w.row_eq]
  exact Geometry.baseline_le_iff.mpr hrow

end PackingCounts
end BinPackingGap

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Inventory/EdgeLongConsumption.lean =====
namespace OAI

noncomputable section

namespace BinPackingGap
namespace InventoryData

section

variable (D : InventoryData) {b : ℕ}

def earlierKeyItems (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Finset D.packingInstance.Item := (D.earlierKeys h hle).image D.itemEquiv

def earlierWItems (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Finset D.packingInstance.Item := (D.earlierW h hle).image D.itemEquiv

theorem earlierKeyItems_card (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierKeyItems h hle).card = 2 * D.d * D.R * h := by
  rw [earlierKeyItems, Finset.card_image_of_injective _ D.itemEquiv.injective,
    D.earlierKeys_card]

theorem earlierWItems_card (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierWItems h hle).card = 2 * D.d * D.R * h := by
  rw [earlierWItems, Finset.card_image_of_injective _ D.itemEquiv.injective,
    D.earlierW_card]

theorem mem_earlierKeyItems (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (i : D.packingInstance.Item) :
    i ∈ D.earlierKeyItems h hle ↔
      ∃ j : Σ v : D.Vertex, D.JobCopy v,
        D.itemEquiv (D.keyItem j) = i ∧ (D.jobPosition j.2).1.val < h := by
  classical
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j, rfl, hj⟩ := (D.mem_earlierKeys h hle a).mp ha
    exact ⟨j, rfl, hj⟩
  · rintro ⟨j, rfl, hj⟩
    exact Finset.mem_image.mpr ⟨D.keyItem j,
      (D.mem_earlierKeys h hle _).mpr ⟨j, rfl, hj⟩, rfl⟩

theorem mem_earlierWItems (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (i : D.packingInstance.Item) :
    i ∈ D.earlierWItems h hle ↔
      ∃ w : (D.Edge × Bool) × Fin (D.d * D.R),
        D.itemEquiv (D.edgeResourceItem w) = i ∧ w.1.1.val < h := by
  classical
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨w, rfl, hw⟩ := (D.mem_earlierW h hle a).mp ha
    exact ⟨w, rfl, hw⟩
  · rintro ⟨w, rfl, hw⟩
    exact Finset.mem_image.mpr ⟨D.edgeResourceItem w,
      (D.mem_earlierW h hle _).mpr ⟨w, rfl, hw⟩, rfl⟩

@[simp] theorem keyItem_mem_earlierKeyItems (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (j : Σ v : D.Vertex, D.JobCopy v) :
    D.itemEquiv (D.keyItem j) ∈ D.earlierKeyItems h hle ↔
      (D.jobPosition j.2).1.val < h := by
  rw [D.mem_earlierKeyItems]
  constructor
  · rintro ⟨z, hz, hlt⟩
    have heq := D.keyItem_injective (D.itemEquiv.injective hz)
    subst z
    exact hlt
  · intro hlt
    exact ⟨j, rfl, hlt⟩

@[simp] theorem edgeResourceItem_mem_earlierWItems
    (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (w : (D.Edge × Bool) × Fin (D.d * D.R)) :
    D.itemEquiv (D.edgeResourceItem w) ∈ D.earlierWItems h hle ↔ w.1.1.val < h := by
  rw [D.mem_earlierWItems]
  constructor
  · rintro ⟨z, hz, hlt⟩
    have heq := D.edgeResourceItem_injective (D.itemEquiv.injective hz)
    simpa only [heq] using hlt
  · intro hlt
    exact ⟨w, rfl, hlt⟩

def earlierGoodKeyTuples (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) : Finset (p.TableBin D.encodedSubclass) := by
  classical
  exact Finset.univ.filter fun t => p.IsGoodTableBin D.encodedSubclass D.encodedLabel t ∧
    p.itemAtRole D.encodedSubclass t .anchor ∈ D.earlierKeyItems h hle

@[simp] theorem mem_earlierGoodKeyTuples (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) (t : p.TableBin D.encodedSubclass) :
    t ∈ D.earlierGoodKeyTuples p h hle ↔
      p.IsGoodTableBin D.encodedSubclass D.encodedLabel t ∧
        p.itemAtRole D.encodedSubclass t .anchor ∈ D.earlierKeyItems h hle := by
  classical
  simp [earlierGoodKeyTuples]

theorem earlierGoodKeyTuples_anchor_subset (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .anchor ⊆
      D.earlierKeyItems h hle := by
  intro i hi
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
  exact ((D.mem_earlierGoodKeyTuples p h hle t).mp ht).2

theorem earlierGoodKeyTuples_edge (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.earlierGoodKeyTuples p h hle) :
    ∃ v, t ∈ Coverage.edgeTuplesAt p D.encodedSubclass D.encodedLabel v := by
  obtain ⟨hgood, hkey⟩ := (D.mem_earlierGoodKeyTuples p h hle t).mp ht
  obtain ⟨j, hj, _⟩ := (D.mem_earlierKeyItems h hle _).mp hkey
  have hlabel : D.encodedLabel (p.itemAtRole D.encodedSubclass t .anchor) = some j.1 := by
    rw [← hj]
    simp [encodedLabel]
  have hsub : D.encodedSubclass (p.itemAtRole D.encodedSubclass t .anchor) = .y := by
    rw [← hj]
    simp [encodedSubclass]
  have hpat : p.tablePattern D.encodedSubclass t = .edgeJob := by
    have hx := (p.itemAtRole_subclass D.encodedSubclass t .anchor).symm.trans hsub
    cases hp : p.tablePattern D.encodedSubclass t <;> simp_all [patternSubclass]
  exact ⟨j.1, (Coverage.mem_edgeTuplesAt p D.encodedSubclass D.encodedLabel j.1 t).mpr
    ⟨hgood, hlabel, hpat⟩⟩

theorem earlierGoodKeyTuples_global_subset (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .«global» ⊆
      D.earlierWItems h hle := by
  classical
  intro i hi
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨v, htv⟩ := D.earlierGoodKeyTuples_edge p h hle t ht
  obtain ⟨w, _, _, he⟩ := PackingCounts.edge_tuple_feasible p D.itemEquiv
    D.packingInstance_size_eq v t htv
  obtain ⟨j, hj, hjlt⟩ := (D.mem_earlierKeyItems h hle _).mp
    (((D.mem_earlierGoodKeyTuples p h hle t).mp ht).2)
  have hkey : D.itemEquiv (D.keyItem ⟨(PackingCounts.anchorCopy p D.itemEquiv t).1, w.key⟩) =
      p.itemAtRole D.encodedSubclass t .anchor := by
    have ha := congrArg
      (fun a : D.AnchorAt (PackingCounts.anchorCopy p D.itemEquiv t).1 =>
        D.itemEquiv (⟨.anchor,
          ⟨(PackingCounts.anchorCopy p D.itemEquiv t).1, a⟩⟩ : D.Item)) w.anchor_eq
    have heta := congrArg
      (fun a : Σ v : D.Vertex, D.AnchorAt v => D.itemEquiv (⟨.anchor, a⟩ : D.Item))
      (Sigma.eta (PackingCounts.anchorCopy p D.itemEquiv t))
    exact ha.symm.trans (heta.trans (PackingCounts.roleCopy_item p D.itemEquiv t .anchor))
  have hjEq := D.keyItem_injective (D.itemEquiv.injective (hkey.trans hj.symm))
  have hpos := congrArg (fun z : Σ v : D.Vertex, D.JobCopy v =>
    (D.jobPosition z.2).1.val) hjEq
  have hwe : w.edge.val < h := lt_of_le_of_lt he (by simpa only [hpos] using hjlt)
  apply (D.mem_earlierWItems h hle _).mpr
  refine ⟨((w.edge, w.permit), w.globalIndex), ?_, hwe⟩
  exact (congrArg (fun g : D.GlobalCopy => D.itemEquiv (⟨.«global», g⟩ : D.Item))
    w.global_eq.symm).trans (PackingCounts.roleCopy_item p D.itemEquiv t .«global»)

def remainingEarlierW (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) : Finset D.packingInstance.Item :=
  D.earlierWItems h hle \
    Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .«global»

theorem remainingEarlierW_card_eq_missingKeys (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.remainingEarlierW p h hle).card =
      (D.earlierKeyItems h hle \
        Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .anchor).card := by
  rw [remainingEarlierW, Finset.card_sdiff_of_subset (D.earlierGoodKeyTuples_global_subset p h hle),
    Finset.card_sdiff_of_subset (D.earlierGoodKeyTuples_anchor_subset p h hle),
    Coverage.roleItems_card, Coverage.roleItems_card, D.earlierWItems_card,
    D.earlierKeyItems_card]

theorem missingEarlierKeys_subset_bad (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    D.earlierKeyItems h hle \
      Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .anchor ⊆
        (Finset.univ : Finset D.Vertex).biUnion
          (Coverage.badAnchorsAt p D.encodedSubclass D.encodedLabel) := by
  classical
  intro i hi
  obtain ⟨hik, hin⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨j, hj, _⟩ := (D.mem_earlierKeyItems h hle i).mp hik
  apply Finset.mem_biUnion.mpr
  refine ⟨j.1, Finset.mem_univ _, ?_⟩
  apply (Coverage.mem_badAnchorsAt p D.encodedSubclass D.encodedLabel j.1 i).mpr
  constructor
  · apply (Coverage.mem_anchorItemsAt D.encodedSubclass D.encodedLabel j.1 i).mpr
    rw [← hj]
    simp [encodedSubclass, encodedLabel, Subclass.role]
  · intro hgood
    obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hgood
    apply hin
    refine Finset.mem_image.mpr ⟨t, ?_, hti⟩
    apply (D.mem_earlierGoodKeyTuples p h hle t).mpr
    refine ⟨((Coverage.mem_goodTuplesAt p D.encodedSubclass D.encodedLabel j.1 t).mp ht).1, ?_⟩
    simpa only [hti] using hik

theorem remainingEarlierW_card_le {c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.remainingEarlierW p h hle).card ≤ 3 * D.graph.n * lossAllowance c := by
  rw [D.remainingEarlierW_card_eq_missingKeys]
  exact (Finset.card_le_card (D.missingEarlierKeys_subset_bad p h hle)).trans
    (D.badAnchors_global_card_le hk p hb)

end

open scoped BigOperators
open PackingCounts

variable (D : InventoryData) {b : ℕ}

def edgeLongTuplesAt (p : Packing D.packingInstance b) (edge : D.Edge)
    (q : Fin 2 × Fin D.R) : Finset (p.TableBin D.encodedSubclass) :=
  Coverage.currentLongEdgeAt p D.encodedSubclass D.encodedLabel
    (D.graph.endpoint edge q.1)
    (InventoryCoverage.rowBaseline D.itemEquiv)
    (InventoryCoverage.keyBaseline D.itemEquiv)
    (InventoryCoverage.rowShort D.itemEquiv)
    (Geometry.baseline D.graph.edges.length D.R (edge, q.2))

@[simp] theorem mem_edgeLongTuplesAt (p : Packing D.packingInstance b) (edge : D.Edge)
    (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass) :
    t ∈ D.edgeLongTuplesAt p edge q ↔
      t ∈ Coverage.edgeTuplesAt p D.encodedSubclass D.encodedLabel
        (D.graph.endpoint edge q.1) ∧
      InventoryCoverage.keyBaseline D.itemEquiv
        (p.itemAtRole D.encodedSubclass t .anchor) =
          Geometry.baseline D.graph.edges.length D.R (edge, q.2) ∧
      InventoryCoverage.rowBaseline D.itemEquiv
        (p.itemAtRole D.encodedSubclass t .x) =
          Geometry.baseline D.graph.edges.length D.R (edge, q.2) ∧
      InventoryCoverage.rowShort D.itemEquiv
        (p.itemAtRole D.encodedSubclass t .x) ≠ true := by
  classical
  simp [edgeLongTuplesAt, Coverage.currentLongEdgeAt, Coverage.currentEdgeTuplesAt,
    and_assoc]

theorem edgeLongTuplesAt_disjoint (p : Packing D.packingInstance b) (edge : D.Edge)
    {q r : Fin 2 × Fin D.R} (hne : q ≠ r) :
    Disjoint (D.edgeLongTuplesAt p edge q) (D.edgeLongTuplesAt p edge r) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t hq hr
  obtain ⟨hGq, hkeyq, _, _⟩ := (D.mem_edgeLongTuplesAt p edge q t).mp hq
  obtain ⟨hGr, hkeyr, _, _⟩ := (D.mem_edgeLongTuplesAt p edge r t).mp hr
  have hlq := ((Coverage.mem_edgeTuplesAt p D.encodedSubclass D.encodedLabel
    (D.graph.endpoint edge q.1) t).mp hGq).2.1
  have hlr := ((Coverage.mem_edgeTuplesAt p D.encodedSubclass D.encodedLabel
    (D.graph.endpoint edge r.1) t).mp hGr).2.1
  have hside : q.1 = r.1 := D.graph.endpoint_injective edge
    (Option.some.inj (hlq.symm.trans hlr))
  have hrep : q.2 = r.2 := congrArg (fun z : D.Edge × Fin D.R => z.2)
    ((Geometry.baseline_eq_iff (r := (edge, q.2)) (s := (edge, r.2))).mp
      (hkeyq.symm.trans hkeyr))
  exact hne (Prod.ext hside hrep)

def edgeLongTuples (p : Packing D.packingInstance b) (edge : D.Edge)
    (J : Finset (Fin D.R)) : Finset (p.TableBin D.encodedSubclass) := by
  classical
  exact ((Finset.univ : Finset (Fin 2)).product J).biUnion (D.edgeLongTuplesAt p edge)

theorem edgeLongTuples_card (p : Packing D.packingInstance b) (edge : D.Edge)
    (J : Finset (Fin D.R)) :
    (D.edgeLongTuples p edge J).card =
      ∑ side : Fin 2, ∑ rep ∈ J, (D.edgeLongTuplesAt p edge (side, rep)).card := by
  classical
  have hdis : ∀ q ∈ (Finset.univ : Finset (Fin 2)).product J,
      ∀ r ∈ (Finset.univ : Finset (Fin 2)).product J,
        q ≠ r → Disjoint (D.edgeLongTuplesAt p edge q) (D.edgeLongTuplesAt p edge r) := by
    intro q _ r _ hne
    exact D.edgeLongTuplesAt_disjoint p edge hne
  rw [edgeLongTuples, Finset.card_biUnion hdis]
  exact Finset.sum_product (Finset.univ : Finset (Fin 2)) J
    (fun q : Fin 2 × Fin D.R => (D.edgeLongTuplesAt p edge q).card)

theorem edgeLongTuplesAt_witness (p : Packing D.packingInstance b) (edge : D.Edge)
    (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.edgeLongTuplesAt p edge q) :
    ∃ w : EdgeTupleData p D.itemEquiv t, w.expression ≤ 0 ∧
      D.jobPosition w.key = (edge, q.2) ∧
      D.jobPosition w.row = (edge, q.2) ∧ w.short = false := by
  obtain ⟨hG, hkey, hrow, hshort⟩ := (D.mem_edgeLongTuplesAt p edge q t).mp ht
  obtain ⟨w, hf, _, _⟩ := edge_tuple_feasible p D.itemEquiv
    D.packingInstance_size_eq (D.graph.endpoint edge q.1) t hG
  have hcopy : anchorCopy p D.itemEquiv t =
      ⟨(anchorCopy p D.itemEquiv t).1, .inr w.key⟩ := by
    conv_lhs => rw [← Sigma.eta (anchorCopy p D.itemEquiv t)]
    rw [w.anchor_eq]
  erw [InventoryCoverage.keyBaseline_selected_of_key p D.itemEquiv t _ w.key hcopy] at hkey
  erw [InventoryCoverage.rowBaseline_selected p D.itemEquiv t, w.row_eq] at hrow
  change Geometry.baseline D.graph.edges.length D.R (D.jobPosition w.row) = _ at hrow
  erw [InventoryCoverage.rowShort_selected p D.itemEquiv t, w.row_eq] at hshort
  change w.short ≠ true at hshort
  refine ⟨w, hf, Geometry.baseline_eq_iff.mp hkey, Geometry.baseline_eq_iff.mp hrow, ?_⟩
  exact Bool.eq_false_of_not_eq_true hshort

private theorem witness_key_item (p : Packing D.packingInstance b)
    (t : p.TableBin D.encodedSubclass) (w : EdgeTupleData p D.itemEquiv t) :
    D.itemEquiv (D.keyItem ⟨(anchorCopy p D.itemEquiv t).1, w.key⟩) =
      p.itemAtRole D.encodedSubclass t .anchor := by
  erw [← roleCopy_item p D.itemEquiv t .anchor]
  apply congrArg D.itemEquiv
  change (⟨.anchor, ⟨_, .inr w.key⟩⟩ : D.Item) =
    ⟨.anchor, anchorCopy p D.itemEquiv t⟩
  conv_rhs => rw [← Sigma.eta (anchorCopy p D.itemEquiv t), w.anchor_eq]

private theorem witness_global_item (p : Packing D.packingInstance b)
    (t : p.TableBin D.encodedSubclass) (w : EdgeTupleData p D.itemEquiv t) :
    D.itemEquiv (D.edgeResourceItem ((w.edge, w.permit), w.globalIndex)) =
      p.itemAtRole D.encodedSubclass t .«global» := by
  erw [← roleCopy_item p D.itemEquiv t .«global»]
  change D.itemEquiv ⟨.«global», ⟨.edge w.edge w.permit, w.globalIndex⟩⟩ =
    D.itemEquiv ⟨.«global», globalCopy p D.itemEquiv t⟩
  rw [w.global_eq]

theorem edgeLongTuplesAt_not_earlierGoodKeyTuples (p : Packing D.packingInstance b)
    (edge : D.Edge) (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.edgeLongTuplesAt p edge q) :
    t ∉ D.earlierGoodKeyTuples p edge.val edge.isLt.le := by
  obtain ⟨w, _, hkey, _, _⟩ := D.edgeLongTuplesAt_witness p edge q t ht
  intro hearlier
  have hmem := ((D.mem_earlierGoodKeyTuples p edge.val edge.isLt.le t).mp hearlier).2
  rw [← D.witness_key_item p t w, D.keyItem_mem_earlierKeyItems] at hmem
  simp only [hkey, Nat.lt_irrefl] at hmem

theorem edgeLongTuplesAt_global_not_used_earlier (p : Packing D.packingInstance b)
    (edge : D.Edge) (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.edgeLongTuplesAt p edge q) :
    p.itemAtRole D.encodedSubclass t .«global» ∉
      Coverage.roleItems p D.encodedSubclass
        (D.earlierGoodKeyTuples p edge.val edge.isLt.le) .«global» := by
  intro hi
  obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hi
  have hut : u = t := p.itemAtRole_injective D.encodedSubclass .«global» heq
  subst u
  exact D.edgeLongTuplesAt_not_earlierGoodKeyTuples p edge q t ht hu

theorem edgeLongTuplesAt_global_mem (p : Packing D.packingInstance b)
    (edge : D.Edge) (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.edgeLongTuplesAt p edge q) :
    p.itemAtRole D.encodedSubclass t .«global» ∈
      globalResources D.itemEquiv (.edge edge true) ∪
        D.remainingEarlierW p edge.val edge.isLt.le := by
  classical
  obtain ⟨w, hf, hkey, hrow, hshort⟩ := D.edgeLongTuplesAt_witness p edge q t ht
  have hresource := w.exact_long_resource hf (hrow.trans hkey.symm) hshort
  rcases hresource with hearlier | ⟨heq, hpermit⟩
  · apply Finset.mem_union_right
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, D.edgeLongTuplesAt_global_not_used_earlier p edge q t ht⟩
    apply (D.mem_earlierWItems edge.val edge.isLt.le _).mpr
    refine ⟨((w.edge, w.permit), w.globalIndex), D.witness_global_item p t w, ?_⟩
    have hlt : w.edge < edge := by simpa only [hkey] using hearlier
    exact hlt
  · apply Finset.mem_union_left
    apply (selected_global_resource_iff p D.itemEquiv t (.edge edge true)).mpr
    rw [w.global_eq]
    have hedge : w.edge = edge := by simpa only [hkey] using heq
    simp only [hedge, hpermit]

theorem edgeLongTuples_global_subset (p : Packing D.packingInstance b)
    (edge : D.Edge) (J : Finset (Fin D.R)) :
    Coverage.roleItems p D.encodedSubclass (D.edgeLongTuples p edge J) .«global» ⊆
      globalResources D.itemEquiv (.edge edge true) ∪
        D.remainingEarlierW p edge.val edge.isLt.le := by
  classical
  intro i hi
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp ht
  exact D.edgeLongTuplesAt_global_mem p edge q t hq

theorem edge_long_matches_capacity {c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (edge : D.Edge) (J : Finset (Fin D.R)) :
    (∑ side : Fin 2, ∑ rep ∈ J, (D.edgeLongTuplesAt p edge (side, rep)).card) ≤
      D.d * D.R + 3 * D.graph.n * lossAllowance c := by
  classical
  rw [← D.edgeLongTuples_card]
  have hbound := Finset.card_le_card (D.edgeLongTuples_global_subset p edge J)
  rw [Coverage.roleItems_card] at hbound
  refine hbound.trans ((Finset.card_union_le _ _).trans ?_)
  rw [globalResources_card]
  change D.d * D.R + (D.remainingEarlierW p edge.val edge.isLt.le).card ≤ _
  exact Nat.add_le_add_left (D.remainingEarlierW_card_le hk p hb edge.val edge.isLt.le) _

theorem edge_long_matches_capacity_raw {c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (edge : D.Edge) (J : Finset (Fin D.R)) :
    (∑ side : Fin 2, ∑ rep ∈ J,
      (Coverage.currentLongEdgeAt p D.encodedSubclass D.encodedLabel
        (D.graph.endpoint edge side)
        (InventoryCoverage.rowBaseline D.itemEquiv)
        (InventoryCoverage.keyBaseline D.itemEquiv)
        (InventoryCoverage.rowShort D.itemEquiv)
        (Geometry.baseline D.graph.edges.length D.R (edge, rep))).card) ≤
      D.d * D.R + 3 * D.graph.n * lossAllowance c :=
  D.edge_long_matches_capacity hk p hb edge J

end InventoryData
end BinPackingGap

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Trees/TreeAttachment.lean =====
namespace OAI

namespace BinPackingGap
namespace UniformTree

def graftLeaves (T : UniformTree) (G : T.leaves → UniformTree) : Finset (List ℕ) :=
  Finset.univ.biUnion (fun l : T.leaves =>
    (G l).leaves.image (fun w => l.val ++ w))

theorem mem_graftLeaves (T : UniformTree) (G : T.leaves → UniformTree)
    {x : List ℕ} :
    x ∈ graftLeaves T G ↔ ∃ l : T.leaves, ∃ w ∈ (G l).leaves, x = l.val ++ w := by
  constructor
  · intro hx
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨w, hw, hx⟩ := Finset.mem_image.mp hl
    exact ⟨l, w, hw, hx.symm⟩
  · rintro ⟨l, w, hw, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨l, Finset.mem_univ l, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩

def graft (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) : UniformTree where
  height := T.height + N
  leaves := graftLeaves T G
  leaves_nonempty := by
    obtain ⟨l, hl⟩ := T.leaves_nonempty
    obtain ⟨w, hw⟩ := (G ⟨l, hl⟩).leaves_nonempty
    exact ⟨l ++ w, (mem_graftLeaves T G).mpr ⟨⟨l, hl⟩, w, hw, rfl⟩⟩
  length_leaf := by
    intro x hx
    obtain ⟨l, w, hw, rfl⟩ := (mem_graftLeaves T G).mp hx
    rw [List.length_append, T.length_leaf l.val l.property,
      (G l).length_leaf w hw, hG l]
  positive_labels := by
    intro x hx a ha
    obtain ⟨l, w, hw, rfl⟩ := (mem_graftLeaves T G).mp hx
    rcases List.mem_append.mp ha with ha | ha
    · exact T.positive_labels l.val l.property a ha
    · exact (G l).positive_labels w hw a ha

@[simp] theorem graft_height (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) :
    (graft T G N hG).height = T.height + N := rfl

theorem mem_graft_leaves (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) {x : List ℕ} :
    x ∈ (graft T G N hG).leaves ↔
      ∃ l : T.leaves, ∃ w ∈ (G l).leaves, x = l.val ++ w :=
  mem_graftLeaves T G

theorem append_eq_append_iff (T : UniformTree) (l₁ l₂ : T.leaves)
    (u v : List ℕ) :
    l₁.val ++ u = l₂.val ++ v ↔ l₁ = l₂ ∧ u = v := by
  constructor
  · intro h
    have hlen : l₁.val.length = l₂.val.length :=
      (T.length_leaf l₁.val l₁.property).trans (T.length_leaf l₂.val l₂.property).symm
    exact ⟨Subtype.ext (List.append_inj_left h hlen), List.append_inj_right h hlen⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem old_prefix_iff (T : UniformTree) {u : List ℕ} (hu : u ∈ T.vertices)
    (l : T.leaves) (w : List ℕ) :
    u.IsPrefix (l.val ++ w) ↔ u.IsPrefix l.val := by
  apply List.isPrefix_append_of_length
  rw [T.length_leaf l.val l.property]
  exact T.length_le_height hu

theorem leaf_prefix_append_iff (T : UniformTree) (l₁ l₂ : T.leaves)
    (w : List ℕ) : l₁.val.IsPrefix (l₂.val ++ w) ↔ l₁ = l₂ := by
  rw [T.old_prefix_iff (T.leaf_mem_vertices l₁.property) l₂ w]
  constructor
  · intro h
    exact Subtype.ext (h.eq_of_length
      ((T.length_leaf l₁.val l₁.property).trans
        (T.length_leaf l₂.val l₂.property).symm))
  · rintro rfl
    exact List.prefix_refl l₁.val

theorem vertices_subset_graft (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) :
    T.vertices ⊆ (graft T G N hG).vertices := by
  intro u hu
  obtain ⟨l, hl, hul⟩ := T.mem_vertices_iff.mp hu
  let oldLeaf : T.leaves := ⟨l, hl⟩
  obtain ⟨w, hw⟩ := (G oldLeaf).leaves_nonempty
  apply (graft T G N hG).mem_vertices_iff.mpr
  refine ⟨l ++ w, ?_, hul.trans (List.prefix_append l w)⟩
  exact (mem_graft_leaves T G N hG).mpr ⟨oldLeaf, w, hw, rfl⟩

theorem append_mem_graft_vertices (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) (l : T.leaves)
    {v : List ℕ} (hv : v ∈ (G l).vertices) :
    l.val ++ v ∈ (graft T G N hG).vertices := by
  obtain ⟨w, hw, hvw⟩ := (G l).mem_vertices_iff.mp hv
  exact (graft T G N hG).mem_vertices_iff.mpr
    ⟨l.val ++ w, (mem_graft_leaves T G N hG).mpr ⟨l, w, hw, rfl⟩,
      (List.prefix_append_right_inj l.val).mpr hvw⟩

theorem mem_graft_vertices_iff (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) {x : List ℕ} :
    x ∈ (graft T G N hG).vertices ↔
      x ∈ T.vertices ∨
        ∃ l : T.leaves, ∃ v ∈ (G l).vertices, v ≠ [] ∧ x = l.val ++ v := by
  constructor
  · intro hx
    obtain ⟨word, hword, hp⟩ := (graft T G N hG).mem_vertices_iff.mp hx
    obtain ⟨l, w, hw, rfl⟩ := (mem_graft_leaves T G N hG).mp hword
    have hx' : x ∈ prefixes (l.val ++ w) := mem_prefixes_iff.mpr hp
    rw [prefixes_append_eq] at hx'
    rcases Finset.mem_union.mp hx' with h | h
    · exact Or.inl (T.mem_vertices_iff.mpr
        ⟨l.val, l.property, mem_prefixes_iff.mp h⟩)
    · obtain ⟨v, hv, hpv, heq⟩ := mem_prefixesAfter_iff.mp h
      exact Or.inr ⟨l, v, (G l).mem_vertices_iff.mpr ⟨w, hw, hpv⟩, hv, heq.symm⟩
  · rintro (hx | ⟨l, v, hv, _, rfl⟩)
    · exact vertices_subset_graft T G N hG hx
    · exact append_mem_graft_vertices T G N hG l hv

theorem append_not_mem_old_vertices (T : UniformTree) (l : T.leaves)
    {v : List ℕ} (hv : v ≠ []) : l.val ++ v ∉ T.vertices := by
  intro h
  have hlen := T.length_le_height h
  rw [List.length_append, T.length_leaf l.val l.property] at hlen
  have hz : v.length = 0 := by omega
  exact hv (List.length_eq_zero_iff.mp hz)

theorem filter_old_prefix_append (T : UniformTree) (marks : Finset (List ℕ))
    (hmarks : marks ⊆ T.vertices) (l : T.leaves) (w : List ℕ) :
    marks.filter (fun u => u.IsPrefix (l.val ++ w)) =
      marks.filter (fun u => u.IsPrefix l.val) := by
  apply Finset.filter_congr
  intro u hu
  exact T.old_prefix_iff (hmarks hu) l w

theorem append_not_prefix_of_ne_leaves (T : UniformTree) (l₁ l₂ : T.leaves)
    (hne : l₁ ≠ l₂) (u v : List ℕ) :
    ¬ (l₁.val ++ u).IsPrefix (l₂.val ++ v) := by
  intro h
  apply hne
  exact (T.leaf_prefix_append_iff l₁ l₂ v).mp
    ((List.prefix_append l₁.val u).trans h)

theorem append_prefix_append_iff (T : UniformTree) (l₁ l₂ : T.leaves)
    (u v : List ℕ) :
    (l₁.val ++ u).IsPrefix (l₂.val ++ v) ↔ l₁ = l₂ ∧ u.IsPrefix v := by
  constructor
  · intro h
    have heq : l₁ = l₂ := (T.leaf_prefix_append_iff l₁ l₂ v).mp
      ((List.prefix_append l₁.val u).trans h)
    subst l₂
    exact ⟨rfl, (List.prefix_append_right_inj l₁.val).mp h⟩
  · rintro ⟨rfl, h⟩
    exact (List.prefix_append_right_inj l₁.val).mpr h

theorem filter_other_lift_prefix (T : UniformTree) (l₁ l₂ : T.leaves)
    (hne : l₁ ≠ l₂) (marks : Finset (List ℕ)) (w : List ℕ) :
    (marks.image (fun u => l₁.val ++ u)).filter
      (fun u => u.IsPrefix (l₂.val ++ w)) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hx
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hm
  exact T.append_not_prefix_of_ne_leaves l₁ l₂ hne u w hp

theorem old_disjoint_lift (T : UniformTree) (old : Finset (List ℕ))
    (hold : old ⊆ T.vertices) (l : T.leaves) (marks : Finset (List ℕ))
    (hroot : [] ∉ marks) : Disjoint old (marks.image (fun u => l.val ++ u)) := by
  apply Finset.disjoint_left.mpr
  intro x hxold hxlift
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hxlift
  have hne : u ≠ [] := by
    intro heq
    exact hroot (heq ▸ hu)
  exact T.append_not_mem_old_vertices l hne (hold hxold)

end UniformTree
end BinPackingGap

end OAI


