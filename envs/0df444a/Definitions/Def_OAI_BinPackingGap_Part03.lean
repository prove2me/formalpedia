-- Prove2me | Definitions.Def_OAI_BinPackingGap_Part03
-- name    : OAI_BinPackingGap_Part03
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T18:14:47.810989+00:00
-- url     : https://prove2.me/theorems/5dd142f5-3f36-488d-a34b-9508dfc39fae
-- title:
--   Structural additive gap for bin packing, part 3 of 10 (port of OpenAI's formalization)
-- statement:
--   Part 3 of 10 of a port of OpenAI's Lean formalization of the structural additive gap from the manuscript *Additive hardness and unbounded configuration gaps in bin packing* (OpenAI, September 24, 2026). For every $c$, it constructs an instance with $5B$ items of sizes in $(1/6,1)$ whose individual and type configuration LPs both equal $B$, while the optimum exceeds $B+c$. This part contains the modules `Trees/IntegerTreeGeometry`, `Inventory/InventoryScores`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/BinPacking`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `BinPackingGap`, which matches upstream `Model.lean` up to two private lemmas and a section wrapper.
--
--   The development is split into 10 parts only so that each compiles within the platform's time limit. The final part proves `OAI.BinPackingGap.structural_additive_gap`, the first clause of `OAI.BinPackingGap.main_results`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/BinPacking: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Trees/IntegerTreeGeometry.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Inventory/InventoryScores.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf

/-
Structural additive gap for bin packing (port of OpenAI's formalization), part 3 of 10.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/BinPacking/: Trees/IntegerTreeGeometry.lean, Inventory/InventoryScores.lean
These files formalize part of the manuscript "Additive hardness and unbounded configuration gaps in
bin packing" (OpenAI, September 24, 2026). Copyright OpenAI. Licensed under the Apache License,
Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same
license, on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Model.lean) come from the platform definition `BinPackingGap`, to which upstream Model.lean
is identical up to two private lemmas and a section wrapper.
-/
import Mathlib
import Definitions.Def_OAI_BinPackingGap_Part02

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/BinPacking/Trees/IntegerTreeGeometry.lean =====
namespace OAI

namespace BinPackingGap

structure UniformTree where
  height : ℕ
  leaves : Finset (List ℕ)
  leaves_nonempty : leaves.Nonempty
  length_leaf : ∀ l ∈ leaves, l.length = height
  positive_labels : ∀ l ∈ leaves, ∀ a ∈ l, 0 < a

namespace UniformTree

def prefixes (l : List ℕ) : Finset (List ℕ) :=
  (Finset.range (l.length + 1)).image (fun k => l.take k)

@[simp] theorem mem_prefixes_iff {w l : List ℕ} :
    w ∈ prefixes l ↔ w.IsPrefix l := by
  constructor
  · intro hw
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw
    exact List.take_prefix k l
  · intro h
    exact Finset.mem_image.mpr
      ⟨w.length, Finset.mem_range.mpr (Nat.lt_succ_of_le h.length_le),
        (List.prefix_iff_eq_take.mp h).symm⟩

def vertices (T : UniformTree) : Finset (List ℕ) :=
  T.leaves.biUnion prefixes

theorem mem_vertices_iff (T : UniformTree) {w : List ℕ} :
    w ∈ T.vertices ↔ ∃ l ∈ T.leaves, w.IsPrefix l := by
  simp only [vertices, Finset.mem_biUnion, mem_prefixes_iff]

theorem leaf_mem_vertices (T : UniformTree) {l : List ℕ} (hl : l ∈ T.leaves) :
    l ∈ T.vertices :=
  (T.mem_vertices_iff).mpr ⟨l, hl, List.prefix_refl l⟩

theorem nil_mem_vertices (T : UniformTree) : [] ∈ T.vertices := by
  obtain ⟨l, hl⟩ := T.leaves_nonempty
  exact (T.mem_vertices_iff).mpr ⟨l, hl, List.nil_prefix⟩

theorem vertices_nonempty (T : UniformTree) : T.vertices.Nonempty :=
  ⟨[], T.nil_mem_vertices⟩

theorem prefix_mem_vertices (T : UniformTree) {u v : List ℕ}
    (hv : v ∈ T.vertices) (h : u.IsPrefix v) : u ∈ T.vertices := by
  obtain ⟨l, hl, hvl⟩ := T.mem_vertices_iff.mp hv
  exact T.mem_vertices_iff.mpr ⟨l, hl, h.trans hvl⟩

theorem take_mem_vertices (T : UniformTree) {w : List ℕ}
    (hw : w ∈ T.vertices) (k : ℕ) : w.take k ∈ T.vertices :=
  T.prefix_mem_vertices hw (List.take_prefix k w)

theorem length_le_height (T : UniformTree) {w : List ℕ}
    (hw : w ∈ T.vertices) : w.length ≤ T.height := by
  obtain ⟨l, hl, h⟩ := T.mem_vertices_iff.mp hw
  exact (T.length_leaf l hl) ▸ h.length_le

theorem mem_leaves_iff_length_eq_height (T : UniformTree) {w : List ℕ}
    (hw : w ∈ T.vertices) : w ∈ T.leaves ↔ w.length = T.height := by
  constructor
  · exact T.length_leaf w
  · intro hlen
    obtain ⟨l, hl, h⟩ := T.mem_vertices_iff.mp hw
    have heq : w = l := h.eq_of_length (hlen.trans (T.length_leaf l hl).symm)
    simpa only [heq] using hl

abbrev Node (T : UniformTree) := {w : List ℕ // w ∈ T.vertices}

instance nodeFintype (T : UniformTree) : Fintype T.Node :=
  Finset.fintypeCoeSort T.vertices

def root (T : UniformTree) : T.Node := ⟨[], T.nil_mem_vertices⟩

instance nodeNonempty (T : UniformTree) : Nonempty T.Node := ⟨T.root⟩

@[simp] theorem root_val (T : UniformTree) : T.root.val = [] := rfl

@[simp] theorem node_card (T : UniformTree) :
    Fintype.card T.Node = T.vertices.card := Fintype.card_coe T.vertices

theorem node_card_pos (T : UniformTree) : 0 < Fintype.card T.Node :=
  Fintype.card_pos

def depth {T : UniformTree} (v : T.Node) : ℕ := v.val.length

def ancestor {T : UniformTree} (u v : T.Node) : Prop := u.val.IsPrefix v.val

def leaf {T : UniformTree} (v : T.Node) : Prop := v.val ∈ T.leaves

def child {T : UniformTree} (u v : T.Node) : Prop :=
  ∃ a : ℕ, v.val = u.val ++ [a]

@[simp] theorem depth_root (T : UniformTree) : depth T.root = 0 := rfl

theorem depth_le_height {T : UniformTree} (v : T.Node) : depth v ≤ T.height :=
  T.length_le_height v.property

theorem leaf_iff_depth_eq_height {T : UniformTree} (v : T.Node) :
    leaf v ↔ depth v = T.height :=
  T.mem_leaves_iff_length_eq_height v.property

@[simp] theorem ancestor_refl {T : UniformTree} (v : T.Node) : ancestor v v :=
  List.prefix_refl v.val

theorem ancestor_trans {T : UniformTree} {u v w : T.Node}
    (huv : ancestor u v) (hvw : ancestor v w) : ancestor u w := huv.trans hvw

theorem ancestor_depth_le {T : UniformTree} {u v : T.Node}
    (h : ancestor u v) : depth u ≤ depth v := h.length_le

theorem eq_of_ancestor_of_depth_eq {T : UniformTree} {u v : T.Node}
    (h : ancestor u v) (hlen : depth u = depth v) : u = v :=
  Subtype.ext (h.eq_of_length hlen)

@[simp] theorem root_ancestor {T : UniformTree} (v : T.Node) : ancestor T.root v :=
  List.nil_prefix

theorem eq_root_iff_depth_eq_zero {T : UniformTree} (v : T.Node) :
    v = T.root ↔ depth v = 0 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    exact List.length_eq_zero_iff.mp h

def ancestorAt {T : UniformTree} (v : T.Node) (k : ℕ) : T.Node :=
  ⟨v.val.take k, T.take_mem_vertices v.property k⟩

@[simp] theorem ancestorAt_val {T : UniformTree} (v : T.Node) (k : ℕ) :
    (ancestorAt v k).val = v.val.take k := rfl

theorem ancestorAt_ancestor {T : UniformTree} (v : T.Node) (k : ℕ) :
    ancestor (ancestorAt v k) v := List.take_prefix k v.val

theorem depth_ancestorAt {T : UniformTree} (v : T.Node) {k : ℕ}
    (hk : k ≤ depth v) : depth (ancestorAt v k) = k := by
  exact List.length_take_of_le hk

theorem ancestor_eq_ancestorAt {T : UniformTree} {u v : T.Node}
    (h : ancestor u v) : u = ancestorAt v (depth u) :=
  Subtype.ext (List.prefix_iff_eq_take.mp h)

def branchBound (T : UniformTree) : ℕ :=
  max 1 (T.leaves.sup (fun l => l.toFinset.sup id))

theorem one_le_branchBound (T : UniformTree) : 1 ≤ T.branchBound :=
  le_max_left _ _

theorem branchBound_pos (T : UniformTree) : 0 < T.branchBound :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one T.one_le_branchBound

theorem label_pos {T : UniformTree} (v : T.Node) {a : ℕ} (ha : a ∈ v.val) :
    0 < a := by
  obtain ⟨l, hl, h⟩ := T.mem_vertices_iff.mp v.property
  exact T.positive_labels l hl a (h.subset ha)

theorem label_le_branchBound {T : UniformTree} (v : T.Node) {a : ℕ}
    (ha : a ∈ v.val) : a ≤ T.branchBound := by
  obtain ⟨l, hl, h⟩ := T.mem_vertices_iff.mp v.property
  calc
    a ≤ l.toFinset.sup id :=
      Finset.le_sup (f := id) (List.mem_toFinset.mpr (h.subset ha))
    _ ≤ T.leaves.sup (fun l => l.toFinset.sup id) :=
      Finset.le_sup (f := fun l : List ℕ => l.toFinset.sup id) hl
    _ ≤ T.branchBound := le_max_right _ _

theorem exists_child_word {T : UniformTree} (v : T.Node) (hv : depth v < T.height) :
    ∃ a : ℕ, v.val ++ [a] ∈ T.vertices := by
  obtain ⟨l, hl, tail, htail⟩ := T.mem_vertices_iff.mp v.property
  cases tail with
  | nil =>
    have heq : v.val = l := by simpa using htail
    have hlen : depth v = T.height := by
      change v.val.length = T.height
      rw [heq, T.length_leaf l hl]
    exact (Nat.ne_of_lt hv hlen).elim
  | cons a tail =>
    refine ⟨a, T.mem_vertices_iff.mpr ⟨l, hl, tail, ?_⟩⟩
    simpa [List.append_assoc] using htail

theorem exists_child {T : UniformTree} (v : T.Node) (hv : depth v < T.height) :
    ∃ u : T.Node, child v u := by
  obtain ⟨a, ha⟩ := exists_child_word v hv
  exact ⟨⟨v.val ++ [a], ha⟩, a, rfl⟩

theorem child_depth {T : UniformTree} {u v : T.Node} (h : child u v) :
    depth v = depth u + 1 := by
  obtain ⟨a, ha⟩ := h
  simp only [depth, ha, List.length_append, List.length_singleton]

theorem child_ancestor {T : UniformTree} {u v : T.Node} (h : child u v) :
    ancestor u v := by
  obtain ⟨a, ha⟩ := h
  exact ⟨[a], ha.symm⟩

theorem child_label_bounds {T : UniformTree} {u v : T.Node} {a : ℕ}
    (h : v.val = u.val ++ [a]) : 0 < a ∧ a ≤ T.branchBound := by
  have ha : a ∈ v.val := by simp [h]
  exact ⟨label_pos v ha, label_le_branchBound v ha⟩

theorem leaf_iff_no_child {T : UniformTree} (v : T.Node) :
    leaf v ↔ ¬ ∃ u : T.Node, child v u := by
  constructor
  · intro hv ⟨u, hu⟩
    have heq := (leaf_iff_depth_eq_height v).mp hv
    have hle := depth_le_height u
    have hdepth := child_depth hu
    omega
  · intro h
    apply (leaf_iff_depth_eq_height v).mpr
    have hle := depth_le_height v
    by_contra hne
    exact h (exists_child v (lt_of_le_of_ne hle hne))

end UniformTree

def levelCount (marks : Finset (List ℕ)) (depth : ℕ) : ℕ :=
  (marks.filter (fun w => w.length = depth)).card

def colorCount (marks : Finset (List ℕ)) (leaf : List ℕ) : ℕ :=
  (marks.filter (fun w => w.IsPrefix leaf)).card

theorem colorCount_eq_card_inter_prefixes (marks : Finset (List ℕ))
    (leaf : List ℕ) :
    colorCount marks leaf = (marks ∩ UniformTree.prefixes leaf).card := by
  unfold colorCount
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_inter,
    UniformTree.mem_prefixes_iff]

def RespectsTreeQuota (T : UniformTree) (quota : ℕ → ℕ)
    (marks : Finset (List ℕ)) : Prop :=
  [] ∉ marks ∧ ∀ depth, 1 ≤ depth → depth ≤ T.height →
    levelCount marks depth ≤ quota depth

structure AuxiliaryTree (phases : ℕ) where
  tree : UniformTree
  quota : ℕ → ℕ
  quota_pos : ∀ depth, 1 ≤ depth → depth ≤ tree.height → 0 < quota depth
  red : Finset (List ℕ)
  blue : Finset (List ℕ)
  red_subset : red ⊆ tree.vertices
  blue_subset : blue ⊆ tree.vertices
  root_not_red : [] ∉ red
  root_not_blue : [] ∉ blue
  red_blue_disjoint : Disjoint red blue
  red_level : ∀ depth, 1 ≤ depth → depth ≤ tree.height →
    levelCount red depth ≤ quota depth
  blue_level : ∀ depth, 1 ≤ depth → depth ≤ tree.height →
    levelCount blue depth ≤ quota depth
  total_count : ∀ leaf ∈ tree.leaves,
    colorCount red leaf + colorCount blue leaf = phases
  red_witness : ∃ leaf ∈ tree.leaves, colorCount red leaf = phases
  blue_witness : ∃ leaf ∈ tree.leaves, colorCount blue leaf = phases

  avoids : ∀ marks : Finset (List ℕ),
    RespectsTreeQuota tree quota marks →
    ∃ leaf ∈ tree.leaves, Disjoint marks (UniformTree.prefixes leaf)

theorem card_hit_le {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (A : Finset α) (P : ι → Finset α)
    (hP : (I : Set ι).PairwiseDisjoint P) :
    (I.filter (fun i => ¬ Disjoint A (P i))).card ≤ A.card := by
  classical
  let hit := I.filter (fun i => ¬ Disjoint A (P i))
  have hx (i : {i // i ∈ hit}) : ∃ x : {x // x ∈ A}, x.val ∈ P i.val := by
    obtain ⟨x, hxA, hxP⟩ :=
      Finset.not_disjoint_iff.mp (Finset.mem_filter.mp i.property).2
    exact ⟨⟨x, hxA⟩, hxP⟩
  let f (i : {i // i ∈ hit}) : {x // x ∈ A} := (hx i).choose
  have hf (i : {i // i ∈ hit}) : (f i).val ∈ P i.val := (hx i).choose_spec
  have hinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    apply Finset.disjoint_left.mp
      (hP (Finset.mem_filter.mp i.property).1
        (Finset.mem_filter.mp j.property).1 hne) (hf i)
    rw [hij]
    exact hf j
  simpa only [Fintype.card_coe, hit] using Fintype.card_le_of_injective f hinj

theorem exists_disjoint_of_card_lt {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (A : Finset α) (P : ι → Finset α)
    (hP : (I : Set ι).PairwiseDisjoint P) (hcard : A.card < I.card) :
    ∃ i ∈ I, Disjoint A (P i) := by
  classical
  by_contra h
  have hhit : ∀ i ∈ I, ¬ Disjoint A (P i) := fun i hi hd => h ⟨i, hi, hd⟩
  have hfilter : I.filter (fun i => ¬ Disjoint A (P i)) = I :=
    Finset.filter_eq_self.mpr hhit
  have hle := card_hit_le I A P hP
  rw [hfilter] at hle
  exact (Nat.not_le_of_lt hcard) hle

def prefixesAfter (stem word : List ℕ) : Finset (List ℕ) :=
  ((UniformTree.prefixes word).erase []).image (fun v => stem ++ v)

@[simp]
theorem mem_prefixesAfter_iff {stem word w : List ℕ} :
    w ∈ prefixesAfter stem word ↔
      ∃ v, v ≠ [] ∧ v.IsPrefix word ∧ stem ++ v = w := by
  simp [prefixesAfter, Finset.mem_image, and_assoc]

theorem stem_not_mem_prefixesAfter (stem word : List ℕ) :
    stem ∉ prefixesAfter stem word := by
  intro h
  obtain ⟨v, hv, _, heq⟩ := mem_prefixesAfter_iff.mp h
  apply hv
  apply List.append_cancel_left (as := stem)
  simpa only [List.append_nil] using heq

theorem prefixes_append_eq (stem word : List ℕ) :
    UniformTree.prefixes (stem ++ word) =
      UniformTree.prefixes stem ∪ prefixesAfter stem word := by
  ext w
  simp only [Finset.mem_union, UniformTree.mem_prefixes_iff]
  constructor
  · intro hw
    rcases List.prefix_or_prefix_of_prefix hw (List.prefix_append stem word) with h | h
    · exact Or.inl h
    · obtain ⟨v, rfl⟩ := h
      by_cases hv : v = []
      · subst v
        exact Or.inl (by simpa only [List.append_nil] using List.prefix_refl stem)
      · exact Or.inr (mem_prefixesAfter_iff.mpr
          ⟨v, hv, (List.prefix_append_right_inj stem).mp hw, rfl⟩)
  · rintro (hw | hw)
    · exact hw.trans (List.prefix_append stem word)
    · obtain ⟨v, _, hv, rfl⟩ := mem_prefixesAfter_iff.mp hw
      exact (List.prefix_append_right_inj stem).mpr hv

theorem disjoint_positive_prefixes_cons {a b : ℕ} (u v : List ℕ) (hab : a ≠ b) :
    Disjoint ((UniformTree.prefixes (a :: u)).erase [])
      ((UniformTree.prefixes (b :: v)).erase []) := by
  apply Finset.disjoint_left.mpr
  intro w hwa hwb
  have hpa := UniformTree.mem_prefixes_iff.mp (Finset.mem_erase.mp hwa).2
  have hpb := UniformTree.mem_prefixes_iff.mp (Finset.mem_erase.mp hwb).2
  cases w with
  | nil => exact (Finset.mem_erase.mp hwa).1 rfl
  | cons x xs =>
      exact hab ((List.cons_prefix_cons.mp hpa).1.symm.trans
        (List.cons_prefix_cons.mp hpb).1)

theorem disjoint_prefixesAfter_cons (stem : List ℕ) {a b : ℕ}
    (u v : List ℕ) (hab : a ≠ b) :
    Disjoint (prefixesAfter stem (a :: u)) (prefixesAfter stem (b :: v)) := by
  apply Finset.disjoint_left.mpr
  intro w hwa hwb
  obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hwa
  obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hwb
  have hxy : x = y := List.append_cancel_left (hxeq.trans hyeq.symm)
  exact Finset.disjoint_left.mp (disjoint_positive_prefixes_cons u v hab)
    hx (hxy.symm ▸ hy)

theorem disjoint_positive_spine_prefixes {a b n m : ℕ} (hab : a ≠ b) :
    Disjoint ((UniformTree.prefixes ((a + 1) :: List.replicate n 1)).erase [])
      ((UniformTree.prefixes ((b + 1) :: List.replicate m 1)).erase []) := by
  apply disjoint_positive_prefixes_cons
  exact fun h => hab (Nat.add_right_cancel h)

theorem disjoint_spine_prefixesAfter (stem : List ℕ) {a b n m : ℕ} (hab : a ≠ b) :
    Disjoint (prefixesAfter stem ((a + 1) :: List.replicate n 1))
      (prefixesAfter stem ((b + 1) :: List.replicate m 1)) := by
  apply disjoint_prefixesAfter_cons
  exact fun h => hab (Nat.add_right_cancel h)

end BinPackingGap

namespace BinPackingGap.TreeGeometry

open _root_.OAI.BinPackingGap.Geometry UniformTree

inductive Side where
  | plus
  | minus
  deriving DecidableEq

instance : Fintype Side where
  elems := {.plus, .minus}
  complete s := by cases s <;> simp

def rootOffset : Side → ℚ
  | .plus => 0
  | .minus => 4

def pathSum (m R D : ℕ) : ℕ → List ℕ → ℚ
  | _, [] => 0
  | k, a :: w => 4 * (a : ℚ) * lambda m R D (k + 1) + pathSum m R D (k + 1) w

def left (m R D : ℕ) (s : Side) (w : List ℕ) : ℚ :=
  rootOffset s + pathSum m R D 0 w

def width (m R D : ℕ) (w : List ℕ) : ℚ :=
  if w = [] then 1 else lambda m R D w.length

def right (m R D : ℕ) (s : Side) (w : List ℕ) : ℚ :=
  left m R D s w + width m R D w

def cell (m R D : ℕ) (s : Side) (w : List ℕ) : Set ℚ :=
  Set.Icc (left m R D s w) (right m R D s w)

def BoundedAddress (D : ℕ) (w : List ℕ) : Prop := ∀ a ∈ w, a ≤ D

theorem boundedAddress_node {T : UniformTree} (v : T.Node) {D : ℕ}
    (hD : T.branchBound ≤ D) : BoundedAddress D v.val :=
  fun _ ha => (label_le_branchBound v ha).trans hD

@[simp] theorem left_nil (m R D : ℕ) (s : Side) :
    left m R D s [] = rootOffset s := by simp [left, pathSum]

@[simp] theorem width_nil (m R D : ℕ) : width m R D [] = 1 := by simp [width]

@[simp] theorem right_nil (m R D : ℕ) (s : Side) :
    right m R D s [] = rootOffset s + 1 := by simp [right]

theorem width_of_ne_nil (m R D : ℕ) {w : List ℕ} (hw : w ≠ []) :
    width m R D w = lambda m R D w.length := by simp [width, hw]

theorem width_pos (m R D : ℕ) (w : List ℕ) : 0 < width m R D w := by
  by_cases hw : w = []
  · simp [width, hw]
  · simpa [width, hw] using lambda_pos m R D w.length

theorem left_lt_right (m R D : ℕ) (s : Side) (w : List ℕ) :
    left m R D s w < right m R D s w := by
  exact lt_add_of_pos_right _ (width_pos m R D w)

theorem cell_nonempty (m R D : ℕ) (s : Side) (w : List ℕ) :
    (cell m R D s w).Nonempty :=
  ⟨left m R D s w, le_rfl, (left_lt_right m R D s w).le⟩

theorem pathSum_append (m R D k : ℕ) (u v : List ℕ) :
    pathSum m R D k (u ++ v) =
      pathSum m R D k u + pathSum m R D (k + u.length) v := by
  induction u generalizing k with
  | nil => simp [pathSum]
  | cons a u ih =>
    simp only [List.cons_append, pathSum, ih, List.length_cons]
    rw [show k + 1 + u.length = k + (u.length + 1) by omega]
    ring

theorem left_append_singleton (m R D : ℕ) (s : Side) (w : List ℕ) (a : ℕ) :
    left m R D s (w ++ [a]) =
      left m R D s w + 4 * (a : ℚ) * lambda m R D (w.length + 1) := by
  simp only [left, pathSum_append, Nat.zero_add, pathSum, add_zero]
  ring

theorem right_append_singleton (m R D : ℕ) (s : Side) (w : List ℕ) (a : ℕ) :
    right m R D s (w ++ [a]) =
      left m R D s w + (4 * (a : ℚ) + 1) * lambda m R D (w.length + 1) := by
  have hn : w ++ [a] ≠ [] := by simp
  rw [right, left_append_singleton, width_of_ne_nil m R D hn]
  simp only [List.length_append, List.length_singleton]
  ring

theorem child_endpoints (m R D : ℕ) (s : Side) (w : List ℕ) {a : ℕ}
    (ha : a ≤ D) :
    left m R D s w ≤ left m R D s (w ++ [a]) ∧
      right m R D s (w ++ [a]) ≤ right m R D s w := by
  have hscale := lambda_pos m R D (w.length + 1)
  have hcast : (a : ℚ) ≤ D := by exact_mod_cast ha
  have ha0 : (0 : ℚ) ≤ a := Nat.cast_nonneg a
  constructor
  · rw [left_append_singleton]
    nlinarith
  · rw [right_append_singleton, right]
    have hmul : (4 * (a : ℚ) + 1) * lambda m R D (w.length + 1) ≤
        (4 * (D : ℚ) + 1) * lambda m R D (w.length + 1) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hscale.le
    by_cases hw : w = []
    · subst w
      have hfirst := first_children_lt_tenth m R D
      simp only [List.length_nil, Nat.zero_add, width_nil] at *
      linarith
    · rw [width_of_ne_nil m R D hw]
      have hchild := children_succ_lt_parent m R D w.length
      linarith

theorem append_endpoints (m R D : ℕ) (s : Side) (u v : List ℕ)
    (hv : BoundedAddress D v) :
    left m R D s u ≤ left m R D s (u ++ v) ∧
      right m R D s (u ++ v) ≤ right m R D s u := by
  induction v generalizing u with
  | nil => simp
  | cons a v ih =>
    have hc := child_endpoints m R D s u (hv a (by simp))
    have ht := ih (u ++ [a]) (fun b hb => hv b (by simp [hb]))
    have heq : (u ++ [a]) ++ v = u ++ a :: v := by simp [List.append_assoc]
    rw [heq] at ht
    exact ⟨hc.1.trans ht.1, ht.2.trans hc.2⟩

theorem prefix_endpoints (m R D : ℕ) (s : Side) {u v : List ℕ}
    (h : u.IsPrefix v) (hv : BoundedAddress D v) :
    left m R D s u ≤ left m R D s v ∧ right m R D s v ≤ right m R D s u := by
  obtain ⟨t, rfl⟩ := h
  exact append_endpoints m R D s u t (fun a ha => hv a (by simp [ha]))

theorem cell_subset_of_prefix (m R D : ℕ) (s : Side) {u v : List ℕ}
    (h : u.IsPrefix v) (hv : BoundedAddress D v) :
    cell m R D s v ⊆ cell m R D s u := by
  have hb := prefix_endpoints m R D s h hv
  intro x hx
  exact ⟨hb.1.trans hx.1, hx.2.trans hb.2⟩

theorem nonroot_endpoints (m R D : ℕ) (s : Side) {w : List ℕ}
    (hw : w ≠ []) (hb : BoundedAddress D w) :
    rootOffset s ≤ left m R D s w ∧ right m R D s w < rootOffset s + 1 / 10 := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w =>
    have ha := hb a (by simp)
    have hroot := prefix_endpoints m R D s (u := []) List.nil_prefix hb
    have hfirst := prefix_endpoints m R D s (u := [a]) ⟨w, rfl⟩ hb
    simp only [List.singleton_append] at hfirst
    have hm : (4 * (a : ℚ) + 1) * lambda m R D 1 ≤
        (4 * (D : ℚ) + 1) * lambda m R D 1 := by
      have hcast : (a : ℚ) ≤ D := by exact_mod_cast ha
      exact mul_le_mul_of_nonneg_right (by linarith) (lambda_nonneg m R D 1)
    have hf := first_children_lt_tenth m R D
    have hr := right_append_singleton m R D s [] a
    simp only [List.nil_append, List.length_nil, Nat.zero_add, left_nil] at hr
    exact ⟨by simpa only [left_nil] using hroot.1, by linarith [hfirst.2]⟩

private theorem exists_snoc_of_length_succ {w : List ℕ} {ell : ℕ}
    (h : w.length = ell + 1) :
    ∃ u a, w = u ++ [a] ∧ u.length = ell := by
  induction w using List.reverseRecOn with
  | nil => simp at h
  | append_singleton u a _ =>
    exact ⟨u, a, rfl, by simpa using h⟩

theorem same_depth_gap (m R D ell : ℕ) {s t : Side} {u v : List ℕ}
    (hu : u.length = ell) (hv : v.length = ell)
    (hbu : BoundedAddress D u) (hbv : BoundedAddress D v)
    (hne : (s, u) ≠ (t, v)) :
    right m R D s u + 3 * lambda m R D ell ≤ left m R D t v ∨
      right m R D t v + 3 * lambda m R D ell ≤ left m R D s u := by
  induction ell generalizing s t u v with
  | zero =>
    have hu0 : u = [] := List.length_eq_zero_iff.mp hu
    have hv0 : v = [] := List.length_eq_zero_iff.mp hv
    subst u
    subst v
    have hscale := lambda_le_one m R D 0
    cases s <;> cases t <;> simp only [left_nil, right_nil, rootOffset] at *
    · exact (hne rfl).elim
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact (hne rfl).elim
  | succ ell ih =>
    obtain ⟨u, a, rfl, hup⟩ := exists_snoc_of_length_succ hu
    obtain ⟨v, b, rfl, hvp⟩ := exists_snoc_of_length_succ hv
    have hau : a ≤ D := hbu a (by simp)
    have hbv' : b ≤ D := hbv b (by simp)
    have hpu : BoundedAddress D u := fun c hc => hbu c (by simp [hc])
    have hpv : BoundedAddress D v := fun c hc => hbv c (by simp [hc])
    by_cases hp : (s, u) = (t, v)
    · have hs : s = t := congrArg Prod.fst hp
      have huv : u = v := congrArg Prod.snd hp
      subst t
      subst v
      have hab : a ≠ b := by
        intro heq
        exact hne (by simp [heq])
      have hscale := lambda_nonneg m R D (ell + 1)
      rw [right_append_singleton, right_append_singleton,
        left_append_singleton, left_append_singleton, hup]
      rcases lt_or_gt_of_ne hab with hab | hba
      · left
        have hc : (a : ℚ) + 1 ≤ b := by exact_mod_cast (Nat.succ_le_iff.mpr hab)
        nlinarith
      · right
        have hc : (b : ℚ) + 1 ≤ a := by exact_mod_cast (Nat.succ_le_iff.mpr hba)
        nlinarith
    · have hgap := ih hup hvp hpu hpv hp
      have hcu := child_endpoints m R D s u hau
      have hcv := child_endpoints m R D t v hbv'
      have hscale := lambda_antitone m R D (Nat.le_succ ell)
      rcases hgap with hgap | hgap
      · left
        linarith [hcu.2, hcv.1]
      · right
        linarith [hcv.2, hcu.1]

theorem eq_of_short_intersections (m R D : ℕ) {ell L : ℕ}
    (hell : ell ≤ L) {s t : Side} {u v : List ℕ} {a b : ℚ}
    (hu : u.length = ell) (hv : v.length = ell)
    (hbu : BoundedAddress D u) (hbv : BoundedAddress D v)
    (hlen : b - a ≤ lambda m R D ell + delta m R D L)
    (hiu : (Set.Icc a b ∩ cell m R D s u).Nonempty)
    (hiv : (Set.Icc a b ∩ cell m R D t v).Nonempty) : (s, u) = (t, v) := by
  by_contra hne
  have hgap := same_depth_gap m R D ell hu hv hbu hbv hne
  obtain ⟨x, hx, hxu⟩ := hiu
  obtain ⟨y, hy, hyv⟩ := hiv
  have hshort := lambda_add_delta_lt_three m R D hell
  rcases hgap with hgap | hgap
  · linarith [hx.1, hx.2, hy.1, hy.2, hxu.1, hxu.2, hyv.1, hyv.2]
  · linarith [hx.1, hx.2, hy.1, hy.2, hxu.1, hxu.2, hyv.1, hyv.2]

def nodeCell (m R D : ℕ) (s : Side) {T : UniformTree} (v : T.Node) : Set ℚ :=
  cell m R D s v.val

theorem nodeCell_subset_of_ancestor (m R D : ℕ) (s : Side) {T : UniformTree}
    (hD : T.branchBound ≤ D) {u v : T.Node} (h : ancestor u v) :
    nodeCell m R D s v ⊆ nodeCell m R D s u :=
  cell_subset_of_prefix m R D s h (boundedAddress_node v hD)

theorem nodeCell_subset_root (m R D : ℕ) (s : Side) {T : UniformTree}
    (hD : T.branchBound ≤ D) (v : T.Node) :
    nodeCell m R D s v ⊆ Set.Icc (rootOffset s) (rootOffset s + 1) := by
  simpa [nodeCell, cell] using
    nodeCell_subset_of_ancestor m R D s hD (root_ancestor v)

theorem nonroot_nodeCell_first_tenth (m R D : ℕ) (s : Side) {T : UniformTree}
    (hD : T.branchBound ≤ D) {v : T.Node} (hv : v ≠ T.root) :
    nodeCell m R D s v ⊆ Set.Ico (rootOffset s) (rootOffset s + 1 / 10) := by
  have hn : v.val ≠ [] := by
    intro heq
    exact hv (Subtype.ext heq)
  have he := nonroot_endpoints m R D s hn (boundedAddress_node v hD)
  intro x hx
  exact ⟨he.1.trans hx.1, hx.2.trans_lt he.2⟩

theorem mem_ancestor_cell (m R D : ℕ) (s : Side) {T : UniformTree}
    (hD : T.branchBound ≤ D) (v : T.Node) (ell : ℕ) {x : ℚ}
    (hx : x ∈ nodeCell m R D s v) :
    x ∈ nodeCell m R D s (ancestorAt v ell) :=
  nodeCell_subset_of_ancestor m R D s hD (ancestorAt_ancestor v ell) hx

theorem leaf_intersection_is_ancestor (m R D : ℕ) {L ell : ℕ}
    (hell : ell ≤ L) {T U : UniformTree} (hT : T.height = L)
    (hDT : T.branchBound ≤ D) (hDU : U.branchBound ≤ D)
    {s t : Side} (v : T.Node) (hv : leaf v) (w : U.Node)
    (hw : depth w = ell) {a b x : ℚ}
    (hlen : b - a ≤ lambda m R D ell + delta m R D L)
    (hx : x ∈ Set.Icc a b) (hxv : x ∈ nodeCell m R D s v)
    (hwI : (Set.Icc a b ∩ nodeCell m R D t w).Nonempty) :
    (t, w.val) = (s, (ancestorAt v ell).val) := by
  have hdepth : depth v = L := ((leaf_iff_depth_eq_height v).mp hv).trans hT
  have hanc : depth (ancestorAt v ell) = ell :=
    depth_ancestorAt v (by simpa only [hdepth] using hell)
  exact eq_of_short_intersections m R D hell hw hanc
    (boundedAddress_node w hDU) (boundedAddress_node (ancestorAt v ell) hDT)
    hlen hwI ⟨x, hx, mem_ancestor_cell m R D s hDT v ell hxv⟩

def commonBranchBound (plus minus : UniformTree) : ℕ :=
  max plus.branchBound minus.branchBound

theorem plus_branch_le (plus minus : UniformTree) :
    plus.branchBound ≤ commonBranchBound plus minus := le_max_left _ _

theorem minus_branch_le (plus minus : UniformTree) :
    minus.branchBound ≤ commonBranchBound plus minus := le_max_right _ _

end BinPackingGap.TreeGeometry

namespace BinPackingGap.IntegerPackingArithmetic

def pathNumerator (D L : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | k, a :: w => 40 * a * widthRadix D ^ (L - (k + 1)) +
      pathNumerator D L (k + 1) w

def rootOffsetNumerator : TreeGeometry.Side → ℕ
  | .plus => 0
  | .minus => 4

def treeLeftNumerator (m R D L : ℕ) (side : TreeGeometry.Side)
    (w : List ℕ) : ℕ :=
  rootOffsetNumerator side * geomDenominator m R D L + pathNumerator D L 0 w

def treeRightNumerator (m R D L : ℕ) (side : TreeGeometry.Side)
    (w : List ℕ) : ℕ :=
  treeLeftNumerator m R D L side w +
    if w = [] then geomDenominator m R D L else localNumerator D L w.length

theorem geomDenominator_mul_pathSum (m R D L k : ℕ) (w : List ℕ)
    (hdepth : k + w.length ≤ L) :
    (geomDenominator m R D L : ℚ) * TreeGeometry.pathSum m R D k w =
      (pathNumerator D L k w : ℚ) := by
  induction w generalizing k with
  | nil => simp [TreeGeometry.pathSum, pathNumerator]
  | cons a w ih =>
      have hdepth' : k + (w.length + 1) ≤ L := hdepth
      have hfirst : k + 1 ≤ L := by omega
      have htail : (k + 1) + w.length ≤ L := by
        omega
      have hlocal := geomDenominator_mul_lambda m R D L (k + 1) hfirst
      have hrest := ih (k + 1) htail
      simp only [TreeGeometry.pathSum, pathNumerator, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_pow]
      calc
        _ = 4 * (a : ℚ) * ((geomDenominator m R D L : ℚ) *
              Geometry.lambda m R D (k + 1)) +
            (geomDenominator m R D L : ℚ) * TreeGeometry.pathSum m R D (k + 1) w := by ring
        _ = _ := by
          rw [hlocal, hrest]
          simp only [localNumerator, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
          ring

theorem rootOffsetNumerator_cast (side : TreeGeometry.Side) :
    (rootOffsetNumerator side : ℚ) = TreeGeometry.rootOffset side := by
  cases side <;> rfl

theorem geomDenominator_mul_treeLeft (m R D L : ℕ)
    (side : TreeGeometry.Side) (w : List ℕ) (hdepth : w.length ≤ L) :
    (geomDenominator m R D L : ℚ) * TreeGeometry.left m R D side w =
      (treeLeftNumerator m R D L side w : ℚ) := by
  have hpath := geomDenominator_mul_pathSum m R D L 0 w (by simpa using hdepth)
  simp only [TreeGeometry.left, treeLeftNumerator, Nat.cast_add, Nat.cast_mul,
    rootOffsetNumerator_cast]
  rw [mul_add, hpath]
  ring

theorem geomDenominator_mul_treeRight (m R D L : ℕ)
    (side : TreeGeometry.Side) (w : List ℕ) (hdepth : w.length ≤ L) :
    (geomDenominator m R D L : ℚ) * TreeGeometry.right m R D side w =
      (treeRightNumerator m R D L side w : ℚ) := by
  have hleft := geomDenominator_mul_treeLeft m R D L side w hdepth
  simp only [TreeGeometry.right, mul_add, hleft, treeRightNumerator, Nat.cast_add]
  by_cases hw : w = []
  · simp [TreeGeometry.width, hw]
  · simp only [TreeGeometry.width, hw, ite_false]
    rw [geomDenominator_mul_lambda m R D L w.length hdepth]

end BinPackingGap.IntegerPackingArithmetic

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Inventory/InventoryScores.lean =====
namespace OAI

namespace BinPackingGap

open scoped BigOperators

structure InventoryData where
  graph : GraphInput
  plus : UniformTree
  minus : UniformTree
  d : ℕ
  R : ℕ
  L : ℕ
  quota : ℕ → ℕ
  k : ℕ

namespace InventoryData

variable (D : InventoryData)

abbrev Vertex := D.graph.Vertex
abbrev Edge := D.graph.Edge
abbrev Position := D.graph.Edge × Fin D.R
abbrev IncidencePosition (v : D.Vertex) := D.graph.IncidencePosition D.R v
abbrev JobCopy (v : D.Vertex) := D.graph.JobCopy D.R D.d v
abbrev Depth := {ell : ℕ // ell ∈ Finset.Icc 1 D.L}

def P : ℕ := ∑ ell ∈ Finset.Icc 1 D.L, D.quota ell

def tPlus : ℕ := D.d * Fintype.card D.plus.Node + D.P
def tMinus : ℕ := D.d * Fintype.card D.minus.Node
def t : ℕ := D.tPlus + D.tMinus
def J (v : D.Vertex) : ℕ := D.d * D.R * D.graph.degree v
def B : ℕ := ∑ v : D.Vertex, (D.t + 2 * D.J v)

abbrev TreeRow :=
  (D.plus.Node × Fin D.d) ⊕ ((D.minus.Node × Fin D.d) ⊕ Fin D.P)

abbrev RowAt (v : D.Vertex) := D.TreeRow ⊕ (Bool × D.JobCopy v)

abbrev MBase (v : D.Vertex) := D.TreeRow ⊕ D.JobCopy v

abbrev AnchorAt (v : D.Vertex) := D.MBase v ⊕ D.JobCopy v

abbrev PositiveLocal := Σ ell : D.Depth, Fin (D.quota ell.val)

abbrev ZeroLocalAt (v : D.Vertex) := Fin (D.t - D.P) ⊕ D.JobCopy v
abbrev DMAt (v : D.Vertex) := D.PositiveLocal ⊕ D.ZeroLocalAt v
abbrev LocalAt (v : D.Vertex) := D.DMAt v ⊕ D.JobCopy v

abbrev LocalBin (v : D.Vertex) := D.MBase v ⊕ D.JobCopy v

abbrev PlusLeaf := {v : D.plus.Node // v.val ∈ D.plus.leaves}
abbrev MinusLeaf := {v : D.minus.Node // v.val ∈ D.minus.leaves}
abbrev TestAt (v : D.Vertex) :=
  D.PlusLeaf ⊕ (D.MinusLeaf ⊕ D.IncidencePosition v)

def designated {v : D.Vertex} : D.TestAt v × Fin D.d → D.MBase v
  | ⟨.inl leaf, j⟩ => .inl (.inl (leaf.val, j))
  | ⟨.inr (.inl leaf), j⟩ => .inl (.inr (.inl (leaf.val, j)))
  | ⟨.inr (.inr r), j⟩ => .inr (r, j)

def plusSlots : ℕ := ∑ v : D.Vertex, (D.tPlus + D.J v)
def minusSlots : ℕ := D.graph.n * D.tMinus
def treeFlags : ℕ := D.graph.n * D.t
def jobFlags : ℕ := ∑ v : D.Vertex, D.J v

end InventoryData

inductive GlobalSpecies (G : GraphInput) where
  | up (unitLength : Bool)
  | um (unitLength : Bool)
  | edge (e : G.Edge) (permit : Bool)
  deriving DecidableEq

instance (G : GraphInput) : Fintype (GlobalSpecies G) where
  elems := (Finset.univ.image GlobalSpecies.up) ∪
    (Finset.univ.image GlobalSpecies.um) ∪
    ((Finset.univ : Finset (G.Edge × Bool)).image
      (fun p => GlobalSpecies.edge p.1 p.2))
  complete := by
    intro s
    cases s <;> simp

inductive FlagSpecies where
  | tree
  | main
  | edge
  deriving DecidableEq

instance : Fintype FlagSpecies where
  elems := {.tree, .main, .edge}
  complete := by intro s; cases s <;> simp

namespace InventoryData

variable (D : InventoryData)

def globalStock : GlobalSpecies D.graph → ℕ
  | .up true => D.d * D.k
  | .up false => D.plusSlots - D.d * D.k
  | .um true => D.d * (D.graph.n - D.k)
  | .um false => D.minusSlots - D.d * (D.graph.n - D.k)
  | .edge _ _ => D.d * D.R

def flagStock : FlagSpecies → ℕ
  | .tree => D.treeFlags
  | .main => D.jobFlags
  | .edge => D.jobFlags

abbrev GlobalCopy := Σ s : GlobalSpecies D.graph, Fin (D.globalStock s)
abbrev FlagCopy := Σ s : FlagSpecies, Fin (D.flagStock s)

def RoleCopies : Role → Type
  | .x => Σ v : D.Vertex, D.RowAt v
  | .anchor => Σ v : D.Vertex, D.AnchorAt v
  | .«global» => D.GlobalCopy
  | .«local» => Σ v : D.Vertex, D.LocalAt v
  | .flag => D.FlagCopy

instance roleCopiesFintype (r : Role) : Fintype (D.RoleCopies r) := by
  cases r <;> dsimp [RoleCopies] <;> infer_instance

abbrev Item := Σ r : Role, D.RoleCopies r

def itemRole (i : D.Item) : Role := i.1

def itemLabel : D.Item → Option D.Vertex
  | ⟨.x, x⟩ => some x.1
  | ⟨.anchor, a⟩ => some a.1
  | ⟨.«global», _⟩ => none
  | ⟨.«local», a⟩ => some a.1
  | ⟨.flag, _⟩ => none

def treeSubclass : D.TreeRow → Subclass
  | .inl _ => .tp
  | .inr (.inl _) => .tm
  | .inr (.inr _) => .tp

def rowSubclass {v : D.Vertex} : D.RowAt v → Subclass
  | .inl t => D.treeSubclass t
  | .inr _ => .s

def itemSubclass : D.Item → Subclass
  | ⟨.x, ⟨_, r⟩⟩ => D.rowSubclass r
  | ⟨.anchor, ⟨_, .inl _⟩⟩ => .z
  | ⟨.anchor, ⟨_, .inr _⟩⟩ => .y
  | ⟨.«global», ⟨.up _, _⟩⟩ => .up
  | ⟨.«global», ⟨.um _, _⟩⟩ => .um
  | ⟨.«global», ⟨.edge _ _, _⟩⟩ => .w
  | ⟨.«local», ⟨_, .inl _⟩⟩ => .dm
  | ⟨.«local», ⟨_, .inr _⟩⟩ => .dg
  | ⟨.flag, ⟨.tree, _⟩⟩ => .ft
  | ⟨.flag, ⟨.main, _⟩⟩ => .fm
  | ⟨.flag, ⟨.edge, _⟩⟩ => .fg

theorem itemSubclass_role (i : D.Item) : (D.itemSubclass i).role = D.itemRole i := by
  rcases i with ⟨r, i⟩
  cases r with
  | x =>
      rcases i with ⟨v, (row | job)⟩
      · rcases row with (plus | (minus | padding)) <;> rfl
      · rfl
  | anchor => rcases i with ⟨v, (deadline | key)⟩ <;> rfl
  | «global» =>
      rcases i with ⟨s, copy⟩
      cases s <;> rfl
  | «local» => rcases i with ⟨v, (main | edge)⟩ <;> rfl
  | flag =>
      rcases i with ⟨s, copy⟩
      cases s <;> rfl

def rowShort {v : D.Vertex} : D.RowAt v → Bool
  | .inl _ => false
  | .inr r => r.1

def jobPosition {v : D.Vertex} (j : D.JobCopy v) : D.Position :=
  (j.1.1.val.1, j.1.2)

def rowPosition {v : D.Vertex} : D.RowAt v → Option D.Position
  | .inl _ => none
  | .inr r => some (D.jobPosition r.2)

def keyPosition {v : D.Vertex} (k : D.JobCopy v) : D.Position :=
  D.jobPosition k

def globalUnit : D.GlobalCopy → Bool
  | ⟨.up unit, _⟩ => unit
  | ⟨.um unit, _⟩ => unit
  | ⟨.edge _ _, _⟩ => false

def globalEdge : D.GlobalCopy → Option D.Edge
  | ⟨.edge e _, _⟩ => some e
  | _ => none

def globalPermit : D.GlobalCopy → Bool
  | ⟨.edge _ permit, _⟩ => permit
  | _ => false

def localDepth {v : D.Vertex} : D.LocalAt v → Option D.Depth
  | .inl (.inl p) => some p.1
  | _ => none

end InventoryData

theorem sum_primaryScore_eq_zero_of_inventory {ι : Type*} [Fintype ι]
    (s : ι → Subclass) (B : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hrole : ∀ r : Role, roleCount s r = (B : ℤ))
    (htree : subclassCount s .tp + subclassCount s .tm = subclassCount s .ft)
    (hanchor : subclassCount s .z = subclassCount s .ft + subclassCount s .fm)
    (hglobal : subclassCount s .up + subclassCount s .um =
      subclassCount s .ft + subclassCount s .fm)
    (hlocal : subclassCount s .dm = subclassCount s .ft + subclassCount s .fm)
    (hminus : subclassCount s .tm = subclassCount s .um) :
    (∑ i, primaryScore (s i)) = 0 := by
  apply sum_primaryScore_eq_zero_of_coefficients
  have hr (r : Role) : (∑ i, primaryCoeff (roleCoeffIndex r) (s i)) = 0 := by
    rw [sum_primaryCoeff_role, hrole, hcard]
    push_cast
    ring
  intro j
  fin_cases j
  · simpa [roleCoeffIndex, Role.index] using hr .x
  · simpa [roleCoeffIndex, Role.index] using hr .anchor
  · simpa [roleCoeffIndex, Role.index] using hr .«global»
  · simpa [roleCoeffIndex, Role.index] using hr .«local»
  · simpa [roleCoeffIndex, Role.index] using hr .flag
  · change (∑ i, primaryCoeff (5 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_five s, htree, sub_self]
  · change (∑ i, primaryCoeff (6 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_six s, hanchor]
    ring
  · change (∑ i, primaryCoeff (7 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_seven s, hglobal]
    ring
  · change (∑ i, primaryCoeff (8 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_eight s, hlocal]
    ring
  · change (∑ i, primaryCoeff (9 : Fin 10) (s i)) = 0
    rw [sum_primaryCoeff_nine s, hminus, sub_self]

def labelledRoleCount {ι : Type*} [Fintype ι] {n : ℕ}
    (s : ι → Subclass) (label : ι → Option (Fin n)) (r : Role) (v : Fin n) : ℤ :=
  ∑ i, if (s i).role = r ∧ label i = some v then 1 else 0

theorem sum_secondaryScore_eq {ι : Type*} [Fintype ι] {n : ℕ}
    (s : ι → Subclass) (label : ι → Option (Fin n)) :
    (∑ i, secondaryScore (s i) (label i)) =
      ∑ v : Fin n, (labelledRoleCount s label .x v -
        2 * labelledRoleCount s label .anchor v +
        labelledRoleCount s label .«local» v) * labelWeight v := by
  classical
  have pointwise (c : Subclass) (l : Option (Fin n)) :
      secondaryScore c l =
        ∑ v : Fin n,
          ((if c.role = Role.x ∧ l = some v then (1 : ℤ) else 0) -
            2 * (if c.role = Role.anchor ∧ l = some v then (1 : ℤ) else 0) +
            (if c.role = Role.«local» ∧ l = some v then (1 : ℤ) else 0)) *
              labelWeight v := by
    cases l with
    | none => cases hc : c.role <;> simp [secondaryScore, hc]
    | some a =>
        cases hc : c.role <;>
          simp [secondaryScore, hc, eq_comm]
  simp_rw [pointwise]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp only [labelledRoleCount, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum,
    add_mul, sub_mul, mul_assoc]

theorem sum_secondaryScore_eq_zero_of_inventory {ι : Type*} [Fintype ι] {n : ℕ}
    (s : ι → Subclass) (label : ι → Option (Fin n))
    (hx : ∀ v, labelledRoleCount s label .x v = labelledRoleCount s label .anchor v)
    (hd : ∀ v, labelledRoleCount s label .«local» v =
      labelledRoleCount s label .anchor v) :
    (∑ i, secondaryScore (s i) (label i)) = 0 := by
  rw [sum_secondaryScore_eq]
  apply Finset.sum_eq_zero
  intro v _
  rw [hx, hd]
  ring

namespace GlobalSpecies

def equivSum (G : GraphInput) :
    GlobalSpecies G ≃ (Bool ⊕ Bool) ⊕ (G.Edge × Bool) where
  toFun
    | .up b => .inl (.inl b)
    | .um b => .inl (.inr b)
    | .edge e b => .inr (e, b)
  invFun
    | .inl (.inl b) => .up b
    | .inl (.inr b) => .um b
    | .inr (e, b) => .edge e b
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with ((b | b) | ⟨e, b⟩) <;> rfl

theorem sum_univ {A : Type*} [AddCommMonoid A] (G : GraphInput)
    (f : GlobalSpecies G → A) :
    (∑ s, f s) = f (.up true) + f (.up false) + f (.um true) + f (.um false) +
      ∑ e : G.Edge, (f (.edge e true) + f (.edge e false)) := by
  calc
    _ = ∑ x : (Bool ⊕ Bool) ⊕ (G.Edge × Bool), f ((equivSum G).symm x) :=
      Fintype.sum_equiv (equivSum G) _ _ (fun _ => by simp)
    _ = _ := by
      simp [equivSum, Fintype.sum_sum_type, Fintype.sum_prod_type,
        add_assoc, add_comm]

end GlobalSpecies

namespace FlagSpecies

theorem sum_univ {A : Type*} [AddCommMonoid A] (f : FlagSpecies → A) :
    (∑ s, f s) = f .tree + f .main + f .edge := by
  have h : (Finset.univ : Finset FlagSpecies) = {.tree, .main, .edge} := by decide
  rw [h]
  simp [add_assoc]

end FlagSpecies

namespace InventoryData

variable (D : InventoryData)

theorem card_treeRow : Fintype.card D.TreeRow = D.t := by
  simp [TreeRow, t, tPlus, tMinus, Nat.mul_comm, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

theorem card_jobCopy (v : D.Vertex) : Fintype.card (D.JobCopy v) = D.J v :=
  D.graph.card_jobCopy D.R D.d v

theorem card_rowAt (v : D.Vertex) : Fintype.card (D.RowAt v) = D.t + 2 * D.J v := by
  change Fintype.card (D.TreeRow ⊕ (Bool × D.JobCopy v)) = _
  rw [Fintype.card_sum, D.card_treeRow, Fintype.card_prod, Fintype.card_bool,
    D.card_jobCopy]

theorem card_mBase (v : D.Vertex) : Fintype.card (D.MBase v) = D.t + D.J v := by
  change Fintype.card (D.TreeRow ⊕ D.JobCopy v) = _
  rw [Fintype.card_sum, D.card_treeRow, D.card_jobCopy]

theorem card_anchorAt (v : D.Vertex) :
    Fintype.card (D.AnchorAt v) = D.t + 2 * D.J v := by
  change Fintype.card (D.MBase v ⊕ D.JobCopy v) = _
  rw [Fintype.card_sum, D.card_mBase, D.card_jobCopy]
  omega

theorem card_localBin (v : D.Vertex) :
    Fintype.card (D.LocalBin v) = D.t + 2 * D.J v :=
  D.card_anchorAt v

theorem P_le_t : D.P ≤ D.t := by
  dsimp [t, tPlus, tMinus]
  omega

theorem d_le_tPlus : D.d ≤ D.tPlus := by
  have h := Nat.mul_le_mul_left D.d (D.plus.node_card_pos)
  simpa [tPlus] using (show D.d ≤ D.d * Fintype.card D.plus.Node + D.P by omega)

theorem d_le_tMinus : D.d ≤ D.tMinus := by
  have h := Nat.mul_le_mul_left D.d (D.minus.node_card_pos)
  simpa [tMinus] using h

theorem two_mul_d_le_t_sub_P : 2 * D.d ≤ D.t - D.P := by
  have hp := Nat.mul_le_mul_left D.d (D.plus.node_card_pos)
  have hm := D.d_le_tMinus
  dsimp [t, tPlus, tMinus] at *
  omega

theorem card_positiveLocal : Fintype.card D.PositiveLocal = D.P := by
  classical
  simp only [PositiveLocal, Fintype.card_sigma, Fintype.card_fin]
  exact Finset.sum_coe_sort (Finset.Icc 1 D.L) D.quota

theorem card_zeroLocalAt (v : D.Vertex) :
    Fintype.card (D.ZeroLocalAt v) = D.t + D.J v - D.P := by
  simp only [ZeroLocalAt, Fintype.card_sum, Fintype.card_fin, card_jobCopy]
  have h := D.P_le_t
  omega

theorem card_dmAt (v : D.Vertex) : Fintype.card (D.DMAt v) = D.t + D.J v := by
  change Fintype.card (D.PositiveLocal ⊕ D.ZeroLocalAt v) = _
  rw [Fintype.card_sum, D.card_positiveLocal, D.card_zeroLocalAt]
  have h := D.P_le_t
  omega

theorem card_localAt (v : D.Vertex) : Fintype.card (D.LocalAt v) = D.t + 2 * D.J v := by
  change Fintype.card (D.DMAt v ⊕ D.JobCopy v) = _
  rw [Fintype.card_sum, D.card_dmAt, D.card_jobCopy]
  omega

theorem sum_J : (∑ v : D.Vertex, D.J v) = 2 * D.d * D.graph.edges.length * D.R := by
  simpa only [D.card_jobCopy] using D.graph.sum_card_jobCopy D.R D.d

theorem plusSlots_eq : D.plusSlots = D.graph.n * D.tPlus + ∑ v : D.Vertex, D.J v := by
  simp [plusSlots, Finset.sum_add_distrib, Finset.sum_const]

theorem B_eq : D.B = D.graph.n * D.t + 2 * ∑ v : D.Vertex, D.J v := by
  simp [B, Finset.sum_add_distrib, Finset.sum_const, Finset.mul_sum]

theorem B_closed : D.B = D.graph.n * D.t + 4 * D.d * D.graph.edges.length * D.R := by
  rw [B_eq, sum_J]
  ring

theorem unitPlus_le_stock (hk : D.k ≤ D.graph.n) : D.d * D.k ≤ D.plusSlots := by
  calc
    D.d * D.k ≤ D.d * D.graph.n := Nat.mul_le_mul_left D.d hk
    _ ≤ D.graph.n * D.tPlus := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left D.graph.n D.d_le_tPlus
    _ ≤ D.plusSlots := by rw [plusSlots_eq]; omega

theorem unitMinus_le_stock : D.d * (D.graph.n - D.k) ≤ D.minusSlots := by
  calc
    D.d * (D.graph.n - D.k) ≤ D.d * D.graph.n :=
      Nat.mul_le_mul_left D.d (Nat.sub_le _ _)
    _ ≤ D.minusSlots := by
      simpa [minusSlots, Nat.mul_comm] using
        Nat.mul_le_mul_left D.graph.n D.d_le_tMinus

theorem up_species_total (hk : D.k ≤ D.graph.n) :
    D.globalStock (.up true) + D.globalStock (.up false) = D.plusSlots := by
  dsimp [globalStock]
  exact Nat.add_sub_of_le (D.unitPlus_le_stock hk)

theorem um_species_total :
    D.globalStock (.um true) + D.globalStock (.um false) = D.minusSlots := by
  dsimp [globalStock]
  exact Nat.add_sub_of_le D.unitMinus_le_stock

theorem card_globalCopy (hk : D.k ≤ D.graph.n) : Fintype.card D.GlobalCopy = D.B := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [GlobalSpecies.sum_univ]
  rw [D.up_species_total hk]
  rw [show D.plusSlots + D.globalStock (.um true) + D.globalStock (.um false) =
    D.plusSlots + D.minusSlots by rw [Nat.add_assoc, D.um_species_total]]
  simp only [globalStock, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [D.plusSlots_eq, D.B_eq, D.sum_J]
  dsimp [minusSlots, t]
  ring

theorem card_flagCopy : Fintype.card D.FlagCopy = D.B := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [FlagSpecies.sum_univ]
  dsimp [flagStock, treeFlags, jobFlags]
  rw [D.B_eq]
  ring

theorem card_roleCopies (hk : D.k ≤ D.graph.n) (r : Role) :
    Fintype.card (D.RoleCopies r) = D.B := by
  cases r with
  | x => simp [RoleCopies, Fintype.card_sigma, D.card_rowAt, B]
  | anchor => simp [RoleCopies, Fintype.card_sigma, D.card_anchorAt, B]
  | «global» => exact D.card_globalCopy hk
  | «local» => simp [RoleCopies, Fintype.card_sigma, D.card_localAt, B]
  | flag => exact D.card_flagCopy

theorem card_item (hk : D.k ≤ D.graph.n) : Fintype.card D.Item = 5 * D.B := by
  rw [Fintype.card_sigma, Role.sum_univ]
  simp only [D.card_roleCopies hk]
  omega

end InventoryData

end BinPackingGap

noncomputable section

namespace BinPackingGap
namespace InventoryData

variable (D : InventoryData)

def allJobEquiv : (Σ v : D.Vertex, D.JobCopy v) ≃
    ((D.Edge × Fin 2) × Fin D.R) × Fin D.d where
  toFun j := ((j.2.1.1.val, j.2.1.2), j.2.2)
  invFun j := ⟨D.graph.endpoint j.1.1.1 j.1.1.2,
    ((⟨j.1.1, rfl⟩, j.1.2), j.2)⟩
  left_inv := by
    rintro ⟨v, ⟨⟨⟨es, hv⟩, rep⟩, copy⟩⟩
    cases hv
    rfl
  right_inv := by rintro ⟨⟨⟨edge, side⟩, rep⟩, copy⟩; rfl

def keyItem (j : Σ v : D.Vertex, D.JobCopy v) : D.Item :=
  ⟨.anchor, ⟨j.1, .inr j.2⟩⟩

def keyData : D.Item → Option (Σ v : D.Vertex, D.JobCopy v)
  | ⟨.anchor, ⟨v, .inr j⟩⟩ => some ⟨v, j⟩
  | _ => none

@[simp] theorem keyData_keyItem (j : Σ v : D.Vertex, D.JobCopy v) :
    D.keyData (D.keyItem j) = some j := by cases j; rfl

theorem keyItem_injective : Function.Injective D.keyItem := by
  intro i j h
  exact Option.some.inj (by simpa only [D.keyData_keyItem] using congrArg D.keyData h)

@[simp] theorem keyItem_role (j : Σ v : D.Vertex, D.JobCopy v) :
    D.itemRole (D.keyItem j) = .anchor := rfl

@[simp] theorem keyItem_subclass (j : Σ v : D.Vertex, D.JobCopy v) :
    D.itemSubclass (D.keyItem j) = .y := rfl

@[simp] theorem keyItem_label (j : Σ v : D.Vertex, D.JobCopy v) :
    D.itemLabel (D.keyItem j) = some j.1 := rfl

def edgeResourceItem (w : (D.Edge × Bool) × Fin (D.d * D.R)) : D.Item :=
  ⟨.«global», ⟨.edge w.1.1 w.1.2, w.2⟩⟩

def edgeResourceData : D.Item → Option ((D.Edge × Bool) × Fin (D.d * D.R))
  | ⟨.«global», ⟨.edge e permit, copy⟩⟩ => some ((e, permit), copy)
  | _ => none

@[simp] theorem edgeResourceData_edgeResourceItem
    (w : (D.Edge × Bool) × Fin (D.d * D.R)) :
    D.edgeResourceData (D.edgeResourceItem w) = some w := by cases w; rfl

theorem edgeResourceItem_injective : Function.Injective D.edgeResourceItem := by
  intro i j h
  exact Option.some.inj (by
    simpa only [D.edgeResourceData_edgeResourceItem] using congrArg D.edgeResourceData h)

def prefixJobIndex (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (j : ((Fin h × Fin 2) × Fin D.R) × Fin D.d) :
    ((D.Edge × Fin 2) × Fin D.R) × Fin D.d :=
  ((⟨⟨j.1.1.1.val, lt_of_lt_of_le j.1.1.1.isLt hle⟩, j.1.1.2⟩, j.1.2), j.2)

theorem prefixJobIndex_injective (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Function.Injective (D.prefixJobIndex h hle) := by
  intro i j hij
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · apply Fin.ext
        exact congrArg (fun x => x.1.1.1.val) hij
      · exact congrArg (fun x => x.1.1.2) hij
    · exact congrArg (fun x => x.1.2) hij
  · exact congrArg (fun x : ((D.Edge × Fin 2) × Fin D.R) × Fin D.d => x.2) hij

def earlierKeys (h : ℕ) (hle : h ≤ D.graph.edges.length) : Finset D.Item := by
  classical
  exact Finset.univ.image fun j => D.keyItem (D.allJobEquiv.symm (D.prefixJobIndex h hle j))

theorem earlierKeys_card (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierKeys h hle).card = 2 * D.d * D.R * h := by
  classical
  have hinj : Function.Injective (fun j : ((Fin h × Fin 2) × Fin D.R) × Fin D.d =>
      D.keyItem (D.allJobEquiv.symm (D.prefixJobIndex h hle j))) := by
    intro i j hij
    exact D.prefixJobIndex_injective h hle
      (D.allJobEquiv.symm.injective (D.keyItem_injective hij))
  rw [earlierKeys, Finset.card_image_of_injective _ hinj]
  simp [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm]

theorem mem_earlierKeys (h : ℕ) (hle : h ≤ D.graph.edges.length) (i : D.Item) :
    i ∈ D.earlierKeys h hle ↔
      ∃ j : Σ v : D.Vertex, D.JobCopy v,
        D.keyItem j = i ∧ (D.jobPosition j.2).1.val < h := by
  classical
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨D.allJobEquiv.symm (D.prefixJobIndex h hle j), rfl, j.1.1.1.isLt⟩
  · rintro ⟨j, rfl, hj⟩
    let a := D.allJobEquiv j
    let x : ((Fin h × Fin 2) × Fin D.R) × Fin D.d :=
      ((⟨⟨a.1.1.1.val, hj⟩, a.1.1.2⟩, a.1.2), a.2)
    have hx : D.prefixJobIndex h hle x = a := by
      apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext
          · apply Fin.ext; rfl
          · rfl
        · rfl
      · rfl
    refine Finset.mem_image.mpr ⟨x, Finset.mem_univ _, ?_⟩
    rw [hx]
    exact congrArg D.keyItem (D.allJobEquiv.symm_apply_apply j)

def prefixWIndex (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (w : (Fin h × Bool) × Fin (D.d * D.R)) :
    (D.Edge × Bool) × Fin (D.d * D.R) :=
  ((⟨w.1.1.val, lt_of_lt_of_le w.1.1.isLt hle⟩, w.1.2), w.2)

theorem prefixWIndex_injective (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Function.Injective (D.prefixWIndex h hle) := by
  intro i j hij
  apply Prod.ext
  · apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun x => x.1.1.val) hij
    · exact congrArg (fun x => x.1.2) hij
  · exact congrArg (fun x : (D.Edge × Bool) × Fin (D.d * D.R) => x.2) hij

def earlierW (h : ℕ) (hle : h ≤ D.graph.edges.length) : Finset D.Item := by
  classical
  exact Finset.univ.image fun w => D.edgeResourceItem (D.prefixWIndex h hle w)

theorem earlierW_card (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierW h hle).card = 2 * D.d * D.R * h := by
  classical
  have hinj : Function.Injective (fun w : (Fin h × Bool) × Fin (D.d * D.R) =>
      D.edgeResourceItem (D.prefixWIndex h hle w)) := by
    intro i j hij
    exact D.prefixWIndex_injective h hle (D.edgeResourceItem_injective hij)
  rw [earlierW, Finset.card_image_of_injective _ hinj]
  simp [Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem mem_earlierW (h : ℕ) (hle : h ≤ D.graph.edges.length) (i : D.Item) :
    i ∈ D.earlierW h hle ↔
      ∃ w : (D.Edge × Bool) × Fin (D.d * D.R),
        D.edgeResourceItem w = i ∧ w.1.1.val < h := by
  classical
  constructor
  · intro hi
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨D.prefixWIndex h hle w, rfl, w.1.1.isLt⟩
  · rintro ⟨w, rfl, hw⟩
    let x : (Fin h × Bool) × Fin (D.d * D.R) :=
      ((⟨w.1.1.val, hw⟩, w.1.2), w.2)
    have hx : D.prefixWIndex h hle x = w := by
      apply Prod.ext
      · apply Prod.ext
        · apply Fin.ext; rfl
        · rfl
      · rfl
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, congrArg D.edgeResourceItem hx⟩

theorem earlierW_card_eq_keys (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierW h hle).card = (D.earlierKeys h hle).card := by
  rw [D.earlierW_card, D.earlierKeys_card]

end InventoryData
end BinPackingGap

end

namespace BinPackingGap

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

private theorem subclassCount_by_role (subclass : Subclass) :
    subclassCount D.itemSubclass subclass =
      ∑ i : D.RoleCopies subclass.role,
        subclassIndicator (D.itemSubclass ⟨subclass.role, i⟩) subclass := by
  classical
  unfold subclassCount
  rw [Fintype.sum_sigma]
  refine Finset.sum_eq_single subclass.role ?_ ?_
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro i _
    apply ite_eq_right
    intro hi
    apply hr
    calc
      r = (D.itemSubclass ⟨r, i⟩).role := (D.itemSubclass_role ⟨r, i⟩).symm
      _ = subclass.role := congrArg Subclass.role hi
  · simp

theorem roleCount_itemSubclass (hk : D.k ≤ D.graph.n) (r : Role) :
    roleCount D.itemSubclass r = (D.B : ℤ) := by
  classical
  simp only [roleCount, D.itemSubclass_role, itemRole, Fintype.sum_sigma]
  have hrole : (∑ s : Role, ∑ _ : D.RoleCopies s,
      if s = r then (1 : ℤ) else 0) = (Fintype.card (D.RoleCopies r) : ℤ) := by
    simp
  rw [hrole, D.card_roleCopies hk]

theorem subclassCount_tp :
    subclassCount D.itemSubclass .tp = D.graph.n * (D.tPlus : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.RowAt v), subclassIndicator (D.itemSubclass ⟨.x, i⟩) .tp) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, rowSubclass, TreeRow, treeSubclass, subclassIndicator,
    Fintype.sum_sum_type, tPlus, Nat.cast_add, Nat.cast_mul, mul_add,
    mul_comm, mul_left_comm]

theorem subclassCount_tm :
    subclassCount D.itemSubclass .tm = D.graph.n * (D.tMinus : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.RowAt v), subclassIndicator (D.itemSubclass ⟨.x, i⟩) .tm) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, rowSubclass, TreeRow, treeSubclass, subclassIndicator,
    Fintype.sum_sum_type, tMinus, Nat.cast_mul, mul_comm, mul_left_comm]

theorem subclassCount_s :
    subclassCount D.itemSubclass .s = 2 * ∑ v : D.Vertex, (D.J v : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.RowAt v), subclassIndicator (D.itemSubclass ⟨.x, i⟩) .s) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, rowSubclass, TreeRow, treeSubclass, subclassIndicator,
    Fintype.sum_sum_type, D.card_jobCopy, Finset.mul_sum, mul_comm]

theorem subclassCount_z :
    subclassCount D.itemSubclass .z = ∑ v : D.Vertex, ((D.t + D.J v : ℕ) : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.AnchorAt v), subclassIndicator (D.itemSubclass ⟨.anchor, i⟩) .z) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sum_type, D.card_mBase]

theorem subclassCount_y :
    subclassCount D.itemSubclass .y = ∑ v : D.Vertex, (D.J v : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.AnchorAt v), subclassIndicator (D.itemSubclass ⟨.anchor, i⟩) .y) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sum_type, D.card_jobCopy]

theorem subclassCount_up (hk : D.k ≤ D.graph.n) :
    subclassCount D.itemSubclass .up = (D.plusSlots : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : GlobalSpecies D.graph, Fin (D.globalStock t)), subclassIndicator (D.itemSubclass ⟨.«global», i⟩) .up) = _
  rw [Fintype.sum_sigma]
  have h := congrArg (fun x : ℕ => (x : ℤ)) (D.up_species_total hk)
  simpa [subclassCount, itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sigma, Role.sum_univ, GlobalSpecies.sum_univ,
    Fintype.sum_sum_type] using h

theorem subclassCount_um :
    subclassCount D.itemSubclass .um = (D.minusSlots : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : GlobalSpecies D.graph, Fin (D.globalStock t)), subclassIndicator (D.itemSubclass ⟨.«global», i⟩) .um) = _
  rw [Fintype.sum_sigma]
  have h := congrArg (fun x : ℕ => (x : ℤ)) D.um_species_total
  simpa [subclassCount, itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sigma, Role.sum_univ, GlobalSpecies.sum_univ,
    Fintype.sum_sum_type] using h

theorem subclassCount_dm :
    subclassCount D.itemSubclass .dm = ∑ v : D.Vertex, ((D.t + D.J v : ℕ) : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.LocalAt v), subclassIndicator (D.itemSubclass ⟨.«local», i⟩) .dm) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sum_type, D.card_dmAt]

theorem subclassCount_dg :
    subclassCount D.itemSubclass .dg = ∑ v : D.Vertex, (D.J v : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ v : D.Vertex, D.LocalAt v), subclassIndicator (D.itemSubclass ⟨.«local», i⟩) .dg) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator,
    Fintype.sum_sum_type, D.card_jobCopy]

theorem subclassCount_ft :
    subclassCount D.itemSubclass .ft = (D.treeFlags : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : FlagSpecies, Fin (D.flagStock t)), subclassIndicator (D.itemSubclass ⟨.flag, i⟩) .ft) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator, FlagSpecies.sum_univ, flagStock]
  change Fintype.card (Fin D.treeFlags) = D.treeFlags
  exact Fintype.card_fin _

theorem subclassCount_fm :
    subclassCount D.itemSubclass .fm = (D.jobFlags : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : FlagSpecies, Fin (D.flagStock t)), subclassIndicator (D.itemSubclass ⟨.flag, i⟩) .fm) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator, FlagSpecies.sum_univ, flagStock]
  change Fintype.card (Fin D.jobFlags) = D.jobFlags
  exact Fintype.card_fin _

theorem subclassCount_fg :
    subclassCount D.itemSubclass .fg = (D.jobFlags : ℤ) := by
  classical
  rw [D.subclassCount_by_role]
  change (∑ i : (Σ t : FlagSpecies, Fin (D.flagStock t)), subclassIndicator (D.itemSubclass ⟨.flag, i⟩) .fg) = _
  rw [Fintype.sum_sigma]
  simp [itemSubclass, RoleCopies, subclassIndicator, FlagSpecies.sum_univ, flagStock]
  change Fintype.card (Fin D.jobFlags) = D.jobFlags
  exact Fintype.card_fin _

theorem total_primaryScore_eq_zero (hk : D.k ≤ D.graph.n) :
    (∑ i : D.Item, primaryScore (D.itemSubclass i)) = 0 := by
  apply sum_primaryScore_eq_zero_of_inventory D.itemSubclass D.B
    (D.card_item hk) (D.roleCount_itemSubclass hk)
  · rw [D.subclassCount_tp, D.subclassCount_tm, D.subclassCount_ft]
    simp [treeFlags, t, Nat.cast_mul, Nat.cast_add, mul_add]
  · rw [D.subclassCount_z, D.subclassCount_ft, D.subclassCount_fm]
    simp [treeFlags, jobFlags, Nat.cast_mul, Nat.cast_sum, Nat.cast_add,
      Finset.sum_add_distrib]
  · rw [D.subclassCount_up hk, D.subclassCount_um, D.subclassCount_ft,
      D.subclassCount_fm, D.plusSlots_eq]
    simp [minusSlots, treeFlags, jobFlags, t, Nat.cast_mul, Nat.cast_add,
      Nat.cast_sum, mul_add]
    ring
  · rw [D.subclassCount_dm, D.subclassCount_ft, D.subclassCount_fm]
    simp [treeFlags, jobFlags, Nat.cast_mul, Nat.cast_sum, Nat.cast_add,
      Finset.sum_add_distrib]
  · rw [D.subclassCount_tm, D.subclassCount_um]
    simp [minusSlots]

theorem labelledRoleCount_x (v : D.Vertex) :
    labelledRoleCount D.itemSubclass D.itemLabel .x v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  classical
  unfold labelledRoleCount
  simp_rw [D.itemSubclass_role]
  rw [Fintype.sum_sigma, Role.sum_univ]
  simp only [itemRole, RoleCopies, Fintype.sum_sigma]
  simp [itemLabel, D.card_rowAt]

theorem labelledRoleCount_anchor (v : D.Vertex) :
    labelledRoleCount D.itemSubclass D.itemLabel .anchor v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  classical
  unfold labelledRoleCount
  simp_rw [D.itemSubclass_role]
  rw [Fintype.sum_sigma, Role.sum_univ]
  simp only [itemRole, RoleCopies, Fintype.sum_sigma]
  simp [itemLabel, D.card_anchorAt]

theorem labelledRoleCount_local (v : D.Vertex) :
    labelledRoleCount D.itemSubclass D.itemLabel .«local» v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  classical
  unfold labelledRoleCount
  simp_rw [D.itemSubclass_role]
  rw [Fintype.sum_sigma, Role.sum_univ]
  simp only [itemRole, RoleCopies, Fintype.sum_sigma]
  simp [itemLabel, D.card_localAt]

theorem total_secondaryScore_eq_zero :
    (∑ i : D.Item, secondaryScore (D.itemSubclass i) (D.itemLabel i)) = 0 := by
  apply sum_secondaryScore_eq_zero_of_inventory D.itemSubclass D.itemLabel
  · intro v
    rw [D.labelledRoleCount_x, D.labelledRoleCount_anchor]
  · intro v
    rw [D.labelledRoleCount_local, D.labelledRoleCount_anchor]

end InventoryData

end BinPackingGap

end OAI


