-- Prove2me | Definitions.Def_OAI_BinPackingGap_Part04
-- name    : OAI_BinPackingGap_Part04
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T18:17:28.346991+00:00
-- url     : https://prove2.me/theorems/620ebf43-5baa-4974-9ffc-d95c4a9ab471
-- title:
--   Structural additive gap for bin packing, part 4 of 10 (port of OpenAI's formalization)
-- statement:
--   Part 4 of 10 of a port of OpenAI's Lean formalization of the structural additive gap from the manuscript *Additive hardness and unbounded configuration gaps in bin packing* (OpenAI, September 24, 2026). For every $c$, it constructs an instance with $5B$ items of sizes in $(1/6,1)$ whose individual and type configuration LPs both equal $B$, while the optimum exceeds $B+c$. This part contains the modules `Inventory/LabelConservation`, `Packing/GoodAnchorBound`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/BinPacking`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `BinPackingGap`, which matches upstream `Model.lean` up to two private lemmas and a section wrapper.
--
--   The development is split into 10 parts only so that each compiles within the platform's time limit. The final part proves `OAI.BinPackingGap.structural_additive_gap`, the first clause of `OAI.BinPackingGap.main_results`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/BinPacking: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Inventory/LabelConservation.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/GoodAnchorBound.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf

/-
Structural additive gap for bin packing (port of OpenAI's formalization), part 4 of 10.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/BinPacking/: Inventory/LabelConservation.lean, Packing/GoodAnchorBound.lean
These files formalize part of the manuscript "Additive hardness and unbounded configuration gaps in
bin packing" (OpenAI, September 24, 2026). Copyright OpenAI. Licensed under the Apache License,
Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same
license, on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Model.lean) come from the platform definition `BinPackingGap`, to which upstream Model.lean
is identical up to two private lemmas and a section wrapper.
-/
import Mathlib
import Definitions.Def_OAI_BinPackingGap_Part03

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/BinPacking/Inventory/LabelConservation.lean =====
namespace OAI

namespace BinPackingGap
namespace FinitePrefixConservation

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem remaining_eq_bad (keys good : Finset α) (resources : Finset β)
    (f : α → β) (hgood : good ⊆ keys)
    (hmap : ∀ x ∈ good, f x ∈ resources)
    (hinj : Set.InjOn f (good : Set α))
    (hcard : resources.card = keys.card) :
    (resources \ good.image f).card = (keys \ good).card := by
  have himage : good.image f ⊆ resources := Finset.image_subset_iff.mpr hmap
  rw [Finset.card_sdiff_of_subset himage, Finset.card_sdiff_of_subset hgood,
    Finset.card_image_of_injOn hinj, hcard]

theorem remaining_le_bad (keys good : Finset α) (resources remaining : Finset β)
    (f : α → β) (hgood : good ⊆ keys)
    (hmap : ∀ x ∈ good, f x ∈ resources)
    (hinj : Set.InjOn f (good : Set α))
    (hcard : resources.card = keys.card)
    (hremaining : remaining ⊆ resources \ good.image f) :
    remaining.card ≤ (keys \ good).card := by
  calc
    remaining.card ≤ (resources \ good.image f).card := Finset.card_le_card hremaining
    _ = (keys \ good).card := remaining_eq_bad keys good resources f hgood hmap hinj hcard

end FinitePrefixConservation

namespace LabelConservation

open scoped BigOperators

variable {n : ℕ}
variable {T A R D : Type*}
variable [Fintype T] [Fintype A] [Fintype R] [Fintype D]
variable [DecidableEq A] [DecidableEq R] [DecidableEq D]

def outsideItems (f : T → A) : Finset A := Finset.univ \ Finset.univ.image f

def prefixItems (label : A → Fin n) (h : ℕ) : Finset A :=
  Finset.univ.filter fun x => (label x).val < h

def prefixOutside (label : A → Fin n) (f : T → A) (h : ℕ) : Finset A :=
  (outsideItems f).filter fun x => (label x).val < h

def exports (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R) (h : ℕ) : Finset T :=
  Finset.univ.filter fun t =>
    (labelR (role t)).val < h ∧ ¬ (labelA (anchor t)).val < h

def labelDefects (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R) (v : Fin n) : Finset T :=
  Finset.univ.filter fun t => labelA (anchor t) = v ∧ labelR (role t) ≠ v

omit [DecidableEq A] in
@[simp] theorem prefixItems_zero (label : A → Fin n) : prefixItems label 0 = ∅ := by
  simp [prefixItems]

@[simp] theorem prefixOutside_zero (label : A → Fin n) (f : T → A) :
    prefixOutside label f 0 = ∅ := by
  simp [prefixOutside]

omit [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] in
@[simp] theorem exports_zero (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R) : exports labelA labelR anchor role 0 = ∅ := by
  simp [exports]

omit [DecidableEq A] [DecidableEq R] in
theorem prefix_inventory_eq (labelA : A → Fin n) (labelR : R → Fin n)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (h : ℕ) :
    (prefixItems labelA h).card = (prefixItems labelR h).card := by
  let labels : Finset (Fin n) := Finset.univ.filter fun v => v.val < h
  have hA := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset A)
    labels labelA
  have hR := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset R)
    labels labelR
  have hsum : (∑ v ∈ labels, (Finset.univ.filter fun a => labelA a = v).card) =
      ∑ v ∈ labels, (Finset.univ.filter fun r => labelR r = v).card := by
    exact Finset.sum_congr rfl fun v _ => hInv v
  simpa only [labels, Finset.mem_filter, Finset.mem_univ, true_and, prefixItems]
    using hA.symm.trans (hsum.trans hR)

theorem outside_add_selected_eq (label : A → Fin n) (f : T → A)
    (hf : Function.Injective f) (h : ℕ) :
    (prefixOutside label f h).card + (prefixItems (label ∘ f) h).card =
      (prefixItems label h).card := by
  have hsplit := Finset.card_sdiff_add_card_inter
    (prefixItems label h) (Finset.univ.image f)
  have hout : prefixItems label h \ Finset.univ.image f = prefixOutside label f h := by
    ext x
    simp [prefixItems, prefixOutside, outsideItems, and_comm]
  have hin : prefixItems label h ∩ Finset.univ.image f =
      (Finset.univ.image f).filter (fun x => (label x).val < h) := by
    ext x
    simp [prefixItems, and_comm]
  rw [hout, hin, Finset.filter_image, Finset.card_image_of_injective _ hf] at hsplit
  simpa only [prefixItems, Function.comp_apply] using hsplit

omit [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] in
theorem selected_add_exports_eq (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val) (h : ℕ) :
    (prefixItems (labelA ∘ anchor) h).card + (exports labelA labelR anchor role h).card =
      (prefixItems (labelR ∘ role) h).card := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := prefixItems (labelR ∘ role) h) (fun t => (labelA (anchor t)).val < h)
  have hin : (prefixItems (labelR ∘ role) h).filter
      (fun t => (labelA (anchor t)).val < h) = prefixItems (labelA ∘ anchor) h := by
    ext t
    simp only [Finset.mem_filter, prefixItems, Finset.mem_univ, true_and,
      Function.comp_apply]
    exact ⟨fun ht => ht.2, fun ht => ⟨lt_of_le_of_lt (hle t) ht, ht⟩⟩
  have hout : (prefixItems (labelR ∘ role) h).filter
      (fun t => ¬ (labelA (anchor t)).val < h) = exports labelA labelR anchor role h := by
    ext t
    simp [prefixItems, exports]
  rw [hin, hout] at hsplit
  exact hsplit

theorem exports_add_outsideRole_eq_outsideAnchor
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (h : ℕ) :
    (exports labelA labelR anchor role h).card + (prefixOutside labelR role h).card =
      (prefixOutside labelA anchor h).card := by
  have hA := outside_add_selected_eq labelA anchor hAnchor h
  have hR := outside_add_selected_eq labelR role hRole h
  have hE := selected_add_exports_eq labelA labelR anchor role hle h
  have hI := prefix_inventory_eq labelA labelR hInv h
  omega

theorem exports_eq_outside_sub
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (h : ℕ) :
    ((exports labelA labelR anchor role h).card : ℤ) =
      (prefixOutside labelA anchor h).card - (prefixOutside labelR role h).card := by
  have hcon := exports_add_outsideRole_eq_outsideAnchor
    labelA labelR anchor role hAnchor hRole hle hInv h
  omega

theorem exports_card_le_outside
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (h : ℕ) :
    (exports labelA labelR anchor role h).card ≤ (outsideItems anchor).card := by
  have hcon := exports_add_outsideRole_eq_outsideAnchor
    labelA labelR anchor role hAnchor hRole hle hInv h
  have hout : (prefixOutside labelA anchor h).card ≤ (outsideItems anchor).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

omit [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] in
theorem labelDefects_subset_exports
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val) (v : Fin n) :
    labelDefects labelA labelR anchor role v ⊆ exports labelA labelR anchor role v.val := by
  intro t ht
  obtain ⟨ha, hr⟩ := (Finset.mem_filter.mp ht).2
  have hl := hle t
  rw [ha] at hl
  have hn : (labelR (role t)).val ≠ v.val := fun he => hr (Fin.ext he)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · omega
  · simp [ha]

theorem labelDefects_card_le_outside
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (v : Fin n) :
    (labelDefects labelA labelR anchor role v).card ≤ (outsideItems anchor).card := by
  exact (Finset.card_le_card (labelDefects_subset_exports labelA labelR anchor role hle v)).trans
    (exports_card_le_outside labelA labelR anchor role hAnchor hRole hle hInv v.val)

def badAnchors (labelA : A → Fin n) (labelR : R → Fin n) (labelD : D → Fin n)
    (anchor : T → A) (role : T → R) (localRole : T → D) (v : Fin n) : Finset A :=
  ((outsideItems anchor).filter fun a => labelA a = v) ∪
    (labelDefects labelA labelR anchor role v).image anchor ∪
    (labelDefects labelA labelD anchor localRole v).image anchor

omit [Fintype R] [Fintype D] [DecidableEq R] [DecidableEq D] in
theorem mem_badAnchors_iff
    (labelA : A → Fin n) (labelR : R → Fin n) (labelD : D → Fin n)
    (anchor : T → A) (role : T → R) (localRole : T → D)
    (hAnchor : Function.Injective anchor) (v : Fin n) (a : A) :
    a ∈ badAnchors labelA labelR labelD anchor role localRole v ↔
      labelA a = v ∧
        ¬ ∃ t, anchor t = a ∧ labelR (role t) = v ∧ labelD (localRole t) = v := by
  constructor
  · intro hbad
    rcases Finset.mem_union.mp hbad with hleft | hd
    · rcases Finset.mem_union.mp hleft with ho | hr
      · obtain ⟨hoa, hv⟩ := Finset.mem_filter.mp ho
        refine ⟨hv, ?_⟩
        rintro ⟨t, hat, _, _⟩
        exact (Finset.mem_sdiff.mp hoa).2
          (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, hat⟩)
      · obtain ⟨t, ht, hat⟩ := Finset.mem_image.mp hr
        obtain ⟨hva, hvr⟩ := (Finset.mem_filter.mp ht).2
        refine ⟨by simpa only [hat] using hva, ?_⟩
        rintro ⟨u, hua, hur, _⟩
        have htu : t = u := hAnchor (hat.trans hua.symm)
        exact hvr (by simpa only [htu] using hur)
    · obtain ⟨t, ht, hat⟩ := Finset.mem_image.mp hd
      obtain ⟨hva, hvd⟩ := (Finset.mem_filter.mp ht).2
      refine ⟨by simpa only [hat] using hva, ?_⟩
      rintro ⟨u, hua, _, hud⟩
      have htu : t = u := hAnchor (hat.trans hua.symm)
      exact hvd (by simpa only [htu] using hud)
  · rintro ⟨hv, hnot⟩
    by_cases ha : a ∈ Finset.univ.image anchor
    · obtain ⟨t, _, hat⟩ := Finset.mem_image.mp ha
      have htv : labelA (anchor t) = v := by simpa only [hat] using hv
      by_cases hr : labelR (role t) = v
      · have hd : labelD (localRole t) ≠ v := fun hd => hnot ⟨t, hat, hr, hd⟩
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, htv, hd⟩, hat⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, htv, hr⟩, hat⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩, hv⟩

theorem badAnchors_card_le_three_mul
    (labelA : A → Fin n) (labelR : R → Fin n) (labelD : D → Fin n)
    (anchor : T → A) (role : T → R) (localRole : T → D)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hLocal : Function.Injective localRole)
    (hleR : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hleD : ∀ t, (labelD (localRole t)).val ≤ (labelA (anchor t)).val)
    (hInvR : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card)
    (hInvD : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun d => labelD d = v).card)
    (K : ℕ) (hOutside : (outsideItems anchor).card ≤ K) (v : Fin n) :
    (badAnchors labelA labelR labelD anchor role localRole v).card ≤ 3 * K := by
  have hR := labelDefects_card_le_outside labelA labelR anchor role hAnchor hRole hleR hInvR v
  have hD := labelDefects_card_le_outside labelA labelD anchor localRole
    hAnchor hLocal hleD hInvD v
  have hO : ((outsideItems anchor).filter fun a => labelA a = v).card ≤
      (outsideItems anchor).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hRi := Finset.card_image_le (s := labelDefects labelA labelR anchor role v) (f := anchor)
  have hDi := Finset.card_image_le (s := labelDefects labelA labelD anchor localRole v)
    (f := anchor)
  have hU := Finset.card_union_le
    ((outsideItems anchor).filter fun a => labelA a = v)
    ((labelDefects labelA labelR anchor role v).image anchor)
  have hV := Finset.card_union_le
    (((outsideItems anchor).filter fun a => labelA a = v) ∪
      (labelDefects labelA labelR anchor role v).image anchor)
    ((labelDefects labelA labelD anchor localRole v).image anchor)
  unfold badAnchors
  omega

end LabelConservation
end BinPackingGap

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/GoodAnchorBound.lean =====
namespace OAI

noncomputable section

namespace BinPackingGap

open scoped BigOperators

variable {I : Instance} {b n : ℕ}

abbrev RoleItem (cls : I.Item → Subclass) (r : Role) :=
  {i : I.Item // (cls i).role = r}

theorem roleItem_label_count (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (r : Role)
    (roleLabel : RoleItem cls r → Fin n)
    (hspec : ∀ i, label i.val = some (roleLabel i)) (v : Fin n) :
    ((Finset.univ.filter fun i => roleLabel i = v).card : ℤ) =
      labelledRoleCount cls label r v := by
  classical
  have himage : (Finset.univ.filter fun i => roleLabel i = v).image Subtype.val =
      Finset.univ.filter (fun i => (cls i).role = r ∧ label i = some v) := by
    ext i
    constructor
    · intro hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      have hv := (Finset.mem_filter.mp ha).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.property,
        (hspec a).trans (congrArg some hv)⟩
    · intro hi
      obtain ⟨hr, hv⟩ := (Finset.mem_filter.mp hi).2
      let a : RoleItem cls r := ⟨i, hr⟩
      have ha : roleLabel a = v := Option.some.inj ((hspec a).symm.trans hv)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
  have hcard : (Finset.univ.filter fun i => roleLabel i = v).card =
      (Finset.univ.filter fun i => (cls i).role = r ∧ label i = some v).card := by
    rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  rw [hcard]
  simp [labelledRoleCount]

structure RoleLabelData (cls : I.Item → Subclass) (label : I.Item → Option (Fin n)) where
  row : RoleItem cls .x → Fin n
  anchor : RoleItem cls .anchor → Fin n
  localLabel : RoleItem cls .«local» → Fin n
  row_spec : ∀ i, label i.val = some (row i)
  anchor_spec : ∀ i, label i.val = some (anchor i)
  local_spec : ∀ i, label i.val = some (localLabel i)
  global_spec : ∀ i : RoleItem cls .«global», label i.val = none
  flag_spec : ∀ i : RoleItem cls .flag, label i.val = none

namespace RoleLabelData

theorem row_count {cls : I.Item → Subclass} {label : I.Item → Option (Fin n)}
    (L : RoleLabelData cls label) (v : Fin n) :
    ((Finset.univ.filter fun i => L.row i = v).card : ℤ) =
      labelledRoleCount cls label .x v :=
  roleItem_label_count cls label .x L.row L.row_spec v

theorem anchor_count {cls : I.Item → Subclass} {label : I.Item → Option (Fin n)}
    (L : RoleLabelData cls label) (v : Fin n) :
    ((Finset.univ.filter fun i => L.anchor i = v).card : ℤ) =
      labelledRoleCount cls label .anchor v :=
  roleItem_label_count cls label .anchor L.anchor L.anchor_spec v

theorem local_count {cls : I.Item → Subclass} {label : I.Item → Option (Fin n)}
    (L : RoleLabelData cls label) (v : Fin n) :
    ((Finset.univ.filter fun i => L.localLabel i = v).card : ℤ) =
      labelledRoleCount cls label .«local» v :=
  roleItem_label_count cls label .«local» L.localLabel L.local_spec v

def of_valid (cls : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (hlabeled : ∀ i, (cls i).role = .x ∨ (cls i).role = .anchor ∨
      (cls i).role = .«local» → ∃ v, label i = some v)
    (hunlabeled : ∀ i, (cls i).role = .«global» ∨ (cls i).role = .flag →
      label i = none) : RoleLabelData cls label where
  row i := Classical.choose (hlabeled i.val (Or.inl i.property))
  anchor i := Classical.choose (hlabeled i.val (Or.inr (Or.inl i.property)))
  localLabel i := Classical.choose (hlabeled i.val (Or.inr (Or.inr i.property)))
  row_spec i := Classical.choose_spec (hlabeled i.val (Or.inl i.property))
  anchor_spec i := Classical.choose_spec (hlabeled i.val (Or.inr (Or.inl i.property)))
  local_spec i := Classical.choose_spec (hlabeled i.val (Or.inr (Or.inr i.property)))
  global_spec i := hunlabeled i.val (Or.inl i.property)
  flag_spec i := hunlabeled i.val (Or.inr i.property)

end RoleLabelData

namespace Packing

def roleItemAt (p : Packing I b) (cls : I.Item → Subclass) (r : Role)
    (t : p.TableBin cls) : RoleItem cls r :=
  ⟨p.itemAtRole cls t r, p.itemAtRole_role cls t r⟩

theorem roleItemAt_injective (p : Packing I b) (cls : I.Item → Subclass) (r : Role) :
    Function.Injective (p.roleItemAt cls r) := by
  intro t u h
  exact p.itemAtRole_injective cls r (congrArg Subtype.val h)

theorem roleItemAt_labels (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
    (t : p.TableBin cls) (r : Role) :
    label (p.itemAtRole cls t r) = tableRoleLabel
      (L.row (p.roleItemAt cls .x t))
      (L.localLabel (p.roleItemAt cls .«local» t))
      (L.anchor (p.roleItemAt cls .anchor t)) r := by
  cases r with
  | x => exact L.row_spec (p.roleItemAt cls .x t)
  | anchor => exact L.anchor_spec (p.roleItemAt cls .anchor t)
  | «global» => exact L.global_spec (p.roleItemAt cls .«global» t)
  | «local» => exact L.local_spec (p.roleItemAt cls .«local» t)
  | flag => exact L.flag_spec (p.roleItemAt cls .flag t)

theorem roleItemAt_labels_le (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (cls i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6) (t : p.TableBin cls) :
    L.row (p.roleItemAt cls .x t) ≤ L.anchor (p.roleItemAt cls .anchor t) ∧
      L.localLabel (p.roleItemAt cls .«local» t) ≤ L.anchor (p.roleItemAt cls .anchor t) :=
  p.table_labels_le_anchor cls label coordinate hsize hw t _ _ _
    (p.roleItemAt_labels cls label L t)

theorem outside_roleItems_image_subset (p : Packing I b) (cls : I.Item → Subclass)
    (r : Role) :
    (LabelConservation.outsideItems (p.roleItemAt cls r)).image Subtype.val ⊆
      p.outsideTableItems cls := by
  classical
  intro i hi
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro ht
  have haout := (Finset.mem_sdiff.mp ha).2
  apply haout
  let t : p.TableBin cls := ⟨p.assignment a.val, ht⟩
  refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  exact p.itemAtRole_eq_of_mem cls t r a.val (p.mem_own_bin a.val) a.property

theorem outside_roleItems_card_le (p : Packing I b) (cls : I.Item → Subclass) (r : Role) :
    (LabelConservation.outsideItems (p.roleItemAt cls r)).card ≤
      (p.outsideTableItems cls).card := by
  classical
  rw [← Finset.card_image_of_injective
    (LabelConservation.outsideItems (p.roleItemAt cls r)) Subtype.val_injective]
  exact Finset.card_le_card (p.outside_roleItems_image_subset cls r)

end Packing

namespace Coverage

theorem goodTuplesAt_iff_roleLabels (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
    (v : Fin n) (t : p.TableBin cls) :
    t ∈ goodTuplesAt p cls label v ↔
      L.anchor (p.roleItemAt cls .anchor t) = v ∧
        L.row (p.roleItemAt cls .x t) = v ∧
          L.localLabel (p.roleItemAt cls .«local» t) = v := by
  rw [mem_goodTuplesAt]
  have hx := L.row_spec (p.roleItemAt cls .x t)
  have ha := L.anchor_spec (p.roleItemAt cls .anchor t)
  have hd := L.local_spec (p.roleItemAt cls .«local» t)
  change label (p.itemAtRole cls t .x) = some _ at hx
  change label (p.itemAtRole cls t .anchor) = some _ at ha
  change label (p.itemAtRole cls t .«local») = some _ at hd
  simp only [Packing.IsGoodTableBin, hx, ha, hd, Option.some.injEq]
  constructor
  · rintro ⟨⟨hr, hl⟩, hv⟩
    exact ⟨hv, hr.trans hv, hl.trans hv⟩
  · rintro ⟨hv, hr, hl⟩
    exact ⟨⟨hr.trans hv.symm, hl.trans hv.symm⟩, hv⟩

def badRoleAnchors (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label) (v : Fin n) :
    Finset (RoleItem cls .anchor) := by
  classical
  exact LabelConservation.badAnchors L.anchor L.row L.localLabel
    (p.roleItemAt cls .anchor) (p.roleItemAt cls .x) (p.roleItemAt cls .«local») v

theorem mem_badRoleAnchors (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
    (v : Fin n) (a : RoleItem cls .anchor) :
    a ∈ badRoleAnchors p cls label L v ↔ L.anchor a = v ∧
      ¬ ∃ t, p.roleItemAt cls .anchor t = a ∧
        L.row (p.roleItemAt cls .x t) = v ∧
          L.localLabel (p.roleItemAt cls .«local» t) = v := by
  classical
  exact LabelConservation.mem_badAnchors_iff L.anchor L.row L.localLabel
    (p.roleItemAt cls .anchor) (p.roleItemAt cls .x) (p.roleItemAt cls .«local»)
    (p.roleItemAt_injective cls .anchor) v a

theorem badRoleAnchors_image_eq (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label) (v : Fin n) :
    (badRoleAnchors p cls label L v).image Subtype.val = badAnchorsAt p cls label v := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hv, hnot⟩ := (mem_badRoleAnchors p cls label L v a).mp ha
    apply (mem_badAnchorsAt p cls label v a.val).mpr
    refine ⟨(mem_anchorItemsAt cls label v a.val).mpr ⟨a.property, ?_⟩, ?_⟩
    · rw [L.anchor_spec, hv]
    · intro hgood
      obtain ⟨t, ht, hat⟩ := Finset.mem_image.mp hgood
      obtain ⟨_, hr, hd⟩ := (goodTuplesAt_iff_roleLabels p cls label L v t).mp ht
      exact hnot ⟨t, Subtype.ext hat, hr, hd⟩
  · intro hi
    obtain ⟨hiA, hiBad⟩ := (mem_badAnchorsAt p cls label v i).mp hi
    obtain ⟨hr, hv⟩ := (mem_anchorItemsAt cls label v i).mp hiA
    let a : RoleItem cls .anchor := ⟨i, hr⟩
    have hva : L.anchor a = v := Option.some.inj ((L.anchor_spec a).symm.trans hv)
    refine Finset.mem_image.mpr ⟨a, ?_, rfl⟩
    apply (mem_badRoleAnchors p cls label L v a).mpr
    refine ⟨hva, ?_⟩
    rintro ⟨t, hat, hrow, hlocal⟩
    apply hiBad
    refine Finset.mem_image.mpr ⟨t, ?_, congrArg Subtype.val hat⟩
    apply (goodTuplesAt_iff_roleLabels p cls label L v t).mpr
    exact ⟨by simpa only [hat] using hva, hrow, hlocal⟩

@[simp] theorem badRoleAnchors_card (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label) (v : Fin n) :
    (badRoleAnchors p cls label L v).card = (badAnchorsAt p cls label v).card := by
  classical
  rw [← badRoleAnchors_image_eq p cls label L v,
    Finset.card_image_of_injective _ Subtype.val_injective]

variable (p : Packing I b) (cls : I.Item → Subclass)
variable (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
variable (coordinate : I.Item → ℚ)
variable (hsize : ∀ i, I.size i = encodedSize (cls i) (label i) (coordinate i))
variable (hw : ∀ i, |coordinate i| ≤ 6) (B c : ℕ)
variable (hcard : I.n = 5 * B) (hb : b ≤ B + c)
variable (htotal : (∑ i, primaryScore (cls i)) = 0)
variable (hInvR : ∀ v, (Finset.univ.filter fun a => L.anchor a = v).card =
  (Finset.univ.filter fun r => L.row r = v).card)
variable (hInvD : ∀ v, (Finset.univ.filter fun a => L.anchor a = v).card =
  (Finset.univ.filter fun d => L.localLabel d = v).card)

include L coordinate hsize hw B hcard hb htotal hInvR hInvD

theorem badAnchorsAt_card_le (v : Fin n) :
    (badAnchorsAt p cls label v).card ≤
      3 * (25 * (c + 1) * (1 + 5 * primaryBound)) := by
  classical
  have hOutside := (p.outside_roleItems_card_le cls .anchor).trans
    (p.outsideTableItems_card_lt cls label coordinate hsize hw B c hcard hb htotal).le
  have hleR (t : p.TableBin cls) :
      (L.row (p.roleItemAt cls .x t)).val ≤
        (L.anchor (p.roleItemAt cls .anchor t)).val :=
    (p.roleItemAt_labels_le cls label L coordinate hsize hw t).1
  have hleD (t : p.TableBin cls) :
      (L.localLabel (p.roleItemAt cls .«local» t)).val ≤
        (L.anchor (p.roleItemAt cls .anchor t)).val :=
    (p.roleItemAt_labels_le cls label L coordinate hsize hw t).2
  have h := LabelConservation.badAnchors_card_le_three_mul L.anchor L.row L.localLabel
    (p.roleItemAt cls .anchor) (p.roleItemAt cls .x) (p.roleItemAt cls .«local»)
    (p.roleItemAt_injective cls .anchor) (p.roleItemAt_injective cls .x)
    (p.roleItemAt_injective cls .«local») hleR hleD hInvR hInvD
    (25 * (c + 1) * (1 + 5 * primaryBound)) hOutside v
  change (badRoleAnchors p cls label L v).card ≤ _ at h
  simpa only [badRoleAnchors_card] using h

theorem badAnchorsAt_subset_card_le (v : Fin n) (s : Finset I.Item)
    (hs : s ⊆ badAnchorsAt p cls label v) :
    s.card ≤ 3 * (25 * (c + 1) * (1 + 5 * primaryBound)) :=
  (Finset.card_le_card hs).trans
    (badAnchorsAt_card_le p cls label L coordinate hsize hw B c hcard hb htotal hInvR hInvD v)

theorem anchor_subset_loss_le (v : Fin n) (s : Finset I.Item)
    (hs : s ⊆ anchorItemsAt (I := I) cls label v) :
    (s \ roleItems p cls (goodTuplesAt p cls label v) .anchor).card ≤
      3 * (25 * (c + 1) * (1 + 5 * primaryBound)) := by
  apply badAnchorsAt_subset_card_le p cls label L coordinate hsize hw B c
    hcard hb htotal hInvR hInvD v
  intro i hi
  obtain ⟨his, hin⟩ := Finset.mem_sdiff.mp hi
  exact Finset.mem_sdiff.mpr ⟨hs his, hin⟩

theorem badAnchors_global_card_le :
    ((Finset.univ : Finset (Fin n)).biUnion (badAnchorsAt p cls label)).card ≤
      3 * n * (25 * (c + 1) * (1 + 5 * primaryBound)) := by
  classical
  calc
    _ ≤ ∑ v : Fin n, (badAnchorsAt p cls label v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin n, 3 * (25 * (c + 1) * (1 + 5 * primaryBound)) := by
      apply Finset.sum_le_sum
      intro v _
      exact badAnchorsAt_card_le p cls label L coordinate hsize hw B c
        hcard hb htotal hInvR hInvD v
    _ = _ := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end Coverage
end BinPackingGap

end

end OAI


