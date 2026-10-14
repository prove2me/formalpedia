-- Prove2me | Definitions.Def_OAI_BinPackingGap_Part01
-- name    : OAI_BinPackingGap_Part01
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T18:08:26.770609+00:00
-- url     : https://prove2.me/theorems/ce6090aa-7613-4e2c-8046-038a5f61ff58
-- title:
--   Structural additive gap for bin packing, part 1 of 10 (port of OpenAI's formalization)
-- statement:
--   Part 1 of 10 of a port of OpenAI's Lean formalization of the structural additive gap from the manuscript *Additive hardness and unbounded configuration gaps in bin packing* (OpenAI, September 24, 2026). For every $c$, it constructs an instance with $5B$ items of sizes in $(1/6,1)$ whose individual and type configuration LPs both equal $B$, while the optimum exceeds $B+c$. This part contains the modules `Packing/FiniteHall`, `Packing/FractionWidth`, `Packing/PrimaryLoss`, `Packing/PackingScalar`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/BinPacking`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `BinPackingGap`, which matches upstream `Model.lean` up to two private lemmas and a section wrapper. Part 1 also adds compatibility shims restating four core lemmas (`ite_eq_left`, `ite_eq_right`, `dite_eq_left`, `dite_eq_right`) absent from Lean 4.33.1. This part also makes a small compatibility edit for Lean 4.33.1 / Mathlib 0df444a: in Packing/PackingScalar.lean, two `norm_num` calls whose remaining enum-constructor `if`s are no longer decided by `simp` are finished with `decide`.
--
--   The development is split into 10 parts only so that each compiles within the platform's time limit. The final part proves `OAI.BinPackingGap.structural_additive_gap`, the first clause of `OAI.BinPackingGap.main_results`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/BinPacking: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/FiniteHall.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/FractionWidth.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/PrimaryLoss.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/PackingScalar.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf

/-
Structural additive gap for bin packing (port of OpenAI's formalization), part 1 of 10.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/BinPacking/: Packing/FiniteHall.lean, Packing/FractionWidth.lean, Packing/PrimaryLoss.lean, Packing/PackingScalar.lean
These files formalize part of the manuscript "Additive hardness and unbounded configuration gaps in
bin packing" (OpenAI, September 24, 2026). Copyright OpenAI. Licensed under the Apache License,
Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same
license, on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Model.lean) come from the platform definition `BinPackingGap`, to which upstream Model.lean
is identical up to two private lemmas and a section wrapper; compatibility shims restating four core lemmas absent from Lean 4.33.1 are added; compatibility edits for the platform Lean/Mathlib versions: in Packing/PackingScalar.lean, two `norm_num` calls whose remaining enum-constructor `if`s are no longer decided by `simp` are finished with `decide`.
-/
import Mathlib
import Definitions.Def_BinPackingGap

set_option autoImplicit false

-- Compatibility shims: core lemmas present in the newer Lean version used upstream but not in
-- Lean 4.33.1, restated from `if_pos`, `if_neg`, `dif_pos` and `dif_neg`.
namespace OAI

theorem ite_eq_left {c : Prop} {_ : Decidable c} {α : Sort*} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h

theorem ite_eq_right {c : Prop} {_ : Decidable c} {α : Sort*} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h

theorem dite_eq_left {c : Prop} {_ : Decidable c} {α : Sort*} {t : c → α} {e : ¬c → α}
    (h : c) : dite c t e = t h := dif_pos h

theorem dite_eq_right {c : Prop} {_ : Decidable c} {α : Sort*} {t : c → α} {e : ¬c → α}
    (h : ¬c) : dite c t e = e h := dif_neg h

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/FiniteHall.lean =====
/-
This file has been adapted from an external source.
The source copyright header and license information are preserved below.
-/

/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Bhavik Mehta, Kyle Miller

This file is adapted from Mathlib.Combinatorics.Hall.Finite.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Combinatorics/Hall/Finite.lean

This code has been modified.
-/


namespace OAI

open Finset

namespace BinPackingGap.FiniteHall

universe u v

namespace HallMarriageTheorem

variable {ι : Type u} {α : Type v} [DecidableEq α] {t : ι → Finset α}

section Fintype

variable [Fintype ι]

theorem hall_cond_of_erase {x : ι} (a : α)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t))
    (s' : Finset { x' : ι | x' ≠ x }) : #s' ≤ #(s'.biUnion fun x' => (t x').erase a) := by
  have := Classical.decEq ι
  specialize ha (s'.image fun z => z.1)
  rw [image_nonempty, Finset.card_image_of_injective s' Subtype.coe_injective] at ha
  by_cases! he : s'.Nonempty
  · have ha' : #s' < #(s'.biUnion fun x => t x) := by
      convert! ha he fun h => by simpa [← h] using mem_univ x using 2
      ext x
      simp only [mem_image, mem_biUnion, SetCoe.exists, exists_and_right,
        exists_eq_right]
    rw [← erase_biUnion]
    by_cases hb : a ∈ s'.biUnion fun x => t x
    · rw [card_erase_of_mem hb]
      exact Nat.le_sub_one_of_lt ha'
    · rw [erase_eq_of_notMem hb]
      exact Nat.le_of_lt ha'
  · subst s'
    simp

theorem hall_hard_inductive_step_A {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (hn.symm ▸ Nat.succ_pos _)
  have := Classical.decEq ι

  let x := Classical.arbitrary ι
  have tx_ne : (t x).Nonempty := by
    rw [← Finset.card_pos]
    calc
      0 < 1 := Nat.one_pos
      _ ≤ #(.biUnion {x} t) := ht {x}
      _ = (t x).card := by rw [Finset.singleton_biUnion]
  choose y hy using tx_ne

  let ι' := { x' : ι | x' ≠ x }
  let t' : ι' → Finset α := fun x' => (t x').erase y
  have card_ι' : Fintype.card ι' = n :=
    calc
      Fintype.card ι' = Fintype.card ι - 1 := Set.card_ne_eq _
      _ = n := by rw [hn, Nat.add_succ_sub_one, add_zero]
  rcases ih t' card_ι'.le (hall_cond_of_erase y ha) with ⟨f', hfinj, hfr⟩

  refine ⟨fun z => if h : z = x then y else f' ⟨z, h⟩, ?_, ?_⟩
  · rintro z₁ z₂
    have key : ∀ {x}, y ≠ f' x := by
      intro x h
      simpa [t', ← h] using hfr x
    by_cases h₁ : z₁ = x <;> by_cases h₂ : z₂ = x <;>
      simp [h₁, h₂, hfinj.eq_iff, key, key.symm]
  · intro z
    simp only
    split_ifs with hz
    · rwa [hz]
    · specialize hfr ⟨z, hz⟩
      rw [mem_erase] at hfr
      exact hfr.2

theorem hall_cond_of_restrict {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) (s' : Finset (s : Set ι)) :
    #s' ≤ #(s'.biUnion fun a' => t a') := by
  classical
    rw [← card_image_of_injective s' Subtype.coe_injective]
    convert! ht (s'.image fun z => z.1) using 1
    apply congr_arg
    ext y
    simp

theorem hall_cond_of_compl {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (hus : #s = #(s.biUnion t)) (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (s' : Finset (sᶜ : Set ι)) : #s' ≤ #(s'.biUnion fun x' => t x' \ s.biUnion t) := by
  have := Classical.decEq ι
  have disj : Disjoint s (s'.image fun z => z.1) := by
    simp only [disjoint_left, not_exists, mem_image, SetCoe.exists, exists_and_right,
      exists_eq_right]
    intro x hx hc _
    exact absurd hx hc
  have : #s' = #(s ∪ s'.image fun z => z.1) - #s := by
    simp [disj, card_image_of_injective _ Subtype.coe_injective, Nat.add_sub_cancel_left]
  rw [this, hus]
  refine (Nat.sub_le_sub_right (ht _) _).trans ?_
  rw [← card_sdiff_of_subset]
  · gcongr
    intro t
    simp only [mem_biUnion, mem_sdiff, not_exists, mem_image, and_imp, mem_union,
      exists_imp]
    rintro x (hx | ⟨x', hx', rfl⟩) rat hs
    · exact False.elim <| (hs x) <| And.intro hx rat
    · use x', hx', rat, hs
  · apply biUnion_subset_biUnion_of_subset_left
    apply subset_union_left

theorem hall_hard_inductive_step_B {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (s : Finset ι) (hs : s.Nonempty) (hns : s ≠ univ) (hus : #s = #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  have := Classical.decEq ι

  rw [Nat.add_one] at hn
  have card_ι'_le : Fintype.card s ≤ n := by
    apply Nat.le_of_lt_succ
    calc
      Fintype.card s = #s := Fintype.card_coe _
      _ < Fintype.card ι := (card_lt_iff_ne_univ _).mpr hns
      _ = n.succ := hn
  let t' : s → Finset α := fun x' => t x'
  rcases ih t' card_ι'_le (hall_cond_of_restrict ht) with ⟨f', hf', hsf'⟩

  set ι'' := (s : Set ι)ᶜ
  let t'' : ι'' → Finset α := fun a'' => t a'' \ s.biUnion t
  have card_ι''_le : Fintype.card ι'' ≤ n := by
    simp_rw [ι'', ← Nat.lt_succ_iff, ← hn, ← Finset.coe_compl, coe_sort_coe]
    rwa [Fintype.card_coe, card_compl_lt_iff_nonempty]
  rcases ih t'' card_ι''_le (hall_cond_of_compl hus ht) with ⟨f'', hf'', hsf''⟩

  have f''_notMem_biUnion : ∀ (x'') (hx'' : x'' ∉ s), f'' ⟨x'', hx''⟩ ∉ s.biUnion t := by
    intro x'' hx''
    have h := hsf'' ⟨x'', hx''⟩
    rw [mem_sdiff] at h
    exact h.2
  have im_disj :
      ∀ (x' x'' : ι) (hx' : x' ∈ s) (hx'' : x'' ∉ s), f' ⟨x', hx'⟩ ≠ f'' ⟨x'', hx''⟩ := by
    grind
  refine ⟨fun x => if h : x ∈ s then f' ⟨x, h⟩ else f'' ⟨x, h⟩, ?_, ?_⟩
  · refine hf'.dite _ hf'' (@fun x x' => im_disj x x' _ _)
  · intro x
    simp only
    split_ifs with h
    · exact hsf' ⟨x, h⟩
    · exact sdiff_subset (hsf'' ⟨x, h⟩)

end Fintype

variable [Finite ι]

theorem hall_hard_inductive (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  cases nonempty_fintype ι
  generalize hn : Fintype.card ι = m
  induction m using Nat.strongRecOn generalizing ι with | ind n ih => _
  rcases n with (_ | n)
  · rw [Fintype.card_eq_zero_iff] at hn
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩
  · have ih' : ∀ (ι' : Type u) [Fintype ι'] (t' : ι' → Finset α), Fintype.card ι' ≤ n →
        (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
        ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x := by
      intro ι' _ _ hι' ht'
      exact ih _ (Nat.lt_succ_of_le hι') ht' _ rfl
    by_cases! h : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)
    · refine hall_hard_inductive_step_A hn ht (@fun ι' => ih' ι') h
    · rcases h with ⟨s, sne, snu, sle⟩
      exact hall_hard_inductive_step_B hn ht (@fun ι' => ih' ι')
        s sne snu (Nat.le_antisymm (ht _) sle)

end HallMarriageTheorem

theorem all_card_le_biUnion_card_iff_existsInjective {ι α : Type*} [Finite ι]
    [DecidableEq α] (t : ι → Finset α) :
    (∀ s : Finset ι, #s ≤ #(s.biUnion t)) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  constructor
  · exact HallMarriageTheorem.hall_hard_inductive
  · rintro ⟨f, hf₁, hf₂⟩ s
    rw [← card_image_of_injective s hf₁]
    apply card_le_card
    intro
    rw [mem_image, mem_biUnion]
    rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hf₂ x⟩

end BinPackingGap.FiniteHall

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/FractionWidth.lean =====
namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace Instance

noncomputable def ofFintype {ι : Type*} [Fintype ι]
    (s : ι → ℚ) (hpos : ∀ i, 0 < s i) (hle : ∀ i, s i ≤ 1) : Instance where
  n := Fintype.card ι
  size i := s ((Fintype.equivFin ι).symm i)
  size_pos _ := hpos _
  size_le_one _ := hle _

end Instance

namespace Packing

variable {I : Instance} {b : ℕ}

def binItems (p : Packing I b) (j : Fin b) : Finset I.Item :=
  Finset.univ.filter fun i => p.assignment i = j

@[simp] theorem mem_binItems (p : Packing I b) (j : Fin b) (i : I.Item) :
    i ∈ p.binItems j ↔ p.assignment i = j := by
  simp [binItems]

theorem bin_capacity (p : Packing I b) (j : Fin b) :
    ∑ i ∈ p.binItems j, I.size i ≤ 1 := by
  simpa [binItems, Finset.sum_filter] using p.capacity j

theorem binItems_disjoint (p : Packing I b) {j k : Fin b} (h : j ≠ k) :
    Disjoint (p.binItems j) (p.binItems k) := by
  refine Finset.disjoint_left.mpr ?_
  intro i hi hj
  have hji := (p.mem_binItems j i).mp hi
  have hki := (p.mem_binItems k i).mp hj
  exact h (hji.symm.trans hki)

theorem mem_own_bin (p : Packing I b) (i : I.Item) :
    i ∈ p.binItems (p.assignment i) := by simp

theorem unique_bin (p : Packing I b) (i : I.Item) :
    ∃! j, i ∈ p.binItems j := by
  refine ⟨p.assignment i, p.mem_own_bin i, ?_⟩
  intro j hj
  exact ((p.mem_binItems j i).mp hj).symm

theorem chosen_injective (p : Packing I b) {J : Type*}
    (bin : J → Fin b) (hbin : Function.Injective bin)
    (chosen : J → I.Item) (hchosen : ∀ j, chosen j ∈ p.binItems (bin j)) :
    Function.Injective chosen := by
  intro j k hjk
  apply hbin
  have hj := (p.mem_binItems (bin j) (chosen j)).mp (hchosen j)
  have hk := (p.mem_binItems (bin k) (chosen k)).mp (hchosen k)
  rw [hjk] at hj
  exact hj.symm.trans hk

theorem sum_bins (p : Packing I b) {M : Type*} [AddCommMonoid M]
    (f : I.Item → M) :
    ∑ j, ∑ i ∈ p.binItems j, f i = ∑ i, f i := by
  simp only [binItems, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, if p.assignment i = j then f i else 0) =
        (if p.assignment i = p.assignment i then f i else 0) :=
      Finset.sum_eq_single (p.assignment i)
        (fun j _ hj => ite_eq_right (Ne.symm hj))
        (fun h => False.elim (h (Finset.mem_univ _)))
    _ = f i := ite_eq_left rfl

theorem sum_bin_card (p : Packing I b) :
    ∑ j, (p.binItems j).card = I.n := by
  simpa using p.sum_bins (fun _ => (1 : ℕ))

def enlarge (p : Packing I b) {c : ℕ} (hbc : b ≤ c) : Packing I c where
  assignment i := Fin.castLE hbc (p.assignment i)
  capacity j := by
    by_cases hj : j.val < b
    · let k : Fin b := ⟨j.val, hj⟩
      have heq : ∀ i, Fin.castLE hbc (p.assignment i) = j ↔ p.assignment i = k := by
        intro i
        simp [Fin.ext_iff, k]
      simpa only [heq] using p.capacity k
    · have heq : ∀ i, Fin.castLE hbc (p.assignment i) ≠ j := by
        intro i h
        have hv := congrArg Fin.val h
        have hi := (p.assignment i).isLt
        exact hj (hv ▸ hi)
      simp [heq]

end Packing

theorem opt_attained (I : Instance) : HasPacking I (opt I) := by
  classical
  exact Nat.find_spec (exists_packing I)

theorem opt_le_of_hasPacking {I : Instance} {b : ℕ} (h : HasPacking I b) :
    opt I ≤ b := by
  classical
  exact Nat.find_min' (exists_packing I) h

theorem opt_le_n (I : Instance) : opt I ≤ I.n :=
  opt_le_of_hasPacking ⟨singletonPacking I⟩

theorem opt_eq_zero_of_n_eq_zero (I : Instance) (h : I.n = 0) : opt I = 0 := by
  have := opt_le_n I
  omega

theorem HasPacking.mono {I : Instance} {b c : ℕ} (h : HasPacking I b) (hbc : b ≤ c) :
    HasPacking I c := by
  obtain ⟨p⟩ := h
  exact ⟨p.enlarge hbc⟩

theorem hasPacking_iff_opt_le (I : Instance) (b : ℕ) :
    HasPacking I b ↔ opt I ≤ b :=
  ⟨opt_le_of_hasPacking, fun h => (opt_attained I).mono h⟩

theorem not_hasPacking_iff_lt_opt (I : Instance) (b : ℕ) :
    ¬ HasPacking I b ↔ b < opt I := by
  rw [hasPacking_iff_opt_le, Nat.not_le]

noncomputable def packingOfFintype {ι : Type*} [Fintype ι]
    (s : ι → ℚ) (hpos : ∀ i, 0 < s i) (hle : ∀ i, s i ≤ 1)
    {b : ℕ} (a : ι → Fin b)
    (hcap : ∀ j, (∑ i, if a i = j then s i else 0) ≤ 1) :
    Packing (Instance.ofFintype s hpos hle) b where
  assignment i := a ((Fintype.equivFin ι).symm i)
  capacity j := by
    change (∑ i : Fin (Fintype.card ι),
      if a ((Fintype.equivFin ι).symm i) = j
      then s ((Fintype.equivFin ι).symm i) else 0) ≤ 1
    rw [(Fintype.equivFin ι).symm.sum_comp
      (fun i : ι => if a i = j then s i else 0)]
    exact hcap j

namespace IndividualConfiguration

variable {I : Instance}

def singleton (i : I.Item) : IndividualConfiguration I :=
  ⟨{i}, by simpa using I.size_le_one i⟩

theorem card_le_five (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    (H : IndividualConfiguration I) : H.val.card ≤ 5 := by
  by_contra h
  have hcard : 6 ≤ H.val.card := by omega
  have hne : H.val.Nonempty := Finset.card_pos.mp (by omega)
  have hstrict := Finset.sum_lt_sum_of_nonempty hne (fun i _ => hlarge i)
  have hsum : (H.val.card : ℚ) * (1 / 6) < ∑ i ∈ H.val, I.size i := by
    simpa using hstrict
  have hc : (6 : ℚ) ≤ H.val.card := by exact_mod_cast hcard
  have hcap := H.property
  linarith

end IndividualConfiguration

namespace Packing

def configuration {I : Instance} {b : ℕ} (p : Packing I b) (j : Fin b) :
    IndividualConfiguration I := ⟨p.binItems j, p.bin_capacity j⟩

theorem bin_card_le_five {I : Instance} {b : ℕ}
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i) (p : Packing I b) (j : Fin b) :
    (p.binItems j).card ≤ 5 :=
  (p.configuration j).card_le_five hlarge

theorem item_count_le_five_mul {I : Instance} {b : ℕ}
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i) (p : Packing I b) : I.n ≤ 5 * b := by
  rw [← p.sum_bin_card]
  calc
    ∑ j, (p.binItems j).card ≤ ∑ _j : Fin b, 5 :=
      Finset.sum_le_sum (fun j _ => p.bin_card_le_five hlarge j)
    _ = 5 * b := by simp [Nat.mul_comm]

end Packing

namespace Instance

structure Reindexing (I J : Instance) where
  equiv : I.Item ≃ J.Item
  size_eq : ∀ i, I.size i = J.size (equiv i)

namespace Reindexing

variable {I J : Instance}

def symm (e : Reindexing I J) : Reindexing J I where
  equiv := e.equiv.symm
  size_eq j := by
    simpa using (e.size_eq (e.equiv.symm j)).symm

theorem count_eq (e : Reindexing I J) : I.n = J.n := by
  simpa [Item] using Fintype.card_congr e.equiv

theorem lower_bound_iff (e : Reindexing I J) (a : ℚ) :
    (∀ i, a < I.size i) ↔ ∀ j, a < J.size j := by
  constructor
  · intro h j
    simpa only [e.size_eq, Equiv.apply_symm_apply] using h (e.equiv.symm j)
  · intro h i
    rw [e.size_eq]
    exact h _

end Reindexing

end Instance

namespace Packing

def reindex {I J : Instance} {b : ℕ} (p : Packing I b)
    (e : Instance.Reindexing I J) : Packing J b where
  assignment j := p.assignment (e.equiv.symm j)
  capacity k := by
    calc
      (∑ j : J.Item, if p.assignment (e.equiv.symm j) = k then J.size j else 0) =
          ∑ i : I.Item, if p.assignment (e.equiv.symm (e.equiv i)) = k
            then J.size (e.equiv i) else 0 :=
        (e.equiv.sum_comp (fun j =>
          if p.assignment (e.equiv.symm j) = k then J.size j else 0)).symm
      _ = ∑ i : I.Item, if p.assignment i = k then I.size i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Equiv.symm_apply_apply, ← e.size_eq i]
      _ ≤ 1 := p.capacity k

end Packing

namespace Instance.Reindexing

variable {I J : Instance}

theorem hasPacking_iff (e : Reindexing I J) (b : ℕ) :
    HasPacking I b ↔ HasPacking J b := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.reindex e⟩
  · rintro ⟨p⟩
    exact ⟨p.reindex e.symm⟩

theorem opt_eq (e : Reindexing I J) : opt I = opt J := by
  apply Nat.le_antisymm
  · exact opt_le_of_hasPacking ((e.hasPacking_iff (opt J)).mpr (opt_attained J))
  · exact opt_le_of_hasPacking ((e.hasPacking_iff (opt I)).mp (opt_attained I))

end Instance.Reindexing

namespace RawInstance

@[simp] theorem toInstance_n (r : RawInstance) (hr : r.Valid) :
    (r.toInstance hr).n = r.length := rfl

@[simp] theorem toInstance_size (r : RawInstance) (hr : r.Valid) (i : Fin r.length) :
    (r.toInstance hr).size i = ratValue (r.get i) := rfl

@[simp] theorem valid_nil : Valid [] := by simp [Valid]

end RawInstance

namespace RawPacking

def addFraction (x y : ℕ × ℕ) : ℕ × ℕ :=
  (x.1 * y.2 + y.1 * x.2, x.2 * y.2)

def loadFraction (r : RawInstance) (a : List ℕ) (j : ℕ) : ℕ × ℕ :=
  (r.zip a).foldl
    (fun acc qa => if qa.2 = j then addFraction acc qa.1 else acc) (0, 1)

theorem addFraction_den_pos (x y : ℕ × ℕ) (hx : 0 < x.2) (hy : 0 < y.2) :
    0 < (addFraction x y).2 := Nat.mul_pos hx hy

theorem ratValue_addFraction (x y : ℕ × ℕ) (hx : 0 < x.2) (hy : 0 < y.2) :
    RawInstance.ratValue (addFraction x y) =
      RawInstance.ratValue x + RawInstance.ratValue y := by
  unfold RawInstance.ratValue addFraction
  simp only [Nat.cast_add, Nat.cast_mul]
  have hx' : (x.2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hx)
  have hy' : (y.2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hy)
  field_simp [hx', hy']

private theorem foldFraction_spec (rows : List ((ℕ × ℕ) × ℕ)) (j : ℕ)
    (acc : ℕ × ℕ) (hacc : 0 < acc.2)
    (hrows : ∀ row ∈ rows, 0 < row.1.2) :
    0 < (rows.foldl
      (fun acc qa => if qa.2 = j then addFraction acc qa.1 else acc) acc).2 ∧
    RawInstance.ratValue (rows.foldl
      (fun acc qa => if qa.2 = j then addFraction acc qa.1 else acc) acc) =
      RawInstance.ratValue acc +
        (rows.map fun qa => if qa.2 = j then RawInstance.ratValue qa.1 else 0).sum := by
  induction rows generalizing acc with
  | nil => simpa using And.intro hacc (rfl : RawInstance.ratValue acc = _)
  | cons row rows ih =>
      have hhead : 0 < row.1.2 := hrows row (List.mem_cons_self ..)
      have htail : ∀ q ∈ rows, 0 < q.1.2 :=
        fun q hq => hrows q (List.mem_cons_of_mem _ hq)
      by_cases h : row.2 = j
      · have hrec := ih (addFraction acc row.1) (addFraction_den_pos _ _ hacc hhead) htail
        refine ⟨?_, ?_⟩
        · simpa only [List.foldl_cons, ite_eq_left h] using hrec.1
        · simpa only [List.foldl_cons, ite_eq_left h, List.map_cons, List.sum_cons,
            ratValue_addFraction _ _ hacc hhead, add_assoc] using hrec.2
      · have hrec := ih acc hacc htail
        simpa only [List.foldl_cons, ite_eq_right h, List.map_cons, List.sum_cons, zero_add]
          using hrec

private theorem zip_den_pos {r : RawInstance} (hr : r.Valid) (a : List ℕ) :
    ∀ row ∈ r.zip a, 0 < row.1.2 := by
  intro row hrow
  exact RawInstance.den_pos hr (List.of_mem_zip hrow).1

theorem loadFraction_den_pos (r : RawInstance) (hr : r.Valid) (a : List ℕ) (j : ℕ) :
    0 < (loadFraction r a j).2 :=
  (foldFraction_spec (r.zip a) j (0, 1) (by decide) (zip_den_pos hr a)).1

theorem load_eq_loadFraction (r : RawInstance) (hr : r.Valid) (a : List ℕ) (j : ℕ) :
    load r a j = RawInstance.ratValue (loadFraction r a j) := by
  have h := (foldFraction_spec (r.zip a) j (0, 1) (by decide) (zip_den_pos hr a)).2
  simpa [load, loadFraction, RawInstance.ratValue] using h.symm

theorem load_le_one_iff (r : RawInstance) (hr : r.Valid) (a : List ℕ) (j : ℕ) :
    load r a j ≤ 1 ↔ (loadFraction r a j).1 ≤ (loadFraction r a j).2 := by
  rw [load_eq_loadFraction r hr a j]
  unfold RawInstance.ratValue
  rw [div_le_one₀ (Nat.cast_pos.mpr (loadFraction_den_pos r hr a j))]
  exact Nat.cast_le

theorem load_eq_zero_of_not_mem (r : RawInstance) (a : List ℕ) (j : ℕ)
    (hj : j ∉ a) : load r a j = 0 := by
  unfold load
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
  have hmem : row.2 ∈ a := (List.of_mem_zip hrow).2
  have hne : row.2 ≠ j := fun h => hj (h ▸ hmem)
  simp [hne]

theorem feasible_iff_mem_capacity (r : RawInstance) (p : RawPacking) :
    Feasible r p ↔
      p.assignments.length = r.length ∧
      (∀ j ∈ p.assignments, j < p.bins) ∧
      ∀ j ∈ p.assignments, load r p.assignments j ≤ 1 := by
  constructor
  · rintro ⟨hl, hr, hc⟩
    exact ⟨hl, hr, fun j hj => hc j (hr j hj)⟩
  · rintro ⟨hl, hr, hc⟩
    refine ⟨hl, hr, fun j _ => ?_⟩
    by_cases hj : j ∈ p.assignments
    · exact hc j hj
    · rw [load_eq_zero_of_not_mem _ _ _ hj]
      decide

private theorem zip_ofFn_eq {α β : Type*} {n : ℕ} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn (fun i => (f i, g i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ, List.zip_cons_cons, ih]

theorem load_ofFn (r : RawInstance) (f : Fin r.length → ℕ) (j : ℕ) :
    load r (List.ofFn f) j =
      ∑ i : Fin r.length, if f i = j then RawInstance.ratValue (r.get i) else 0 := by
  have hz : r.zip (List.ofFn f) = List.ofFn (fun i => (r.get i, f i)) := by
    calc
      r.zip (List.ofFn f) = (List.ofFn r.get).zip (List.ofFn f) :=
        congrArg (fun xs => xs.zip (List.ofFn f)) (List.ofFn_get r).symm
      _ = _ := zip_ofFn_eq r.get f
  simp only [load, hz, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

def assignmentFn (r : RawInstance) (p : RawPacking)
    (h : p.assignments.length = r.length) (i : Fin r.length) : ℕ :=
  p.assignments.get (Fin.cast h.symm i)

theorem assignments_eq_ofFn (r : RawInstance) (p : RawPacking)
    (h : p.assignments.length = r.length) :
    p.assignments = List.ofFn (assignmentFn r p h) := by
  exact (List.ofFn_get p.assignments).symm.trans
    (List.ofFn_congr h p.assignments.get)

def toPacking (r : RawInstance) (hr : r.Valid) (p : RawPacking) (hp : Feasible r p) :
    Packing (r.toInstance hr) p.bins where
  assignment i := ⟨assignmentFn r p hp.1 i,
    hp.2.1 _ (List.get_mem p.assignments (Fin.cast hp.1.symm i))⟩
  capacity j := by
    have hcap := hp.2.2 j.val j.isLt
    rw [assignments_eq_ofFn r p hp.1, load_ofFn] at hcap
    simpa only [RawInstance.toInstance, Fin.ext_iff] using! hcap

@[simp] theorem toPacking_assignment_val (r : RawInstance) (hr : r.Valid)
    (p : RawPacking) (hp : Feasible r p) (i : Fin r.length) :
    ((toPacking r hr p hp).assignment i).val = assignmentFn r p hp.1 i := rfl

def ofPacking {I : Instance} {b : ℕ} (q : Packing I b) : RawPacking where
  bins := b
  assignments := List.ofFn (fun i => (q.assignment i).val)

theorem ofPacking_feasible (r : RawInstance) (hr : r.Valid) {b : ℕ}
    (q : Packing (r.toInstance hr) b) : Feasible r (ofPacking q) := by
  refine ⟨by simp [ofPacking, RawInstance.toInstance], ?_, ?_⟩
  · intro j hj
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
    exact (q.assignment i).isLt
  · intro j hj
    have hcap := q.capacity ⟨j, hj⟩
    change load r (List.ofFn (fun i : Fin r.length => (q.assignment i).val)) j ≤ 1
    rw [load_ofFn]
    simpa only [RawInstance.toInstance, Fin.ext_iff] using! hcap

theorem feasible_iff_exists_packing (r : RawInstance) (hr : r.Valid) (p : RawPacking) :
    Feasible r p ↔
      ∃ q : Packing (r.toInstance hr) p.bins,
        p.assignments = List.ofFn (fun i => (q.assignment i).val) := by
  constructor
  · intro hp
    exact ⟨toPacking r hr p hp, assignments_eq_ofFn r p hp.1⟩
  · rintro ⟨q, hq⟩
    have hp := ofPacking_feasible r hr q
    simpa only [ofPacking, ← hq] using hp

theorem hasPacking_iff_exists_feasible (r : RawInstance) (hr : r.Valid) (b : ℕ) :
    HasPacking (r.toInstance hr) b ↔
      ∃ a : List ℕ, Feasible r ⟨b, a⟩ := by
  constructor
  · rintro ⟨q⟩
    exact ⟨(ofPacking q).assignments, ofPacking_feasible r hr q⟩
  · rintro ⟨a, ha⟩
    exact ⟨toPacking r hr ⟨b, a⟩ ha⟩

@[simp] theorem feasible_nil_iff (p : RawPacking) :
    Feasible [] p ↔ p.assignments = [] := by
  constructor
  · intro hp
    exact List.length_eq_zero_iff.mp hp.1
  · intro h
    cases p with
    | mk b a =>
        dsimp at h
        subst a
        simp [Feasible, load]

theorem feasible_zero_bins_iff (r : RawInstance) (a : List ℕ) :
    Feasible r ⟨0, a⟩ ↔ r = [] ∧ a = [] := by
  constructor
  · rintro ⟨hl, hr, _⟩
    have ha : a = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro j hj
      exact Nat.not_lt_zero j (hr j hj)
    refine ⟨?_, ha⟩
    apply List.length_eq_zero_iff.mp
    simpa [ha] using hl.symm
  · rintro ⟨rfl, rfl⟩
    simp

end RawPacking

namespace Instance

def toRaw (I : Instance) : RawInstance :=
  List.ofFn fun i : Fin I.n => ((I.size i).num.toNat, (I.size i).den)

@[simp] theorem toRaw_length (I : Instance) : I.toRaw.length = I.n := by
  simp [toRaw]

private theorem ratValue_num_den (x : ℚ) (hx : 0 ≤ x) :
    RawInstance.ratValue (x.num.toNat, x.den) = x := by
  have hn : 0 ≤ x.num := Rat.num_nonneg.mpr hx
  have hc : (x.num.toNat : ℚ) = (x.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  simpa only [RawInstance.ratValue, hc] using Rat.num_div_den x

theorem toRaw_valid (I : Instance) : I.toRaw.Valid := by
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  have hpos : 0 < (I.size i).num := Rat.num_pos.mpr (I.size_pos i)
  have hn : 0 < (I.size i).num.toNat := Int.pos_iff_toNat_pos.mp hpos
  refine ⟨hn, ?_⟩
  have hrat := I.size_le_one i
  rw [← ratValue_num_den (I.size i) (I.size_pos i).le] at hrat
  change ((I.size i).num.toNat : ℚ) / (I.size i).den ≤ 1 at hrat
  exact Nat.cast_le.mp ((div_le_one₀ (Nat.cast_pos.mpr (I.size i).den_pos)).mp hrat)

theorem toRaw_size (I : Instance) (i : Fin I.toRaw.length) :
    RawInstance.ratValue (I.toRaw.get i) = I.size (Fin.cast (toRaw_length I) i) := by
  have hget : I.toRaw.get i =
      ((I.size (Fin.cast (toRaw_length I) i)).num.toNat,
        (I.size (Fin.cast (toRaw_length I) i)).den) :=
    List.get_ofFn (fun j : Fin I.n => ((I.size j).num.toNat, (I.size j).den)) i
  rw [hget]
  exact ratValue_num_den (I.size (Fin.cast (toRaw_length I) i)) (I.size_pos _).le

def toRawReindexing (I : Instance) :
    Reindexing I (I.toRaw.toInstance (toRaw_valid I)) where
  equiv := finCongr (toRaw_length I).symm
  size_eq i := by
    change I.size i =
      RawInstance.ratValue (I.toRaw.get (Fin.cast (toRaw_length I).symm i))
    rw [toRaw_size]
    rfl

private theorem eq_of_indexed_sizes {I J : Instance} (h : I.n = J.n)
    (hs : ∀ i : I.Item, I.size i = J.size (Fin.cast h i)) : I = J := by
  cases I with
  | mk n s hp hl =>
    cases J with
    | mk m t hq hk =>
      dsimp at h hs
      subst m
      simp only [Fin.cast_refl] at hs
      have hst : s = t := funext hs
      subst t
      rfl

theorem toInstance_toRaw (I : Instance) :
    I.toRaw.toInstance (toRaw_valid I) = I := by
  apply eq_of_indexed_sizes (toRaw_length I)
  intro i
  exact toRaw_size I i

end Instance

namespace RawPacking

theorem ofPacking_cast {I J : Instance} {b : ℕ} (h : I = J) (q : Packing I b) :
    ofPacking (h ▸ q) = ofPacking q := by
  cases h
  rfl

theorem ofPacking_toRaw_feasible {I : Instance} {b : ℕ} (q : Packing I b) :
    Feasible I.toRaw (ofPacking q) := by
  have hI := (Instance.toInstance_toRaw I).symm
  have h := ofPacking_feasible I.toRaw I.toRaw_valid (hI ▸ q)
  rwa [ofPacking_cast hI q] at h

end RawPacking

end BinPackingGap

namespace BinPackingGap.FractionWidth

def denominatorBits (r : RawInstance) : ℕ :=
  (r.map fun q => q.2.size).sum

@[simp] theorem denominatorBits_nil : denominatorBits [] = 0 := rfl

@[simp] theorem denominatorBits_cons (q : ℕ × ℕ) (r : RawInstance) :
    denominatorBits (q :: r) = q.2.size + denominatorBits r := rfl

theorem size_mono {a b : ℕ} (h : a ≤ b) : a.size ≤ b.size := by
  apply Nat.size_le.mpr
  exact lt_of_le_of_lt h (Nat.size_le.mp (le_refl b.size))

theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ a.size := Nat.size_le.mp (le_refl a.size)
  have hb : b < 2 ^ b.size := Nat.size_le.mp (le_refl b.size)
  calc
    a * b ≤ a * 2 ^ b.size := Nat.mul_le_mul_left a (Nat.le_of_lt hb)
    _ < 2 ^ a.size * 2 ^ b.size :=
      mul_lt_mul_of_pos_right ha (pow_pos (by decide) _)
    _ = 2 ^ (a.size + b.size) := (pow_add 2 a.size b.size).symm

theorem size_add_le {a b H : ℕ} (ha : a.size ≤ H) (hb : b.size ≤ H) :
    (a + b).size ≤ H + 1 := by
  apply Nat.size_le.mpr
  have h := Nat.add_lt_add (Nat.size_le.mp ha) (Nat.size_le.mp hb)
  simpa only [pow_succ, Nat.mul_two] using h

theorem addFraction_left_product_size_le {x q : ℕ × ℕ} (hx : x.1 ≤ x.2) :
    (x.1 * q.2).size ≤ x.2.size + q.2.size := by
  exact (size_mono (Nat.mul_le_mul_right q.2 hx)).trans (size_mul_le x.2 q.2)

theorem addFraction_right_product_size_le {x q : ℕ × ℕ} (hq : q.1 ≤ q.2) :
    (q.1 * x.2).size ≤ x.2.size + q.2.size := by
  have h := (size_mono (Nat.mul_le_mul_right x.2 hq)).trans
    (size_mul_le q.2 x.2)
  simpa only [Nat.add_comm] using h

theorem addFraction_num_size_le {x q : ℕ × ℕ}
    (hx : x.1 ≤ x.2) (hq : q.1 ≤ q.2) :
    (RawPacking.addFraction x q).1.size ≤ x.2.size + q.2.size + 1 := by
  exact size_add_le (addFraction_left_product_size_le hx)
    (addFraction_right_product_size_le hq)

theorem addFraction_den_size_le (x q : ℕ × ℕ) :
    (RawPacking.addFraction x q).2.size ≤ x.2.size + q.2.size :=
  size_mul_le x.2 q.2

theorem fold_den_size_le (r : RawInstance) (a : List ℕ) (j : ℕ) (x : ℕ × ℕ) :
    ((r.zip a).foldl
      (fun acc qa => if qa.2 = j then RawPacking.addFraction acc qa.1 else acc) x).2.size
      ≤ x.2.size + denominatorBits r := by
  induction r generalizing a x with
  | nil => simp
  | cons q r ih =>
      cases a with
      | nil => simp
      | cons b a =>
          simp only [List.zip_cons_cons, List.foldl_cons, denominatorBits_cons]
          by_cases hb : b = j
          · simp only [ite_eq_left hb]
            have hfold := ih a (RawPacking.addFraction x q)
            have hstep := addFraction_den_size_le x q
            omega
          · simp only [ite_eq_right hb]
            have hfold := ih a x
            omega

theorem loadFraction_den_size_le (r : RawInstance) (a : List ℕ) (j : ℕ) :
    (RawPacking.loadFraction r a j).2.size ≤ denominatorBits r + 1 := by
  simpa [RawPacking.loadFraction, Nat.add_comm] using
    fold_den_size_le r a j (0, 1)

theorem loadFraction_num_size_le_of_accepted
    (r : RawInstance) (a : List ℕ) (j : ℕ)
    (h : (RawPacking.loadFraction r a j).1 ≤ (RawPacking.loadFraction r a j).2) :
    (RawPacking.loadFraction r a j).1.size ≤ denominatorBits r + 1 :=
  (size_mono h).trans (loadFraction_den_size_le r a j)

theorem addFraction_width_of_budget {x q : ℕ × ℕ} {H : ℕ}
    (hx : x.1 ≤ x.2) (hq : q.1 ≤ q.2) (hD : x.2.size ≤ H + 1) :
    (RawPacking.addFraction x q).2.size ≤ H + q.2.size + 1 ∧
    (x.1 * q.2).size ≤ H + q.2.size + 1 ∧
    (q.1 * x.2).size ≤ H + q.2.size + 1 ∧
    (RawPacking.addFraction x q).1.size ≤ H + q.2.size + 2 := by
  have hden := addFraction_den_size_le x q
  have hleft := addFraction_left_product_size_le (q := q) hx
  have hright := addFraction_right_product_size_le (x := x) hq
  have hnum := addFraction_num_size_le hx hq
  omega

theorem loadFraction_next_width (r : RawInstance) (a : List ℕ) (j : ℕ)
    (q : ℕ × ℕ)
    (h : (RawPacking.loadFraction r a j).1 ≤ (RawPacking.loadFraction r a j).2)
    (hq : q.1 ≤ q.2) :
    (RawPacking.addFraction (RawPacking.loadFraction r a j) q).2.size
        ≤ denominatorBits r + q.2.size + 1 ∧
    ((RawPacking.loadFraction r a j).1 * q.2).size
        ≤ denominatorBits r + q.2.size + 1 ∧
    (q.1 * (RawPacking.loadFraction r a j).2).size
        ≤ denominatorBits r + q.2.size + 1 ∧
    (RawPacking.addFraction (RawPacking.loadFraction r a j) q).1.size
        ≤ denominatorBits r + q.2.size + 2 :=
  addFraction_width_of_budget h hq (loadFraction_den_size_le r a j)

theorem addFraction_overflow {x q : ℕ × ℕ}
    (hx : x.2 < x.1) (hq : 0 < q.2) :
    (RawPacking.addFraction x q).2 < (RawPacking.addFraction x q).1 := by
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hx hq)
    (Nat.le_add_right (x.1 * q.2) (q.1 * x.2))

theorem fold_overflow (r : RawInstance) (a : List ℕ) (j : ℕ) (x : ℕ × ℕ)
    (hr : r.Valid) (hx : x.2 < x.1) :
    let y := (r.zip a).foldl
      (fun acc qa => if qa.2 = j then RawPacking.addFraction acc qa.1 else acc) x
    y.2 < y.1 := by
  induction r generalizing a x with
  | nil => simpa using hx
  | cons q r ih =>
      have hr' : RawInstance.Valid r := fun z hz => hr z (List.mem_cons_of_mem q hz)
      have hq : 0 < q.2 := RawInstance.den_pos hr (List.mem_cons_self ..)
      cases a with
      | nil => simpa using hx
      | cons b a =>
          simp only [List.zip_cons_cons, List.foldl_cons]
          by_cases hb : b = j
          · simp only [ite_eq_left hb]
            exact ih a (RawPacking.addFraction x q) hr' (addFraction_overflow hx hq)
          · simp only [ite_eq_right hb]
            exact ih a x hr' hx

end BinPackingGap.FractionWidth

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/PrimaryLoss.lean =====
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

theorem fibers_disjoint (f : ι → Fin N) {b d : Fin N} (h : b ≠ d) :
    Disjoint (fiber f b) (fiber f d) := by
  apply Finset.disjoint_left.mpr
  intro i hi hd
  simp only [fiber, binItems, Finset.mem_filter, Finset.mem_univ, true_and] at hi hd
  exact h (hi.symm.trans hd)

theorem sum_fibers (f : ι → Fin N) (s : Finset (Fin N))
    {A : Type*} [AddCommMonoid A] (w : ι → A) :
    (∑ b ∈ s, ∑ i ∈ fiber f b, w i) = ∑ i ∈ itemsIn f s, w i := by
  exact Finset.sum_fiberwise_eq_sum_filter Finset.univ s f w

theorem card_itemsIn (f : ι → Fin N) (s : Finset (Fin N)) :
    (itemsIn f s).card = ∑ b ∈ s, (fiber f b).card := by
  exact (Finset.sum_card_fiberwise_eq_card_filter Finset.univ s f).symm

theorem sum_fiber_card (f : ι → Fin N) :
    ∑ b, (fiber f b).card = Fintype.card ι := by
  simpa [itemsIn] using (card_itemsIn f Finset.univ).symm

theorem sum_binPrimary (f : ι → Fin N) (p : ι → ℤ) :
    ∑ b, binPrimary f p b = ∑ i, p i := by
  simpa [itemsIn, binPrimary] using sum_fibers f Finset.univ p

theorem card_itemsIn_le (f : ι → Fin N)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (s : Finset (Fin N)) :
    (itemsIn f s).card ≤ 5 * s.card := by
  rw [card_itemsIn]
  calc
    (∑ b ∈ s, (fiber f b).card) ≤ ∑ _ ∈ s, 5 :=
      Finset.sum_le_sum fun b _ => hcap b
    _ = 5 * s.card := by simp [Nat.mul_comm]

theorem nonfullBins_card_le (f : ι → Fin N) (B c : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (hN : N ≤ B + c) :
    (nonfullBins f).card ≤ 5 * c := by
  have hmass : ∑ b, (fiber f b).card = 5 * B := (sum_fiber_card f).trans hcard
  have hdef : (∑ b, (5 - (fiber f b).card)) = 5 * N - 5 * B := by
    rw [Finset.sum_tsub_distrib _ (fun b _ => hcap b), hmass]
    simp [Nat.mul_comm]
  calc
    (nonfullBins f).card = ∑ _ ∈ nonfullBins f, 1 := by simp
    _ ≤ ∑ b ∈ nonfullBins f, (5 - (fiber f b).card) := by
      apply Finset.sum_le_sum
      intro b hb
      have hb' : (fiber f b).card < 5 := (Finset.mem_filter.mp hb).2
      omega
    _ ≤ ∑ b : Fin N, (5 - (fiber f b).card) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ 5 * c := by rw [hdef]; omega

theorem nonfullItems_card_le (f : ι → Fin N) (B c : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (hN : N ≤ B + c) :
    (nonfullItems f).card ≤ 25 * c := by
  have hi := card_itemsIn_le f hcap (nonfullBins f)
  have hb := nonfullBins_card_le f B c hcard hcap hN
  change (itemsIn f (nonfullBins f)).card ≤ 25 * c
  omega

theorem full_nonfull_disjoint (f : ι → Fin N) :
    Disjoint (nonfullBins f) (fullBins f) := by
  apply Finset.disjoint_left.mpr
  intro b hn hf
  have hn' := (Finset.mem_filter.mp hn).2
  have hf' := (Finset.mem_filter.mp hf).2
  omega

theorem full_nonfull_union (f : ι → Fin N)
    (hcap : ∀ b, (fiber f b).card ≤ 5) :
    nonfullBins f ∪ fullBins f = Finset.univ := by
  ext b
  simp only [Finset.mem_union, nonfullBins, fullBins, Finset.mem_filter,
    Finset.mem_univ, true_and, iff_true]
  have := hcap b
  omega

theorem primary_conservation (f : ι → Fin N) (p : ι → ℤ)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (htotal : ∑ i, p i = 0) :
    (∑ b ∈ nonfullBins f, binPrimary f p b) +
      (∑ b ∈ fullBins f, binPrimary f p b) = 0 := by
  rw [← Finset.sum_union (full_nonfull_disjoint f), full_nonfull_union f hcap,
    sum_binPrimary, htotal]

theorem negativeFullBins_card_le (f : ι → Fin N) (p : ι → ℤ) (B c P0 : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (hN : N ≤ B + c)
    (hp : ∀ i, p i ≤ (P0 : ℤ)) (htotal : ∑ i, p i = 0)
    (hfull : ∀ b, (fiber f b).card = 5 → binPrimary f p b ≤ 0) :
    (negativeFullBins f p).card ≤ 25 * c * P0 := by
  have hnegative : ((negativeFullBins f p).card : ℤ) ≤
      -(∑ b ∈ fullBins f, binPrimary f p b) := by
    calc
      ((negativeFullBins f p).card : ℤ) = ∑ _ ∈ negativeFullBins f p, (1 : ℤ) := by simp
      _ = ∑ b ∈ fullBins f, if binPrimary f p b < 0 then (1 : ℤ) else 0 := by
        rw [negativeFullBins, Finset.sum_filter]
      _ ≤ ∑ b ∈ fullBins f, -binPrimary f p b := by
        apply Finset.sum_le_sum
        intro b hb
        have h := hfull b (Finset.mem_filter.mp hb).2
        split_ifs <;> omega
      _ = _ := Finset.sum_neg_distrib (fun b => binPrimary f p b)
  have hnonfull : (∑ b ∈ nonfullBins f, binPrimary f p b) ≤
      ((nonfullItems f).card : ℤ) * (P0 : ℤ) := by
    change (∑ b ∈ nonfullBins f, ∑ i ∈ fiber f b, p i) ≤ _
    rw [sum_fibers]
    calc
      (∑ i ∈ itemsIn f (nonfullBins f), p i) ≤
          ∑ _ ∈ itemsIn f (nonfullBins f), (P0 : ℤ) :=
        Finset.sum_le_sum fun i _ => hp i
      _ = _ := by simp [nonfullItems]
  have hcons := primary_conservation f p hcap htotal
  have hitems : ((nonfullItems f).card : ℤ) ≤ (25 * c : ℕ) := by
    exact_mod_cast nonfullItems_card_le f B c hcard hcap hN
  have hscaled := mul_le_mul_of_nonneg_right hitems (Int.natCast_nonneg P0)
  have hbound : ((negativeFullBins f p).card : ℤ) ≤ ((25 * c * P0 : ℕ) : ℤ) := by
    push_cast
    push_cast at hscaled
    linarith
  exact_mod_cast hbound

variable [DecidableEq ι] in
theorem outsideZeroFullItems_eq (f : ι → Fin N) (p : ι → ℤ)
    (hcap : ∀ b, (fiber f b).card ≤ 5)
    (hfull : ∀ b, (fiber f b).card = 5 → binPrimary f p b ≤ 0) :
    outsideZeroFullItems f p = nonfullItems f ∪ itemsIn f (negativeFullBins f p) := by
  ext i
  simp only [outsideZeroFullItems, nonfullItems, itemsIn, negativeFullBins,
    nonfullBins, fullBins, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  have hc := hcap (f i)
  have hs := hfull (f i)
  omega

theorem loss_items_disjoint (f : ι → Fin N) (p : ι → ℤ) :
    Disjoint (nonfullItems f) (itemsIn f (negativeFullBins f p)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [nonfullItems, itemsIn, negativeFullBins, nonfullBins, fullBins,
    Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  omega

variable [DecidableEq ι] in
theorem primary_loss_bound (f : ι → Fin N) (p : ι → ℤ) (B c P0 : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (hN : N ≤ B + c)
    (hp : ∀ i, |p i| < (P0 : ℤ)) (htotal : ∑ i, p i = 0)
    (hfull : ∀ b, (fiber f b).card = 5 → binPrimary f p b ≤ 0) :
    (nonfullItems f).card ≤ 25 * c ∧
    (negativeFullBins f p).card ≤ 25 * c * P0 ∧
    (outsideZeroFullItems f p).card ≤ 25 * c * (1 + 5 * P0) ∧
    (outsideZeroFullItems f p).card < 25 * (c + 1) * (1 + 5 * P0) := by
  have hnf := nonfullItems_card_le f B c hcard hcap hN
  have hneg := negativeFullBins_card_le f p B c P0 hcard hcap hN
    (fun i => (le_abs_self (p i)).trans (hp i).le) htotal hfull
  have hni := card_itemsIn_le f hcap (negativeFullBins f p)
  have hbad : (outsideZeroFullItems f p).card ≤ 25 * c * (1 + 5 * P0) := by
    rw [outsideZeroFullItems_eq f p hcap hfull,
      Finset.card_union_of_disjoint (loss_items_disjoint f p)]
    nlinarith
  refine ⟨hnf, hneg, hbad, hbad.trans_lt ?_⟩
  nlinarith

end BinPackingGap.PrimaryLoss

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/PackingScalar.lean =====
namespace OAI

noncomputable section

namespace BinPackingGap

section

open scoped BigOperators

inductive Role
  | x
  | anchor
  | «global»
  | «local»
  | flag
  deriving DecidableEq

instance : Fintype Role where
  elems := {.x, .anchor, .«global», .«local», .flag}
  complete := by intro r; cases r <;> simp

inductive Subclass
  | tp
  | tm
  | s
  | z
  | y
  | up
  | um
  | w
  | dm
  | dg
  | ft
  | fm
  | fg
  deriving DecidableEq

instance : Fintype Subclass where
  elems := {.tp, .tm, .s, .z, .y, .up, .um, .w, .dm, .dg, .ft, .fm, .fg}
  complete := by intro subclass; cases subclass <;> simp

inductive Pattern
  | plusTree
  | minusTree
  | mainJob
  | edgeJob
  deriving DecidableEq

instance : Fintype Pattern where
  elems := {.plusTree, .minusTree, .mainJob, .edgeJob}
  complete := by intro p; cases p <;> simp

namespace Role

def index : Role → Fin 5
  | .x => 0
  | .anchor => 1
  | .«global» => 2
  | .«local» => 3
  | .flag => 4

theorem index_injective : Function.Injective index := by
  intro r s
  cases r <;> cases s <;> decide

theorem sum_univ {A : Type*} [AddCommMonoid A] (f : Role → A) :
    (∑ r, f r) = f .x + f .anchor + f .«global» + f .«local» + f .flag := by
  have h : (Finset.univ : Finset Role) =
      {.x, .anchor, .«global», .«local», .flag} := by decide
  rw [h]
  simp [add_assoc]

end Role

def Subclass.role : Subclass → Role
  | .tp | .tm | .s => .x
  | .z | .y => .anchor
  | .up | .um | .w => .«global»
  | .dm | .dg => .«local»
  | .ft | .fm | .fg => .flag

@[simp] theorem role_eq_x_iff (c : Subclass) :
    c.role = Role.x ↔ c = .tp ∨ c = .tm ∨ c = .s := by
  cases c <;> simp [Subclass.role]

@[simp] theorem role_eq_anchor_iff (c : Subclass) :
    c.role = Role.anchor ↔ c = .z ∨ c = .y := by
  cases c <;> simp [Subclass.role]

@[simp] theorem role_eq_global_iff (c : Subclass) :
    c.role = Role.«global» ↔ c = .up ∨ c = .um ∨ c = .w := by
  cases c <;> simp [Subclass.role]

@[simp] theorem role_eq_local_iff (c : Subclass) :
    c.role = Role.«local» ↔ c = .dm ∨ c = .dg := by
  cases c <;> simp [Subclass.role]

@[simp] theorem role_eq_flag_iff (c : Subclass) :
    c.role = Role.flag ↔ c = .ft ∨ c = .fm ∨ c = .fg := by
  cases c <;> simp [Subclass.role]

def patternSubclass : Pattern → Role → Subclass
  | .plusTree, .x => .tp
  | .plusTree, .anchor => .z
  | .plusTree, .«global» => .up
  | .plusTree, .«local» => .dm
  | .plusTree, .flag => .ft
  | .minusTree, .x => .tm
  | .minusTree, .anchor => .z
  | .minusTree, .«global» => .um
  | .minusTree, .«local» => .dm
  | .minusTree, .flag => .ft
  | .mainJob, .x => .s
  | .mainJob, .anchor => .z
  | .mainJob, .«global» => .up
  | .mainJob, .«local» => .dm
  | .mainJob, .flag => .fm
  | .edgeJob, .x => .s
  | .edgeJob, .anchor => .y
  | .edgeJob, .«global» => .w
  | .edgeJob, .«local» => .dg
  | .edgeJob, .flag => .fg

@[simp] theorem patternSubclass_role (p : Pattern) (r : Role) :
    (patternSubclass p r).role = r := by
  cases p <;> cases r <;> rfl

theorem patternSubclass_injective (p : Pattern) :
    Function.Injective (patternSubclass p) := by
  intro r s h
  simpa only [patternSubclass_role] using congrArg Subclass.role h

theorem patternSubclass_function_injective : Function.Injective patternSubclass := by
  intro p q hpq
  have hx := congrFun hpq Role.x
  have hf := congrFun hpq Role.flag
  cases p <;> cases q <;> simp_all [patternSubclass]

@[simp] theorem card_role : Fintype.card Role = 5 := by decide

@[simp] theorem card_subclass : Fintype.card Subclass = 13 := by decide

@[simp] theorem card_pattern : Fintype.card Pattern = 4 := by decide

def IsPatternTuple (t : Fin 5 → Subclass) : Prop :=
  ∃ p : Pattern, ∃ e : Fin 5 ≃ Role, ∀ i, t i = patternSubclass p (e i)

theorem existsUnique_role_of_pattern {t : Fin 5 → Subclass}
    (ht : IsPatternTuple t) (r : Role) : ∃! i : Fin 5, (t i).role = r := by
  obtain ⟨p, e, he⟩ := ht
  refine ⟨e.symm r, ?_, ?_⟩
  · change (t (e.symm r)).role = r
    rw [he, patternSubclass_role, e.apply_symm_apply]
  · intro i hi
    apply e.injective
    simpa only [he, patternSubclass_role, e.apply_symm_apply] using hi

theorem pattern_eq_of_tuple {t : Fin 5 → Subclass} {p q : Pattern}
    {e f : Fin 5 ≃ Role}
    (hp : ∀ i, t i = patternSubclass p (e i))
    (hq : ∀ i, t i = patternSubclass q (f i)) : p = q := by
  have hef : e = f := by
    apply Equiv.ext
    intro i
    simpa only [patternSubclass_role] using
      congrArg Subclass.role ((hp i).symm.trans (hq i))
  apply patternSubclass_function_injective
  funext r
  simpa only [← hef, e.apply_symm_apply] using
    (hp (e.symm r)).symm.trans (hq (e.symm r))

end

section

def labelWeight {n : ℕ} (v : Fin n) : ℤ := 3 ^ (v.val + 1)

def labelSecondary {n : ℕ} (x d a : Fin n) : ℤ :=
  labelWeight x + labelWeight d - 2 * labelWeight a

theorem labelWeight_pos {n : ℕ} (v : Fin n) : 0 < labelWeight v := by
  exact pow_pos (by norm_num : (0 : ℤ) < 3) _

theorem labelWeight_le {n : ℕ} (v : Fin n) : labelWeight v ≤ (3 : ℤ) ^ n := by
  unfold labelWeight
  exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3)
    (Nat.succ_le_of_lt v.isLt)

theorem labelWeight_strictMono {n : ℕ} : StrictMono (@labelWeight n) := by
  intro x y hxy
  change (3 : ℤ) ^ (x.val + 1) < (3 : ℤ) ^ (y.val + 1)
  exact pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 3)
    (Nat.add_lt_add_right hxy 1)

theorem labelWeight_mono {n : ℕ} {x a : Fin n} (h : x ≤ a) :
    labelWeight x ≤ labelWeight a :=
  labelWeight_strictMono.monotone h

theorem labelWeight_gap {n : ℕ} {a x : Fin n} (h : a < x) :
    3 * labelWeight a ≤ labelWeight x := by
  have hax : a.val + 1 ≤ x.val := Nat.succ_le_of_lt h
  have hpow : (3 : ℤ) ^ ((a.val + 1) + 1) ≤ (3 : ℤ) ^ (x.val + 1) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3)
      (Nat.add_le_add_right hax 1)
  calc
    3 * labelWeight a = (3 : ℤ) ^ ((a.val + 1) + 1) := by
      change (3 : ℤ) * (3 : ℤ) ^ (a.val + 1) = _
      rw [pow_succ (3 : ℤ) (a.val + 1), mul_comm]
    _ ≤ labelWeight x := hpow

theorem labelSecondary_nonpos_bounds {n : ℕ} {x d a : Fin n}
    (hq : labelSecondary x d a ≤ 0) : x ≤ a ∧ d ≤ a := by
  have ha := labelWeight_pos a
  have hx := labelWeight_pos x
  have hd := labelWeight_pos d
  change labelWeight x + labelWeight d - 2 * labelWeight a ≤ 0 at hq
  constructor
  · by_contra hxa
    have hgap := labelWeight_gap (lt_of_not_ge hxa)
    linarith
  · by_contra hda
    have hgap := labelWeight_gap (lt_of_not_ge hda)
    linarith

theorem labelSecondary_nonpos_iff {n : ℕ} {x d a : Fin n} :
    labelSecondary x d a ≤ 0 ↔ x ≤ a ∧ d ≤ a := by
  constructor
  · exact labelSecondary_nonpos_bounds
  · rintro ⟨hx, hd⟩
    have hqx := labelWeight_mono hx
    have hqd := labelWeight_mono hd
    unfold labelSecondary
    linarith

@[simp] theorem labelSecondary_self {n : ℕ} (a : Fin n) :
    labelSecondary a a a = 0 := by
  unfold labelSecondary
  linarith

theorem labelSecondary_eq_zero_iff {n : ℕ} {x d a : Fin n} :
    labelSecondary x d a = 0 ↔ x = a ∧ d = a := by
  constructor
  · intro hq
    obtain ⟨hx, hd⟩ := labelSecondary_nonpos_bounds (le_of_eq hq)
    have hqx := labelWeight_mono hx
    have hqd := labelWeight_mono hd
    change labelWeight x + labelWeight d - 2 * labelWeight a = 0 at hq
    constructor
    · rcases lt_or_eq_of_le hx with hxa | hxa
      · have hlt := labelWeight_strictMono hxa
        linarith
      · exact hxa
    · rcases lt_or_eq_of_le hd with hda | hda
      · have hlt := labelWeight_strictMono hda
        linarith
      · exact hda
  · rintro ⟨rfl, rfl⟩
    exact labelSecondary_self _

open scoped BigOperators

def subclassIndicator (a b : Subclass) : ℤ := if a = b then 1 else 0

def primaryCoeff (j : Fin 10) (subclass : Subclass) : ℤ :=
  match j.val with
  | 0 => 5 * (if subclass.role = .x then 1 else 0) - 1
  | 1 => 5 * (if subclass.role = .anchor then 1 else 0) - 1
  | 2 => 5 * (if subclass.role = .«global» then 1 else 0) - 1
  | 3 => 5 * (if subclass.role = .«local» then 1 else 0) - 1
  | 4 => 5 * (if subclass.role = .flag then 1 else 0) - 1
  | 5 => subclassIndicator subclass .tp + subclassIndicator subclass .tm - subclassIndicator subclass .ft
  | 6 => subclassIndicator subclass .z - subclassIndicator subclass .ft - subclassIndicator subclass .fm
  | 7 => subclassIndicator subclass .up + subclassIndicator subclass .um -
      subclassIndicator subclass .ft - subclassIndicator subclass .fm
  | 8 => subclassIndicator subclass .dm - subclassIndicator subclass .ft - subclassIndicator subclass .fm
  | 9 => subclassIndicator subclass .tm - subclassIndicator subclass .um
  | _ => 0

def primaryScore (subclass : Subclass) : ℤ :=
  ∑ j : Fin 10, (100 : ℤ) ^ j.val * primaryCoeff j subclass

def primaryBound : ℕ := 100 ^ 11

def roleCoeffIndex (r : Role) : Fin 10 :=
  ⟨r.index.val, lt_trans r.index.isLt (by decide)⟩

theorem primaryCoeff_role (r : Role) (subclass : Subclass) :
    primaryCoeff (roleCoeffIndex r) subclass = 5 * (if subclass.role = r then 1 else 0) - 1 := by
  cases r <;> cases subclass <;> decide

theorem primaryCoeff_abs_le (j : Fin 10) (subclass : Subclass) :
    |primaryCoeff j subclass| ≤ 4 := by
  fin_cases j <;> cases subclass <;> decide

theorem primaryScore_abs_lt (subclass : Subclass) :
    |primaryScore subclass| < (primaryBound : ℤ) := by
  cases subclass <;>
    norm_num [primaryScore, primaryCoeff, subclassIndicator, Subclass.role,
      primaryBound, Fin.sum_univ_succ] <;> decide

theorem sum_primaryScore_eq {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryScore (t i)) =
      ∑ j : Fin 10, (100 : ℤ) ^ j.val * (∑ i, primaryCoeff j (t i)) := by
  simp only [primaryScore, Finset.mul_sum]
  exact Finset.sum_comm

def roleCount {I : Type*} [Fintype I] (t : I → Subclass) (r : Role) : ℤ :=
  ∑ i, if (t i).role = r then 1 else 0

def subclassCount {I : Type*} [Fintype I] (t : I → Subclass) (subclass : Subclass) : ℤ :=
  ∑ i, subclassIndicator (t i) subclass

theorem sum_primaryCoeff_role {I : Type*} [Fintype I]
    (t : I → Subclass) (r : Role) :
    (∑ i, primaryCoeff (roleCoeffIndex r) (t i)) =
      5 * roleCount t r - (Fintype.card I : ℤ) := by
  simp only [primaryCoeff_role, Finset.sum_sub_distrib, ← Finset.mul_sum,
    roleCount, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem sum_primaryCoeff_five {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 5 (t i)) =
      subclassCount t .tp + subclassCount t .tm - subclassCount t .ft := by
  simp [primaryCoeff, subclassCount, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem sum_primaryCoeff_six {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 6 (t i)) =
      subclassCount t .z - subclassCount t .ft - subclassCount t .fm := by
  simp [primaryCoeff, subclassCount, Finset.sum_sub_distrib]

theorem sum_primaryCoeff_seven {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 7 (t i)) =
      subclassCount t .up + subclassCount t .um -
        subclassCount t .ft - subclassCount t .fm := by
  simp [primaryCoeff, subclassCount, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem sum_primaryCoeff_eight {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 8 (t i)) =
      subclassCount t .dm - subclassCount t .ft - subclassCount t .fm := by
  simp [primaryCoeff, subclassCount, Finset.sum_sub_distrib]

theorem sum_primaryCoeff_nine {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 9 (t i)) = subclassCount t .tm - subclassCount t .um := by
  simp [primaryCoeff, subclassCount, Finset.sum_sub_distrib]

theorem radix100_eq_zero_iff {n : ℕ} (a : Fin n → ℤ)
    (ha : ∀ i, |a i| < 100) :
    (∑ i, (100 : ℤ) ^ i.val * a i) = 0 ↔ ∀ i, a i = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      constructor
      · intro hs
        have hsplit : a 0 + 100 * (∑ i : Fin n, (100 : ℤ) ^ i.val * a i.succ) = 0 := by
          calc
            a 0 + 100 * (∑ i : Fin n, (100 : ℤ) ^ i.val * a i.succ) =
                ∑ i : Fin (n + 1), (100 : ℤ) ^ i.val * a i := by
              rw [Fin.sum_univ_succ]
              simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ]
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [pow_succ]
              ring
            _ = 0 := hs
        have hfirst := abs_lt.mp (ha 0)
        have hz : a 0 = 0 := by omega
        have htail : (∑ i : Fin n, (100 : ℤ) ^ i.val * a i.succ) = 0 := by omega
        have hrest := (ih (fun i => a i.succ) (fun i => ha i.succ)).mp htail
        intro i
        exact Fin.cases hz (fun k => hrest k) i
      · intro hz
        simp [hz]

theorem primaryCoeff_total_abs_lt (t : Fin 5 → Subclass) (j : Fin 10) :
    |∑ i, primaryCoeff j (t i)| < 100 := by
  calc
    |∑ i, primaryCoeff j (t i)| ≤ ∑ i, |primaryCoeff j (t i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 5, (4 : ℤ) :=
      Finset.sum_le_sum (fun i _ => primaryCoeff_abs_le j (t i))
    _ < 100 := by norm_num

theorem sum_primaryScore_eq_zero_iff_coefficients (t : Fin 5 → Subclass) :
    (∑ i, primaryScore (t i)) = 0 ↔ ∀ j : Fin 10, (∑ i, primaryCoeff j (t i)) = 0 := by
  rw [sum_primaryScore_eq]
  exact radix100_eq_zero_iff _ (primaryCoeff_total_abs_lt t)

theorem pattern_primaryCoeff_sum (p : Pattern) (j : Fin 10) :
    (∑ r : Role, primaryCoeff j (patternSubclass p r)) = 0 := by
  cases p <;> fin_cases j <;>
    norm_num [Role.sum_univ, patternSubclass, primaryCoeff, subclassIndicator,
      Subclass.role] <;> decide

private theorem sum_role_subclassIndicator (v : Role → Subclass)
    (hrole : ∀ r, (v r).role = r) (c : Subclass) :
    (∑ r : Role, subclassIndicator (v r) c) = subclassIndicator (v c.role) c := by
  classical
  apply Finset.sum_eq_single c.role
  · intro r _ hr
    have hne : v r ≠ c := by
      intro he
      exact hr ((hrole r).symm.trans (congrArg Subclass.role he))
    simp [subclassIndicator, hne]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem roleTuple_eq_pattern (v : Role → Subclass)
    (hrole : ∀ r, (v r).role = r)
    (hcoeff : ∀ j : Fin 10, (∑ r, primaryCoeff j (v r)) = 0) :
    ∃ p : Pattern, ∀ r, v r = patternSubclass p r := by
  have hx := (role_eq_x_iff _).mp (hrole .x)
  have ha := (role_eq_anchor_iff _).mp (hrole .anchor)
  have hu := (role_eq_global_iff _).mp (hrole .«global»)
  have hd := (role_eq_local_iff _).mp (hrole .«local»)
  have hf := (role_eq_flag_iff _).mp (hrole .flag)
  have h5 := hcoeff 5
  have h6 := hcoeff 6
  have h7 := hcoeff 7
  have h8 := hcoeff 8
  have h9 := hcoeff 9
  rw [sum_primaryCoeff_five] at h5
  rw [sum_primaryCoeff_six] at h6
  rw [sum_primaryCoeff_seven] at h7
  rw [sum_primaryCoeff_eight] at h8
  rw [sum_primaryCoeff_nine] at h9
  simp only [subclassCount, sum_role_subclassIndicator v hrole, Subclass.role]
    at h5 h6 h7 h8 h9
  rcases hf with hf | hf | hf
  all_goals
    rcases ha with ha | ha <;> rcases hd with hd | hd
  all_goals
    simp +decide [subclassIndicator, ha, hd, hf] at h6 h8
  all_goals
    rcases hx with hx | hx | hx <;> rcases hu with hu | hu | hu
  all_goals
    simp +decide [subclassIndicator, hx, hu, hf] at h5 h7 h9
  · refine ⟨.plusTree, ?_⟩
    intro r
    cases r <;> simp [patternSubclass, hx, ha, hu, hd, hf]
  · refine ⟨.minusTree, ?_⟩
    intro r
    cases r <;> simp [patternSubclass, hx, ha, hu, hd, hf]
  · refine ⟨.mainJob, ?_⟩
    intro r
    cases r <;> simp [patternSubclass, hx, ha, hu, hd, hf]
  · refine ⟨.edgeJob, ?_⟩
    intro r
    cases r <;> simp [patternSubclass, hx, ha, hu, hd, hf]

theorem sum_primaryScore_eq_zero_iff_pattern (t : Fin 5 → Subclass) :
    (∑ i, primaryScore (t i)) = 0 ↔ IsPatternTuple t := by
  classical
  rw [sum_primaryScore_eq_zero_iff_coefficients]
  constructor
  · intro hc
    have hcount (r : Role) : roleCount t r = 1 := by
      have h := hc (roleCoeffIndex r)
      rw [sum_primaryCoeff_role] at h
      norm_num at h
      omega
    have hsurj : Function.Surjective (fun i : Fin 5 => (t i).role) := by
      intro r
      by_contra hno
      have hne : ∀ i : Fin 5, (t i).role ≠ r := fun i hi => hno ⟨i, hi⟩
      have hh := hcount r
      simp [roleCount, hne] at hh
    let e₀ : Fin 5 ≃ Role := Fintype.equivOfCardEq (by simp)
    have hinj : Function.Injective (fun i : Fin 5 => (t i).role) :=
      (Finite.injective_iff_surjective_of_equiv e₀).mpr hsurj
    let e : Fin 5 ≃ Role := Equiv.ofBijective _ ⟨hinj, hsurj⟩
    let v : Role → Subclass := fun r => t (e.symm r)
    have hvrole (r : Role) : (v r).role = r := by
      change e (e.symm r) = r
      exact e.apply_symm_apply r
    have hvcoeff (j : Fin 10) : (∑ r : Role, primaryCoeff j (v r)) = 0 := by
      calc
        (∑ r : Role, primaryCoeff j (v r)) =
            ∑ i : Fin 5, primaryCoeff j (v (e i)) := (e.sum_comp _).symm
        _ = 0 := by simpa [v] using hc j
    obtain ⟨p, hp⟩ := roleTuple_eq_pattern v hvrole hvcoeff
    refine ⟨p, e, ?_⟩
    intro i
    simpa [v] using hp (e i)
  · rintro ⟨p, e, he⟩ j
    calc
      (∑ i, primaryCoeff j (t i)) =
          ∑ i : Fin 5, primaryCoeff j (patternSubclass p (e i)) := by simp only [he]
      _ = ∑ r : Role, primaryCoeff j (patternSubclass p r) :=
        e.sum_comp (fun r : Role => primaryCoeff j (patternSubclass p r))
      _ = 0 := pattern_primaryCoeff_sum p j

theorem sum_primaryScore_eq_zero_of_coefficients {I : Type*} [Fintype I]
    (t : I → Subclass) (h : ∀ j : Fin 10, (∑ i, primaryCoeff j (t i)) = 0) :
    (∑ i, primaryScore (t i)) = 0 := by
  rw [sum_primaryScore_eq]
  simp [h]

end

section

def secondaryScore {n : ℕ} (subclass : Subclass) (label : Option (Fin n)) : ℤ :=
  let q := label.elim 0 labelWeight
  match subclass.role with
  | .x => q
  | .anchor => -2 * q
  | .«global» => 0
  | .«local» => q
  | .flag => 0

@[simp] theorem secondaryScore_none {n : ℕ} (subclass : Subclass) :
    secondaryScore subclass (none : Option (Fin n)) = 0 := by
  cases hs : subclass.role <;> simp [secondaryScore, hs]

def tableRoleLabel {n : ℕ} (x d a : Fin n) : Role → Option (Fin n)
  | .x => some x
  | .anchor => some a
  | .«global» => none
  | .«local» => some d
  | .flag => none

def gamma : ℚ := 1 / (1000 * (primaryBound : ℚ))

def mu (n : ℕ) : ℚ := gamma / (1000 * (3 : ℚ) ^ n)

def nu (n : ℕ) : ℚ := mu n / 1000

def encodedSize {n : ℕ} (subclass : Subclass) (label : Option (Fin n)) (w : ℚ) : ℚ :=
  1 / 5 + gamma * (primaryScore subclass : ℚ) +
    mu n * (secondaryScore subclass label : ℚ) + nu n * w

theorem gamma_pos : 0 < gamma := by
  norm_num [gamma, primaryBound]

theorem gamma_le_one : gamma ≤ 1 := by
  norm_num [gamma, primaryBound]

theorem gamma_mul_primaryBound : gamma * (primaryBound : ℚ) = 1 / 1000 := by
  norm_num [gamma, primaryBound]

theorem mu_pos (n : ℕ) : 0 < mu n := by
  exact div_pos gamma_pos (mul_pos (by norm_num) (pow_pos (by norm_num) n))

theorem nu_pos (n : ℕ) : 0 < nu n := div_pos (mu_pos n) (by norm_num)

theorem mu_mul_labelBound (n : ℕ) : mu n * (3 : ℚ) ^ n = gamma / 1000 := by
  unfold mu
  have hn : (3 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp [hn]

theorem mu_le_gamma_div (n : ℕ) : mu n ≤ gamma / 1000 := by
  have hn : (1 : ℚ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have h := mul_le_mul_of_nonneg_left hn (mu_pos n).le
  rw [mul_one, mu_mul_labelBound] at h
  exact h

theorem nu_le_gamma_div (n : ℕ) : nu n ≤ gamma / 1000000 := by
  have h := div_le_div_of_nonneg_right (mu_le_gamma_div n) (by norm_num : (0 : ℚ) ≤ 1000)
  simpa only [nu, div_div, show (1000 : ℚ) * 1000 = 1000000 by norm_num] using h

theorem secondaryScore_abs_le {n : ℕ} (subclass : Subclass) (label : Option (Fin n)) :
    |secondaryScore subclass label| ≤ 2 * (3 : ℤ) ^ n := by
  cases label with
  | none =>
      cases hs : subclass.role <;> simp [secondaryScore, hs]
  | some v =>
      have hv0 := labelWeight_pos v
      have hv := labelWeight_le v
      cases hs : subclass.role <;>
        norm_num [secondaryScore, hs, abs_mul, abs_of_pos hv0] <;> linarith

theorem secondaryScore_rat_abs_le {n : ℕ} (subclass : Subclass) (label : Option (Fin n)) :
    |(secondaryScore subclass label : ℚ)| ≤ 2 * (3 : ℚ) ^ n := by
  exact_mod_cast secondaryScore_abs_le subclass label

theorem primaryScore_rat_abs_le (subclass : Subclass) :
    |(primaryScore subclass : ℚ)| ≤ (primaryBound : ℚ) := by
  exact_mod_cast (primaryScore_abs_lt subclass).le

private theorem perturbation_triangle (g m v p q w : ℚ)
    (hg : 0 ≤ g) (hm : 0 ≤ m) (hv : 0 ≤ v) :
    |(1 / 5 + g * p + m * q + v * w) - 1 / 5| ≤
      g * |p| + m * |q| + v * |w| := by
  have heq : (1 / 5 + g * p + m * q + v * w) - 1 / 5 =
      g * p + m * q + v * w := by ring
  rw [heq]
  have hp : |g * p| = g * |p| := by rw [abs_mul, abs_of_nonneg hg]
  have hq : |m * q| = m * |q| := by rw [abs_mul, abs_of_nonneg hm]
  have hw : |v * w| = v * |w| := by rw [abs_mul, abs_of_nonneg hv]
  have hfirst : |g * p + m * q| ≤ |g * p| + |m * q| :=
    abs_add_le (g * p) (m * q)
  have hsecond : |g * p + m * q + v * w| ≤ |g * p + m * q| + |v * w| :=
    abs_add_le (g * p + m * q) (v * w)
  rw [hp, hq] at hfirst
  rw [hw] at hsecond
  linarith only [hfirst, hsecond]

private theorem perturbation_small (g m v p q w : ℚ)
    (hg : 0 ≤ g) (hm : 0 ≤ m) (hv : 0 ≤ v) (hg1 : g ≤ 1)
    (hp : g * |p| ≤ 1 / 1000) (hq : m * |q| ≤ 2 * g / 1000)
    (hw : v * |w| ≤ v * 6) (hnu : v ≤ g / 1000000) :
    |(1 / 5 + g * p + m * q + v * w) - 1 / 5| ≤ 1 / 100 := by
  have hsum := perturbation_triangle g m v p q w hg hm hv
  nlinarith only [hsum, hg1, hp, hq, hw, hnu]

theorem encodedSize_perturbation_bound {n : ℕ} (subclass : Subclass)
    (label : Option (Fin n)) (w : ℚ) (hw : |w| ≤ 6) :
    |encodedSize subclass label w - 1 / 5| ≤ 1 / 100 := by
  have hp := mul_le_mul_of_nonneg_left (primaryScore_rat_abs_le subclass) gamma_pos.le
  rw [gamma_mul_primaryBound] at hp
  have hq := mul_le_mul_of_nonneg_left (secondaryScore_rat_abs_le subclass label) (mu_pos n).le
  have hq' : mu n * |(secondaryScore subclass label : ℚ)| ≤ 2 * gamma / 1000 := by
    calc
      _ ≤ mu n * (2 * (3 : ℚ) ^ n) := hq
      _ = 2 * gamma / 1000 := by
        rw [← mul_assoc, mul_comm (mu n) 2, mul_assoc, mu_mul_labelBound]
        ring
  have hw' := mul_le_mul_of_nonneg_left hw (nu_pos n).le
  exact perturbation_small gamma (mu n) (nu n) (primaryScore subclass)
    (secondaryScore subclass label) w gamma_pos.le (mu_pos n).le (nu_pos n).le
    gamma_le_one hp hq' hw' (nu_le_gamma_div n)

theorem encodedSize_mem_interval {n : ℕ} (subclass : Subclass)
    (label : Option (Fin n)) (w : ℚ) (hw : |w| ≤ 6) :
    1 / 6 < encodedSize subclass label w ∧ encodedSize subclass label w < 1 := by
  have hb := abs_le.mp (encodedSize_perturbation_bound subclass label w hw)
  constructor <;> linarith

theorem primary_tail_lt (n : ℕ) :
    mu n * (10 * (3 : ℚ) ^ n) + nu n * 30 < gamma := by
  have heq : mu n * (10 * (3 : ℚ) ^ n) = 10 * gamma / 1000 := by
    rw [← mul_assoc, mul_comm (mu n) 10, mul_assoc, mu_mul_labelBound]
    ring
  rw [heq]
  have hn := nu_le_gamma_div n
  have hg := gamma_pos
  nlinarith

theorem secondary_tail_lt (n : ℕ) : nu n * 30 < mu n := by
  have hμ := mu_pos n
  unfold nu
  nlinarith

open scoped BigOperators

namespace Packing

variable {I : Instance} {b : ℕ}

def primaryTotal (p : Packing I b) (subclass : I.Item → Subclass) (j : Fin b) : ℤ :=
  ∑ i ∈ p.binItems j, primaryScore (subclass i)

def IsTableBin (p : Packing I b) (subclass : I.Item → Subclass) (j : Fin b) : Prop :=
  (p.binItems j).card = 5 ∧ p.primaryTotal subclass j = 0

abbrev TableBin (p : Packing I b) (subclass : I.Item → Subclass) :=
  {j : Fin b // p.IsTableBin subclass j}

instance (p : Packing I b) (subclass : I.Item → Subclass) :
    Fintype (p.TableBin subclass) := Fintype.ofFinite _

instance (p : Packing I b) (subclass : I.Item → Subclass) :
    DecidableEq (p.TableBin subclass) := Classical.decEq _

theorem table_pattern (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) :
    ∃ pat : Pattern, ∃ e : Role ≃ p.binItems t.val,
      ∀ r, subclass (e r).val = patternSubclass pat r := by
  classical
  let e : Fin 5 ≃ p.binItems t.val :=
    (Finset.equivFinOfCardEq t.property.1).symm
  have hz : (∑ i : Fin 5, primaryScore (subclass (e i).val)) = 0 := by
    rw [e.sum_comp (fun i : p.binItems t.val => primaryScore (subclass i.val))]
    change (∑ i ∈ (p.binItems t.val).attach, primaryScore (subclass i.val)) = 0
    rw [Finset.sum_attach (p.binItems t.val) (fun i => primaryScore (subclass i))]
    exact t.property.2
  obtain ⟨pat, perm, hp⟩ :=
    (sum_primaryScore_eq_zero_iff_pattern (fun i => subclass (e i).val)).mp hz
  refine ⟨pat, perm.symm.trans e, ?_⟩
  intro r
  simpa using hp (perm.symm r)

def tablePattern (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) : Pattern :=
  Classical.choose (p.table_pattern subclass t)

def tableEquiv (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) : Role ≃ p.binItems t.val :=
  Classical.choose (Classical.choose_spec (p.table_pattern subclass t))

theorem tableEquiv_subclass (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) :
    subclass (p.tableEquiv subclass t r).val =
      patternSubclass (p.tablePattern subclass t) r :=
  Classical.choose_spec (Classical.choose_spec (p.table_pattern subclass t)) r

def itemAtRole (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) : I.Item :=
  (p.tableEquiv subclass t r).val

theorem itemAtRole_mem (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) :
    p.itemAtRole subclass t r ∈ p.binItems t.val :=
  (p.tableEquiv subclass t r).property

theorem itemAtRole_subclass (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) :
    subclass (p.itemAtRole subclass t r) =
      patternSubclass (p.tablePattern subclass t) r :=
  p.tableEquiv_subclass subclass t r

@[simp] theorem itemAtRole_role (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) :
    (subclass (p.itemAtRole subclass t r)).role = r := by
  rw [p.itemAtRole_subclass subclass t r, patternSubclass_role]

theorem itemAtRole_injective (p : Packing I b) (subclass : I.Item → Subclass)
    (r : Role) : Function.Injective (fun t => p.itemAtRole subclass t r) :=
  p.chosen_injective Subtype.val Subtype.val_injective
    (fun t => p.itemAtRole subclass t r) (fun t => p.itemAtRole_mem subclass t r)

theorem itemAtRole_joint_injective (p : Packing I b) (subclass : I.Item → Subclass) :
    Function.Injective (fun tr : p.TableBin subclass × Role =>
      p.itemAtRole subclass tr.1 tr.2) := by
  intro x y h
  have hr : x.2 = y.2 := by
    have := congrArg (fun i => (subclass i).role) h
    simpa only [itemAtRole_role] using this
  have ht : x.1 = y.1 := by
    apply p.itemAtRole_injective subclass x.2
    simpa only [hr] using h
  exact Prod.ext ht hr

theorem mem_table_bin_iff (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (i : I.Item) :
    i ∈ p.binItems t.val ↔ ∃ r, p.itemAtRole subclass t r = i := by
  constructor
  · intro hi
    refine ⟨(p.tableEquiv subclass t).symm ⟨i, hi⟩, ?_⟩
    simp [itemAtRole]
  · rintro ⟨r, rfl⟩
    exact p.itemAtRole_mem subclass t r

theorem itemAtRole_eq_of_mem (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) (i : I.Item)
    (hi : i ∈ p.binItems t.val) (hr : (subclass i).role = r) :
    p.itemAtRole subclass t r = i := by
  obtain ⟨s, hs⟩ := (p.mem_table_bin_iff subclass t i).mp hi
  have hsr : s = r := by
    rw [← hs, p.itemAtRole_role] at hr
    exact hr
  simpa only [hsr] using hs

def IsGoodTableBin (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) (t : p.TableBin subclass) : Prop :=
  label (p.itemAtRole subclass t .x) = label (p.itemAtRole subclass t .anchor) ∧
    label (p.itemAtRole subclass t .«local») =
      label (p.itemAtRole subclass t .anchor)

abbrev GoodTableBin (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) :=
  {t : p.TableBin subclass // p.IsGoodTableBin subclass label t}

instance (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) :
    Fintype (p.GoodTableBin subclass label) := Fintype.ofFinite _

abbrev GoodM (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) :=
  {t : p.GoodTableBin subclass label // p.tablePattern subclass t.val ≠ .edgeJob}

abbrev GoodG (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) :=
  {t : p.GoodTableBin subclass label // p.tablePattern subclass t.val = .edgeJob}

instance (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) :
    Fintype (p.GoodM subclass label) := Fintype.ofFinite _

instance (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) :
    Fintype (p.GoodG subclass label) := Fintype.ofFinite _

end Packing

end

open scoped BigOperators

def primaryTotal (s : Fin 5 → Subclass) : ℤ := ∑ i, primaryScore (s i)

def secondaryTotal {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) : ℤ := ∑ i, secondaryScore (s i) (label i)

def coordinateTotal (w : Fin 5 → ℚ) : ℚ := ∑ i, w i

theorem encodedSize_sum {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (w : Fin 5 → ℚ) :
    (∑ i, encodedSize (s i) (label i) (w i)) =
      1 + gamma * (primaryTotal s : ℚ) +
        mu n * (secondaryTotal s label : ℚ) + nu n * coordinateTotal w := by
  simp [encodedSize, primaryTotal, secondaryTotal, coordinateTotal,
    Finset.sum_add_distrib, Finset.mul_sum]

theorem secondaryTotal_rat_abs_le {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) :
    |(secondaryTotal s label : ℚ)| ≤ 10 * (3 : ℚ) ^ n := by
  calc
    _ = |∑ i, (secondaryScore (s i) (label i) : ℚ)| := by simp [secondaryTotal]
    _ ≤ ∑ i, |(secondaryScore (s i) (label i) : ℚ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 5, 2 * (3 : ℚ) ^ n :=
      Finset.sum_le_sum (fun i _ => secondaryScore_rat_abs_le (s i) (label i))
    _ = _ := by norm_num; ring

theorem coordinateTotal_abs_le (w : Fin 5 → ℚ) (hw : ∀ i, |w i| ≤ 6) :
    |coordinateTotal w| ≤ 30 := by
  calc
    _ ≤ ∑ i, |w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 5, (6 : ℚ) := Finset.sum_le_sum (fun i _ => hw i)
    _ = _ := by norm_num

theorem sum_primary_nonpos_of_feasible {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (w : Fin 5 → ℚ)
    (hw : ∀ i, |w i| ≤ 6)
    (hfeas : (∑ i, encodedSize (s i) (label i) (w i)) ≤ 1) :
    primaryTotal s ≤ 0 := by
  by_contra h
  have hp : (1 : ℤ) ≤ primaryTotal s :=
    Int.add_one_le_iff.mpr (lt_of_not_ge h)
  have hpQ : (1 : ℚ) ≤ (primaryTotal s : ℚ) := by exact_mod_cast hp
  have hp' := mul_le_mul_of_nonneg_left hpQ gamma_pos.le
  have hq := mul_le_mul_of_nonneg_left
    (abs_le.mp (secondaryTotal_rat_abs_le s label)).1 (mu_pos n).le
  have hw' := mul_le_mul_of_nonneg_left
    (abs_le.mp (coordinateTotal_abs_le w hw)).1 (nu_pos n).le
  have htail := primary_tail_lt n
  rw [encodedSize_sum] at hfeas
  nlinarith only [hfeas, hp', hq, hw', htail]

theorem sum_secondary_nonpos_of_feasible {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (w : Fin 5 → ℚ)
    (hw : ∀ i, |w i| ≤ 6) (hp : primaryTotal s = 0)
    (hfeas : (∑ i, encodedSize (s i) (label i) (w i)) ≤ 1) :
    secondaryTotal s label ≤ 0 := by
  by_contra h
  have hq : (1 : ℤ) ≤ secondaryTotal s label :=
    Int.add_one_le_iff.mpr (lt_of_not_ge h)
  have hqQ : (1 : ℚ) ≤ (secondaryTotal s label : ℚ) := by exact_mod_cast hq
  have hq' := mul_le_mul_of_nonneg_left hqQ (mu_pos n).le
  have hw' := mul_le_mul_of_nonneg_left
    (abs_le.mp (coordinateTotal_abs_le w hw)).1 (nu_pos n).le
  have htail := secondary_tail_lt n
  rw [encodedSize_sum, hp] at hfeas
  norm_num only [Int.cast_zero, mul_zero, add_zero] at hfeas
  nlinarith only [hfeas, hq', hw', htail]

theorem feasible_iff_coordinateSum_nonpos {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (w : Fin 5 → ℚ)
    (hp : primaryTotal s = 0) (hq : secondaryTotal s label = 0) :
    ((∑ i, encodedSize (s i) (label i) (w i)) ≤ 1) ↔ coordinateTotal w ≤ 0 := by
  rw [encodedSize_sum, hp, hq]
  norm_num only [Int.cast_zero, mul_zero, add_zero]
  constructor
  · intro h
    have hmul : nu n * coordinateTotal w ≤ nu n * 0 := by linarith
    exact le_of_mul_le_mul_left hmul (nu_pos n)
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h (nu_pos n).le
    linarith

theorem secondaryTotal_eq_labelSecondary {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (e : Fin 5 ≃ Role) (x d a : Fin n)
    (hs : ∀ i, (s i).role = e i)
    (hl : ∀ i, label i = tableRoleLabel x d a (e i)) :
    secondaryTotal s label = labelSecondary x d a := by
  let f : Role → ℤ := fun r => match r with
    | .x => labelWeight x
    | .anchor => -2 * labelWeight a
    | .«global» => 0
    | .«local» => labelWeight d
    | .flag => 0
  calc
    secondaryTotal s label = ∑ i, f (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [secondaryScore, hs i, hl i]
      cases he : e i <;> rfl
    _ = ∑ r, f r := e.sum_comp f
    _ = labelSecondary x d a := by
      rw [Role.sum_univ]
      simp only [f, labelSecondary]
      ring

theorem secondaryTotal_nonpos_iff_labels {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (e : Fin 5 ≃ Role) (x d a : Fin n)
    (hs : ∀ i, (s i).role = e i)
    (hl : ∀ i, label i = tableRoleLabel x d a (e i)) :
    secondaryTotal s label ≤ 0 ↔ x ≤ a ∧ d ≤ a := by
  rw [secondaryTotal_eq_labelSecondary s label e x d a hs hl]
  exact labelSecondary_nonpos_iff

theorem secondaryTotal_eq_zero_iff_labels {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (e : Fin 5 ≃ Role) (x d a : Fin n)
    (hs : ∀ i, (s i).role = e i)
    (hl : ∀ i, label i = tableRoleLabel x d a (e i)) :
    secondaryTotal s label = 0 ↔ x = a ∧ d = a := by
  rw [secondaryTotal_eq_labelSecondary s label e x d a hs hl]
  exact labelSecondary_eq_zero_iff

namespace Packing

variable {I : Instance} {b n : ℕ}

def fiveEquiv (p : Packing I b) (j : Fin b) (hc : (p.binItems j).card = 5) :
    Fin 5 ≃ p.binItems j := (Finset.equivFinOfCardEq hc).symm

theorem sum_fiveEquiv (p : Packing I b) (j : Fin b) (hc : (p.binItems j).card = 5)
    {M : Type*} [AddCommMonoid M] (f : I.Item → M) :
    (∑ i : Fin 5, f (p.fiveEquiv j hc i).val) = ∑ i ∈ p.binItems j, f i := by
  rw [(p.fiveEquiv j hc).sum_comp (fun i : p.binItems j => f i.val)]
  change (∑ i ∈ (p.binItems j).attach, f i.val) = ∑ i ∈ p.binItems j, f i
  exact Finset.sum_attach (p.binItems j) f

theorem full_primary_nonpos (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6)
    (j : Fin b) (hc : (p.binItems j).card = 5) :
    p.primaryTotal subclass j ≤ 0 := by
  let e := p.fiveEquiv j hc
  have hcap : (∑ i : Fin 5,
      encodedSize (subclass (e i).val) (label (e i).val) (coordinate (e i).val)) ≤ 1 := by
    simp_rw [← hsize]
    rw [p.sum_fiveEquiv]
    exact p.bin_capacity j
  have hp := sum_primary_nonpos_of_feasible
    (fun i => subclass (e i).val) (fun i => label (e i).val)
    (fun i => coordinate (e i).val) (fun i => hw _) hcap
  change (∑ i : Fin 5, primaryScore (subclass (p.fiveEquiv j hc i).val)) ≤ 0 at hp
  rw [p.sum_fiveEquiv j hc (fun i => primaryScore (subclass i))] at hp
  exact hp

theorem table_secondary_nonpos (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6) (t : p.TableBin subclass) :
    (∑ i ∈ p.binItems t.val, secondaryScore (subclass i) (label i)) ≤ 0 := by
  let e := p.fiveEquiv t.val t.property.1
  have hp : BinPackingGap.primaryTotal (fun i => subclass (e i).val) = 0 := by
    change (∑ i : Fin 5,
      primaryScore (subclass (p.fiveEquiv t.val t.property.1 i).val)) = 0
    rw [p.sum_fiveEquiv t.val t.property.1 (fun i => primaryScore (subclass i))]
    exact t.property.2
  have hcap : (∑ i : Fin 5,
      encodedSize (subclass (e i).val) (label (e i).val) (coordinate (e i).val)) ≤ 1 := by
    simp_rw [← hsize]
    rw [p.sum_fiveEquiv]
    exact p.bin_capacity t.val
  have hq := sum_secondary_nonpos_of_feasible
    (fun i => subclass (e i).val) (fun i => label (e i).val)
    (fun i => coordinate (e i).val) (fun i => hw _) hp hcap
  change (∑ i : Fin 5,
    secondaryScore (subclass (p.fiveEquiv t.val t.property.1 i).val)
      (label (p.fiveEquiv t.val t.property.1 i).val)) ≤ 0 at hq
  rw [p.sum_fiveEquiv t.val t.property.1
    (fun i => secondaryScore (subclass i) (label i))] at hq
  exact hq

theorem sum_itemAtRole (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) {M : Type*} [AddCommMonoid M] (f : I.Item → M) :
    (∑ r : Role, f (p.itemAtRole subclass t r)) = ∑ i ∈ p.binItems t.val, f i := by
  change (∑ r : Role, f (p.tableEquiv subclass t r).val) =
    ∑ i ∈ p.binItems t.val, f i
  rw [(p.tableEquiv subclass t).sum_comp (fun i : p.binItems t.val => f i.val)]
  change (∑ i ∈ (p.binItems t.val).attach, f i.val) = ∑ i ∈ p.binItems t.val, f i
  exact Finset.sum_attach (p.binItems t.val) f

theorem table_secondary_eq (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (t : p.TableBin subclass) (x d a : Fin n)
    (hl : ∀ r, label (p.itemAtRole subclass t r) = tableRoleLabel x d a r) :
    (∑ i ∈ p.binItems t.val, secondaryScore (subclass i) (label i)) =
      labelSecondary x d a := by
  rw [← p.sum_itemAtRole subclass t]
  simp only [secondaryScore, p.itemAtRole_role, hl]
  rw [Role.sum_univ]
  simp [tableRoleLabel, labelSecondary]
  ring

theorem table_labels_le_anchor (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6) (t : p.TableBin subclass)
    (x d a : Fin n)
    (hl : ∀ r, label (p.itemAtRole subclass t r) = tableRoleLabel x d a r) :
    x ≤ a ∧ d ≤ a := by
  have hq := p.table_secondary_nonpos subclass label coordinate hsize hw t
  rw [p.table_secondary_eq subclass label t x d a hl] at hq
  exact labelSecondary_nonpos_iff.mp hq

theorem table_coordinate_nonpos (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (t : p.TableBin subclass)
    (hq : (∑ i ∈ p.binItems t.val, secondaryScore (subclass i) (label i)) = 0) :
    (∑ i ∈ p.binItems t.val, coordinate i) ≤ 0 := by
  let e := p.fiveEquiv t.val t.property.1
  have hp : BinPackingGap.primaryTotal (fun i => subclass (e i).val) = 0 := by
    change (∑ i : Fin 5,
      primaryScore (subclass (p.fiveEquiv t.val t.property.1 i).val)) = 0
    rw [p.sum_fiveEquiv t.val t.property.1 (fun i => primaryScore (subclass i))]
    exact t.property.2
  have hq' : secondaryTotal (fun i => subclass (e i).val)
      (fun i => label (e i).val) = 0 := by
    change (∑ i : Fin 5,
      secondaryScore (subclass (p.fiveEquiv t.val t.property.1 i).val)
        (label (p.fiveEquiv t.val t.property.1 i).val)) = 0
    rw [p.sum_fiveEquiv t.val t.property.1
      (fun i => secondaryScore (subclass i) (label i))]
    exact hq
  have hcap : (∑ i : Fin 5,
      encodedSize (subclass (e i).val) (label (e i).val) (coordinate (e i).val)) ≤ 1 := by
    simp_rw [← hsize]
    rw [p.sum_fiveEquiv]
    exact p.bin_capacity t.val
  have hw := (feasible_iff_coordinateSum_nonpos
    (fun i => subclass (e i).val) (fun i => label (e i).val)
    (fun i => coordinate (e i).val) hp hq').mp hcap
  change (∑ i : Fin 5, coordinate (p.fiveEquiv t.val t.property.1 i).val) ≤ 0 at hw
  rw [p.sum_fiveEquiv t.val t.property.1 coordinate] at hw
  exact hw

theorem table_coordinate_nonpos_of_same_label (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (t : p.TableBin subclass) (v : Fin n)
    (hl : ∀ r, label (p.itemAtRole subclass t r) = tableRoleLabel v v v r) :
    (∑ r : Role, coordinate (p.itemAtRole subclass t r)) ≤ 0 := by
  rw [p.sum_itemAtRole]
  apply p.table_coordinate_nonpos subclass label coordinate hsize t
  rw [p.table_secondary_eq subclass label t v v v hl]
  simp [labelSecondary]
  ring

def outsideTableItems (p : Packing I b) (subclass : I.Item → Subclass) :
    Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => ¬ p.IsTableBin subclass (p.assignment i)

theorem outsideTableItems_card_lt (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6) (B c : ℕ)
    (hcard : I.n = 5 * B) (hb : b ≤ B + c)
    (htotal : (∑ i, primaryScore (subclass i)) = 0) :
    (p.outsideTableItems subclass).card <
      25 * (c + 1) * (1 + 5 * primaryBound) := by
  classical
  have hlarge (i : I.Item) : (1 / 6 : ℚ) < I.size i := by
    rw [hsize]
    exact (encodedSize_mem_interval _ _ _ (hw i)).1
  have hcap := p.bin_card_le_five hlarge
  have hfull (j : Fin b) (hc : (PrimaryLoss.fiber p.assignment j).card = 5) :
      PrimaryLoss.binPrimary p.assignment (fun i => primaryScore (subclass i)) j ≤ 0 := by
    exact p.full_primary_nonpos subclass label coordinate hsize hw j hc
  have h := PrimaryLoss.primary_loss_bound p.assignment
    (fun i => primaryScore (subclass i)) B c primaryBound
    (by simpa using hcard) hcap hb (fun i => primaryScore_abs_lt (subclass i)) htotal hfull
  have hsets : p.outsideTableItems subclass =
      PrimaryLoss.outsideZeroFullItems p.assignment (fun i => primaryScore (subclass i)) := by
    ext i
    constructor
    · intro hi
      have hi' := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi'⟩
    · intro hi
      have hi' := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi'⟩
  rw [hsets]
  exact h.2.2.2

end Packing

end BinPackingGap

end

end OAI


