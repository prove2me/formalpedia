-- Prove2me | Definitions.Def_ChainBounding_Solution
-- name    : ChainBounding_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:45:10.497638+00:00
-- url     : https://prove2.me/theorems/2cf7c258-b407-4f14-a054-29c30623d197
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Pedro Sanchez Terraf (sterraf/chain-bounding; mathematical results joint with Guillermo L. Incatasciato; see pinned Apache-2.0 LICENSE and README.md)'s pinned Chain bounding: unified ordinal-free proof of Zorn's lemma and the Bourbaki-Witt theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sterraf/chain-bounding/blob/f3eb6e0becc13d645f0809c98ed28912ee41ee6a/Solution.lean

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
set_option autoImplicit true
variable {α : Type*}
open Set IsChain
section Segment
def IsSegment [LE α] (S C : Set α) : Prop := S ⊆ C ∧ ∀ c ∈ C, ∀ s ∈ S, c ≤ s → c ∈ S
def IsPropSegment [LE α] (S C : Set α) : Prop := IsSegment S C ∧ S ≠ C
@[inherit_doc]
infix:70 " ⊏ " => IsPropSegment
@[inherit_doc]
infix:70 " ⊑ " => IsSegment
variable [PartialOrder α]
@[refl]
lemma IsSegment_refl (S : Set α) : S ⊑ S := ⟨fun _ b => b, fun _ a _ _ _ => a⟩
lemma ssubset_of_IsPropSegment {S C : Set α} (prseg : S ⊏ C) : S ⊂ C :=
    Set.ssubset_iff_subset_ne.mpr ⟨prseg.1.1, prseg.2⟩
@[trans]
lemma IsSegment_trans {S C D : Set α} (hSC : S ⊑ C) (hCD : C ⊑ D) :
    S ⊑ D := by
  constructor
  · exact fun _ hz => hCD.left <| hSC.left hz
  · exact fun x hx y hy hxy => hSC.right x (hCD.right x hx y (hSC.left hy) hxy) y hy hxy
@[trans]
lemma IsPropSegment_trans {S C D : Set α} (hSC : S ⊏ C) (hCD : C ⊏ D) :
    S ⊏ D := by
    have : S ⊂ D := by
      calc
      S ⊂ C := ssubset_of_IsPropSegment hSC
      _ ⊂ D := ssubset_of_IsPropSegment hCD
    exact ⟨IsSegment_trans hSC.1 hCD.1, ne_of_ssubset this⟩
@[trans]
lemma IsPropSegment_of_IsPropSegment_of_IsSegment {S C D : Set α} (hSC : S ⊏ C) (hCD : C ⊑ D) :
    S ⊏ D := by
    have : S ⊂ D := by
      calc
      S ⊂ C := ssubset_of_IsPropSegment hSC
      _ ⊆ D := hCD.1
    exact ⟨IsSegment_trans hSC.1 hCD, ne_of_ssubset this⟩
@[trans]
lemma IsPropSegment_of_IsSegment_of_IsPropSegment {S C D : Set α} (hSC : S ⊑ C) (hCD : C ⊏ D) :
    S ⊏ D := by
    have : S ⊂ D := by
      calc
      S ⊆ C := hSC.1
      _ ⊂ D := ssubset_of_IsPropSegment hCD
    exact ⟨IsSegment_trans hSC hCD.1, ne_of_ssubset this⟩
instance : @Trans (Set α) (Set α) (Set α) IsSegment IsSegment IsSegment := ⟨IsSegment_trans⟩
instance : @Trans (Set α) (Set α) (Set α) IsPropSegment IsPropSegment IsPropSegment :=
  ⟨IsPropSegment_trans⟩
instance : @Trans (Set α) (Set α) (Set α) IsPropSegment IsSegment IsPropSegment :=
  ⟨IsPropSegment_of_IsPropSegment_of_IsSegment⟩
instance : @Trans (Set α) (Set α) (Set α) IsSegment IsPropSegment IsPropSegment :=
  ⟨IsPropSegment_of_IsSegment_of_IsPropSegment⟩
end Segment
section GreatestGood
class OrderExpander (α : Type*) [PartialOrder α] where
  /--
  The “expander” function.
  -/
  g : Set α → Set α
namespace OrderExpander
variable [PartialOrder α] [OrderExpander α]
def Good (C : Set α) := IsChain (· ≤ ·) C ∧ ∀ {S}, S ⊏ C → S ⊏ g S ∧ g S ⊑ C
def U : Set α :=  ⋃₀ {C | Good C}
end OrderExpander
end GreatestGood
section good_implies_well
class OrderSelector (α : Type*) [PartialOrder α] where
  /--
  The “selector” function.
  -/
  f : Set α → α
instance [PartialOrder α] [OrderSelector α] : OrderExpander α := ⟨fun C => C ∪ {OrderSelector.f C}⟩
@[simp]
lemma OrderSelector.g_def [PartialOrder α] [OrderSelector α] {C : Set α} :
    OrderExpander.g C = C ∪ {OrderSelector.f (α := α) C} := rfl
end good_implies_well
section GoodWellOrdered
variable [PartialOrder α] [OrderSelector α]
open OrderExpander
namespace OrderSelector
end OrderSelector
end GoodWellOrdered
noncomputable section ChainBounding
class ChainBounding (α : Type*) [PartialOrder α] [OrderSelector α] : Prop where
  -- `strbds` below means *strictly bounds*.
  strbds : ∀ C, IsChain (· ≤ ·) C → ∀ a ∈ C, a < OrderSelector.f (α := α) C
variable [PartialOrder α] [OrderSelector α] [ChainBounding α]
open OrderSelector OrderExpander
namespace ChainBounding
lemma le_f {C : Set α} (hC : IsChain (· ≤ ·) C) (c : ↑(g C)): c ≤ f C := by
  have : ↑c ∈ g C := c.property
  have : ↑c ∈ insert (f C) C := by simp_all
  by_cases cinC : ↑c ∈ C
  · exact le_of_lt (strbds C hC (↑c) cinC)
  · rcases mem_insert_iff.mp this with h | h
    · exact le_of_eq h
    · exact absurd h cinC
class Chain (C : Set α) : Prop where
  chain : IsChain (· ≤ ·) C
instance {C : Set α} : Top ↑(g C) := ⟨f C, mem_union_right C rfl⟩
instance orderTop_successor {C : Set α} [Chain C] : OrderTop ↑(g C) :=
  ⟨fun c => le_f (C := C) Chain.chain c⟩
end ChainBounding
end ChainBounding
class UnboundedChain (α : Type*) [PartialOrder α] [Inhabited α] : Prop where
  strbd : ∀ C, IsChain (· ≤ ·) C → ∃ sb : α, ∀ c ∈ C, c < sb
section UnboundedChain
variable [PartialOrder α] [Inhabited α] [UnboundedChain α]
namespace UnboundedChain
open Classical in
/--
The assigment of a strict upper bound resulting from *reductio* applied to the statement
of the Unbounded Chain Lemma.
-/
noncomputable def f (C : Set α) : α := if chain : IsChain (· ≤ ·) C then
  Classical.choose (strbd C chain) else default
end UnboundedChain
noncomputable instance : OrderSelector α := ⟨UnboundedChain.f⟩
end UnboundedChain
open ChainBounding
section Zorn
def IsMaximal [LE α] (m : α) := ∀ z, m ≤ z → z = m
end Zorn
section BourbakiWitt
end BourbakiWitt


