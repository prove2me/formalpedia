-- Prove2me | Definitions.Def_EventStructures_CCS_Par
-- name    : EventStructures_CCS_Par
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:50:33.508196+00:00
-- url     : https://prove2.me/theorems/2b7dc0ca-6ac3-4926-86b3-781f92ecdf49
-- title:
--   Par
-- statement:
--   Definitions and structural lemmas for Par, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Par.lean

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Theorems.Thm_CCS_Action_strip_map
import Theorems.Thm_CCS_Label_co_co
import Theorems.Thm_CCS_Label_strip_map
import Theorems.Thm_GES_toFamily_Config
import Theorems.Thm_GES_toFamily_Event
import Theorems.Thm_PES_enables_iff
import Theorems.Thm_PES_toFamily_Config
import Theorems.Thm_PES_toFamily_Event
import Theorems.Thm_SES_toFamily_Config
attribute [local simp] CCS.Action.strip_map
attribute [local simp] CCS.Label.co_co
attribute [local simp] CCS.Label.strip_map
attribute [local simp] GES.toFamily_Config
attribute [local simp] GES.toFamily_Event
attribute [local simp] PES.enables_iff
attribute [local simp] PES.toFamily_Config
attribute [local simp] PES.toFamily_Event
attribute [local simp] SES.toFamily_Config


set_option autoImplicit true
open GES
namespace CCS
variable {Name : Type*}
inductive Tag (E F : SES (Action Name)) where
  | left : E.Event → Tag E F
  | right : F.Event → Tag E F
  | sync (e : E.Event) (f : F.Event)
      (h : ∃ a, E.label e = .vis a ∧ F.label f = .vis a.co) : Tag E F
namespace Tag
variable {E F : SES (Action Name)}
def evL : Tag E F → Option E.Event
  | left e => some e
  | right _ => none
  | sync e _ _ => some e
def evR : Tag E F → Option F.Event
  | left _ => none
  | right f => some f
  | sync _ f _ => some f
def label : Tag E F → Action Name
  | left e => E.label e
  | right f => F.label f
  | sync .. => .tau
end Tag
variable {E F : SES (Action Name)}
def projL (C : Set (Tag E F)) : Set E.Event := {e | ∃ t ∈ C, t.evL = some e}
def projR (C : Set (Tag E F)) : Set F.Event := {f | ∃ t ∈ C, t.evR = some f}
lemma projL_mono {C D : Set (Tag E F)} (h : C ⊆ D) : projL C ⊆ projL D :=
  fun _ ⟨t, ht, he⟩ => ⟨t, h ht, he⟩
lemma projR_mono {C D : Set (Tag E F)} (h : C ⊆ D) : projR C ⊆ projR D :=
  fun _ ⟨t, ht, he⟩ => ⟨t, h ht, he⟩
def ParCon₂ (t₁ t₂ : Tag E F) : Prop :=
  (∀ e, t₁.evL = some e → t₂.evL = some e → t₁ = t₂) ∧
  (∀ f, t₁.evR = some f → t₂.evR = some f → t₁ = t₂)
def ParCon (X : Finset (Tag E F)) : Prop :=
  (∀ t₁ ∈ X, ∀ t₂ ∈ X, ParCon₂ t₁ t₂) ∧
  E.toGES.Consistent (projL (X : Set (Tag E F))) ∧
  F.toGES.Consistent (projR (X : Set (Tag E F)))
def ParEnable (X : Finset (Tag E F)) (t : Tag E F) : Prop :=
  (∀ e, t.evL = some e →
    ∃ Y : Finset E.Event, (∀ e' ∈ Y, e' ∈ projL (X : Set (Tag E F))) ∧ E.enable Y e) ∧
  (∀ f, t.evR = some f →
    ∃ Y : Finset F.Event, (∀ f' ∈ Y, f' ∈ projR (X : Set (Tag E F))) ∧ F.enable Y f)
lemma exists_cover_L {s : Set (Tag E F)} (V : Finset E.Event) (hV : ↑V ⊆ projL s) :
    ∃ W : Finset (Tag E F), ↑W ⊆ s ∧ ↑V ⊆ projL (W : Set (Tag E F)) := by
  classical
  have hpick : ∀ v ∈ V, ∃ u, u ∈ s ∧ u.evL = some v := fun v hv => hV (by exact_mod_cast hv)
  refine ⟨V.attach.image fun v => (hpick v.1 v.2).choose, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
    exact (hpick v.1 v.2).choose_spec.1
  · intro v hv
    have hv' : v ∈ V := by exact_mod_cast hv
    refine ⟨(hpick v hv').choose, ?_, (hpick v hv').choose_spec.2⟩
    have : (hpick v hv').choose ∈ V.attach.image fun z => (hpick z.1 z.2).choose :=
      Finset.mem_image.mpr ⟨⟨v, hv'⟩, Finset.mem_attach _ _, rfl⟩
    exact_mod_cast this
lemma exists_cover_R {s : Set (Tag E F)} (V : Finset F.Event) (hV : ↑V ⊆ projR s) :
    ∃ W : Finset (Tag E F), ↑W ⊆ s ∧ ↑V ⊆ projR (W : Set (Tag E F)) := by
  classical
  have hpick : ∀ v ∈ V, ∃ u, u ∈ s ∧ u.evR = some v := fun v hv => hV (by exact_mod_cast hv)
  refine ⟨V.attach.image fun v => (hpick v.1 v.2).choose, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
    exact (hpick v.1 v.2).choose_spec.1
  · intro v hv
    have hv' : v ∈ V := by exact_mod_cast hv
    refine ⟨(hpick v hv').choose, ?_, (hpick v hv').choose_spec.2⟩
    have : (hpick v hv').choose ∈ V.attach.image fun z => (hpick z.1 z.2).choose :=
      Finset.mem_image.mpr ⟨⟨v, hv'⟩, Finset.mem_attach _ _, rfl⟩
    exact_mod_cast this
lemma con_projL {s : Set (Tag E F)} (h : ∀ W : Finset (Tag E F), ↑W ⊆ s → ParCon W) :
    E.toGES.Consistent (projL s) := by
  intro V hV
  obtain ⟨W, hWs, hVW⟩ := exists_cover_L V hV
  exact (h W hWs).2.1 V hVW
lemma con_projR {s : Set (Tag E F)} (h : ∀ W : Finset (Tag E F), ↑W ⊆ s → ParCon W) :
    F.toGES.Consistent (projR s) := by
  intro V hV
  obtain ⟨W, hWs, hVW⟩ := exists_cover_R V hV
  exact (h W hWs).2.2 V hVW
lemma parCon_subset {X Y : Finset (Tag E F)} (h : ParCon Y) (hsub : X ⊆ Y) : ParCon X := by
  have hL : projL (X : Set (Tag E F)) ⊆ projL (Y : Set (Tag E F)) :=
    projL_mono (by exact_mod_cast hsub)
  have hR : projR (X : Set (Tag E F)) ⊆ projR (Y : Set (Tag E F)) :=
    projR_mono (by exact_mod_cast hsub)
  exact ⟨fun t₁ h₁ t₂ h₂ => h.1 t₁ (hsub h₁) t₂ (hsub h₂),
         fun W hW => h.2.1 W (hW.trans hL),
         fun W hW => h.2.2 W (hW.trans hR)⟩
@[reducible] def parSES (E F : SES (Action Name)) : SES (Action Name) where
  Event := Tag E F
  Con := ParCon
  enable := ParEnable
  label := Tag.label
  con_empty := by
    refine ⟨fun t ht => absurd ht (Finset.notMem_empty t), ?_, ?_⟩ <;>
      · intro W hW
        have hE : W = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
          obtain ⟨u, hu, -⟩ := hW (by exact_mod_cast hz)
          simp at hu
        first
          | exact hE ▸ E.con_empty
          | exact hE ▸ F.con_empty
  con_subset := parCon_subset
  enable_mono h hsub _ :=
    ⟨fun e he => (h.1 e he).imp fun _ hY =>
       ⟨fun e' he' => projL_mono (by exact_mod_cast hsub) (hY.1 e' he'), hY.2⟩,
     fun f hf => (h.2 f hf).imp fun _ hY =>
       ⟨fun f' hf' => projR_mono (by exact_mod_cast hsub) (hY.1 f' hf'), hY.2⟩⟩
  enable_inter := by
    classical
    rintro X Y Z t hX hY hcons hZ
    have hmemZ : ∀ {u : Tag E F}, u ∈ X → u ∈ Y → u ∈ (Z : Set (Tag E F)) :=
      fun h₁ h₂ => hZ ▸ ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
    have hpair : ∀ {t₁ t₂ : Tag E F}, t₁ ∈ X → t₂ ∈ Y → ParCon₂ t₁ t₂ := by
      intro t₁ t₂ h₁ h₂
      refine (hcons {t₁, t₂} fun u hu => ?_).1 t₁ (Finset.mem_insert_self _ _) t₂
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rcases Finset.mem_insert.mp (by exact_mod_cast hu) with rfl | hu'
      · exact Or.inl (Or.inl (by exact_mod_cast h₁))
      · exact Or.inl (Or.inr (by rw [Finset.mem_singleton.mp hu']; exact_mod_cast h₂))
    have hsubL : ∀ {V : Finset E.Event} {W : Finset (Tag E F)},
        (∀ e' ∈ V, e' ∈ projL (W : Set (Tag E F))) → ↑W ⊆ (X : Set (Tag E F)) →
        ↑V ⊆ projL ((X : Set (Tag E F)) ∪ ↑Y ∪ {t}) := by
      intro V W hVW hWX v hv
      obtain ⟨u, hu, hev⟩ := hVW v (by exact_mod_cast hv)
      exact ⟨u, Or.inl (Or.inl (hWX hu)), hev⟩
    constructor
    · rintro e he
      obtain ⟨YX, hYX, henX⟩ := hX.1 e he
      obtain ⟨YY, hYY, henY⟩ := hY.1 e he
      refine ⟨YX ∩ YY, fun e' he' => ?_,
        E.enable_inter henX henY (fun V hV => con_projL hcons V (hV.trans ?_))
          (Finset.coe_inter _ _)⟩
      · rw [Finset.mem_inter] at he'
        obtain ⟨u₁, hu₁, hev₁⟩ := hYX e' he'.1
        obtain ⟨u₂, hu₂, hev₂⟩ := hYY e' he'.2
        have h₁ : u₁ ∈ X := by exact_mod_cast hu₁
        have h₂ : u₂ ∈ Y := by exact_mod_cast hu₂
        exact ⟨u₁, hmemZ h₁ ((hpair h₁ h₂).1 e' hev₁ hev₂ ▸ h₂), hev₁⟩
      · rintro v ((hv | hv) | hv)
        · obtain ⟨u, hu, hev⟩ := hYX v hv
          exact ⟨u, Or.inl (Or.inl hu), hev⟩
        · obtain ⟨u, hu, hev⟩ := hYY v hv
          exact ⟨u, Or.inl (Or.inr hu), hev⟩
        · exact ⟨t, Or.inr rfl, (Set.mem_singleton_iff.mp hv) ▸ he⟩
    · rintro f hf
      obtain ⟨YX, hYX, henX⟩ := hX.2 f hf
      obtain ⟨YY, hYY, henY⟩ := hY.2 f hf
      refine ⟨YX ∩ YY, fun f' hf' => ?_,
        F.enable_inter henX henY (fun V hV => con_projR hcons V (hV.trans ?_))
          (Finset.coe_inter _ _)⟩
      · rw [Finset.mem_inter] at hf'
        obtain ⟨u₁, hu₁, hev₁⟩ := hYX f' hf'.1
        obtain ⟨u₂, hu₂, hev₂⟩ := hYY f' hf'.2
        have h₁ : u₁ ∈ X := by exact_mod_cast hu₁
        have h₂ : u₂ ∈ Y := by exact_mod_cast hu₂
        exact ⟨u₁, hmemZ h₁ ((hpair h₁ h₂).2 f' hev₁ hev₂ ▸ h₂), hev₁⟩
      · rintro v ((hv | hv) | hv)
        · obtain ⟨u, hu, hev⟩ := hYX v hv
          exact ⟨u, Or.inl (Or.inl hu), hev⟩
        · obtain ⟨u, hu, hev⟩ := hYY v hv
          exact ⟨u, Or.inl (Or.inr hu), hev⟩
        · exact ⟨t, Or.inr rfl, (Set.mem_singleton_iff.mp hv) ▸ hf⟩
variable {c : Set (Tag E F)}
end CCS


