-- Prove2me | Definitions.Def_EventStructures_CCS_Semantics
-- name    : EventStructures_CCS_Semantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:53:00.579242+00:00
-- url     : https://prove2.me/theorems/b1cd9b1c-341e-4c4b-9a91-7e89f848265f
-- title:
--   Semantics
-- statement:
--   Definitions and structural lemmas for Semantics, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/CCS/Semantics.lean

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
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
open PES Configuration ConfFamily
namespace CCS
variable {Name : Type*}
variable {Name : Type*}
@[reducible] def empty : SES (Action Name) where
  Event := PEmpty
  Con _ := True
  enable _ _ := True
  label := PEmpty.elim
  con_empty := trivial
  con_subset _ _ := trivial
  enable_mono _ _ _ := trivial
  enable_inter _ _ _ _ := trivial
@[reducible] def pfx (α : Action Name) (E : SES (Action Name)) : SES (Action Name) where
  Event := Option E.Event
  Con X := E.toGES.Consistent {e | some e ∈ (X : Set (Option E.Event))}
  enable X
    | none => True
    | some e => none ∈ X ∧ ∃ Y : Finset E.Event, (∀ e' ∈ Y, some e' ∈ X) ∧ E.enable Y e
  label
    | none => α
    | some e => E.label e
  con_empty := by
    intro Y hY
    have hE : Y = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun e he => ?_
      have := hY (show e ∈ (Y : Set E.Event) by exact_mod_cast he)
      simp at this
    exact hE ▸ E.con_empty
  con_subset h hsub := fun Y hY => h Y fun e he => hsub (hY he)
  enable_mono := by
    rintro X Y (_ | e) h hsub -
    · exact trivial
    · exact ⟨hsub h.1, h.2.imp fun _ hY => ⟨fun e' he' => hsub (hY.1 e' he'), hY.2⟩⟩
  enable_inter := by
    classical
    rintro X Y Z (_ | e) hX hY hcons hZ
    · exact trivial
    · obtain ⟨hnX, YX, hYX, henX⟩ := hX
      obtain ⟨hnY, YY, hYY, henY⟩ := hY
      have hmemZ : ∀ {u : Option E.Event}, u ∈ X → u ∈ Y → u ∈ Z := by
        intro u h₁ h₂
        have : u ∈ (Z : Set (Option E.Event)) :=
          hZ ▸ ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
        exact_mod_cast this
      refine ⟨hmemZ hnX hnY, YX ∩ YY, ?_, E.enable_inter henX henY ?_ (Finset.coe_inter _ _)⟩
      · intro e' he'
        rw [Finset.mem_inter] at he'
        exact hmemZ (hYX e' he'.1) (hYY e' he'.2)
      · intro W hW
        refine (hcons (W.image some) fun u hu => ?_) W fun w hw => ?_
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
          rcases hW (by exact_mod_cast hw) with (h | h) | h
          · exact Or.inl (Or.inl (by exact_mod_cast hYX w (by exact_mod_cast h)))
          · exact Or.inl (Or.inr (by exact_mod_cast hYY w (by exact_mod_cast h)))
          · exact Or.inr (congrArg some h)
        · exact_mod_cast Finset.mem_image.mpr ⟨w, by exact_mod_cast hw, rfl⟩
@[reducible] def sum (E F : SES (Action Name)) : SES (Action Name) where
  Event := E.Event ⊕ F.Event
  Con X :=
    (∀ e, Sum.inl e ∈ X → ∀ f, Sum.inr f ∈ X → False) ∧
    E.toGES.Consistent {e | Sum.inl e ∈ (X : Set (E.Event ⊕ F.Event))} ∧
    F.toGES.Consistent {f | Sum.inr f ∈ (X : Set (E.Event ⊕ F.Event))}
  enable X
    | .inl e => ∃ Y : Finset E.Event, (∀ e' ∈ Y, Sum.inl e' ∈ X) ∧ E.enable Y e
    | .inr f => ∃ Y : Finset F.Event, (∀ f' ∈ Y, Sum.inr f' ∈ X) ∧ F.enable Y f
  label
    | .inl e => E.label e
    | .inr f => F.label f
  con_empty := by
    refine ⟨fun e he => absurd he (Finset.notMem_empty _), ?_, ?_⟩
    · intro Y hY
      have hE : Y = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun e he => ?_
        have := hY (show e ∈ (Y : Set E.Event) by exact_mod_cast he)
        simp at this
      exact hE ▸ E.con_empty
    · intro Y hY
      have hE : Y = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun f hf => ?_
        have := hY (show f ∈ (Y : Set F.Event) by exact_mod_cast hf)
        simp at this
      exact hE ▸ F.con_empty
  con_subset h hsub :=
    ⟨fun e he f hf => h.1 e (hsub he) f (hsub hf),
     fun Y hY => h.2.1 Y fun e he => hsub (hY he),
     fun Y hY => h.2.2 Y fun f hf => hsub (hY hf)⟩
  enable_mono := by
    rintro X Y (e | f) h hsub -
    · exact h.imp fun _ hY => ⟨fun e' he' => hsub (hY.1 e' he'), hY.2⟩
    · exact h.imp fun _ hY => ⟨fun f' hf' => hsub (hY.1 f' hf'), hY.2⟩
  enable_inter := by
    classical
    have hmemZ : ∀ {X Y Z : Finset (E.Event ⊕ F.Event)},
        (Z : Set (E.Event ⊕ F.Event)) = ↑X ∩ ↑Y →
        ∀ {u}, u ∈ X → u ∈ Y → u ∈ Z := by
      intro X Y Z hZ u h₁ h₂
      have : u ∈ (Z : Set (E.Event ⊕ F.Event)) :=
        hZ ▸ ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
      exact_mod_cast this
    rintro X Y Z (e | f) hX hY hcons hZ
    · obtain ⟨YX, hYX, henX⟩ := hX
      obtain ⟨YY, hYY, henY⟩ := hY
      refine ⟨YX ∩ YY, fun e' he' => ?_,
        E.enable_inter henX henY (fun W hW => ?_) (Finset.coe_inter _ _)⟩
      · rw [Finset.mem_inter] at he'
        exact hmemZ hZ (hYX e' he'.1) (hYY e' he'.2)
      · refine (hcons (W.image Sum.inl) fun u hu => ?_).2.1 W fun w hw => by
          exact_mod_cast Finset.mem_image.mpr ⟨w, by exact_mod_cast hw, rfl⟩
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
        rcases hW (by exact_mod_cast hw) with (h | h) | h
        · exact Or.inl (Or.inl (by exact_mod_cast hYX w (by exact_mod_cast h)))
        · exact Or.inl (Or.inr (by exact_mod_cast hYY w (by exact_mod_cast h)))
        · exact Or.inr (congrArg Sum.inl h)
    · obtain ⟨YX, hYX, henX⟩ := hX
      obtain ⟨YY, hYY, henY⟩ := hY
      refine ⟨YX ∩ YY, fun f' hf' => ?_,
        F.enable_inter henX henY (fun W hW => ?_) (Finset.coe_inter _ _)⟩
      · rw [Finset.mem_inter] at hf'
        exact hmemZ hZ (hYX f' hf'.1) (hYY f' hf'.2)
      · refine (hcons (W.image Sum.inr) fun u hu => ?_).2.2 W fun w hw => by
          exact_mod_cast Finset.mem_image.mpr ⟨w, by exact_mod_cast hw, rfl⟩
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
        rcases hW (by exact_mod_cast hw) with (h | h) | h
        · exact Or.inl (Or.inl (by exact_mod_cast hYX w (by exact_mod_cast h)))
        · exact Or.inl (Or.inr (by exact_mod_cast hYY w (by exact_mod_cast h)))
        · exact Or.inr (congrArg Sum.inr h)
@[reducible] def restrict (E : SES (Action (Option Name))) : SES (Action Name) where
  Event := {e : E.Event // (E.label e).strip.isSome = true}
  Con X := E.toGES.Consistent
    {e | ∃ h, (⟨e, h⟩ : {e : E.Event // (E.label e).strip.isSome = true}) ∈ (X : Set _)}
  enable X e := ∃ Y : Finset E.Event,
    (∀ e' ∈ Y, ∃ h, (⟨e', h⟩ : {e : E.Event // (E.label e).strip.isSome = true}) ∈ X) ∧
    E.enable Y e.1
  label e := (E.label e.1).strip.get e.2
  con_empty := by
    intro Y hY
    have hE : Y = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun e he => ?_
      obtain ⟨hv, hmem⟩ := hY (show e ∈ (Y : Set E.Event) by exact_mod_cast he)
      exact absurd hmem (by simp)
    exact hE ▸ E.con_empty
  con_subset h hsub := by
    refine fun Y hY => h Y fun e he => ?_
    obtain ⟨hv, hm⟩ := hY he
    exact ⟨hv, hsub hm⟩
  enable_mono := by
    rintro X Y e ⟨W, hW, hen⟩ hsub -
    refine ⟨W, fun e' he' => ?_, hen⟩
    obtain ⟨hv, hm⟩ := hW e' he'
    exact ⟨hv, hsub hm⟩
  enable_inter := by
    classical
    rintro X Y Z e ⟨YX, hYX, henX⟩ ⟨YY, hYY, henY⟩ hcons hZ
    have hmemZ : ∀ {u}, u ∈ X → u ∈ Y → u ∈ Z := by
      intro u h₁ h₂
      have : u ∈ (Z : Set _) := hZ ▸ ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
      exact_mod_cast this
    refine ⟨YX ∩ YY, fun e' he' => ?_,
      E.enable_inter henX henY (fun W hW => ?_) (Finset.coe_inter _ _)⟩
    · rw [Finset.mem_inter] at he'
      obtain ⟨h₁, hm₁⟩ := hYX e' he'.1
      obtain ⟨h₂, hm₂⟩ := hYY e' he'.2
      exact ⟨h₁, hmemZ hm₁ hm₂⟩
    · have hvis : ∀ w ∈ W, (E.label w).strip.isSome = true := by
        intro w hw
        rcases hW (by exact_mod_cast hw) with (h | h) | h
        · exact (hYX w (by exact_mod_cast h)).choose
        · exact (hYY w (by exact_mod_cast h)).choose
        · exact h ▸ e.2
      refine hcons (W.attach.image fun w => ⟨w.1, hvis w.1 w.2⟩) (fun u hu => ?_) W
        fun w hw => ⟨hvis w (by exact_mod_cast hw), ?_⟩
      · obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
        rcases hW (by exact_mod_cast w.2) with (h | h) | h
        · obtain ⟨hv, hm⟩ := hYX w.1 (by exact_mod_cast h)
          exact Or.inl (Or.inl (by exact_mod_cast hm))
        · obtain ⟨hv, hm⟩ := hYY w.1 (by exact_mod_cast h)
          exact Or.inl (Or.inr (by exact_mod_cast hm))
        · exact Or.inr (Subtype.ext h)
      · have hmem : (⟨w, hvis w (by exact_mod_cast hw)⟩ :
            {e : E.Event // (E.label e).strip.isSome = true}) ∈
            W.attach.image (fun z => (⟨z.1, hvis z.1 z.2⟩ :
              {e : E.Event // (E.label e).strip.isSome = true})) :=
          Finset.mem_image.mpr ⟨⟨w, by exact_mod_cast hw⟩, Finset.mem_attach _ _, rfl⟩
        exact_mod_cast hmem
variable {E F : SES (Action Name)} {α : Action Name}
def unres {E : SES (Action (Option Name))} (c : Set (restrict E).Event) :
    Set E.Event := {y | ∃ h, (⟨y, h⟩ : (restrict E).Event) ∈ c}
variable {E : SES (Action (Option Name))} {c : Set (restrict E).Event}
set_option linter.checkUnivs false in
/-- Event-structure semantics of finitary CCS, as stable event structures. -/
@[reducible] def semantics {Name : Type u} : Process Name → SES (Action Name)
  | .nil => empty
  | .pre α P => pfx α (semantics P)
  | .sum P Q => sum (semantics P) (semantics Q)
  | .par P Q => parSES (semantics P) (semantics Q)
  | .res P => restrict (semantics P)
def opLTSI (P : Process Name) : LTSI (Action Name) where
  State := Process Name
  init := P
  step := Step
  indep _ _ _ _ _ := False
set_option linter.checkUnivs false in
/-- Denotational LTSI: configurations of the semantics. -/
def denLTSI (P : Process Name) : LTSI (Action Name) :=
  ConfFamily.toLTSI (semantics P).toFamily
end CCS


