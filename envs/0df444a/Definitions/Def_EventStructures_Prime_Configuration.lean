-- Prove2me | Definitions.Def_EventStructures_Prime_Configuration
-- name    : EventStructures_Prime_Configuration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:36:24.582584+00:00
-- url     : https://prove2.me/theorems/798180a9-7725-4925-a892-2b69e30ecb33
-- title:
--   Configuration
-- statement:
--   Definitions and structural lemmas for Configuration, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Configuration.lean

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
set_option autoImplicit true
variable {L : Type*} (es : PES L)
@[simp] def isConf (X : Set es.Event) : Prop :=
  (∀ {e₁ e₂}, e₁ ∈ X → e₂ ∈ X → ¬ es.conflict e₁ e₂) ∧
  (∀ {e e'}, e ∈ X → e' ≤ e → e' ∈ X)
def Conf : Type := {X : Set es.Event // isConf es X}
def FinConf : Type := {X : Finset es.Event // isConf es (X : Set es.Event)}
namespace Configuration
def enables (c : Set es.Event) (e : es.Event) : Prop :=
  isConf es c ∧
  (∀ e' ∈ c, es.consistent e e') ∧
  es.past e ⊆ c
local infix:50 " ⊢ " => enables es
lemma isConf_empty : isConf es ∅ :=
  ⟨fun h _ _ => (Set.notMem_empty _ h).elim, fun h _ => (Set.notMem_empty _ h).elim⟩
end Configuration
structure Emb {L : Type*} (E F : PES L) where
  f : E.Event → F.Event
  inj : Function.Injective f
  mono : ∀ {x y}, x ≤ y → f x ≤ f y
  smono : ∀ {x y}, x < y → f x < f y
  conf : ∀ {x y}, E.conflict x y → F.conflict (f x) (f y)
namespace Emb
variable {L : Type*} {E F : PES L} (ι : Emb E F)
end Emb
namespace PES
variable {L : Type*} (P : PES L)
def toFamily : ConfFamily L where
  Event := P.Event
  Config := isConf P
  label := P.label
  empty_mem := Configuration.isConf_empty P
  secured := by
    intro x y hx hy hyx hfin hne
    have hxy : (x \ y).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at h
      exact hne (Set.Subset.antisymm h hyx)
    obtain ⟨e, hemem, hmax⟩ := hfin.exists_maximal hxy
    refine ⟨e, hemem, fun h₁ h₂ => hx.1 h₁.1 h₂.1, ?_⟩
    rintro z w ⟨hzx, hzne⟩ hle
    refine ⟨hx.2 hzx hle, ?_⟩
    rintro rfl
    have hzdiff : z ∈ x \ y := ⟨hzx, fun hzy => hemem.2 (hy.2 hzy hle)⟩
    exact hzne (Set.mem_singleton_iff.mpr (le_antisymm (hmax hzdiff hle) hle))
end PES


