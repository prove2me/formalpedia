-- Prove2me | Definitions.Def_EventStructures_Stable_Prime
-- name    : EventStructures_Stable_Prime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:42:09.63292+00:00
-- url     : https://prove2.me/theorems/c2fae60b-28c8-4349-b908-ac9ffce89ac3
-- title:
--   Prime
-- statement:
--   Definitions and structural lemmas for Prime, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean

import Definitions.Def_EventStructures_Stable_Basic
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_Stable_hist_config
import Theorems.Thm_Stable_hist_least
import Theorems.Thm_Stable_hist_mem
import Theorems.Thm_Stable_hist_subset

set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
namespace Stable
def CoincidenceFree (F : ConfFamily L) : Prop :=
  ∀ {c : Set F.Event}, F.Config c → ∀ {x y : F.Event}, x ∈ c → y ∈ c → x ≠ y →
    ∃ m, F.Config m ∧ m ⊆ c ∧ (x ∈ m ↔ y ∉ m)
def IsPrime (F : ConfFamily L) (p : Set F.Event) : Prop :=
  F.Config p ∧ ∃ x ∈ p, p = hist F p x
def Prime (F : ConfFamily L) : Type _ := {p : Set F.Event // IsPrime F p}
instance : PartialOrder (Prime F) := Subtype.partialOrder _
namespace Prime
lemma config (p : Prime F) : F.Config p.val := p.2.1
noncomputable def top (p : Prime F) : F.Event := Classical.choose p.2.2
end Prime
def Compat (p q : Prime F) : Prop := ∃ c, F.Config c ∧ p.val ⊆ c ∧ q.val ⊆ c
lemma compat_self (p : Prime F) : Compat p p := ⟨p.val, p.config, subset_rfl, subset_rfl⟩
lemma Compat.symm {p q : Prime F} : Compat p q → Compat q p
  | ⟨c, hc, hp, hq⟩ => ⟨c, hc, hq, hp⟩
@[reducible] noncomputable def toPES (F : ConfFamily L) : PES L where
  Event := Prime F
  poEvent := Subtype.partialOrder _
  conflict p q := ¬ Compat p q
  label p := F.label (Prime.top p)
  conflict_irrefl p h := h (compat_self p)
  conflict_symm := ⟨fun _ _ h hc => h hc.symm⟩
  conflict_hereditary {_ _ _} hpq hqr hpr :=
    hpq (let ⟨c, hc, hp, hr⟩ := hpr; ⟨c, hc, hp, Set.Subset.trans hqr hr⟩)
lemma hist_hist (hF : Stable F) {c : Set F.Event} (hc : F.Config c) {x : F.Event}
    (hx : x ∈ c) : hist F c x = hist F (hist F c x) x :=
  Set.Subset.antisymm
    (fun _ hy => Set.mem_sInter.mpr fun _ hm =>
      hist_least hm.1 (hm.2.1.trans (hist_subset hc hx)) hm.2.2 hy)
    (hist_subset (hist_config hF hc hx) hist_mem)
lemma isPrime_hist (hF : Stable F) {c : Set F.Event} (hc : F.Config c) {x : F.Event}
    (hx : x ∈ c) : IsPrime F (hist F c x) :=
  ⟨hist_config hF hc hx, x, hist_mem, hist_hist hF hc hx⟩
noncomputable def histPrime (hF : Stable F) {c : Set F.Event} (hc : F.Config c)
    {x : F.Event} (hx : x ∈ c) : Prime F :=
  ⟨hist F c x, isPrime_hist hF hc hx⟩
def primesOf (F : ConfFamily L) (c : Set F.Event) : Set (Prime F) := {p | p.val ⊆ c}
def flatten (F : ConfFamily L) (S : Set (Prime F)) : Set F.Event := ⋃ p ∈ S, p.val
end Stable


