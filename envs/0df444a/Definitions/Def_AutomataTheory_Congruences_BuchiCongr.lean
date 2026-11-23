-- Prove2me | Definitions.Def_AutomataTheory_Congruences_BuchiCongr
-- name    : AutomataTheory_Congruences_BuchiCongr
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:47:30.98485+00:00
-- url     : https://prove2.me/theorems/2d1a34d8-e130-425a-aa80-dcac0e7731e3
-- title:
--   Buchi Congr
-- statement:
--   Definitions and structural lemmas for Buchi Congr, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/BuchiCongr.lean

import Definitions.Def_AutomataTheory_Automata_Pair
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Theorems.Thm_Automata_pair_acc_lang_concat_0
import Theorems.Thm_Automata_pair_acc_lang_concat_1
import Theorems.Thm_Automata_pair_acc_lang_split
import Theorems.Thm_Automata_pair_lang_concat
import Theorems.Thm_Automata_pair_lang_split

set_option autoImplicit true
open Function Set Filter Stream'
namespace Automata
section BuchiCongrBasic
variable {A : Type}
def NA.BuchiCongr (M : NA A) (acc : Set M.State) : Congruence A where
  eq.r u v := ∀ s s' : M.State,
    (u ∈ M.PairLang s s' ↔ v ∈ M.PairLang s s') ∧ (u ∈ M.PairAccLang acc s s' ↔ v ∈ M.PairAccLang acc s s')
  eq.iseqv.refl := by simp
  eq.iseqv.symm := by intro u v h s s' ; simp_all only [and_self]
  eq.iseqv.trans := by intro u v w h1 h2 s s' ; simp_all only [and_self]
  right_congr := by
    intro u v h w s s'
    constructor <;> [constructor ; constructor] <;> intro h'
    · obtain ⟨t, h_u, h_w⟩ := pair_lang_split h'
      have h_v := (h s t).1.mp h_u
      exact pair_lang_concat h_v h_w
    · obtain ⟨t, h_v, h_w⟩ := pair_lang_split h'
      have h_u := (h s t).1.mpr h_v
      exact pair_lang_concat h_u h_w
    · obtain ⟨t, (⟨h_u, h_w⟩ | ⟨h_u, h_w⟩)⟩ := pair_acc_lang_split h'
      · have h_v := (h s t).2.mp h_u
        exact pair_acc_lang_concat_0 h_v h_w
      · have h_v := (h s t).1.mp h_u
        exact pair_acc_lang_concat_1 h_v h_w
    · obtain ⟨t, (⟨h_v, h_w⟩ | ⟨h_v, h_w⟩)⟩ := pair_acc_lang_split h'
      · have h_u := (h s t).2.mpr h_v
        exact pair_acc_lang_concat_0 h_u h_w
      · have h_u := (h s t).1.mpr h_v
        exact pair_acc_lang_concat_1 h_u h_w
variable {M : NA A} {acc : Set M.State}
end BuchiCongrBasic
attribute [local instance_reducible] NA.BuchiCongr
section BuchiCongrFinite
open Classical
variable {A : Type}
noncomputable def NA.BuchiCongrParam (M : NA A) (acc : Set M.State)
    (π : M.State → M.State → Prop × Prop) : (M.BuchiCongr acc).QuotType :=
  if h : ∃ u, ∀ s s', ((π s s').1 ↔ u ∈ M.PairLang s s') ∧ ((π s s').2 ↔ u ∈ M.PairAccLang acc s s')
  then ⟦ choose h ⟧
  else ⟦ [] ⟧
variable {M : NA A} {acc : Set M.State}
end BuchiCongrFinite


