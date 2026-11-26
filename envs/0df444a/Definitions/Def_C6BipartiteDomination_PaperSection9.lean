-- Prove2me | Definitions.Def_C6BipartiteDomination_PaperSection9
-- name    : C6BipartiteDomination_PaperSection9
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:53:15.671643+00:00
-- url     : https://prove2.me/theorems/277ece1a-abcb-599c-836a-10e433988298
-- title:
--   Paper Section9
-- statement:
--   Definitions and structural lemmas for Paper Section9, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean

import Definitions.Def_C6BipartiteDomination_A9
import Theorems.Thm_C6BipartiteDomination_chosen_repair_beta_three
import Theorems.Thm_C6BipartiteDomination_chosen_repairs_beta_two
import Theorems.Thm_C6BipartiteDomination_lemma_7_2_negative_charge_classification

set_option autoImplicit true
namespace C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
theorem paper8_chosen_repair_witness
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0) :
    ∃ R : Finset V,
      (∀ u ∈ R, IsRepairVertex G D w u) ∧
      ((kCharge G D w = 3 ∧ betaCharge G D w = 2 ∧ R.card = 2) ∨
       (kCharge G D w = 3 ∧ betaCharge G D w = 3 ∧ R.card = 1) ∨
       (kCharge G D w = 4 ∧ betaCharge G D w = 2 ∧ R.card = 2)) := by
  classical
  rcases lemma_7_2_negative_charge_classification G hCan hmax hw ha with
    ⟨hk, hβ⟩ | ⟨hk, hβ⟩ | ⟨hk, hβ⟩
  · obtain ⟨R, hcard, hlegal⟩ := chosen_repairs_beta_two G hCan hw (by omega) hβ
    exact ⟨R, hlegal, Or.inl ⟨hk, hβ, hcard⟩⟩
  · obtain ⟨u, hlegal⟩ := chosen_repair_beta_three G hCan hw hβ
    refine ⟨{u}, ?_, Or.inr (Or.inl ⟨hk, hβ, by simp⟩)⟩
    intro v hv
    have hvEq : v = u := Finset.mem_singleton.mp hv
    simpa [hvEq] using hlegal
  · obtain ⟨R, hcard, hlegal⟩ := chosen_repairs_beta_two G hCan hw (by omega) hβ
    exact ⟨R, hlegal, Or.inr (Or.inr ⟨hk, hβ, hcard⟩)⟩
noncomputable def paperChosenRepairSet
    (D : Finset V) (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (w : V) : Finset V := by
  classical
  exact if h : w ∈ SPart G D ∧ externalCharge G D w < 0 then
    Classical.choose (paper8_chosen_repair_witness G hCan hmax h.1 h.2)
  else ∅
end C6BipartiteDomination


