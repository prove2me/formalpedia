-- Prove2me | Definitions.Def_Polychromatic_PolychromNumber
-- name    : Polychromatic_PolychromNumber
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:39:46.186171+00:00
-- url     : https://prove2.me/theorems/25329a13-010e-457d-aaea-e0caacaa853a
-- title:
--   Polychrom Number
-- statement:
--   Definitions and structural lemmas for Polychrom Number, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean

import Definitions.Def_Polychromatic_Colouring
import Theorems.Thm_HasPolychromColouring_card_le
import Theorems.Thm_HasPolychromColouring_of_surjective
import Theorems.Thm_IsPolychrom_card_le
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_isPolychrom_subsingleton
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
noncomputable def polychromNumber (S : Finset G) : ℕ :=
  sSup {n | HasPolychromColouring (Fin n) S}
lemma bddAbove : BddAbove {n | HasPolychromColouring (Fin n) S} :=
  ⟨#S, fun n hn ↦ by simpa using hn.card_le⟩
lemma nonempty (hS : S.Nonempty) : {n | HasPolychromColouring (Fin n) S}.Nonempty :=
  ⟨1, default, isPolychrom_subsingleton hS⟩
lemma card_le_polychromNumber [Fintype K] (hn : HasPolychromColouring K S) :
    card K ≤ polychromNumber S :=
  le_csSup bddAbove <| hn.of_surjective (equivFin K).surjective
@[simp] lemma polychromNumber_empty : polychromNumber (∅ : Finset G) = 0 := by
  simp [polychromNumber]
lemma hasPolychromColouring_fin (hS : S.Nonempty) :
    HasPolychromColouring (Fin (polychromNumber S)) S :=
  Nat.sSup_mem (nonempty hS) bddAbove
lemma polychromNumber_le_card : polychromNumber S ≤ #S := by
-- ANCHOR_END: polychromNumber_le_card
  obtain rfl | hS' := S.eq_empty_or_nonempty
  · simp
  simpa using (hasPolychromColouring_fin hS').card_le
section Int
example : polychromNumber (G := ℤ) {0, 1, 5} = 3 := by
  set S : Finset ℤ := {0, 1, 5}
  refine le_antisymm ?easy ?hard
  case easy =>
    calc
      polychromNumber S ≤ #S := polychromNumber_le_card
      _ = 3 := by simp [S]
  case hard =>
    suffices HasPolychromColouring (ZMod 3) S by simpa using card_le_polychromNumber this
    refine ⟨Int.castAddHom (ZMod 3), ?_⟩
    have : S.image (Int.castAddHom (ZMod 3)) = Finset.univ := by decide
    rw [isPolychrom_iff_mem_image]
    simp_rw [Finset.image_vadd_distrib, this]
    simp
end Int


