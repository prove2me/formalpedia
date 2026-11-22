-- Prove2me | solution 1 for Autoconvolutions.Construction.disjoint_alphabets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:59.404721+00:00
-- url     : https://prove2.me/submissions/b51d7902-b313-4d61-adef-76e80d27a901

module
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Real.Basic
public import Definitions.Def_Autoconvolutions_Levels
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
attribute [local simp] Autoconvolutions.Construction.card_oddAlphabet
attribute [local simp] Autoconvolutions.Construction.card_evenAlphabet

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Construction
namespace Autoconvolutions.Construction
theorem _root_.solution (r b : ℕ) (hb : b ≤ r) :
    Disjoint (oddAlphabet r) (evenAlphabet r b hb) := by
  apply Finset.disjoint_left.mpr
  intro a ha ha'
  obtain ⟨i, _, hi⟩ := mem_map.mp ha
  obtain ⟨j, _, hj⟩ := mem_map.mp ha'
  have := congrArg Fin.val (hi.trans hj.symm)
  dsimp at this
  omega
end Autoconvolutions.Construction
