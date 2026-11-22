-- Prove2me | Definitions.Def_Polychromatic_FourThree_FourThree
-- name    : Polychromatic_FourThree_FourThree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:53:47.648398+00:00
-- url     : https://prove2.me/theorems/fa974208-3af9-40ed-8edf-f44be047b19f
-- title:
--   Four Three
-- statement:
--   Definitions and structural lemmas for Four Three, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/FourThree.lean

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_FourThree_Theory
import Theorems.Thm_P2M_allB_succ__7fe096bf361f
import Theorems.Thm_accept_of_three
import Theorems.Thm_allA_one
import Theorems.Thm_allA_succ_of_accept
import Theorems.Thm_allA_succ_of_gcd
import Theorems.Thm_allA_zero
import Theorems.Thm_allB_one
import Theorems.Thm_allB_succ
import Theorems.Thm_allB_two
import Theorems.Thm_allB_zero
import Theorems.Thm_allC_one
import Theorems.Thm_allC_succ
import Theorems.Thm_allC_three
import Theorems.Thm_allC_two
import Theorems.Thm_allC_zero
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ


set_option autoImplicit true
open Finset
lemma accept_3_0 (a b c : ℕ)
    (hb : (b.mod (nat_lit 3)).beq (nat_lit 1)) (hc : (c.mod (nat_lit 3)).beq (nat_lit 2)) :
    Accept a b c :=
  accept_of_three (by simp [helper hb, helper hc])
lemma accept_3_1 (a b c : ℕ)
    (hb : (b.mod (nat_lit 3)).beq (nat_lit 2)) (hc : (c.mod (nat_lit 3)).beq (nat_lit 1)) :
    Accept a b c :=
  accept_of_three (by simp [helper hb, helper hc, Finset.insert_subset_iff])
lemma accept_3_2 (a b c : ℕ)
    (ha : (a.mod (nat_lit 3)).beq (nat_lit 1)) (hc : (c.mod (nat_lit 3)).beq (nat_lit 2)) :
    Accept a b c :=
  accept_of_three (by simp [helper ha, helper hc, Finset.insert_subset_iff])
lemma accept_3_3 (a b c : ℕ)
    (ha : (a.mod (nat_lit 3)).beq (nat_lit 2)) (hc : (c.mod (nat_lit 3)).beq (nat_lit 1)) :
    Accept a b c :=
  accept_of_three (by simp [helper ha, helper hc, Finset.insert_subset_iff])
lemma accept_3_4 (a b c : ℕ)
    (ha : (a.mod (nat_lit 3)).beq (nat_lit 1)) (hb : (b.mod (nat_lit 3)).beq (nat_lit 2)) :
    Accept a b c :=
  accept_of_three (by simp [helper ha, helper hb, Finset.insert_subset_iff])
lemma accept_3_5 (a b c : ℕ)
    (ha : (a.mod (nat_lit 3)).beq (nat_lit 2)) (hb : (b.mod (nat_lit 3)).beq (nat_lit 1)) :
    Accept a b c :=
  accept_of_three (by simp [helper ha, helper hb, Finset.insert_subset_iff])
lemma allA_of_3_0 (A b c : ℕ)
    (hb : (b.mod (nat_lit 3)).beq (nat_lit 1)) (hc : (c.mod (nat_lit 3)).beq (nat_lit 2)) :
    allA A b c := by
  intro a _ _ _ _ _
  apply accept_3_0 a b c hb hc
lemma allA_of_3_1 (A b c : ℕ)
    (hb : (b.mod (nat_lit 3)).beq (nat_lit 2)) (hc : (c.mod (nat_lit 3)).beq (nat_lit 1)) :
    allA A b c := by
  intro a _ _ _ _ _
  apply accept_3_1 a b c hb hc
def mkColourVector (l : Array (Fin 3)) (x : Fin 3) : Nat :=
  l.foldr (init := 0) fun k i ↦ Nat.bit (k == x) i


