-- Prove2me | solution 1 for Autoconvolutions.Blocks.low_and_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:52.005364+00:00
-- url     : https://prove2.me/submissions/d3a44f48-308e-4889-aa55-3f3bfd3b05cc

module
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Theorems.Thm_Autoconvolutions_Blocks_ofDigits_eq_code

set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Blocks
open Finset
namespace Autoconvolutions.Blocks
theorem _root_.solution {m D h h' : ℕ} (hD : 1 < D) {a b : Fin m → ℕ}
    (ha : ∀ i, a i < D) (hb : ∀ i, b i < D) (hh : h < D) (hh' : h' < D)
    (heq : h + D*code D a = h' + D*code D b) : h = h' ∧ a = b := by
  have he : h :: List.ofFn a = h' :: List.ofFn b := by
    apply Nat.ofDigits_inj_of_len_eq hD (by simp)
    · simpa [List.forall_mem_cons, hh, List.forall_mem_ofFn_iff] using ha
    · simpa [List.forall_mem_cons, hh', List.forall_mem_ofFn_iff] using hb
    · simpa only [Nat.ofDigits_cons, ofDigits_eq_code] using heq
  exact ⟨(List.cons.inj he).1, List.ofFn_injective (List.cons.inj he).2⟩
end Autoconvolutions.Blocks
