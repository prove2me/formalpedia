-- Prove2me | solution 1 for Autoconvolutions.Blocks.card_goodPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:09.316358+00:00
-- url     : https://prove2.me/submissions/15b66cce-f9e3-4617-b691-bc75e841513e

module
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_Autoconvolutions_Occupancy
public import Theorems.Thm_Autoconvolutions_Blocks_card_goodVectors

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Blocks
variable {ι : Type*} [DecidableEq ι]
namespace Autoconvolutions.Blocks
theorem _root_.solution (I J : Finset ι) (u v : ℕ) :
    ((goodVectors I u) ×ˢ (goodVectors J v)).card = I.card.choose u * J.card.choose v := by
  simp [card_goodVectors]
end Autoconvolutions.Blocks
