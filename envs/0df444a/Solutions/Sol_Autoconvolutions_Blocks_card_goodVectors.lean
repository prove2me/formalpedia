-- Prove2me | solution 1 for Autoconvolutions.Blocks.card_goodVectors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:44.99603+00:00
-- url     : https://prove2.me/submissions/3e9d018a-5b24-4c49-8140-ef91d3cc9f1f

module
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_Autoconvolutions_Occupancy

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Blocks
variable {ι : Type*} [DecidableEq ι]
namespace Autoconvolutions.Blocks
theorem _root_.solution (I : Finset ι) (k : ℕ) :
    (goodVectors I k).card = I.card.choose k := by simp [goodVectors]
end Autoconvolutions.Blocks
