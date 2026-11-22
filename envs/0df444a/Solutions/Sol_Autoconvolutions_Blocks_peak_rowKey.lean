-- Prove2me | solution 1 for Autoconvolutions.Blocks.peak_rowKey
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:49:20.037805+00:00
-- url     : https://prove2.me/submissions/23d41443-56db-4f4f-8813-98df000033b0

module
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Definitions.Def_Autoconvolutions_Occupancy
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_GoodBlocks
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
attribute [local simp] Autoconvolutions.Construction.card_evenAlphabet
attribute [local simp] Autoconvolutions.Construction.card_oddAlphabet



set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Blocks
namespace Autoconvolutions.Blocks
theorem _root_.solution {m : ℕ} (x : Peak m) (D h : ℕ) :
    rowKey D (x.2,h) = D * peakCode D x + h := by
  simp [rowKey, key, peakCode, Nat.add_comm]
end Autoconvolutions.Blocks
