-- Prove2me | Definitions.Def_Autoconvolutions_GoodBlocks
-- name    : Autoconvolutions_GoodBlocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:48:41.279093+00:00
-- url     : https://prove2.me/theorems/2486f3ba-d0e0-48ab-8743-a5e6add79711
-- title:
--   Good Blocks
-- statement:
--   Definitions and structural lemmas for Good Blocks, from Vjekoslav Kovač's pinned Sharpness for autoconvolutions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/GoodBlocks.lean

module
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Definitions.Def_Autoconvolutions_Occupancy
public import Definitions.Def_Autoconvolutions_Estimate
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
open scoped BigOperators
namespace Autoconvolutions.Blocks
abbrev Peak (m : ℕ) := Σ _s : ℕ, (Fin m → ℕ) × (Fin m → ℕ)
noncomputable def peakSet {m : ℕ} (I J : Finset (Fin m)) (n K : ℕ) : Finset (Peak m) :=
  (range (K+1)).sigma (fun s => goodVectors I (2*n-s) ×ˢ goodVectors J (2*n+s))
def peakCode {m : ℕ} (D : ℕ) (x : Peak m) : ℕ := code D x.2.1 + code D x.2.2
end Autoconvolutions.Blocks


