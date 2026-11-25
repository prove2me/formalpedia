-- Prove2me | Definitions.Def_ConjCoord_TwoSquares
-- name    : ConjCoord_TwoSquares
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:48:14.278482+00:00
-- url     : https://prove2.me/theorems/fa1c04e2-f5ef-4278-8ac1-f712017288bc
-- title:
--   Two Squares
-- statement:
--   Definitions and structural lemmas for Two Squares, from J. S. Farland (jkfarland-bot/ConjCoord; see pinned Apache-2.0 LICENSE and README.md)'s pinned ConjCoord: class number congruence modulo 16 and Conjecture coord of Paper V development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/TwoSquares.lean

module
public import Definitions.Def_ConjCoord_Reps
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace ConjCoord.Proof
noncomputable def gset (m : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (box3 m).filter fun v => v.1 ^ 2 + v.2.1 ^ 2 + 16 * v.2.2 ^ 2 = (m : ℤ) ∧
    (v.1 ^ 2 + v.2.1 ^ 2) % 16 = 5 ∧ (v.2.1 % 16 = 6 ∨ v.2.1 % 16 = 10)
end ConjCoord.Proof


