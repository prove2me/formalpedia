-- Prove2me | Definitions.Def_ConjCoord_Reps
-- name    : ConjCoord_Reps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:45:37.252621+00:00
-- url     : https://prove2.me/theorems/c742f25a-ede9-5ad7-b066-38158f167b16
-- title:
--   Reps
-- statement:
--   Definitions and structural lemmas for Reps, from J. S. Farland (jkfarland-bot/ConjCoord; see pinned Apache-2.0 LICENSE and README.md)'s pinned ConjCoord: class number congruence modulo 16 and Conjecture coord of Paper V development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean

module
public import Definitions.Def_ConjCoord_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace ConjCoord.Proof
noncomputable def sol (a b c n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (box3 n).filter fun v => (a : ℤ) * v.1 ^ 2 + b * v.2.1 ^ 2 + c * v.2.2 ^ 2 = n
section ThreeSquares
variable {n : ℕ}
end ThreeSquares
end ConjCoord.Proof


