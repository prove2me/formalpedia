-- Prove2me | Definitions.Def_ConjCoord_Compute
-- name    : ConjCoord_Compute
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:44:45.591294+00:00
-- url     : https://prove2.me/theorems/649f2765-f5d9-5e7c-b92d-4c9a5fea6760
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from J. S. Farland (jkfarland-bot/ConjCoord; see pinned Apache-2.0 LICENSE and README.md)'s pinned ConjCoord: class number congruence modulo 16 and Conjecture coord of Paper V development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Compute.lean

module
public import Definitions.Def_ConjCoord_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace ConjCoord.Proof
def wt (x : ℕ) : ℕ := if x = 0 then 1 else 2
def zc (c r : ℕ) : ℕ :=
  if r % c = 0 ∧ Nat.sqrt (r / c) * Nat.sqrt (r / c) = r / c then (if r = 0 then 1 else 2) else 0
def cntL (a b c n : ℕ) (Q : ℕ → ℕ → Bool) : ℕ :=
  ∑ x ∈ range (Nat.sqrt n + 1), ∑ y ∈ range (Nat.sqrt n + 1),
    if a * x ^ 2 + b * y ^ 2 ≤ n ∧ Q x y = true then wt x * wt y * zc c (n - a * x ^ 2 - b * y ^ 2)
    else 0
def qG (i j : ℕ) : Bool := (i ^ 2 + j ^ 2) % 16 == 5 && (j % 16 == 6 || j % 16 == 10)
def tCoeffL (m : ℕ) : ℤ :=
  if m % 16 = 5 then
    2 * (cntL 1 2 4 m (fun _ _ => true) : ℤ) - cntL 1 2 2 m (fun _ _ => true) - 8 * cntL 1 1 16 m qG
  else 0
end ConjCoord.Proof


