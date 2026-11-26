-- Prove2me | Definitions.Def_Sendov_FiniteRange_Pack
-- name    : Sendov_FiniteRange_Pack
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T17:52:46.987334+00:00
-- url     : https://prove2.me/theorems/dac38fca-abfe-5fae-b803-84b66d5bc606
-- title:
--   Pack
-- statement:
--   Definitions and structural lemmas for Pack, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Pack.lean

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace Sendov
def npev : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: p, b => a + b * npev p b
def unpackN (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | m + 1, x => (x % b) :: unpackN b m (x / b)
def paddN : List ℕ → List ℕ → List ℕ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, c :: q => (a + c) :: paddN p q
def pmulN : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: p, q => paddN (q.map (fun c => a * c)) (0 :: pmulN p q)
def ppowN (p : List ℕ) : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => pmulN p (ppowN p k)
def pevZ : List ℤ → ℤ → ℤ
  | [], _ => 0
  | a :: p, b => a + b * pevZ p b
def bdig (b x : ℤ) : ℤ := if 2 * (x % b) < b then x % b else x % b - b
def unpackZ (b : ℤ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | m + 1, x => bdig b x :: unpackZ b m ((x - bdig b x) / b)
end Sendov


