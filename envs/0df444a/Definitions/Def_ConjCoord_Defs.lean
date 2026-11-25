-- Prove2me | Definitions.Def_ConjCoord_Defs
-- name    : ConjCoord_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:42:16.009893+00:00
-- url     : https://prove2.me/theorems/07730b82-8164-466e-85e6-656794d0dcdb
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from J. S. Farland (jkfarland-bot/ConjCoord; see pinned Apache-2.0 LICENSE and README.md)'s pinned ConjCoord: class number congruence modulo 16 and Conjecture coord of Paper V development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace ConjCoord
noncomputable def box3 (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  Icc (-(n : ℤ)) n ×ˢ (Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n)
noncomputable def reps (a b c n : ℕ) : ℕ :=
  ((box3 n).filter fun v => (a : ℤ) * v.1 ^ 2 + b * v.2.1 ^ 2 + c * v.2.2 ^ 2 = n).card
noncomputable def r3 (n : ℕ) : ℕ := reps 1 1 1 n
noncomputable def gCount (m : ℕ) : ℕ :=
  ((box3 m).filter fun v => v.1 ^ 2 + v.2.1 ^ 2 + 16 * v.2.2 ^ 2 = (m : ℤ) ∧
    (v.1 ^ 2 + v.2.1 ^ 2) % 16 = 5 ∧ (v.2.1 % 16 = 6 ∨ v.2.1 % 16 = 10)).card
noncomputable def tCoeff (m : ℕ) : ℤ :=
  if m % 16 = 5 then 2 * (reps 1 2 4 m : ℤ) - reps 1 2 2 m - 8 * gCount m else 0
noncomputable def phi (n : ℕ) : ℤ :=
  4 * ∑ w ∈ Icc (-(n : ℤ)) n, if w ^ 2 ≤ n then tCoeff (n - (w ^ 2).toNat) else 0
def octA (b : ℤ) : ℤ := if b % 16 = 6 ∨ b % 16 = 10 then 1 else 0
structure SturmInput (f : ℕ → ℤ) (B : ℕ) where
  /-- The integer `q`-expansions of the modular forms in the space. -/
  M : Set (ℕ → ℤ)
  /-- `f` lies in the space (Serre–Stark). -/
  mem : f ∈ M
  /-- Dividing a form with even coefficients by `2` stays in the space. -/
  half_mem : ∀ g ∈ M, (∀ n, 2 ∣ g n) → (fun n => g n / 2) ∈ M
  /-- Sturm's theorem modulo `2`. -/
  sturm : ∀ g ∈ M, (∀ n ≤ B, 2 ∣ g n) → ∀ n, 2 ∣ g n
end ConjCoord


