-- Prove2me | Definitions.Def_AhlswedeKhachatrian
-- name    : AhlswedeKhachatrian
-- status  : Definition
-- author  : @parclytaxel
-- created : 2026-11-10T17:43:27.873385+00:00
-- url     : https://prove2.me/theorems/4159362c-52bf-4db1-a6d4-e85361c7ce03
-- title:
--   Definitions
-- statement:
--   `Family n` is an abbreviation for `Finset (Finset (Fin n))`.
--
--   `A.Sized k` and `A.Inter t` where `A : Family n` together express that `A` is an (n,k,t)-intersecting family.
--
--   `frankl n k t r` gives Frankl's 1978 construction of (n,k,t)-intersecting families.
--
--   `threshold k t r` gives a critical value for `n` and `interval k t r` gives an open interval on which `frankl n k t r` is the unique maximal (n,k,t)-intersecting family.
--
--   `A.PermutesTo B` expresses isomorphism of families.

import Mathlib

namespace AhlswedeKhachatrian

open Finset

abbrev Family (n : ℕ) := Finset (Finset (Fin n))

/-- `A.Sized k` means every set in `A` has `k` elements. -/
def Family.Sized {n : ℕ} (A : Family n) (k : ℕ) : Prop :=
  ∀ x ∈ A, #x = k

/-- `A.Inter t` means every two sets of `A` intersect in at least `t` elements. -/
def Family.Inter {n : ℕ} (A : Family n) (t : ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, t ≤ #(x ∩ y)

/-- Frankl's construction of `t`-intersecting families. -/
def frankl (n k t r : ℕ) : Family n :=
  ({x | #x = k ∧ t + r ≤ #{i ∈ x | i.1 < t + 2 * r}} : Finset _)

/-- The thresholds in the explicit form of Ahlswede–Khachatrian. -/
def threshold (k t r : ℕ) : ℚ := (k - t + 1) * (2 + (t - 1) / (r + 1))

/-- Open interval of `n` where `frankl n k t r` is the unique (up to isomorphism) maximal family. -/
def interval (k t r : ℕ) : Set ℚ :=
  if r = 0 then Set.Ioi (threshold k t 0) else Set.Ioo (threshold k t r) (threshold k t (r - 1))

/-- `A.PermutesTo B` if `A` and `B` are the same up to permuting the ground set. -/
def Family.PermutesTo {n : ℕ} (A B : Family n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), A.image (·.image σ) = B

end AhlswedeKhachatrian


