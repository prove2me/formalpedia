-- Prove2me | Definitions.Def_AaronsonAmbainis_Defs
-- name    : AaronsonAmbainis_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:15:26.243166+00:00
-- url     : https://prove2.me/theorems/b667853b-96e1-4a17-a597-35a4c6a08983
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Defs.lean

import Mathlib
set_option autoImplicit true
namespace AaronsonAmbainis
open Finset
abbrev Cube (ι : Type*) := ι → Bool
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def flipSet (x : Cube ι) (S : Finset ι) : Cube ι :=
  fun i => if i ∈ S then !(x i) else x i
def antipode (x : Cube ι) : Cube ι := fun i => !(x i)
def diffSet (x y : Cube ι) : Finset ι := univ.filter fun i => x i ≠ y i
def bdry (g : Cube ι → Bool) (j : ι) : ℕ :=
  (univ.filter fun x : Cube ι => g x = true ∧ g (flipSet x {j}) = false).card
def zone (g : Cube ι → Bool) : Finset (Cube ι) :=
  univ.filter fun u => g u = true ∧ g (antipode u) = false
def IsWing (g : Cube ι → Bool) (u : Cube ι) (A : Finset ι) : Prop :=
  ∀ S : Finset ι, S ⊆ A → g (flipSet u S) = true
def IsRow (g : Cube ι → Bool) (x : Cube ι) (lam : ι → ℝ) : Prop :=
  (∀ j, 0 ≤ lam j) ∧ ∀ S : Finset ι, g (flipSet x S) ≠ g x → 1 ≤ ∑ j ∈ S, lam j
noncomputable def infl (g : Cube ι → Bool) (j : ι) : ℝ :=
  ((univ.filter fun x : Cube ι => g (flipSet x {j}) ≠ g x).card : ℝ) / 2 ^ Fintype.card ι
noncomputable def mean (f : Cube ι → ℝ) : ℝ := (∑ x, f x) / 2 ^ Fintype.card ι
noncomputable def variance (f : Cube ι → ℝ) : ℝ := (∑ x, (f x - mean f) ^ 2) / 2 ^ Fintype.card ι
noncomputable def inflR (f : Cube ι → ℝ) (j : ι) : ℝ :=
  (∑ x, ((f x - f (flipSet x {j})) / 2) ^ 2) / 2 ^ Fintype.card ι
noncomputable def meanAbsIncr (f : Cube ι → ℝ) (j : ι) : ℝ :=
  (∑ x, |f x - f (flipSet x {j})|) / 2 ^ Fintype.card ι
noncomputable def chi (S : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ S, (if x i then (-1 : ℝ) else 1)
def HasDegreeLE (f : Cube ι → ℝ) (d : ℕ) : Prop :=
  ∃ c : Finset ι → ℝ, (∀ S, d < S.card → c S = 0) ∧ ∀ x, f x = ∑ S, c S * chi S x
end AaronsonAmbainis


