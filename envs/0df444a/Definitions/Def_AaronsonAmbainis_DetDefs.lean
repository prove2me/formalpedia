-- Prove2me | Definitions.Def_AaronsonAmbainis_DetDefs
-- name    : AaronsonAmbainis_DetDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:17:09.219977+00:00
-- url     : https://prove2.me/theorems/c2f735aa-3e5e-4938-9bc5-152975e2e249
-- title:
--   Det Defs
-- statement:
--   Definitions and structural lemmas for Det Defs, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetDefs.lean

import Definitions.Def_AaronsonAmbainis_Statements
set_option autoImplicit true
namespace AaronsonAmbainis
open Finset MvPolynomial
section
variable {ι : Type} [Fintype ι]
def IsLowest (q : MvPolynomial ι ℤ) (m : ι →₀ ℕ) : Prop :=
  m ∈ q.support ∧ ∀ m' ∈ q.support, ∑ i, m i ≤ ∑ i, m' i
noncomputable def agMon (x z : Cube ι) : MvPolynomial ι ℤ :=
  ∏ i, if x i = z i then X i else 1
end
section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
abbrev Ones (g : Cube ι → Bool) := {x : Cube ι // g x = true}
noncomputable def agMatrix (g : Cube ι → Bool) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x z => agMon x.1 z.1
end
def LowestUnit : Prop :=
  ∀ (ι : Type) [Fintype ι] (u q : MvPolynomial ι ℤ), constantCoeff u = 1 →
    ∀ m : ι →₀ ℕ, IsLowest (u * q) m ↔ IsLowest q m
def LowestBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool),
    (agMatrix g).det ≠ 0 ∧
      ∀ m : ι →₀ ℕ, IsLowest (agMatrix g).det m → ∀ j, m j ≤ bdry g j
end AaronsonAmbainis


