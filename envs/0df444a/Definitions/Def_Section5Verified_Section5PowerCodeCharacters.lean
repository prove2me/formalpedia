-- Prove2me | Definitions.Def_Section5Verified_Section5PowerCodeCharacters
-- name    : Section5Verified_Section5PowerCodeCharacters
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:36:56.984837+00:00
-- url     : https://prove2.me/theorems/0cb96894-eebd-5c7c-87f4-f3f30eb7e0d9
-- title:
--   Section5PowerCodeCharacters — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5PowerCodeCharacters; mechanically extracted with exact Lean declaration spans.

import Mathlib
section
set_option autoImplicit false

/-! Uniform seed characters of a finite-field power code. Every nonempty
product of at most `k` distinct output signs has exactly zero mean. -/

namespace Section5PowerCode

variable {F : Type*} [Field F] [Fintype F]

noncomputable def dotCharacter {k : ℕ} (χ : AddChar F ℝ) (c : Fin k → F) :
    AddChar (Fin k → F) ℝ where
  toFun t := χ (∑ j, t j*c j)
  map_zero_eq_one' := by simp
  map_add_eq_mul' t u := by
    simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib,AddChar.map_add_eq_mul]





noncomputable def codeSign {ι : Type*} {k : ℕ} (χ : AddChar F ℝ)
    (v : ι → F) (t : Fin k → F) (i : ι) : ℝ :=
  χ (∑ j, t j*v i ^ (j : ℕ))







end Section5PowerCode

end


