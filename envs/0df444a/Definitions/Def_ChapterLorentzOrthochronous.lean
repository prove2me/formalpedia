-- Prove2me | Definitions.Def_ChapterLorentzOrthochronous
-- name    : ChapterLorentzOrthochronous
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:08:07.156384+00:00
-- url     : https://prove2.me/theorems/6534f25d-1641-44f8-bd17-4be3fcf249e0
-- title:
--   Chapter LorentzOrthochronous
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLorentzOrthochronous.lean`): generated def bundle for ChapterLorentzOrthochronous. See BookProof/ChapterLorentzOrthochronous.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLorentzOrthochronous.lean

import Definitions.Def_ChapterLorentzGroup
import Mathlib


/-!
# Chapter "Real representations, CPT theorem …", §"On the Lorentz, SL(2,C) and Pin(3,1) groups":
the proper orthochronous Lorentz group `SO⁺(1,3)` as a normal subgroup of `O(1,3)`

This file continues Wave 78 (`ChapterLorentzGroup.lean`, Note 43) with the next
self-contained claim of the same **Note 43** (`book.tex` line ~5366):

> The proper orthochronous Lorentz subgroup is defined by
> `SO⁺(1,3) ≡ {λ ∈ O(1,3) : det(λ) = 1, λ⁰₀ > 0}`. It is a normal subgroup.

Everything here uses **only** the Minkowski metric `η = diag(1,-1,-1,-1)` and the
group `O(1,3)` from `BookProof.LorentzGroup`; there are no gamma / Majorana
matrices (staying off both the gravity and the Hankel–Majorana lines).

Results:
* `isLorentz_neg` — `O(1,3)` is closed under negation (`-λ` is Lorentz);
* `isLorentz_mul_eta_transpose` — the "dual" metric relation `λ η λᵀ = η`;
* `lorentz_inv_eq` — the explicit inverse `λ⁻¹ = η λᵀ η`;
* `lorentz_time_col` / `lorentz_time_row` — the time–column / time–row identities
  `(λ⁰₀)² = 1 + Σᵢ(λⁱ₀)² = 1 + Σᵢ(λ⁰ᵢ)²`;
* `lorentz_time_sq_ge_one` (`(λ⁰₀)² ≥ 1`) and `lorentz_time_ne_zero` (`λ⁰₀ ≠ 0`);
* `lorentz_inv_time` — `(λ⁻¹)⁰₀ = λ⁰₀`;
* `product_time_component` — the `(0,0)` entry of a matrix product;
* `orthochronous_mul` — **the crux**: the product of two orthochronous Lorentz
  matrices is orthochronous (`a⁰₀ > 0`, `b⁰₀ > 0 ⇒ (ab)⁰₀ > 0`), proved by the
  reverse Cauchy–Schwarz inequality on the time components;
* `IsProperOrthochronous` — the predicate defining `SO⁺(1,3)`;
* `isPO_one`, `isPO_mul`, `isPO_inv` — `SO⁺(1,3)` is a subgroup;
* `isPO_conj` — **headline**: `SO⁺(1,3)` is a **normal** subgroup of `O(1,3)`
  (`g ∈ O(1,3)`, `s ∈ SO⁺(1,3) ⇒ g s g⁻¹ ∈ SO⁺(1,3)`).
-/

namespace BookProof.LorentzOrthochronous

open Matrix
open BookProof.LorentzGroup





















/-- The proper orthochronous Lorentz group `SO⁺(1,3) = {λ ∈ O(1,3) : det λ = 1, λ⁰₀ > 0}`. -/
def IsProperOrthochronous (l : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  IsLorentz l ∧ l.det = 1 ∧ 0 < l 0 0









end BookProof.LorentzOrthochronous


