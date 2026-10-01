-- Prove2me | Definitions.Def_ChapterLorentzGroup
-- name    : ChapterLorentzGroup
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:19:05.225316+00:00
-- url     : https://prove2.me/theorems/01407f16-9272-4c4e-848c-de13d11dae46
-- title:
--   Chapter LorentzGroup
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLorentzGroup.lean`): generated def bundle for ChapterLorentzGroup. See BookProof/ChapterLorentzGroup.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLorentzGroup.lean

import Mathlib


/-!
# Chapter "Real representations, CPT theorem …", §"On the Lorentz, SL(2,C) and Pin(3,1) groups":
the Lorentz group `O(1,3)` and its discrete subgroup `Δ = {1, η, -η, -1}`

This file formalizes the self-contained group-theoretic content of `book.tex`
**Note 43** (`book.tex` line ~5340, chapter *"Real representations, CPT theorem
and the relativistic position operator"*, §*"On the Lorentz, SL(2,C) and
Pin(3,1) groups"*):

> The Lorentz group, `O(1,3) ≡ {λ ∈ ℝ^{4×4} : λᵀ η λ = η}`, is the set of real
> matrices that leave the metric `η = diag(1,-1,-1,-1)` invariant. […] The
> discrete Lorentz subgroup of parity and time-reversal is `Δ ≡ {1, η, -η, -1}`.

Modelling the Minkowski metric `η = diag(1,-1,-1,-1)` as an explicit real
`4×4` matrix (this uses **only** the metric, no Majorana / gamma matrices).

Results:
* `eta_transpose`, `eta_mul_self` (`η² = 1`), `eta_det` (`det η = -1`) — the basic
  properties of the metric;
* `IsLorentz` — the defining predicate of `O(1,3)`;
* `isLorentz_one`, `isLorentz_mul`, `isLorentz_inv` — `O(1,3)` is closed under the
  identity, matrix product, and matrix inverse: it is a **group**;
* `lorentz_det_sq_one` (`(det λ)² = 1`) and `lorentz_det_ne_zero` — every Lorentz
  matrix is invertible with determinant `±1`;
* `isLorentz_eta`, `isLorentz_neg_eta`, `isLorentz_neg_one` — the three nontrivial
  discrete generators are Lorentz;
* `Delta` — the discrete subgroup `Δ = {1, η, -η, -1}`;
* `delta_subset_lorentz` — `Δ ⊆ O(1,3)`;
* `delta_mul_closed` — `Δ` is closed under multiplication;
* `delta_involutive` — every element of `Δ` squares to `1`
  (so `Δ` is abelian and `≅ ℤ₂ × ℤ₂`, the Klein four-group);
* `delta_card_four` — the four listed elements are distinct, so `|Δ| = 4`.
-/

namespace BookProof.LorentzGroup

open Matrix

/-- The Minkowski metric `η = diag(1, -1, -1, -1)` as an explicit real `4×4`
matrix. -/
def eta : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

/-
The metric is symmetric: `ηᵀ = η`.
-/


/-
The metric is an involution: `η² = 1`.
-/


/-
The determinant of the metric is `-1`.
-/


/-- The Lorentz group `O(1,3)`: real `4×4` matrices preserving the Minkowski
metric `η`, i.e. `λᵀ η λ = η`. -/
def IsLorentz (l : Matrix (Fin 4) (Fin 4) ℝ) : Prop := lᵀ * eta * l = eta

/-
The identity matrix is a Lorentz transformation.
-/


/-
The product of two Lorentz transformations is a Lorentz transformation.
-/


/-
The determinant of a Lorentz transformation squares to `1`.
-/


/-
A Lorentz transformation has nonzero determinant, hence is invertible.
-/


/-
The inverse of a Lorentz transformation is a Lorentz transformation:
so `O(1,3)` is a group.
-/


/-
The metric `η` (parity × time-reversal) is a Lorentz transformation.
-/


/-
`-η` is a Lorentz transformation.
-/


/-
`-1` (full inversion `PT`) is a Lorentz transformation.
-/


/-- The discrete Lorentz subgroup `Δ = {1, η, -η, -1}` of parity and
time-reversal. -/
def Delta : Set (Matrix (Fin 4) (Fin 4) ℝ) := {1, eta, -eta, -1}

/-
Every element of `Δ` is a Lorentz transformation: `Δ ⊆ O(1,3)`.
-/


/-
`Δ` is closed under matrix multiplication.
-/


/-
Every element of `Δ` squares to the identity: `Δ` is abelian and isomorphic
to the Klein four-group `ℤ₂ × ℤ₂`.
-/


/-
The four listed elements `1, η, -η, -1` are pairwise distinct, so `|Δ| = 4`.
-/


end BookProof.LorentzGroup


