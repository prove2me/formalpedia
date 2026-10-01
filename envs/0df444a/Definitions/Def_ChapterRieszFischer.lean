-- Prove2me | Definitions.Def_ChapterRieszFischer
-- name    : ChapterRieszFischer
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:44:34.919804+00:00
-- url     : https://prove2.me/theorems/3d7a3ae3-eaa4-430d-a597-535dca8c17c0
-- title:
--   Chapter RieszFischer
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterRieszFischer.lean`): generated def bundle for ChapterRieszFischer. See BookProof/ChapterRieszFischer.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterRieszFischer.lean

import Mathlib


/-!
# Riesz–Fischer for the PA-free completion: the finitely-supported core in `ℓ²(ℕ)`

`BookProof/ChapterPaFreeCompletion.lean` and `BookProof/ChapterDefinabilityFragment.lean`
describe the "PA-free completion" architecture: the *dense core* of term-denotable
vectors is the space `ℕ →₀ ℝ` of finitely-supported sequences, and the ambient
Hilbert space is its completion `ℓ²(ℕ)`.  Those two files record the
finite-support side of the story; the analytic side (the actual Riesz–Fischer
content) is proved here.

The three facts that make the architecture precise are:

* **completeness** (`ell2_completeSpace`): `ℓ²(ℕ)` is a Hilbert space, so no
  Cauchy sequence of core vectors escapes it;
* **Riesz–Fischer / density** (`riesz_fischer_hasSum`, `finSupport_dense`): every
  vector of `ℓ²(ℕ)` is the norm-limit of its finitely-supported truncations, so
  the completion adds *only* limit points of the core;
* **properness** (`finSupport_ne_univ`): the completion is strictly larger than
  the core — the geometric vector `n ↦ 2⁻ⁿ` lies in `ℓ²(ℕ)` and has infinite
  support — so the passage to the completion is not vacuous.

Together these say exactly what the chapter claims: the completion is the
smallest Hilbert space containing the finitely-supported core, and every one of
its elements is approximated to arbitrary precision by core elements.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Filter
open scoped ENNReal

namespace BookProof.ChapterRieszFischer

/-- The real sequence space `ℓ²(ℕ)`: the completion of the finitely-supported
core `ℕ →₀ ℝ`. -/
abbrev Ell2 := lp (fun _ : ℕ => ℝ) 2

/-- The **dense core** inside `ℓ²(ℕ)`: the vectors with finite support, i.e. the
image of `ℕ →₀ ℝ`.  These are the term-denotable vectors of the chapter. -/
def FinSupport : Set Ell2 := {f | (Function.support ((f : ℕ → ℝ))).Finite}









/-- The geometric sequence `n ↦ 2⁻ⁿ` is square-summable. -/
theorem memℓp_geom : Memℓp (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 := by
  apply memℓp_gen
  have h : ∀ n : ℕ, ‖(1 / 2 : ℝ) ^ n‖ ^ ((2 : ℝ≥0∞).toReal) = ((1 / 4 : ℝ)) ^ n := by
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [ENNReal.toReal_ofNat]
    have h2 : ((1 / 2 : ℝ) ^ n) ^ (2 : ℝ) = ((1 / 2 : ℝ) ^ n) ^ (2 : ℕ) := by
      simp []
    rw [h2, ← pow_mul, mul_comm, pow_mul]
    norm_num
  simp only [h]
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- The geometric vector `n ↦ 2⁻ⁿ`, an element of the completion with infinite
support. -/
noncomputable def geomVec : Ell2 := ⟨fun n : ℕ => (1 / 2 : ℝ) ^ n, memℓp_geom⟩







end BookProof.ChapterRieszFischer


