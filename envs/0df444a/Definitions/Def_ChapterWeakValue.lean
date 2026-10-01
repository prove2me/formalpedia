-- Prove2me | Definitions.Def_ChapterWeakValue
-- name    : ChapterWeakValue
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:05:27.816249+00:00
-- url     : https://prove2.me/theorems/294351e5-fd05-43c3-9803-fc4765927f46
-- title:
--   Chapter WeakValue
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterWeakValue.lean`): generated def bundle for ChapterWeakValue. See BookProof/ChapterWeakValue.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWeakValue.lean

import Definitions.Def_ChapterTrajectory
import Mathlib


/-!
# Chapter "Reconstructing the classical trajectory of any isolated quantum system"
— §"Weak measurements and weak values"

Source: `book.tex`, chapter *"Reconstructing the classical trajectory of any
isolated quantum system"*, §*"Reconstruction of the trajectory"*, and the
double-slit chapter's "Weak Measurements" section (`Book/DoubleSlit.lean`).

`BookProof.ChapterTrajectory` formalizes the post-selected (ABL / two-state)
*probability* of an intermediate outcome.  This module formalizes the companion
object: the **weak value** of an observable `A` for a pre-selection `|i⟩` and a
post-selection `|f⟩`,

  `⟨A⟩_w = ⟨f|A|i⟩ / ⟨f|i⟩`,

on the finite complex Hilbert space `Fin n → ℂ` with the standard inner product
`ip f v = ∑ₖ conj (f k) * v k`.

Main results:

* `weakValue_wellDefined` — whenever `⟨f|i⟩ ≠ 0` the ratio is the unique solution
  of `⟨A⟩_w · ⟨f|i⟩ = ⟨f|A|i⟩` (so it is a well-defined complex number);
* `weakValue_diag` — when the post-selection *is* the pre-selection (`f = i`, a
  unit vector) the weak value collapses to the ordinary expectation `⟨i|A|i⟩`;
* `weakValue_diag_isReal` — and that expectation is real for a Hermitian `A`;
* `weakValue_add`, `weakValue_smul`, `weakValue_linear` — linearity in the
  observable, the algebraic core of "weak measurements are linear in `A`";
* `weakValue_proj`, `weakValue_proj_sum` — weak values of the basis projectors,
  which sum to `1` exactly like the post-selected probabilities of
  `ChapterTrajectory.condProb_sum`;
* `jointProb_eq_normSq_weakNumerator` and `condProb_eq_weakNumerator_ratio` — the
  tie to `ChapterTrajectory`: the ABL joint law is the squared modulus of the
  weak-value numerator for the post-selection vector `b ↦ conj (V f b)`, and the
  post-selected conditional law is the normalized version of it;
* `dslit_weakValue` — the double-slit capstone: pre-selecting the both-slits
  superposition `H·Ψ` and post-selecting the state `Ψ = (1,0)`, the which-slit
  projectors have weak values `1` and `0`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped BigOperators Matrix

namespace BookProof.ChapterWeakValue

variable {n : ℕ}

/-- The standard inner product on `Fin n → ℂ`, conjugate-linear in the first
argument: `⟨f|v⟩ = ∑ₖ conj (f k) · v k`. -/
noncomputable def ip (f v : Fin n → ℂ) : ℂ := ∑ k, starRingEnd ℂ (f k) * v k

/-- The **weak value** of the observable `A` for the pre-selection `i` and the
post-selection `f`: `⟨A⟩_w = ⟨f|A|i⟩ / ⟨f|i⟩`. -/
noncomputable def weakValue (i f : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ip f (A *ᵥ i) / ip f i

/-! ## Elementary properties of the inner product -/







/-! ## Well-definedness -/





/-! ## Diagonal collapse to the ordinary expectation -/





/-! ## Linearity in the observable -/









/-! ## Weak values of the basis projectors -/

/-- The rank-one projector onto the `a`-th basis vector. -/
def projMat (a : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  fun b c => if b = a ∧ c = a then 1 else 0









/-! ## Tie to the post-selected (ABL) probabilities of `ChapterTrajectory` -/

open BookProof.ChapterTrajectory in
/-- The post-selection covector attached to the final outcome `f` of the unitary
`V`: `b ↦ conj (V f b)`, i.e. the state whose overlap with the intermediate
basis vector `e_b` is the transition amplitude `V_{f b}`. -/
def postSelect (V : Matrix (Fin n) (Fin n) ℂ) (f : Fin n) : Fin n → ℂ :=
  fun b => starRingEnd ℂ (V f b)





/-! ## Double-slit capstone -/

open BookProof.ChapterDoubleSlit









end BookProof.ChapterWeakValue


