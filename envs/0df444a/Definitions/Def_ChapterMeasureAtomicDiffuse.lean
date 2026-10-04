-- Prove2me | Definitions.Def_ChapterMeasureAtomicDiffuse
-- name    : ChapterMeasureAtomicDiffuse
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T08:46:06.537113+00:00
-- url     : https://prove2.me/theorems/5869c483-ddcc-4302-97e2-7b0a239fe863
-- title:
--   Chapter MeasureAtomicDiffuse
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMeasureAtomicDiffuse.lean`): generated def bundle for ChapterMeasureAtomicDiffuse. See BookProof/ChapterMeasureAtomicDiffuse.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMeasureAtomicDiffuse.lean

import Definitions.Def_ChapterA4
import Mathlib


/-!
# Atomic and diffuse parts of a measure (plan GAP-2, the classification bookkeeping)

`ChapterAbelianDirectSum` shows that every abelian algebra of operators on a complex
Hilbert space is a direct sum of multiplication algebras `L∞(μₓ)` on `L²(μₓ)`, for
Borel probability measures `μₓ`.  The manuscript's classification list is phrased in
terms of the *type* of each measure — purely atomic (`Iₙ` or `ℓ∞(ℕ)`), diffuse
(`L∞[0,1]`) or a mixture of the two.  This module supplies the measure-theoretic
bookkeeping that sorts a summand into those classes:

* `atomSet` — the set of atoms `{x : μ{x} ≠ 0}`;
* `countable_atomSet` — it is **countable** (the singletons are disjoint and the
  measure is finite);
* `measurableSet_atomSet`, `restrict_atomSet_add_restrict_compl` — the induced
  splitting `μ = μ|atoms + μ|non-atoms`;
* `noAtoms_restrict_compl_atomSet` — the second summand is **diffuse** (it has no
  atoms at all);
* `restrict_atomSet_eq_sum_dirac` — the first summand is **purely atomic**: a
  countable sum of point masses `μ{x} · δₓ`;
* HEADLINE `exists_atomic_diffuse_decomposition` — every finite measure (on a space
  whose singletons are measurable) is the sum of a countable sum of point masses and
  an atomless measure;
* `abelian_multiplication_model_atomic_diffuse` — the two statements combined: every
  abelian algebra of operators is a direct sum of multiplication algebras whose
  measures each split into a purely atomic and a diffuse part.

Everything is `sorry`-free and `axiom`-free.
-/

noncomputable section

open MeasureTheory Complex

namespace BookProof.ChapterMeasureAtomicDiffuse

section AtomSet

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

/-- **The set of atoms** of a measure. -/
def atomSet : Set α := {x : α | mu {x} ≠ 0}



omit [MeasurableSingletonClass α] in
theorem measure_singleton_eq_zero_of_notMem_atomSet {x : α} (hx : x ∉ atomSet mu) :
    mu {x} = 0 := by
  simpa [atomSet] using hx







/-- **The complementary part is diffuse**: off the atoms the measure has no atoms. -/
instance noAtoms_restrict_compl_atomSet : NullSingletonClass (mu.restrict (atomSet mu)ᶜ) := by
  constructor
  intro x
  by_cases hx : x ∈ atomSet mu
  · rw [Measure.restrict_apply (measurableSet_singleton x)]
    have hempty : ({x} : Set α) ∩ (atomSet mu)ᶜ = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_compl_iff,
        Set.mem_empty_iff_false, iff_false, not_and, not_not]
      rintro rfl
      exact hx
    simp [hempty]
  · refine le_antisymm ?_ zero_le
    exact le_trans (Measure.restrict_apply_le _ _)
      (le_of_eq (measure_singleton_eq_zero_of_notMem_atomSet mu hx))







end AtomSet

/-! ## The abelian model with its summands classified -/

section Model


variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



end Model

end BookProof.ChapterMeasureAtomicDiffuse

end


