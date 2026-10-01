-- Prove2me | Definitions.Def_ChapterAbelianMixture
-- name    : ChapterAbelianMixture
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:55:34.547978+00:00
-- url     : https://prove2.me/theorems/5e62bd27-484f-4511-8c7d-8aec225c02bd
-- title:
--   Chapter AbelianMixture
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAbelianMixture.lean`): generated def bundle for ChapterAbelianMixture. See BookProof/ChapterAbelianMixture.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAbelianMixture.lean

import Definitions.Def_ChapterLinftyMultiplication
import Mathlib


/-!
# The mixed (atomic ⊕ diffuse) class of the abelian von Neumann list (plan Part F.5)

The abelian von Neumann classification quoted in the book lists the finite
diagonal algebras `ℓ∞(n)` (`ChapterAbelianDiagonal`,
`ChapterAbelianVonNeumannFinite`), the countable diagonal algebra `ℓ∞(ℕ)` on
`ℓ²(ℕ)` (`ChapterAbelianDiagonalCountable`), the diffuse model `L∞(μ)` on
`L²(μ)` (`ChapterLinftyMultiplication`) — and the **mixtures** of an atomic and a
diffuse part.  This module supplies a mixture.

The witness is deliberately elementary: on `ℝ` take

  `mixtureMeasure := volume|_{[0,1]} + δ₂`,

a finite measure with a genuine atom (at `2`) *and* a diffuse part of positive
mass (`[0,1]`, every point of which is null).  Multiplication by essentially
bounded functions on `L²(mixtureMeasure)` is then a unital, abelian, star-closed
and faithful algebra of bounded operators whose underlying measure is neither
purely atomic nor atomless.

## Deliverables

* `mixtureMeasure`, `instIsFiniteMeasureMixture`, `mixtureMeasure_univ` — the
  mixture is a finite measure of total mass `2`;
* `mixtureMeasure_atom` — the atomic part: `μ{2} = 1 > 0`;
* `mixtureMeasure_diffuse_point` — the diffuse part: `μ{x} = 0` for every
  `x ∈ [0,1]`;
* `mixtureMeasure_diffuse_mass` — that diffuse part carries positive mass,
  `μ([0,1]) = 1`;
* `mixtureMeasure_not_atomless`, `mixtureMeasure_not_purely_atomic_on_Icc` — the
  measure is neither atomless nor concentrated on its atoms;
* `vonNeumann_abelian_class_mixture` — **headline**: the `L∞` multiplication
  algebra over the mixture is unital, abelian, multiplicative, star-closed and
  faithful, i.e. the mixed class of the list is realized.

**Documented gap (unchanged).**  *Exhaustiveness* of the classification — that
every abelian von Neumann algebra is `*`-isomorphic to one of these models — is
not claimed; it needs von-Neumann-algebra machinery that is unavailable in this
toolchain.  What is proved is that the mixed item of the list is a genuine
abelian, faithful, star-closed operator algebra with both an atomic and a
diffuse component.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

open MeasureTheory ENNReal

namespace BookProof.ChapterAbelianMixture

/-- The **mixture measure**: Lebesgue measure on `[0,1]` (the diffuse part) plus
a Dirac mass at `2` (the atomic part). -/
def mixtureMeasure : Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1) + Measure.dirac (2 : ℝ)

theorem mixtureMeasure_apply (s : Set ℝ) (hs : MeasurableSet s) :
    mixtureMeasure s
      = MeasureTheory.volume (s ∩ Set.Icc (0 : ℝ) 1) + Measure.dirac (2 : ℝ) s := by
  rw [mixtureMeasure, Measure.coe_add, Pi.add_apply, Measure.restrict_apply hs]

theorem mixtureMeasure_univ : mixtureMeasure Set.univ = 2 := by
  rw [mixtureMeasure_apply _ MeasurableSet.univ]
  simp only [Real.volume_Icc, Set.univ_inter, sub_zero, ENNReal.ofReal_one,
    Measure.dirac_apply, Set.indicator_of_mem (Set.mem_univ (2 : ℝ)), Pi.one_apply]
  exact one_add_one_eq_two

instance instIsFiniteMeasureMixture : IsFiniteMeasure mixtureMeasure :=
  ⟨by rw [mixtureMeasure_univ]; exact ENNReal.ofNat_lt_top⟩

/-! ## The atomic and the diffuse part -/











/-! ## The mixed class of the classification -/

open BookProof.ChapterLinftyMultiplication



end BookProof.ChapterAbelianMixture

end


