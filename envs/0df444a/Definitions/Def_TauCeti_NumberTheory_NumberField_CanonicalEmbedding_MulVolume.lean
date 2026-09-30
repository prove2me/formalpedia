-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_CanonicalEmbedding_MulVolume
-- name    : TauCeti_NumberTheory_NumberField_CanonicalEmbedding_MulVolume
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:55:11.246637+00:00
-- url     : https://prove2.me/theorems/e6f29bbc-0e8c-46f8-83d3-1aade9c154b0
-- title:
--   The volume scaling of multiplication on the mixed space
-- statement:
--   In a number field's mixed embedding space, the absolute real algebra norm of $c$ equals its mixed norm. Multiplication by $c$ scales volume by this factor. In particular, multiplication by the mixed image of an integral unit $u\in\mathcal O_K^\times$ preserves volume, since its mixed norm is one. These identities supply the measure normalization in lattice counting.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/CanonicalEmbedding/MulVolume.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/CanonicalEmbedding/MulVolume.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_LinearAlgebra_Pi
import Definitions.Def_TauCeti_RingTheory_NormTrace_Pi
import Definitions.Def_TauCeti_RingTheory_NormTrace_Prod
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The volume scaling of multiplication on the mixed space

Multiplication by a fixed point `c` of the mixed space is an `ℝ`-linear endomorphism whose
determinant is the `ℝ`-algebra norm of `c`, so it scales Lebesgue measure by the absolute value
of that norm.  The norm is computed here as one factor per real place and one `Complex.normSq`
per complex place, and its absolute value is `mixedEmbedding.norm c`.

Specialising to the image of a unit, which has mixed norm one, gives that the unit action on the
mixed space leaves the volume of every set unchanged.

## Main results

* `NumberField.mixedEmbedding.algebraNorm_apply`: the `ℝ`-algebra norm of `c`, as a product over
  the places;
* `NumberField.mixedEmbedding.abs_algebraNorm`: the absolute value of that norm is
  `mixedEmbedding.norm c`;
* `NumberField.mixedEmbedding.volume_image_mul_left`: multiplication by `c` scales volume by
  `mixedEmbedding.norm c`;
* `MeasureTheory.SMulInvariantMeasure (𝓞 K)ˣ (mixedSpace K) volume`: the unit action preserves
  volume, so Mathlib's `measure_smul` and `measure_preimage_smul` apply.
-/

 section

open MeasureTheory NumberField NumberField.InfinitePlace

open scoped Pointwise

namespace NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **The `ℝ`-algebra norm of a point of the mixed space.**  Each real coordinate contributes
its own factor and each complex coordinate contributes the norm of multiplication by a complex
number, namely `Complex.normSq`. -/
theorem algebraNorm_apply (c : mixedSpace K) :
    Algebra.norm ℝ c = (∏ w, c.1 w) * ∏ w, Complex.normSq (c.2 w) := by
  simp [TauCeti.Algebra.norm_prod, TauCeti.Algebra.norm_pi, Algebra.norm_complex_apply]

/-- **The absolute `ℝ`-algebra norm of `c` is the mixed norm of `c`.**  Reach for this rather
than `algebraNorm_apply` when the norm feeds a measure-scaling lemma such as
`Measure.addHaar_image_linearMap`, which asks for the absolute value. -/
theorem abs_algebraNorm (c : mixedSpace K) : |Algebra.norm ℝ c| = mixedEmbedding.norm c := by
  -- Both sides are the same product of local absolute values: a real place contributes `|c.1 w|`
  -- with `mult w = 1`, a complex place `Complex.normSq (c.2 w) = ‖c.2 w‖ ^ 2` with `mult w = 2`.
  rw [algebraNorm_apply, abs_mul, Finset.abs_prod, Finset.abs_prod, mixedEmbedding.norm_apply,
    InfinitePlace.prod_eq_prod_mul_prod]
  simp [normAtPlace_apply_of_isReal, normAtPlace_apply_of_isComplex, Complex.normSq_eq_norm_sq,
    Subtype.prop]

open scoped Classical in
/-- **Multiplication by `c` scales volume by the mixed norm of `c`.**  The set `A` is arbitrary,
so there is no measurability hypothesis to discharge.  Its specialisation to the action of a
unit, where the factor is one, is the `SMulInvariantMeasure` instance below. -/
theorem volume_image_mul_left (c : mixedSpace K) (A : Set (mixedSpace K)) :
    volume ((c * ·) '' A) = ENNReal.ofReal (mixedEmbedding.norm c) * volume A := by
  have h : (c * ·) = ⇑(Algebra.lmul ℝ (mixedSpace K) c) := funext fun _ ↦ by simp
  rw [h, Measure.addHaar_image_linearMap, ← Algebra.norm_apply, abs_algebraNorm]

open scoped Classical in
/-- **The unit action preserves volume.**  With it, `measure_smul` and `measure_preimage_smul`
are the volume equations for `u • A` and `(u • ·) ⁻¹' A`, and `measurePreserving_smul` and the
`IsFundamentalDomain` lemmas apply to the unit action.  For a general multiplier `c`, where the
factor is `mixedEmbedding.norm c`, use `volume_image_mul_left`. -/
instance : SMulInvariantMeasure (𝓞 K)ˣ (mixedSpace K) volume :=
  -- A unit has mixed norm one, so the factor `volume_image_mul_left` supplies is one.
  have h (v : (𝓞 K)ˣ) (A : Set (mixedSpace K)) : volume (v • A) = volume A := by
    simp [← Set.image_smul, volume_image_mul_left]
  -- The preimage under `u` is the image under `u⁻¹`.
  ⟨fun u s _ ↦ by rw [Set.preimage_smul, h]⟩

end NumberField.mixedEmbedding

end
end


