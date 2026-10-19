-- Prove2me | Definitions.Def_ChapterCayleySpectralModel
-- name    : ChapterCayleySpectralModel
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-17T01:18:27.931186+00:00
-- url     : https://prove2.me/theorems/0be269ed-b86d-4146-9189-8890d7e9eedd
-- title:
--   Chapter CayleySpectralModel
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCayleySpectralModel.lean`): generated def bundle for ChapterCayleySpectralModel. See BookProof/ChapterCayleySpectralModel.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCayleySpectralModel.lean

import Definitions.Def_ChapterCayleyTransform
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterUnitaryTransport
import Mathlib
import Theorems.Thm_BookProof_ChapterCayleyTransform_sub_cayley_shift
import Theorems.Thm_BookProof_ChapterCayleyTransform_cayley_shift


/-!
# The spectral model of an unbounded self-adjoint operator, via its Cayley transform

`ChapterSpectralMultiplication` proves the spectral theorem in multiplication form
for a **bounded** normal operator with a cyclic vector, and
`ChapterCayleyTransform` turns an **unbounded** self-adjoint operator `A` into the
unitary `V = (A - i)(A + i)⁻¹`.  This module composes the two, and so obtains a
multiplication model for the unbounded operator itself.

The point that makes the composition work without any theory of unbounded
multiplication operators is that the *resolvent* is a **continuous** function of
the Cayley transform:

* `res_neg_one_eq_cayley` — `(A + i)⁻¹ = (2i)⁻¹(1 - V)`;
* `res_one_eq_cayley` — `(A - i)⁻¹ = (2i)⁻¹(V⁻¹ - 1)`;
* `cayleyCLM`, `isStarNormal_cayleyCLM` — `V` as a bounded *normal* operator, so
  the continuous functional calculus applies to it;
* `resSymbol` `g(z) = (1 - z)/(2i)` and `opSymbol` `h(z) = (1 + z)/2`, with
  `cfcHom_resSymbol` (`g(V) = (A + i)⁻¹`) and `cfcHom_opSymbol`
  (`h(V)y = A (A + i)⁻¹ y`).

Feeding these two bounded symbols through the multiplication model of the Cayley
transform gives the headline

* `unbounded_spectral_multiplication_model` — there is a Borel probability measure
  `μ` on the spectrum of `V` and a unitary `U : L²(μ) ≃ H` such that **every**
  vector of `D(A)` is of the form `U(g·u)`, and `A U(g·u) = U(h·u)`.  Since
  `h/g = i(1 + z)/(1 - z)`, this says exactly that `A` is multiplication by the
  real function `i(1 + z)/(1 - z)` on `L²(μ)` — the spectral theorem for the
  unbounded operator, in the cyclic case.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped InnerProductSpace
open MeasureTheory

namespace BookProof.ChapterCayleySpectralModel

open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterCayleyTransform BookProof.ChapterAbelianGelfandModel
open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

/-! ## The resolvents in terms of the Cayley transform -/

/-- `(A + i)⁻¹ = (2i)⁻¹(1 - V)`. -/
theorem res_neg_one_eq_cayley (y : H) :
    ((T.res (-1) y : T.domain) : H) = (2 * Complex.I)⁻¹ • (y - cayley T y) := by
  have h2 : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  have hy : T.shift (-1) (T.res (-1) y) = y := T.shift_res (by norm_num) y
  have h := sub_cayley_shift T (T.res (-1) y)
  rw [hy] at h
  rw [h, smul_smul, inv_mul_cancel₀ h2, one_smul]

/-- `(A - i)⁻¹ = (2i)⁻¹(V⁻¹ - 1)`. -/
theorem res_one_eq_cayley (y : H) :
    ((T.res 1 y : T.domain) : H) = (2 * Complex.I)⁻¹ • ((cayley T).symm y - y) := by
  have h2 : (2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  have hy : T.shift 1 (T.res 1 y) = y := T.shift_res (by norm_num) y
  have hu : cayley T (T.shift (-1) (T.res 1 y)) = y := by rw [cayley_shift, hy]
  have husym := congrArg (cayley T).symm hu
  rw [LinearIsometryEquiv.symm_apply_apply] at husym
  have h := sub_cayley_shift T (T.res 1 y)
  rw [husym, LinearIsometryEquiv.apply_symm_apply] at h
  rw [h, smul_smul, inv_mul_cancel₀ h2, one_smul]

/-! ## The Cayley transform as a bounded normal operator -/

/-- The Cayley transform as a bounded operator. -/
noncomputable def cayleyCLM : H →L[ℂ] H := (cayley T).toContinuousLinearEquiv

@[simp] theorem cayleyCLM_apply (y : H) : cayleyCLM T y = cayley T y := rfl

/-- A unitary is a normal operator, so the continuous functional calculus applies
to the Cayley transform. -/
theorem isStarNormal_cayleyCLM : IsStarNormal (cayleyCLM T) := by
  have hadj : star (cayleyCLM T) = ((cayley T).symm.toContinuousLinearEquiv : H →L[ℂ] H) := by
    symm
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    change ⟪(cayley T).symm x, y⟫_ℂ = ⟪x, cayley T y⟫_ℂ
    rw [← (cayley T).inner_map_map ((cayley T).symm x) y,
      LinearIsometryEquiv.apply_symm_apply]
  constructor
  rw [hadj]
  ext x
  change (cayley T).symm (cayley T x) = cayley T ((cayley T).symm x)
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply]

/-! ## The two bounded symbols -/

/-- The symbol of the resolvent: `g(z) = (1 - z)/(2i)`. -/
noncomputable def resSymbol : C(spectrum ℂ (cayleyCLM T), ℂ) :=
  (2 * Complex.I)⁻¹ • (1 - coordFn (cayleyCLM T))

/-- The symbol of the operator on the range of the resolvent: `h(z) = (1 + z)/2`.
Since `h/g = i(1 + z)/(1 - z)`, the pair `(g, h)` is the multiplication model of
the unbounded operator. -/
noncomputable def opSymbol : C(spectrum ℂ (cayleyCLM T), ℂ) :=
  (2 : ℂ)⁻¹ • (1 + coordFn (cayleyCLM T))

@[simp] theorem resSymbol_apply (z : spectrum ℂ (cayleyCLM T)) :
    resSymbol T z = (1 - (z : ℂ)) / (2 * Complex.I) := by
  simp [resSymbol, coordFn, div_eq_inv_mul]

@[simp] theorem opSymbol_apply (z : spectrum ℂ (cayleyCLM T)) :
    opSymbol T z = (1 + (z : ℂ)) / 2 := by
  simp [opSymbol, coordFn, div_eq_inv_mul, mul_add]

theorem cfcHom_resSymbol_eq :
    cfcHom (isStarNormal_cayleyCLM T) (resSymbol T)
      = (2 * Complex.I)⁻¹ • (1 - cayleyCLM T) := by
  rw [resSymbol, map_smul, map_sub, map_one, cfcHom_coordFn]

theorem cfcHom_opSymbol_eq :
    cfcHom (isStarNormal_cayleyCLM T) (opSymbol T)
      = (2 : ℂ)⁻¹ • (1 + cayleyCLM T) := by
  rw [opSymbol, map_smul, map_add, map_one, cfcHom_coordFn]





/-! ## The multiplication model -/

variable (xi : H)







end BookProof.ChapterCayleySpectralModel


