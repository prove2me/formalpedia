-- Prove2me | Definitions.Def_ChapterCayleyTransform
-- name    : ChapterCayleyTransform
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:31:25.586983+00:00
-- url     : https://prove2.me/theorems/da573e49-d809-4859-a4a3-850db40ca032
-- title:
--   Chapter CayleyTransform
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCayleyTransform.lean`): generated def bundle for ChapterCayleyTransform. See BookProof/ChapterCayleyTransform.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCayleyTransform.lean

import Definitions.Def_ChapterStoneResolvent
import Mathlib


/-!
# The Cayley transform of an unbounded self-adjoint operator

`BookProof.ChapterStoneResolvent` builds the resolvents `(A - i l)⁻¹` of a
densely defined self-adjoint operator `A` (the bundle
`UnboundedSelfAdjoint`).  This module uses them to construct the **Cayley
transform**

`V = (A - i)(A + i)⁻¹`,

the standard device that trades an unbounded self-adjoint operator for a
*bounded* — indeed unitary — one, and which is the usual entry point to the
spectral theorem in the unbounded case.

* `cayleyMap` / `cayley` — the transform, first as a linear map and then, after
  `norm_cayleyMap` (isometry) and `cayleyMap_surjective`, as a **unitary**
  `H ≃ₗᵢ[ℂ] H`;
* `cayley_shift` — the defining relation `V (A + i)ψ = (A - i)ψ`;
* `sub_cayley_shift` / `add_cayley_shift` — `(1 - V)(A + i)ψ = 2iψ` and
  `(1 + V)(A + i)ψ = 2Aψ`;
* `one_sub_cayley_injective`, `cayley_apply_ne_self`,
  `range_one_sub_cayley` (`ran(1 - V) = D(A)`) and
  `denseRange_one_sub_cayley` — `1` is not an eigenvalue of `V` and `1 - V` has
  dense range, the two conditions characterising the Cayley transforms of
  self-adjoint operators;
* `op_eq_cayley` / `coe_eq_cayley` — the **reconstruction** `A = i(1 + V)(1 - V)⁻¹`
  in the pointwise form `Aψ = ½(y + Vy)`, `ψ = -(i/2)(y - Vy)` with `y = (A + i)ψ`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped InnerProductSpace
open Filter Topology

namespace BookProof.ChapterCayleyTransform

open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

/-! ## `A + i` and `A - i` have the same norm -/

omit [CompleteSpace H] in
/-- The Pythagoras identity makes `‖(A - i)ψ‖` and `‖(A + i)ψ‖` equal: both equal
`‖Aψ‖² + ‖ψ‖²`. -/
theorem norm_shift_one_eq_norm_shift_neg_one (x : T.domain) :
    ‖T.shift 1 x‖ = ‖T.shift (-1) x‖ := by
  have h1 := T.norm_shift_sq 1 x
  have h2 := T.norm_shift_sq (-1) x
  have hsq : ‖T.shift 1 x‖ ^ 2 = ‖T.shift (-1) x‖ ^ 2 := by
    rw [h1, h2]; norm_num
  have hroot := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hroot

/-! ## The transform -/

/-- The **Cayley transform** `V = (A - i)(A + i)⁻¹`, as a linear map. -/
noncomputable def cayleyMap : H →ₗ[ℂ] H := (T.shift 1).comp (T.res (-1))

theorem cayleyMap_apply (y : H) : cayleyMap T y = T.shift 1 (T.res (-1) y) := rfl

/-- The defining relation of the Cayley transform: `V (A + i)ψ = (A - i)ψ`. -/
theorem cayleyMap_shift (x : T.domain) : cayleyMap T (T.shift (-1) x) = T.shift 1 x := by
  rw [cayleyMap_apply, T.res_shift (by norm_num)]

theorem norm_cayleyMap (y : H) : ‖cayleyMap T y‖ = ‖y‖ := by
  have hy : T.shift (-1) (T.res (-1) y) = y := T.shift_res (by norm_num) y
  rw [cayleyMap_apply, norm_shift_one_eq_norm_shift_neg_one, hy]

theorem cayleyMap_surjective : Function.Surjective (cayleyMap T) := by
  intro z
  refine ⟨T.shift (-1) (T.res 1 z), ?_⟩
  rw [cayleyMap_shift, T.shift_res (by norm_num)]

/-- The Cayley transform of a self-adjoint operator is **unitary**. -/
noncomputable def cayley : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective ⟨cayleyMap T, norm_cayleyMap T⟩ (cayleyMap_surjective T)





/-! ## `1 - V` and `1 + V` -/













/-! ## Reconstruction: `A = i(1 + V)(1 - V)⁻¹` -/





end BookProof.ChapterCayleyTransform


