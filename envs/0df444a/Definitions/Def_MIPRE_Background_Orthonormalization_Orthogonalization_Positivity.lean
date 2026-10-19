-- Prove2me | Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Positivity
-- name    : MIPRE_Background_Orthonormalization_Orthogonalization_Positivity
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:34.306171+00:00
-- url     : https://prove2.me/theorems/ae0dd804-5667-4340-9e80-2d38a6ff0ce6
-- title:
--   Definitions of Positivity: Products of commuting positive operators
-- statement:
--   The definitions of the module `MIPRE.Background.Orthonormalization.Orthogonalization.Positivity` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). ### Products of commuting positive operators
--
--   The module is vendored read-only from the `orthogonalization` development of [vidick/commuting-repetition](https://github.com/vidick/commuting-repetition) (Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-repetition.py`.
--
--   **Definitions** (1): `Orthogonalization.toPositiveLinearMap` (A positive functional as a bundled `PositiveLinearMap`; this is the input of Mathlib's GNS construction, which is how the Cauchy–Schwarz…).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `le_of_le`, `nonneg_of_nonneg`, `toPositiveLinearMap_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.Orthonormalization.Orthogonalization.Positivity` (`MIPRE/Background/Orthonormalization/Orthogonalization/Positivity.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Orthonormalization/Orthogonalization/Positivity.lean

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Positivity.lean
-/
/-
# Operator-order toolbox

Generic order-theoretic facts about the C⋆-algebra `H →L[ℂ] H` of bounded
operators on a complex Hilbert space, used throughout the formalization of
M. de la Salle, *Orthogonalization of Positive Operator Valued Measures*
(arXiv:2103.14126v2).

Nothing in this file refers to POVMs, von Neumann algebras or the paper's
statements: it collects the elementary Loewner-order manipulations that the
assembly step (`PLAN.md` §1, step **F3**) and the reduction steps use over and
over:

* products of commuting positive operators (`mul_nonneg_of_commute`);
* the two operator inequalities the paper uses for `0 ≤ y ≤ 1`, namely
  `y² ≤ y` (`sq_le_self_of_le_one`) and `(1 - y)² ≤ 1 - y²`
  (`one_sub_sq_le_one_sub_sq'`);
* compressions by a projection commuting with a positive operator
  (`IsStarProjection.mul_le_of_commute`, `IsStarProjection.mul_nonneg_of_commute`);
* the continuous-functional-calculus square root: positivity, the bound
  `√y ≤ 1` for `y ≤ 1`, and the fact that it inherits every commutant
  (`Commute.sqrt`);
* positive linear functionals `φ` on `H →L[ℂ] H`, i.e. `ℂ`-linear maps with
  `0 ≤ φ (x* x)` for the `ComplexOrder` order on `ℂ`: they are monotone
  (`re_le_re_of_le`), real on positives (`im_eq_zero_of_nonneg`), and
  positive on positives (`nonneg_of_nonneg`).

The order on `H →L[ℂ] H` is the Loewner order
(`ContinuousLinearMap.le_def : f ≤ g ↔ (g - f).IsPositive`), for which Mathlib
provides a `StarOrderedRing` structure and the continuous functional calculus.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/Positivity.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit true

namespace Orthogonalization

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Products of commuting positive operators -/

section Order

variable {x y : H →L[ℂ] H}

end Order

/-! ### Compression by a commuting projection -/

namespace IsStarProjection

variable {q b : H →L[ℂ] H}

end IsStarProjection

/-! ### The continuous functional calculus square root -/

section Sqrt

variable {x y : H →L[ℂ] H}

end Sqrt

/-! ### Positive linear functionals

A *positive linear functional* on `H →L[ℂ] H` is a `ℂ`-linear map
`φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ` with `0 ≤ φ (star x * x)` for every `x`, the order on
`ℂ` being the `ComplexOrder` one (`0 ≤ z ↔ 0 ≤ z.re ∧ z.im = 0`). We do not
bundle the hypothesis, so that the lemmas apply verbatim to the functional
underlying a normal state. -/

section Functional

variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}

/-- A positive functional is nonnegative on positive operators: every positive
operator is of the form `star c * c` (`CStarAlgebra.nonneg_iff_eq_star_mul_self`). -/
theorem nonneg_of_nonneg (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) {x : H →L[ℂ] H}
    (hx : 0 ≤ x) : 0 ≤ φ x := by
  obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
  exact hφ c

/-- A positive functional is monotone (hence so is its real part). -/
theorem le_of_le (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) {x y : H →L[ℂ] H}
    (hxy : x ≤ y) : φ x ≤ φ y := by
  have h := nonneg_of_nonneg hφ (sub_nonneg.mpr hxy)
  rw [map_sub] at h
  exact sub_nonneg.mp h

/-- A positive functional as a bundled `PositiveLinearMap`; this is the input of
Mathlib's GNS construction, which is how the Cauchy–Schwarz inequality of
`Orthogonalization/PhiNorm.lean` is obtained. -/
def toPositiveLinearMap (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) : (H →L[ℂ] H) →ₚ[ℂ] ℂ where
  toLinearMap := φ
  monotone' _ _ hab := le_of_le hφ hab

@[simp]
theorem toPositiveLinearMap_apply (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) (x : H →L[ℂ] H) :
    toPositiveLinearMap φ hφ x = φ x := rfl

end Functional

end Orthogonalization


