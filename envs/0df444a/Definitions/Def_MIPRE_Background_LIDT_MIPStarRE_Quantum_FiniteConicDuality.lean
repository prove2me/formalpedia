-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteConicDuality
-- name    : MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteConicDuality
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:11:17.918991+00:00
-- url     : https://prove2.me/theorems/a7464493-ef70-4d7a-93a9-ddc655360900
-- title:
--   Definitions of FiniteConicDuality: Finite conic-duality separation lemmas This module contains the product-space part of the finite-dimensional conic…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteConicDuality` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Finite conic-duality separation lemmas. This module contains the product-space part of the finite-dimensional conic duality argument used by the Section 9 SDP. A separator on a product space `E × ℝ` decomposes into a constraint-coordinate functional and an objective coefficient. If the separator is nonnegative on a conic image and negative at a point with the same constraint coordinate but larger objective coordinate, then the objective coefficient is negative. After normalizing by this negative coefficient one obtains the functional dual bound. The matrix trace-pairing representation and the…
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (3): `MIPStarRE.Quantum.conicNormalizedSeparatorFunctional` (The normalized constraint-coordinate functional associated to a separator.); `MIPStarRE.Quantum.conicSeparatorConstraintFunctional` (The constraint-coordinate part of a separator on a product space.); `MIPStarRE.Quantum.conicSeparatorObjectiveCoefficient` (The objective-coordinate coefficient of a separator on a product space.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `conicNormalizedSeparatorFunctional_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteConicDuality` (`MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteConicDuality.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

set_option backward.isDefEq.respectTransparency false

/-!
# Finite conic-duality separation lemmas

This module contains the product-space part of the finite-dimensional conic
duality argument used by the Section 9 SDP.  A separator on a product space
`E × ℝ` decomposes into a constraint-coordinate functional and an objective
coefficient.  If the separator is nonnegative on a conic image and negative at
a point with the same constraint coordinate but larger objective coordinate,
then the objective coefficient is negative.  After normalizing by this negative
coefficient one obtains the functional dual bound.

The matrix trace-pairing representation and the paper-form SDP witness remain
in the Section 9 matrix-realization layer.

## References

- `references/ldt-paper/self_improvement.tex`
- `docs/reports/issue-2386-finite-sdp-duality-theorem-design.md`
-/

namespace MIPStarRE.Quantum

/-- The constraint-coordinate part of a separator on a product space. -/
noncomputable def conicSeparatorConstraintFunctional
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) :
    StrongDual ℝ E :=
  φ.comp (ContinuousLinearMap.inl ℝ E ℝ)

/-- The objective-coordinate coefficient of a separator on a product space. -/
noncomputable def conicSeparatorObjectiveCoefficient
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) : ℝ :=
  (φ.comp (ContinuousLinearMap.inr ℝ E ℝ)) (1 : ℝ)

/-- The normalized constraint-coordinate functional associated to a separator.

This definition is useful when the objective-coordinate coefficient is known to
be negative. -/
noncomputable def conicNormalizedSeparatorFunctional
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) :
    StrongDual ℝ E :=
  ((-conicSeparatorObjectiveCoefficient φ)⁻¹) •
    conicSeparatorConstraintFunctional φ

@[simp]
theorem conicNormalizedSeparatorFunctional_apply
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ)) (y : E) :
    conicNormalizedSeparatorFunctional φ y =
      ((-conicSeparatorObjectiveCoefficient φ)⁻¹) *
        conicSeparatorConstraintFunctional φ y := by
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

end MIPStarRE.Quantum


