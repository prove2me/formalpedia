-- Prove2me | Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_IsometryData
-- name    : MIPRE_Background_Orthonormalization_Orthogonalization_IsometryData
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:51:29.170271+00:00
-- url     : https://prove2.me/theorems/057673a8-298c-48ae-bd52-dcb1a2a6c23e
-- title:
--   Definitions of IsometryData (1 definitions)
-- statement:
--   The definitions of the module `MIPRE.Background.Orthonormalization.Orthogonalization.IsometryData` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization).
--
--   The module is vendored read-only from the `orthogonalization` development of [vidick/commuting-repetition](https://github.com/vidick/commuting-repetition) (Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-repetition.py`.
--
--   **Definitions** (1): `Orthogonalization.IsometryData` (The block-wise partial isometry of Lemma 3.2 / the proof of Theorem 1.2 in the finite case: (W1) `∑ wᵢ* wᵢ = 1`, (W2) `wᵢ wⱼ* = δᵢⱼ qᵢ`,…).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.Orthonormalization.Orthogonalization.IsometryData` (`MIPRE/Background/Orthonormalization/Orthogonalization/IsometryData.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Orthonormalization/Orthogonalization/IsometryData.lean

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/IsometryData.lean
-/
/-
# The isometry data of Step F3 (proof-side interface)

In the paper's finite case (Section 3), after Lemma 3.1 produced projections
`q_i` commuting with the `a_i` and with `∑ E(q_i) = 1`, Lemma 3.2 supplies a
partial isometry `u ∈ M_n(M)` with `u u* = ∑ e_{ii} ⊗ q_i`, `u* u = e_{11} ⊗ 1`
and `u |x| = x` for `x = ∑ e_{i1} ⊗ q_i a_i^{1/2}`. Reading `u` block by block,
`w_i := (e_{1i} ⊗ 1) u` is a family of operators on `H` with

* (W1) `∑ w_i* w_i = 1`,
* (W2) `w_i w_j* = δ_{ij} q_i`,
* (W3) `w_i √y = q_i √a_i` where `y = ∑ q_i a_i`.

Everything the assembly (`Assembly.lean`) needs is (W1)–(W3); the PVM is
`p_i = w_i* w_i`. This file only defines the interface; it is produced in
finite dimension by `FinDim/Isometry.lean` and in general from the comparison
theory of the structure-theory interface (PLAN.md T3). Nothing here is a
statement of the paper.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/IsometryData.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic
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
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Ring.Basic
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The block-wise partial isometry of Lemma 3.2 / the proof of Theorem 1.2 in
the finite case: (W1) `∑ wᵢ* wᵢ = 1`, (W2) `wᵢ wⱼ* = δᵢⱼ qᵢ`,
(W3) `wᵢ √(∑ qⱼ aⱼ) = qᵢ √aᵢ`. -/
structure IsometryData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a q w : ι → H →L[ℂ] H) : Prop where
  sum_star_mul : ∑ i, star (w i) * w i = 1
  mul_star : ∀ i j, w i * star (w j) = if i = j then q i else 0
  mul_sqrt : ∀ i, w i * CFC.sqrt (∑ j, q j * a j) = q i * CFC.sqrt (a i)

end Orthogonalization


