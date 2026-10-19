-- Prove2me | Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Blocks
-- name    : MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Blocks
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:51:29.845719+00:00
-- url     : https://prove2.me/theorems/163888c2-0a19-4721-8ccb-62b8db2ddf63
-- title:
--   Definitions of Blocks (5 definitions)
-- statement:
--   The definitions of the module `MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.Blocks` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization).
--
--   The module is vendored read-only from the `orthogonalization` development of [vidick/commuting-repetition](https://github.com/vidick/commuting-repetition) (Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-repetition.py`.
--
--   **Definitions** (5): `Orthogonalization.FinDim.BlockSpace` (The Hilbert space direct sum `H^ι`.); `Orthogonalization.FinDim.blockMap` (The map `T = ∑ embed i ∘ X i : H → H^ι` with blocks `X i`.); `Orthogonalization.FinDim.blockProj` (The block projection `Q = ∑ embed i ∘ q i ∘ proj i` on `H^ι`.); `Orthogonalization.FinDim.embed` (Coordinate embedding `v ↦ (0, …, v, …, 0)`.); `Orthogonalization.FinDim.proj` (Coordinate projection.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.Orthonormalization.Orthogonalization.FinDim.Blocks` (`MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/Blocks.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/Blocks.lean

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/Blocks.lean
-/
/-
# The block space `H^ι` and its coordinate maps

`BlockSpace H ι := PiLp 2 (fun _ : ι => H)` is the Hilbert space direct sum of
`card ι` copies of `H`; `embed i : H → H^ι` and `proj i : H^ι → H` are the
coordinate maps, adjoint to each other, with `proj i ∘ embed j = δᵢⱼ` and
`∑ embed i ∘ proj i = 1`. This is the paper's `M_n(M)` picture read on
vectors (cf. the sister project's `VN/BlockOperators`, which is specific to
its tracial standard forms). Proof-side.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/Blocks.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit true

namespace Orthogonalization.FinDim

open scoped InnerProductSpace
open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (H) in
/-- The Hilbert space direct sum `H^ι`. -/
abbrev BlockSpace (ι : Type*) : Type _ := PiLp 2 (fun _ : ι => H)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinate embedding `v ↦ (0, …, v, …, 0)`. -/
noncomputable def embed (i : ι) : H →L[ℂ] BlockSpace H ι :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun j : ι => if j = i then ContinuousLinearMap.id ℂ H else 0)

/-- Coordinate projection. -/
noncomputable def proj (i : ι) : BlockSpace H ι →L[ℂ] H := PiLp.proj 2 (fun _ : ι => H) i

/-- The map `T = ∑ embed i ∘ X i : H → H^ι` with blocks `X i`. -/
noncomputable def blockMap (X : ι → H →L[ℂ] H) : H →L[ℂ] BlockSpace H ι :=
  ∑ i, embed i ∘L X i

/-- The block projection `Q = ∑ embed i ∘ q i ∘ proj i` on `H^ι`. -/
noncomputable def blockProj (q : ι → H →L[ℂ] H) : BlockSpace H ι →L[ℂ] BlockSpace H ι :=
  ∑ i, embed i ∘L q i ∘L proj i

end Orthogonalization.FinDim


