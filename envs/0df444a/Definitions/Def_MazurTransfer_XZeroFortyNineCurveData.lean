-- Prove2me | Definitions.Def_MazurTransfer_XZeroFortyNineCurveData
-- name    : MazurTransfer_XZeroFortyNineCurveData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T14:31:03.982789+00:00
-- url     : https://prove2.me/theorems/bd7933b3-43d3-4632-89aa-9b3f063b9bf8
-- title:
--   The explicit order-49 descent model and its rational cusp
-- statement:
--   The rational Weierstrass model $E_{49}:y^2=x(x^2+21x+112)$ and its specified affine point $T=(0,0)$. This module checks the nonzero discriminant and the equation at the specified point so that its group and point types are available. It contains no finiteness, rank, or rational-point classification proof. Named downstream consumers: the complete two-isogeny descent and the two-cusp classification.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: XZeroFortyNineDescent.lean. Four complete structural commands selected from Lean AST ranges; original headers and values retained.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib

namespace MazurTorsion.XZeroFortyNine

/-- The split model of `X₀(49)` used for the descent. -/
def curve : WeierstrassCurve ℚ :=
  ⟨0, 21, 0, 112, 0⟩

instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma nonsingular_zero_zero :
    curve.toAffine.Nonsingular 0 0 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

/-- The unique nonzero rational point killed by two. -/
def T : curve.toAffine.Point :=
  .some 0 0 nonsingular_zero_zero

end MazurTorsion.XZeroFortyNine


