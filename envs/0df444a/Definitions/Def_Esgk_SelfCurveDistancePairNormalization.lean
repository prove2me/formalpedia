-- Prove2me | Definitions.Def_Esgk_SelfCurveDistancePairNormalization
-- name    : Esgk_SelfCurveDistancePairNormalization
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:50:38.177691+00:00
-- url     : https://prove2.me/theorems/33058bcc-2653-4649-8f37-1b655f48ad54
-- title:
--   Symmetric points on the horizontal axis
-- statement:
--   This defines the planar point $(x,0)$ and proves that the points $(-r,0)$ and $(r,0)$ are distance $2r$ apart when $r$ is nonnegative.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_BridgeIdentity
import Definitions.Def_Esgk_SelfCurveDistancePairs
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry
open scoped EuclideanGeometry

 
def xAxisPoint (x : ℝ) : ℝ² := WithLp.toLp 2 ![x, 0]


lemma dist_xAxisPoint_neg_eq (r : ℝ) (hr : 0 ≤ r) :
    dist (xAxisPoint (-r)) (xAxisPoint r) = 2 * r := by
  have hsq : dist (xAxisPoint (-r)) (xAxisPoint r) ^ 2 = (-r - r) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simp [xAxisPoint, Real.dist_eq]
  nlinarith [dist_nonneg (x := xAxisPoint (-r)) (y := xAxisPoint r)]


end Esgk


