-- Prove2me | Definitions.Def_Esgk_NormalizedDistancePairInfiniteProjection
-- name    : Esgk_NormalizedDistancePairInfiniteProjection
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:48:52.639529+00:00
-- url     : https://prove2.me/theorems/90ea2fd1-9cb5-4c19-95b0-6e0960b768e5
-- title:
--   Normalized left and right squared-distance values
-- statement:
--   For a real parameter and a planar point, this defines the squared distances to the two points on the horizontal axis at offsets plus and minus that parameter.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_SelfCurveReflectionInvariance
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open PachDeZeeuw.Algebraic

 
def normalizedLeftValue (r : ℝ) (x : Point2) : ℝ :=
  (x 0 + r) ^ 2 + (x 1) ^ 2

def normalizedRightValue (r : ℝ) (x : Point2) : ℝ :=
  (x 0 - r) ^ 2 + (x 1) ^ 2


end Esgk


