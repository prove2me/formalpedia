-- Prove2me | Definitions.Def_Esgk_PlaneIsometryFixedPointBisector
-- name    : Esgk_PlaneIsometryFixedPointBisector
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:07:37.92418+00:00
-- url     : https://prove2.me/theorems/8f0b5d2e-c6f1-480b-85da-1ed74c4d1287
-- title:
--   Coordinates for a perpendicular bisector
-- statement:
--   For two planar points, this defines their midpoint and a vector perpendicular to their difference. These give the base point and direction used to describe their perpendicular bisector.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_SelfCurveReversingSymmetryFamily
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry PachDeZeeuw


noncomputable def perpendicularBisectorBase (x z : Point2) : Point2 :=
  !₂[(x 0 + z 0) / 2, (x 1 + z 1) / 2]

 
def perpendicularBisectorDirection (x z : Point2) : Point2 :=
  !₂[-(z 1 - x 1), z 0 - x 0]


end Esgk


