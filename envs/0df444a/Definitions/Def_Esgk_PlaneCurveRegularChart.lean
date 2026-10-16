-- Prove2me | Definitions.Def_Esgk_PlaneCurveRegularChart
-- name    : Esgk_PlaneCurveRegularChart
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:51:09.409326+00:00
-- url     : https://prove2.me/theorems/8addf972-f8f7-488a-8ee4-ae979872e653
-- title:
--   The regular locus of a real plane curve
-- statement:
--   This defines the regular locus of a real polynomial plane curve by removing its singular points from its real zero set.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneCurveRadialChart
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Bezout
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Filter Topology MvPolynomial
open PachDeZeeuw.Algebraic

namespace Esgk

 
def planeCurveRegularLocus (G : PlanePoly) : Set Point2 :=
  PlaneCurveZeroSet G \ SingularPointSet G


end Esgk


