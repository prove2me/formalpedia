-- Prove2me | Definitions.Def_Esgk_PlaneProjectiveModel
-- name    : Esgk_PlaneProjectiveModel
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:49:38.502198+00:00
-- url     : https://prove2.me/theorems/f866b576-dfd0-4f7f-8458-2c5401887baf
-- title:
--   A homogeneous model of an affine plane polynomial
-- statement:
--   This records a complex affine plane polynomial together with a homogeneous three-variable polynomial of the same degree whose restriction to the affine chart recovers it.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_ComplexPlaneProjectiveHomogenization
import Definitions.Def_Esgk_PlaneProjectiveAffineChart
import Definitions.Def_Esgk_PlaneProjectiveHomogenization
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


@[ext]
structure PlaneProjectiveModel where
  affinePolynomial : ComplexPlanePoly
  projectivePolynomial : ProjectivePlanePoly
  projectivePolynomial_isHomogeneous :
    projectivePolynomial.IsHomogeneous affinePolynomial.totalDegree
  projectivePlaneAffineChart_projectivePolynomial :
    projectivePlaneAffineChart projectivePolynomial = affinePolynomial

attribute [simp] PlaneProjectiveModel.projectivePlaneAffineChart_projectivePolynomial


attribute [simp]
  projectivePlaneAffineChart_complexPlaneHomogenization_totalDegree
  projectivePlaneAffineChart_planeHomogenization_totalDegree


end Esgk


