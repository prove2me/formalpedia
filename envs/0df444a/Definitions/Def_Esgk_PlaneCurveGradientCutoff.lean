-- Prove2me | Definitions.Def_Esgk_PlaneCurveGradientCutoff
-- name    : Esgk_PlaneCurveGradientCutoff
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:48:43.259532+00:00
-- url     : https://prove2.me/theorems/c25acab6-399e-40d4-8dd2-6ebc2bde4779
-- title:
--   A gradient cutoff on a plane curve
-- statement:
--   This defines the gradient-square polynomial $G_X^2+G_Y^2$, its difference from a level $\varepsilon$, and the points of $G=0$ where that level is attained.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneInfiniteVanishing
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic

 
def planeGradientSquare (G : PlanePoly) : PlanePoly :=
  (pderiv (0 : Fin 2) G) ^ 2 + (pderiv (1 : Fin 2) G) ^ 2

 
def planeGradientCutoff (G : PlanePoly) (ε : ℝ) : PlanePoly :=
  planeGradientSquare G - C ε

 
def planeGradientCutoffZeroSet (G : PlanePoly) (ε : ℝ) : Set Point2 :=
  PlaneCurveZeroSet G ∩ PlaneCurveZeroSet (planeGradientCutoff G ε)


end Esgk


