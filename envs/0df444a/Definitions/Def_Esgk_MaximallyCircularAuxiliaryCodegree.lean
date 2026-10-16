-- Prove2me | Definitions.Def_Esgk_MaximallyCircularAuxiliaryCodegree
-- name    : Esgk_MaximallyCircularAuxiliaryCodegree
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:57:56.109147+00:00
-- url     : https://prove2.me/theorems/df6b2a9e-2fe7-4e36-9c0d-02f41cd2a9ec
-- title:
--   Auxiliary point-pair and curve-pair incidence
-- statement:
--   This defines the auxiliary incidence relation between a pair of points and a pair of curve labels in a prepared bipartite configuration.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_AuxiliaryIncidenceDeletion
import Definitions.Def_Esgk_FiniteIncidenceCodegreeBound
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

open scoped Classical

namespace Esgk

open PachDeZeeuw (PreparedBipartiteInput auxCurve)
open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)
open IrreduciblePlanePolynomial

 
def auxPointPairCurveIncidence {d : ℕ} (X : PreparedBipartiteInput d)
    (pq : X.P₂ × X.P₂) (ij : X.P₁ × X.P₁) : Prop :=
  encodedAuxPoint
      ((pq.1 : PachDeZeeuw.Algebraic.Point2),
        (pq.2 : PachDeZeeuw.Algebraic.Point2)) ∈ auxCurve X ij.1 ij.2


end Esgk


