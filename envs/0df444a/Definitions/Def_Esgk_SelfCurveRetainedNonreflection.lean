-- Prove2me | Definitions.Def_Esgk_SelfCurveRetainedNonreflection
-- name    : Esgk_SelfCurveRetainedNonreflection
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:03:07.291863+00:00
-- url     : https://prove2.me/theorems/7b2586fa-75f3-4ad5-9bcf-aa0bed75c721
-- title:
--   The chosen irreducible polynomial of a supporting curve
-- statement:
--   This packages the polynomial chosen for the second curve in prepared incidence data together with its proof of irreducibility.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_AuxiliaryIncidenceDeletion
import Definitions.Def_Esgk_IrreduciblePlaneAffineIsometryTransport
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_Esgk_PlaneHorizontalReflection
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Bezout
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 as described in the repository LICENSE.
-/


namespace Esgk

open EuclideanGeometry
open PachDeZeeuw (PreparedBipartiteInput Point4)
open PachDeZeeuw.Algebraic (PlaneCurveZeroSet SingularPointSet)

noncomputable def preparedSecondCurveIrreducible
    {d : ℕ} (X : PreparedBipartiteInput d) : IrreduciblePlanePolynomial ℝ :=
  { polynomial := preparedSecondCurvePolynomial X
    irreducible := preparedSecondCurvePolynomial_irreducible X }


end Esgk


