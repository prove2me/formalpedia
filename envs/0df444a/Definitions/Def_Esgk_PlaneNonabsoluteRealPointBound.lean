-- Prove2me | Definitions.Def_Esgk_PlaneNonabsoluteRealPointBound
-- name    : Esgk_PlaneNonabsoluteRealPointBound
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:45:39.001111+00:00
-- url     : https://prove2.me/theorems/6be6803c-35eb-4bb0-bf63-8928532fc906
-- title:
--   Absolute irreducibility and a real-point bound
-- statement:
--   This defines absolute irreducibility of a real plane polynomial by irreducibility after extending coefficients to the complex numbers. It also defines the proposition asserting that a finite real sample on an irreducible polynomial that is not absolutely irreducible has at most one quarter of the squared degree.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open PachDeZeeuw.Algebraic


def IsAbsolutelyIrreducible (G : PlanePoly) : Prop :=
  Irreducible (MvPolynomial.map Complex.ofRealHom G)


def RealIrreducibleNotAbsolutelyIrreduciblePointBoundStatement : Prop :=
  ∀ (G : PlanePoly) (S : Finset Point2),
    Irreducible G →
      ¬ IsAbsolutelyIrreducible G →
        (S : Set Point2) ⊆ PlaneCurveZeroSet G →
          4 * S.card ≤ G.totalDegree ^ 2


end Esgk


