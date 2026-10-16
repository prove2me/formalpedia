-- Prove2me | Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
-- name    : LeanFormalizations_PachDeZeeuw_CurveInterface
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:44:36.758441+00:00
-- url     : https://prove2.me/theorems/1f80487c-2407-45c7-9261-0d72bc93f5fa
-- title:
--   Bounded-degree plane curves and elementary exceptional sets
-- statement:
--   This defines real plane curves given by nonzero polynomials of bounded total degree, the irreducible subclass, and the predicate that a set is a line or a circle.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

 
abbrev Point2 := EuclideanSpace ℝ (Fin 2)

notation "ℝ²" => Point2


namespace PlaneCurve


def IsBoundedDegreeCurve (d : ℕ) (C : Set Point2) : Prop :=
  ∃ f : MvPolynomial (Fin 2) ℝ, f ≠ 0 ∧ f.totalDegree ≤ d ∧
    C = {x : Point2 | MvPolynomial.eval (fun i => x i) f = 0}


def IsIrreducibleCurve (d : ℕ) (C : Set Point2) : Prop :=
  ∃ f : MvPolynomial (Fin 2) ℝ, f ≠ 0 ∧ f.totalDegree ≤ d ∧ Irreducible f ∧
    C = {x : Point2 | MvPolynomial.eval (fun i => x i) f = 0}


def IsLineOrCircle (C : Set Point2) : Prop :=
  (∃ a b c : ℝ, (a, b) ≠ (0, 0) ∧ C = {p : Point2 | a * p 0 + b * p 1 = c}) ∨
  (∃ center : Point2, ∃ r : ℝ, C = Metric.sphere center r)

end PlaneCurve


