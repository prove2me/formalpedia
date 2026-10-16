-- Prove2me | Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveSymmetries
-- name    : LeanFormalizations_PachDeZeeuw_CurveSymmetries
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:44:36.419819+00:00
-- url     : https://prove2.me/theorems/50a83e49-0596-4406-b221-f82ae2c82299
-- title:
--   The finite symmetry bound for irreducible plane curves
-- statement:
--   This defines real irreducible plane curves and the line-or-circle predicate. It then defines the proposition asserting that any finite family of isometries preserving an irreducible degree-at-most-$d$ curve that is neither a line nor a circle has at most $4d$ members.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

namespace CurveSymmetries

open scoped Classical

 
abbrev Point2 := EuclideanSpace ℝ (Fin 2)


def PlaneCurveZeroSet (p : MvPolynomial (Fin 2) ℝ) : Set Point2 :=
  {x | MvPolynomial.eval (fun i => x i) p = 0}


def IsIrreducibleCurve (d : ℕ) (C : Set Point2) : Prop :=
  ∃ f : MvPolynomial (Fin 2) ℝ, f ≠ 0 ∧ f.totalDegree ≤ d ∧ Irreducible f ∧
    C = PlaneCurveZeroSet f

 
def IsLineOrCircle (C : Set Point2) : Prop :=
  (∃ a b c : ℝ, (a, b) ≠ (0, 0) ∧ C = {p : Point2 | a * p 0 + b * p 1 = c}) ∨
  (∃ center : Point2, ∃ r : ℝ, C = Metric.sphere center r)


def Lemma25Statement : Prop :=
  ∀ (d : ℕ) (C : Set Point2),
    IsIrreducibleCurve d C →
    ¬ IsLineOrCircle C →
    ∀ symmetries : Finset (Point2 ≃ᵢ Point2),
      (∀ g ∈ symmetries, g '' C = C) →
        symmetries.card ≤ 4 * d


end CurveSymmetries


