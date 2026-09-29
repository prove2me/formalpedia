-- Prove2me | Definitions.Def_SchoenfliesCurveCore
-- name    : SchoenfliesCurveCore
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-09-25T07:55:54.89335+00:00
-- url     : https://prove2.me/theorems/0e19b26b-7f0a-45a7-802d-1b1ddeeca843
-- title:
--   Simple arcs and Jordan curves as parametrized planar sets
-- statement:
--   Define an arc as the image of an injective continuous map from $[0,1]$ to the plane; record its optional endpoints. Define a Jordan curve as the image of a continuous loop that is injective before its final return to the initial point. These predicates are the input interface of the constructive Jordan proof.
-- source:
--   https://github.com/alonamaloh/schoenflies-lean/blob/05a43d29cde026618777db3d4e4316204ccca237/Schoenflies/Curve.lean#L42-L58

/-
Derived from Schoenflies/Curve.lean by Álvaro Begué, Apache 2.0.
Source commit 05a43d29cde026618777db3d4e4316204ccca237.
-/
import Definitions.Def_SchoenfliesPlaneCore
import Mathlib.Topology.UnitInterval

open Set unitInterval

namespace Schoenflies

/-- A simple arc: the image of a continuous injective parametrization on `[0,1]`. -/
def IsArc (A : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, ContinuousOn f I ∧ InjOn f I ∧ f '' I = A

/-- An arc with specified endpoints. -/
def IsArcBetween (A : Set Plane) (p q : Plane) : Prop :=
  ∃ f : ℝ → Plane,
    ContinuousOn f I ∧ InjOn f I ∧ f '' I = A ∧ f 0 = p ∧ f 1 = q

/-- A parametrization of a simple closed curve. -/
structure IsLoop (f : ℝ → Plane) : Prop where
  continuousOn : ContinuousOn f I
  closes : f 0 = f 1
  injOn : InjOn f (Ico 0 1)

/-- A Jordan curve is the image of a loop. -/
def IsJordanCurve (C : Set Plane) : Prop :=
  ∃ f : ℝ → Plane, IsLoop f ∧ f '' I = C

end Schoenflies


