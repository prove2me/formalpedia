-- Prove2me | Definitions.Def_SchoenfliesPlaneCore
-- name    : SchoenfliesPlaneCore
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-09-25T07:54:53.134707+00:00
-- url     : https://prove2.me/theorems/516c4124-0811-452d-bc54-1a2aa474eaf2
-- title:
--   Euclidean plane and orientation data for the Schoenflies proof
-- statement:
--   Identify the plane with $\mathbb R^2$, and define its coordinate pair constructor, oriented determinant, and quarter-turn map. These elementary operations form the geometric interface for a formal proof of arc non-separation and the Jordan curve theorem.
-- source:
--   https://github.com/alonamaloh/schoenflies-lean/blob/05a43d29cde026618777db3d4e4316204ccca237/Schoenflies/Plane.lean#L34-L55

/-
Derived from Schoenflies/Plane.lean by Álvaro Begué, Apache 2.0.
Source commit 05a43d29cde026618777db3d4e4316204ccca237.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Schoenflies

/-- The Euclidean plane used throughout the source proof. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

namespace Plane

/-- A point of the plane from its two coordinates. -/
abbrev mk (x y : ℝ) : Plane := !₂[x, y]

@[simp] theorem mk_zero (x y : ℝ) : mk x y 0 = x := rfl
@[simp] theorem mk_one (x y : ℝ) : mk x y 1 = y := rfl

/-- Oriented area form on the plane. -/
def det (a b : Plane) : ℝ := a 0 * b 1 - a 1 * b 0

/-- Counterclockwise rotation through a right angle. -/
def perp (u : Plane) : Plane := mk (-u 1) (u 0)

@[simp] theorem perp_zero (u : Plane) : perp u 0 = -u 1 := rfl
@[simp] theorem perp_one (u : Plane) : perp u 1 = u 0 := rfl

end Plane
end Schoenflies


