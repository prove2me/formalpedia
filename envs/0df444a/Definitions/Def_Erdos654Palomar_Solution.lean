-- Prove2me | Definitions.Def_Erdos654Palomar_Solution
-- name    : Erdos654Palomar_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:33:21.104819+00:00
-- url     : https://prove2.me/theorems/882d97ff-c1c8-44c5-aa77-c72177ca12a3
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Daniel Veljjanoski (veljjanoski/erdos654-palomar; definitions and statements reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 654: distinct distances from a point with no four concyclic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/veljjanoski/erdos654-palomar/blob/fd7a8dc3cf52f6dcadcf5c6bcd05a2dc387dc64f/Solution.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
open scoped EuclideanGeometry Finset
namespace EuclideanGeometry
def NoFourConcyclic (X : Set ℝ²) : Prop :=
  ∀ T ⊆ X, T.ncard = 4 → ¬Cospherical T
end EuclideanGeometry
section
variable {X : Type*} [MetricSpace X]
open Classical in
/-- Given a finite set of points in a metric space, we define the number of distinct distances
between a given point and all other points. -/
noncomputable def distinctDistancesFrom (points : Finset X) (pt : X) : ℕ :=
  #((points.erase pt).image fun x => dist x pt)
end
open Filter Finset EuclideanGeometry
namespace Erdos654Proof
def XAxis : Set ℝ² := {P | P 1 = 0 ∧ ∃ a : ℤ, P 0 = 2 * a}
def YAxis : Set ℝ² := {P | P 0 = 0 ∧ ∃ b : ℤ, P 1 = 2 * b + 1}
def xh (p : Bool × ℕ) : ℤ := if p.1 then p.2 + 1 else -((p.2 : ℤ) + 1)
def yh (p : Bool × ℕ) : ℤ := if p.1 then p.2 else -(p.2 : ℤ) - 1
noncomputable def xpt (p : Bool × ℕ) : ℝ² := !₂[2 * (xh p : ℝ), 0]
noncomputable def ypt (p : Bool × ℕ) : ℝ² := !₂[0, 2 * (yh p : ℝ) + 1]
def idx (m : ℕ) : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.range m
noncomputable def XS (m : ℕ) : Finset ℝ² := (idx m).image xpt
noncomputable def YS (m : ℕ) : Finset ℝ² := (idx m).image ypt
noncomputable def A (m : ℕ) : Finset ℝ² := XS m ∪ YS m
end Erdos654Proof
namespace Erdos654
end Erdos654


