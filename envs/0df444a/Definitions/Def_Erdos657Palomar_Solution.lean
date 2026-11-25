-- Prove2me | Definitions.Def_Erdos657Palomar_Solution
-- name    : Erdos657Palomar_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:18:53.071722+00:00
-- url     : https://prove2.me/theorems/67adf6e8-1af1-5b00-93f3-b2cef9d04e24
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from veljjanoski (veljjanoski/erdos657-palomar; statement and definitions reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 657: Straus's observation on isosceles-free point sets with few distances development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/veljjanoski/erdos657-palomar/blob/e44e1eb1d4a525f66a7a297235c956a29f56a535/Solution.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)
open scoped Finset
section
variable {X : Type*} [MetricSpace X]
noncomputable def distanceSet (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2
noncomputable def distinctDistances (points : Finset X) : ℕ :=
  #(distanceSet points)
end
namespace Set
variable {α : Type*}
protected def Triplewise (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z
end Set
def IsIsosceles {α : Type*} [Dist α] (p q r : α) : Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q
def Set.IsIsoscelesFree {α : Type*} [Dist α] (A : Set α) : Prop :=
  A.Triplewise fun x y z ↦ ¬ _root_.IsIsosceles x y z
open Filter
open scoped EuclideanGeometry
namespace Erdos657Proof
open Finset
noncomputable def w (i : ℕ) : ℝ := Real.sqrt (2 ^ i)
noncomputable def pt {k : ℕ} (S : Finset (Fin k)) : ℝ^k :=
  WithLp.toLp 2 fun i ↦ if i ∈ S then w i else 0
noncomputable def g {k : ℕ} (U : Finset (Fin k)) : ℝ := ∑ i ∈ U, (2 : ℝ) ^ (i : ℕ)
end Erdos657Proof
namespace Erdos657
end Erdos657


