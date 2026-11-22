-- Prove2me | Definitions.Def_LeanPool_ParallelPostulate_Geometry
-- name    : LeanPool_ParallelPostulate_Geometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:04:01.909951+00:00
-- url     : https://prove2.me/theorems/dd95c6dd-527b-4237-9b0b-7aa1df3f8e79
-- title:
--   Geometry
-- statement:
--   Definitions and structural lemmas for Geometry, from Richard Sutton; LeanPool contributors's pinned Independence of the parallel postulate development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean

module
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace ParallelPostulate
namespace Pairs
section Ring
variable {K : Type*} [CommRing K]
structure Dim (K : Type*) where
  /-- The point where the dimension has its zero. -/
  zero : K × K
  /-- The point where the dimension has its 1. -/
  one : K × K
@[expose] def cross (u v : K × K) : K := u.1 * v.2 - u.2 * v.1
namespace Dim
@[expose] def dir (L : Dim K) : K × K := (L.one.1 - L.zero.1, L.one.2 - L.zero.2)
@[expose] def pt (L : Dim K) (t : K) : K × K :=
  (L.zero.1 + t * (L.one.1 - L.zero.1), L.zero.2 + t * (L.one.2 - L.zero.2))
@[expose] def side (L : Dim K) (P : K × K) : K := cross L.dir (P.1 - L.zero.1, P.2 - L.zero.2)
@[expose] def points (L : Dim K) : Set (K × K) := Set.range L.pt
@[expose] def rebase (M : Dim K) (P : K × K) : Dim K :=
  ⟨P, (P.1 + (M.one.1 - M.zero.1), P.2 + (M.one.2 - M.zero.2))⟩
end Dim
structure Figure (K : Type*) where
  /-- The straight line that falls on the two others. -/
  a : Dim K
  /-- The line that leaves `a` at `a0`. -/
  b : Dim K
  /-- The line that leaves `a` at `a1`. -/
  c : Dim K
  /-- The first constraint. -/
  a0_eq_b0 : a.zero = b.zero
  /-- The second constraint. -/
  a1_eq_c0 : a.one = c.zero
namespace Figure
@[expose] def reverse (F : Figure K) : Figure K where
  a := ⟨F.a.one, F.a.zero⟩
  b := F.c
  c := F.b
  a0_eq_b0 := F.a1_eq_c0
  a1_eq_c0 := F.a0_eq_b0
end Figure
end Ring
section Field
variable {K : Type*} [Field K]
end Field
end Pairs
end ParallelPostulate
namespace ParallelPostulate
namespace HyperbolicPlane
open Pairs
section Fractions
variable {K : Type*} [Field K]
end Fractions
section Planes
variable {K : Type*} [Field K]
@[expose] def IsLine (Pl S : Set (K × K)) : Prop :=
  ∃ M : Dim K, M.zero ≠ M.one ∧ S = M.points ∩ Pl ∧ S.Nonempty
@[expose] def Misses (Pl : Set (K × K)) (L : Dim K) (P : K × K) (S : Set (K × K)) : Prop :=
  IsLine Pl S ∧ P ∈ S ∧ S ∩ (L.points ∩ Pl) = ∅
@[expose] def euclid (Pl : Set (K × K)) (L : Dim K) (P : K × K) : Set (K × K) :=
  (L.rebase P).points ∩ Pl
@[expose] def toward (Pl : Set (K × K)) (L : Dim K) (P : K × K) (t : K) : Set (K × K) :=
  (Dim.mk P (L.pt t)).points ∩ Pl
@[expose] def OpenAlong (Pl : Set (K × K)) : Prop :=
  ∀ M : Dim K, M.zero ∈ Pl → ∃ t : K, t ≠ 0 ∧ M.pt t ∈ Pl
end Planes
section Identities
variable {K : Type*} [CommRing K]
end Identities
section Bound
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
@[expose] def plane (κ : K) : Set (K × K) := {p | 0 < 1 + κ * (p.1 ^ 2 + p.2 ^ 2)}
@[expose] def Between (A B C : K × K) : Prop :=
  A ≠ C ∧ ∃ u : K, 0 < u ∧ u < 1 ∧ (Dim.mk A C).pt u = B
end Bound
@[expose] def StrictBetween (a c b : ℝ) : Prop := (a < c ∧ c < b) ∨ (b < c ∧ c < a)
end HyperbolicPlane
end ParallelPostulate


