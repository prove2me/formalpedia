-- Prove2me | Definitions.Def_Disjunctive_CutCorrespondence_Basic
-- name    : Disjunctive_CutCorrespondence_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:44:03.965388+00:00
-- url     : https://prove2.me/theorems/5dca60a2-0419-43a3-972b-e1cd396e9447
-- title:
--   K, K0, and the split-convexification closure
-- statement:
--   This definition restates the LP relaxation, its 0-1 feasible set, and the one-variable
--   convexification closure used throughout the series, needed here to state Theorem 8.7's rank bound
--   for family (a).
--
--   `Poly A b` is the LP relaxation `{x : Ax≥b}`. `ZeroOneSet j` is `{x : x_j∈{0,1}}`.
--   `SplitConvexify S j := conv(S ∩ {x_j∈{0,1}})` is one round of unstrengthened lift-and-project
--   convexification — by Theorem 7.1, exactly the closure of `S` under *every* valid lift-and-project
--   cut from the disjunction on `j`. `K0Set A b N'` is `K_0 := K ∩ {x_j∈{0,1}, j∈N'}`.
--
--   **Formalization Note.** Restated locally per the series convention that a draft mission cannot
--   import another draft mission's definitions.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 91 (restated for Chapter 8)

import Mathlib

namespace Disjunctive.CutCorrespondence

/-- The polyhedron `{x : A x ≥ b}` (restated locally, as in earlier chunks of the series). -/
def Poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, b i ≤ (A.mulVec x) i}

/-- `{x : x_j ∈ {0,1}}` (restated locally). -/
def ZeroOneSet {n : ℕ} (j : Fin n) : Set (Fin n → ℝ) := {x | x j = 0 ∨ x j = 1}

/-- One step of sequential convexification, `conv(S ∩ {x_j ∈ {0,1}})` (restated locally; this is
the unstrengthened lift-and-project cut closure for disjunction `j`, by Theorem 7.1). -/
def SplitConvexify {n : ℕ} (S : Set (Fin n → ℝ)) (j : Fin n) : Set (Fin n → ℝ) :=
  convexHull ℝ (S ∩ ZeroOneSet j)

/-- `IteratedSplit K l := SplitConvexify` folded left to right over `l` (restated locally). -/
def IteratedSplit {n : ℕ} (K : Set (Fin n → ℝ)) (l : List (Fin n)) : Set (Fin n → ℝ) :=
  l.foldl SplitConvexify K

/-- `K₀ := K ∩ {x_j ∈ {0,1}, j ∈ N'}` (restated locally). -/
def K0Set {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (Nprime : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  Poly A b ∩ ⋂ j ∈ Nprime, ZeroOneSet j

end Disjunctive.CutCorrespondence


