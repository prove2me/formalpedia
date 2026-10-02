-- Prove2me | Definitions.Def_Disjunctive_IntroDuality_PolyhedralSystems
-- name    : Disjunctive_IntroDuality_PolyhedralSystems
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:01:42.611749+00:00
-- url     : https://prove2.me/theorems/c8ae92ac-5bcf-4a4b-869b-68ba84c1e154
-- title:
--   The polyhedral systems $P_h$, $X_h$, $U_h$ of a disjunctive program
-- statement:
--   This definition fixes the polyhedral systems that every result of Chapter 1 builds on.
--
--   Given an $m \times n$ real matrix $A$ and a vector $b \in \mathbb{R}^m$, write $A_i$ for the
--   $i$-th row of $A$. Three systems recur throughout:
--
--   $$
--   \mathrm{Poly}(A,b) := \{x \in \mathbb{R}^n : A_i x \ge b_i, \ i = 1,\dots,m\},
--   $$
--
--   the plain polyhedron $\{x : Ax \ge b\}$ used to build a disjunctive set $F = \bigcup_{h \in Q} P_h$
--   with $P_h = \mathrm{Poly}(A_h, b_h)$ (Balas §1.4);
--
--   $$
--   \mathrm{PolyNonneg}(A,b) := \{x \in \mathbb{R}^n : Ax \ge b,\ x \ge 0\},
--   $$
--
--   the primal system $X_h$ of the disjunctive program $(DP)$ (Balas §1.5); and, for a vector
--   $c \in \mathbb{R}^n$,
--
--   $$
--   \mathrm{DualPoly}(A,c) := \{u \in \mathbb{R}^m : uA \le c,\ u \ge 0\},
--   $$
--
--   the dual system $U_h$ of $(DD)$. Here $uA$ denotes the row-vector-times-matrix product
--   (`Matrix.vecMul`), so $(uA)_j = \sum_i u_i A_{ij}$.
--
--   **Formalization Note.** All three definitions are stated for a generic matrix shape
--   `Matrix (Fin m) (Fin n) ℝ`; the disjunctive-program setting instantiates them once per
--   disjunct $h \in Q$, with $m$ allowed to depend on $h$ (Balas never assumes a common row count
--   across the disjuncts).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 13, Section 1.5 (and p. 9, eq. (1.3))

import Mathlib

namespace Disjunctive.IntroDuality

/-- The polyhedron `{x : A x ≥ b}` given by a system `A x ≥ b` (Balas, *Disjunctive
Programming*, §1.4 eq. (1.3): each `P_h := {x ∈ ℝⁿ : A_h x ≥ b_h}`). -/
def Poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, b i ≤ (A.mulVec x) i}

/-- The nonnegative-orthant polyhedron `{x : A x ≥ b, x ≥ 0}` (Balas §1.5, the primal system
`X_h := {x | A_h x ≥ b_h, x ≥ 0}` of the disjunctive program `(DP)`). -/
def PolyNonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, b i ≤ (A.mulVec x) i) ∧ 0 ≤ x}

/-- The dual system `{u ≥ 0 : u A ≤ c}` (Balas §1.5, `U_h := {u_h | u_h A_h ≤ c, u_h ≥ 0}` of
the dual disjunctive program `(DD)`). -/
def DualPoly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) : Set (Fin m → ℝ) :=
  {u | (∀ j, Matrix.vecMul u A j ≤ c j) ∧ 0 ≤ u}

end Disjunctive.IntroDuality


