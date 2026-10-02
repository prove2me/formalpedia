-- Prove2me | Definitions.Def_Disjunctive_ConvexHull_Polyhedra
-- name    : Disjunctive_ConvexHull_Polyhedra
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:09:20.905986+00:00
-- url     : https://prove2.me/theorems/ad6ec232-f73b-4750-ba04-4a571a97371b
-- title:
--   Disjunctive sets, feasible/maximal indices, and recession cones
-- statement:
--   This definition fixes the vocabulary of Chapter 2: a disjunctive set, its feasible and
--   maximal index sets, and the recession cone of a polyhedron.
--
--   Given a finite index set $Q$ and, for $h \in Q$, a matrix $A_h$ and vector $b_h$, let
--   $P_h := \{x \in \mathbb{R}^n : A_h x \ge b_h\}$. The **disjunctive set** is
--   $F := \bigcup_{h \in Q} P_h$. Write $Q^* := \{h \in Q : P_h \ne \emptyset\}$ for the
--   **feasible indices**, and
--
--   $$
--   Q^{**} := \{h \in Q^* : P_h \not\subseteq P_j \text{ for every } j \in Q^* \setminus \{h\}\}
--   $$
--
--   for the **maximal indices** — the feasible disjuncts not redundant against any other feasible
--   disjunct. The **recession cone** of $P_h$ is $C_h := \{y \in \mathbb{R}^n : A_h y \ge 0\}$: if
--   $P_h \ne \emptyset$, this is exactly the set of directions along which one can move
--   indefinitely from any point of $P_h$ while staying in $P_h$. Finally, for a subset
--   $M \subseteq Q$ and sets $S_h$ ($h \in M$), the **Minkowski sum**
--   $\sum_{h \in M} S_h := \{x : x = \sum_{h \in M} y^h \text{ for some } y^h \in S_h\}$.
--
--   These objects recur throughout the chapter: $F$ and $Q^*$ in Theorem 2.1's lifted
--   representation of $\mathrm{cl\,conv}(F)$; $Q^{**}$ and the recession cones in Theorems 2.3 and
--   2.4, which characterize exactly when the lifted representation is tight and when it recovers
--   $F$ itself rather than merely its closed convex hull.
--
--   **Formalization Note.** `m : Q → ℕ` lets each disjunct's constraint matrix have its own row
--   count, since the book never assumes a common row count across disjuncts.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 18, 21-23, Section 2.1

import Mathlib

namespace Disjunctive.ConvexHull

/-- The polyhedron `{x : A x ≥ b}` given by a system `A x ≥ b` (Balas §2.1: each
`P_h := {x ∈ ℝⁿ : A_h x ≥ b_h}`). -/
def Poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, b i ≤ (A.mulVec x) i}

/-- The disjunctive set `F := ⋃_{h ∈ Q} P_h` (Balas §2.1, p. 18, right before Theorem 2.1). -/
def DisjunctiveSet {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) : Set (Fin n → ℝ) :=
  ⋃ h : Q, Poly (A h) (b h)

/-- `Q* := {h ∈ Q : P_h ≠ ∅}` (Balas §2.1, p. 18). -/
def FeasibleIndices {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) : Set Q :=
  {h | (Poly (A h) (b h)).Nonempty}

/-- `Q** := {h ∈ Q* : P_h ⊄ P_j, ∀ j ∈ Q*\{h}}` (Balas §2.1.2, p. 23, Theorem 2.4): the
feasible disjuncts maximal for inclusion. Read as maximality in the inclusion *preorder* (no
feasible `P_j` strictly contains `P_h`) rather than as `∀ j ≠ h, ¬(P_h ⊆ P_j)`: the latter
empties `Q**` of both copies whenever two feasible disjuncts coincide, and Theorem 2.4 is then
false (`P_1 = P_2 = [0,1]`, `P_3 = [5,∞)` gives `Q** = {3}` and recovers `[0,∞)`). -/
def MaximalIndices {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) : Set Q :=
  {h | h ∈ FeasibleIndices m A b ∧
        ∀ j ∈ FeasibleIndices m A b, Poly (A h) (b h) ⊆ Poly (A j) (b j) →
          Poly (A j) (b j) ⊆ Poly (A h) (b h)}

/-- The recession cone `C_h := {y ∈ ℝⁿ : A_h y ≥ 0}` of `P_h` (Balas §2.1, p. 21). -/
def RecessionCone {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {y | 0 ≤ A.mulVec y}

/-- The finite Minkowski sum `Σ_{h ∈ M} S_h := {x : x = Σ_{h∈M} y^h, y^h ∈ S_h}` (Balas §2.1,
p. 22, right before Theorem 2.3), for a subset `M` of a finite index set `Q`. -/
def MinkowskiSumOver {n : ℕ} {Q : Type*} [Fintype Q] (M : Set Q) (S : Q → Set (Fin n → ℝ)) :
    Set (Fin n → ℝ) :=
  {x | ∃ y : Q → Fin n → ℝ, x = ∑ h, y h ∧ (∀ h ∈ M, y h ∈ S h) ∧ ∀ h, h ∉ M → y h = 0}

end Disjunctive.ConvexHull


