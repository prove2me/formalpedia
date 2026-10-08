-- Prove2me | Definitions.Def_Disjunctive_SequentialConvex_Basic_v2
-- name    : Disjunctive_SequentialConvex_Basic_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T22:00:21.67246+00:00
-- url     : https://prove2.me/theorems/b1f98034-67de-4050-9f7a-04cdb6ff4ff1
-- title:
--   Sequential convexification basics (v2: reversed disjunction as a conjunction)
-- statement:
--   Same vocabulary as `Disjunctive_SequentialConvex_Basic` ($F_0$, halfspaces, the conjunctive-normal-form constraint set $F$, faciality, $D_j := \bigcup_{i\in Q_j}\{x : d_i x \ge d_{i0}\}$), with one correction: $\bar D_j := \{x : d_i x \le d_{i0},\ i \in Q_j\} = \bigcap_{i \in Q_j}\{x : d_i x \le d_{i0}\}$, the polyhedron obtained by reversing every inequality of $D_j$; it is the closure of $\mathbb{R}^n \setminus D_j$, so its relative boundary is where segments from outside $D_j$ enter $D_j$.
--
--   **Formalization Note.** Version 1 took the union of the reversed halfspaces, which made Theorem 3.3 false (terms $x\ge 0$, $x \ge 1$: the union is $(-\infty,1]$, whereas the boundary relevant to $D_j = [0,\infty)$ is $\{0\}$). All other declarations are unchanged and keep their names.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, §3.1–3.2, pp. 42–46 (D̄_j right before Theorem 3.3); Balas, Tama, Tind, Math. Programming 44 (1989)

import Mathlib

namespace Disjunctive.SequentialConvex

/-- The polyhedron `{x : A x ≥ b}` (restated locally, as in earlier chunks of the series). -/
def Poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, b i ≤ (A.mulVec x) i}

/-- `F₀ := {x ∈ ℝⁿ : Ax ≥ b, x ≥ 0}` (Balas §3.1, p. 42). -/
def F0Set {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, b i ≤ (A.mulVec x) i) ∧ 0 ≤ x}

/-- The halfspaces `{x : dx ≤ d₀}` and `{x : dx ≥ d₀}` (Balas §3.1-3.2, used throughout). -/
def HalfspaceLE {n : ℕ} (d : Fin n → ℝ) (d0 : ℝ) : Set (Fin n → ℝ) := {x | dotProduct d x ≤ d0}

def HalfspaceGE {n : ℕ} (d : Fin n → ℝ) (d0 : ℝ) : Set (Fin n → ℝ) := {x | d0 ≤ dotProduct d x}

/-- The constraint set `F` of a disjunctive program `DP` in conjunctive normal form (Balas §3,
eq. (3.1), p. 42): `F₀` together with, for every `j ∈ S`, a disjunction `⋁_{i ∈ Q_j} (d_i x ≥
d_{i0})`. -/
def DisjunctiveConstraintSet {n : ℕ} {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {S : Type*} [Fintype S] (Qidx : S → Type*) [∀ j, Fintype (Qidx j)]
    (d : (j : S) → Qidx j → Fin n → ℝ) (d0 : (j : S) → Qidx j → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ F0Set A b ∧ ∀ j : S, ∃ i : Qidx j, d0 j i ≤ dotProduct (d j i) x}

/-- `DP` is facial (Balas §3.1, p. 42): every inequality `d_i x ≥ d_{i0}` appearing in a
disjunction of `(3.1)` defines a face of `F₀`. -/
def Facial {n : ℕ} {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {S : Type*}
    [Fintype S] (Qidx : S → Type*) [∀ j, Fintype (Qidx j)] (d : (j : S) → Qidx j → Fin n → ℝ)
    (d0 : (j : S) → Qidx j → ℝ) : Prop :=
  ∀ j : S, ∀ i : Qidx j, IsExtreme ℝ (F0Set A b) (F0Set A b ∩ HalfspaceGE (d j i) (d0 j i))

/-- `D_j := ⋁_{i ∈ Q_j} (d_i x ≥ d_{i0})` (Balas §3.2, p. 46, right before eq. (3.5)). -/
def Dj {n : ℕ} {Qj : Type*} [Fintype Qj] (d : Qj → Fin n → ℝ) (d0 : Qj → ℝ) : Set (Fin n → ℝ) :=
  ⋃ i : Qj, HalfspaceGE (d i) (d0 i)

/-- `D̄_j`, the "reverse" of the disjunction `D_j` (Balas §3.2, p. 46, right before Theorem 3.3):
the closed convex polyhedron `{x : d_i x ≤ d_{i0}, i ∈ Q_j}` obtained by reversing every
inequality of `D_j`. It is the closure of the complement of `D_j` (`x ∉ D_j` iff `d_i x < d_{i0}`
for all `i`), so its (relative) boundary is exactly where a segment leaving `ℝⁿ \ D_j` enters
`D_j`; this is the convex set `C_j` of the reverse-convex reading `x ∉ int C_j` of the
disjunction (Balas, Tama and Tind 1989).

Version 2: the earlier version took the *union* `⋃_i {x : d_i x ≤ d_{i0}}`, whose boundary need
not contain the boundary of `D_j`, which made Theorem 3.3 false (two terms `x ≥ 0 ∨ x ≥ 1` in
`ℝ`: the union is `(-∞,1]`, while the boundary crossed by segments into `D_j = [0,∞)` is `{0}`).
The reversed system is the *conjunction* of the reversed inequalities. -/
def Dbarj {n : ℕ} {Qj : Type*} [Fintype Qj] (d : Qj → Fin n → ℝ) (d0 : Qj → ℝ) :
    Set (Fin n → ℝ) :=
  ⋂ i : Qj, HalfspaceLE (d i) (d0 i)

end Disjunctive.SequentialConvex


