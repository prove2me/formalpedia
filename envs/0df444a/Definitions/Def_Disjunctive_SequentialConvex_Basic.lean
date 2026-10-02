-- Prove2me | Definitions.Def_Disjunctive_SequentialConvex_Basic
-- name    : Disjunctive_SequentialConvex_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:24:01.02562+00:00
-- url     : https://prove2.me/theorems/500e084c-3146-4570-8dc6-fdf5529039a4
-- title:
--   The constraint set of a disjunctive program in CNF, and faciality
-- statement:
--   This definition fixes the vocabulary of Chapter 3: the base polyhedron $F_0$, the constraint
--   set $F$ of a disjunctive program in conjunctive normal form, faciality, and the per-disjunction
--   sets $D_j$, $\bar D_j$ used by the necessity result (Theorem 3.3).
--
--   Let $F_0 := \{x \in \mathbb{R}^n : Ax \ge b,\ x \ge 0\}$. Given a finite set $S$ and, for each
--   $j \in S$, a finite set $Q_j$ with halfspace data $(d_i, d_{i0})_{i \in Q_j}$, the disjunctive
--   program's constraint set is
--
--   $$
--   F := \Big\{x \in F_0 : \forall j \in S,\ \exists\, i \in Q_j,\ d_i x \ge d_{i0}\Big\},
--   $$
--
--   i.e. $F_0$ together with one disjunction $\bigvee_{i \in Q_j}(d_i x \ge d_{i0})$ per $j \in S$.
--   The program (and $F$) is **facial** if every inequality $d_i x \ge d_{i0}$ appearing in some
--   disjunction *defines a face of $F_0$*: $F_0 \cap \{x : d_i x \ge d_{i0}\}$ is an extreme
--   subset of $F_0$, for every $i \in Q_j$, $j \in S$. For a single disjunction with data
--   $(d_i,d_{i0})_{i \in Q_j}$, write $D_j := \bigvee_{i \in Q_j}(d_i x \ge d_{i0})$ and, with the
--   inequality directions reversed, $\bar D_j := \bigvee_{i \in Q_j}(d_i x \le d_{i0})$.
--
--   **Formalization Note.** Faciality is stated via Mathlib's `IsExtreme` (the same "face of a
--   convex set" notion used throughout this series for extreme points/rays), matching the book's
--   own primary definition rather than its immediate corollary restatement ("$DP$ is facial iff
--   $F_0 \subseteq \{d_i x \le d_{i0}\}$"), per the convention of using the source's exact
--   definition rather than an equivalent paraphrase.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 42, 46, Section 3.1-3.2

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

/-- `D̄_j := ⋁_{i ∈ Q_j} (d_i x ≤ d_{i0})` (Balas §3.2, p. 46, right before Theorem 3.3). -/
def Dbarj {n : ℕ} {Qj : Type*} [Fintype Qj] (d : Qj → Fin n → ℝ) (d0 : Qj → ℝ) :
    Set (Fin n → ℝ) :=
  ⋃ i : Qj, HalfspaceLE (d i) (d0 i)

end Disjunctive.SequentialConvex


