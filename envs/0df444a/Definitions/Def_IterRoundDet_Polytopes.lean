-- Prove2me | Definitions.Def_IterRoundDet_Polytopes
-- name    : IterRoundDet_Polytopes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:25.067207+00:00
-- url     : https://prove2.me/theorems/e1414c7a-1b0a-45d2-9adc-223f87e44307
-- title:
--   The polytopes $P(\mathcal M)$, $P(\mathcal N)$, the region $\mathcal R$, tangent spaces, and proportional pairs
-- statement:
--   For a matroid $\mathcal M$ on $[n]$, $P(\mathcal M)=\operatorname{conv}\{\mathbf 1_B : B\in\mathcal B(\mathcal M)\}$ is its base polytope. For the coefficients $c$ of $p$, $P(\mathcal N)=\operatorname{conv}\{\mathbf 1_S : c_S>0\}$ is the base polytope of the support matroid. The feasible region is
--
--   $$\mathcal R=\{(a,x)\in P(\mathcal N)\times P(\mathcal M): a\le x\}.$$
--
--   The file also defines:
--
--   1. the tangent space at $y$ of the minimal face of a polytope containing $y$;
--   2. the fractional coordinates $A=\{i:0<x_i<1\}$;
--   3. the partition $A=A_1\sqcup\dots\sqcup A_q$ describing the tangent space of a matroid face (Lemma 2.6);
--   4. proportional pairs, $a_i/x_i=a_j/x_j>0$ for $i,j$ in one block, (21);
--   5. balanced directions, $v\in T_F$ with $v(A_j)=0$, (24), and the induced direction $w$ of (25).
--
--   These describe the moves of the rounding walk.
--
--   **Formalization Note** The tangent space of the minimal face $F$ of $y$ in $P$ equals $\{u : y\pm tu\in P \text{ for some } t>0\}$, because a face containing the midpoint of a segment of $P$ contains both ends. So faces need not be named. The partition is a predicate; it is unique when it exists.
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), §1.2, p.3; (13), p.12; Lemma 2.6, p.9; (20), (21), p.15; (24), (25), p.17; Lemma 3.5, p.14

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly

set_option autoImplicit false

namespace IterRoundDet

/-!
# The polytopes `P(M)`, `P(N)`, the region `R`, tangent spaces and proportional pairs

Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…): `P(M)` p.3; `R` and `P(N)`
p.12; the partition, Lemma 2.6, p.9; (20), (21), p.15; (24), (25), p.17.
-/

variable {n : ℕ}

/-- `P(M) = conv{1_B : B ∈ B(M)}`, p.3. -/
def basePolytope (M : Matroid (Fin n)) : Set (Fin n → ℝ) :=
  convexHull ℝ {y | ∃ B : Finset (Fin n), M.IsBase (B : Set (Fin n)) ∧ y = ind B}

/-- `P(N)`, the base polytope of the support matroid `N`, p.12: the convex hull of the `1_S` with
`c_S > 0`.

**Formalization Note.** `N` itself is not needed to define it; Lemma 3.1 item 1 shows that these sets
are the bases of a matroid. This is the Newton polytope of `p` (p.6). -/
def supportPolytope (c : Finset (Fin n) → ℝ) : Set (Fin n → ℝ) :=
  convexHull ℝ {y | ∃ S : Finset (Fin n), 0 < c S ∧ y = ind S}

/-- `(a, x) ∈ R = {(a, x) ∈ P(N) × P(M) : a ≤ x}`, p.12. -/
def Feasible (c : Finset (Fin n) → ℝ) (M : Matroid (Fin n)) (a x : Fin n → ℝ) : Prop :=
  a ∈ supportPolytope c ∧ x ∈ basePolytope M ∧ ∀ i, a i ≤ x i

/-- The tangent space at `y` of the minimal face of `P` containing `y`:
`T_F = {u : y ± t u ∈ F for some t > 0}`, p.14.

**Formalization Note.** For `y ∈ P` with minimal face `F`, this equals `{u : y ± t u ∈ P for some
t > 0}`, which is the form written here: a face of `P` containing the midpoint `y` of a segment in
`P` contains both ends. So `F` need not be named, and Lemma 2.6's "`x ∈ relint Q`" is the case where
`Q` is the minimal face of `x`. -/
def tangentAt (P : Set (Fin n → ℝ)) (y : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {u | ∃ t : ℝ, 0 < t ∧ y + t • u ∈ P ∧ y - t • u ∈ P}

/-- `A = {i : 0 < x_i < 1}`, the fractional coordinates, (20), p.15. -/
noncomputable def fractional (x : Fin n → ℝ) : Finset (Fin n) :=
  by classical exact Finset.univ.filter fun i => 0 < x i ∧ x i < 1

/-- The partition `A = A_1 ∪ ⋯ ∪ A_q` of Lemma 2.6, p.9, as a property of a partition `π`:
`T_Q = {v : v_i = 0 (i ∉ A), v(A_j) = 0 (1 ≤ j ≤ q)}`.

**Formalization Note.** Such a `π` is unique when it exists, since `i, k` lie in one block exactly
when `1_i − 1_k ∈ T_Q`. So a predicate loses nothing against the paper's "the partition". -/
def IsFacePartition (M : Matroid (Fin n)) (x : Fin n → ℝ) (π : Finpartition (fractional x)) : Prop :=
  tangentAt (basePolytope M) x =
    {v | (∀ i, i ∉ fractional x → v i = 0) ∧ ∀ s ∈ π.parts, ∑ i ∈ s, v i = 0}

/-- (21), p.15: `(a, x)` is proportional if `a_i/x_i = a_j/x_j > 0` for `i, j` in one block. -/
def IsProportional {A : Finset (Fin n)} (a x : Fin n → ℝ) (π : Finpartition A) : Prop :=
  ∀ s ∈ π.parts, ∀ i ∈ s, ∀ j ∈ s, a i / x i = a j / x j ∧ 0 < a i / x i

/-- (24), p.17: `v` is balanced if `v ∈ T_F` and `v(A_j) = 0` for every block. -/
def IsBalanced {A : Finset (Fin n)} (c : Finset (Fin n) → ℝ) (a : Fin n → ℝ) (π : Finpartition A)
    (v : Fin n → ℝ) : Prop :=
  v ∈ tangentAt (supportPolytope c) a ∧ ∀ s ∈ π.parts, ∑ i ∈ s, v i = 0

open Classical in
/-- (25), p.17: `w_i = v_i/ρ_j` on `A_j` and `w_i = 0` off `A`, where `ρ_j` is the common value of
`a_i/x_i` on `A_j`; so `w_i = v_i x_i / a_i` on `A`. At a proportional pair `a_i > 0` on `A`. -/
noncomputable def extendDir (a x v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ fractional x then v i * x i / a i else 0

end IterRoundDet


