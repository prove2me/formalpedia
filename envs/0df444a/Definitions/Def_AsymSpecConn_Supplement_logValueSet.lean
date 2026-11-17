-- Prove2me | Definitions.Def_AsymSpecConn_Supplement_logValueSet
-- name    : AsymSpecConn_Supplement_logValueSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:20:10.135609+00:00
-- url     : https://prove2.me/theorems/4002c3c7-bdda-4e57-b109-80628e54886d
-- title:
--   Logarithmic joint spectral values and flattening-rank center polytopes
-- statement:
--   For a commutative semiring $S$ with preorder $\preceq$ and a finite family $(b_j)_{j\in J}$, the **logarithmic joint spectral value set** is
--
--   $$
--   \log\Delta(b)=\bigl\{(\log_2 f(b_j))_{j\in J}: f\in\Delta(S,\preceq)\bigr\}\subseteq\mathbb R^J.
--   $$
--
--   A point $c$ is a **star center** of $C\subseteq\mathbb R^J$ when $c\in C$ and the whole closed line segment from every $y\in C$ to $c$ lies in $C$. The module also defines the closed probability simplex, the flattening-rank vector attached to a leg, its convex hull over a selected set of legs, and the tensor monomial $b^u=\prod_j b_j^{u_j}$.
--
--   These notions are the common interface for Theorems 3.11, 3.12, 4.1, 4.8, and 4.12.
--
--   **Formalization Note** Logarithms are only used on the paper's nonzero tensors, where spectral values are positive. Finite coordinate types allow both numbered families and graph-edge families.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), §3.6 p.27 and §4.1 pp.29–30

import Mathlib
import Definitions.Def_AsymSpecConn_Spectrum

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn.Supplement

/-- The coordinatewise base-two logarithm of the joint spectral value set
`log Δ_F(b₁, …, bᵣ)` used in §§3.6--4.8 of Vrana and Zuiddam,
*The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission,
version of November 2, 2026, sha256 85a0b2ac…), pp.27--36.

**Formalization Note** The source only applies this definition to nonzero tensors, where every
spectral value is positive. `Real.logb 2` is therefore evaluated on its mathematical domain. -/
noncomputable def logValueSet {S : Type*} [CommSemiring S] (P : Preorder S)
    {J : Type*} [Fintype J] (b : J → S) : Set (J → ℝ) :=
  Set.range (fun f : ↥(AsymSpecConn.Spectrum S P) =>
    fun j => Real.logb 2 (((f.1 (b j) : ℝ≥0) : ℝ)))

/-- A point `c` is a star center of `C` when `c ∈ C` and every closed segment from a point
of `C` to `c` lies in `C` (p.12 and Theorems 3.11--4.12). -/
def StarCenter {J : Type*} [Fintype J] (C : Set (J → ℝ)) (c : J → ℝ) : Prop :=
  c ∈ C ∧ ∀ y ∈ C, ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) • y + t • c ∈ C

/-- `C` is star-convex with respect to every point of `D`. -/
def StarConvexWith {J : Type*} [Fintype J] (C D : Set (J → ℝ)) : Prop :=
  ∀ c ∈ D, StarCenter C c

/-- The probability simplex on a finite type, including boundary points with zero weights. -/
def IsProbabilityWeight {I : Type*} [Fintype I] (theta : I → ℝ) : Prop :=
  (∀ i, 0 ≤ theta i) ∧ ∑ i, theta i = 1

/-- The flattening-rank center belonging to a leg `i`. -/
noncomputable def flatteningCenter {S J : Type*} [Fintype J] {k : ℕ}
    (R : Fin k → S → ℕ) (b : J → S) (i : Fin k) : J → ℝ :=
  fun j => Real.logb 2 (R i (b j) : ℝ)

/-- The convex hull of the flattening-rank vectors indexed by `I`. -/
noncomputable def flatteningPolytope {S J : Type*} [Fintype J] {k : ℕ}
    (R : Fin k → S → ℕ) (b : J → S) (I : Set (Fin k)) : Set (J → ℝ) :=
  convexHull ℝ (flatteningCenter R b '' I)

/-- `b^u = ∏_j b_j^{u_j}` (p.30), including the zero multi-index, whose value is `1`. -/
def tensorMonomial {S : Type*} [CommMonoid S] {r : ℕ} (b : Fin r → S) (u : Fin r → ℕ) : S :=
  ∏ j, b j ^ u j

end AsymSpecConn.Supplement


