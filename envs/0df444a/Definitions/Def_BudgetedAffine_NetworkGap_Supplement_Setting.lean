-- Prove2me | Definitions.Def_BudgetedAffine_NetworkGap_Supplement_Setting
-- name    : BudgetedAffine_NetworkGap_Supplement_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:36:22.145618+00:00
-- url     : https://prove2.me/theorems/4a583bc7-bc6d-4778-b197-21767925b0e9
-- title:
--   Definition 5.1, Sec. 5 — permutation invariant sets and polyhedral cones
-- statement:
--   Two properties used by the results of Section 5. A set $\mathcal X\subseteq\mathbb R^n$ is a polyhedral cone if it is a polyhedron, contains zero, and is closed under addition and multiplication by nonnegative scalars. Thus
--   $$0\in\mathcal X,\qquad x+x'\in\mathcal X\ (x,x'\in\mathcal X),\qquad tx\in\mathcal X\ (x\in\mathcal X,\ t\ge0).$$
--   A set $\mathcal U\subseteq\mathbb R^m$ is permutation invariant (Definition 5.1) if every permutation of the coordinates of every vector in $\mathcal U$ also belongs to $\mathcal U$:
--   $$h\in\mathcal U\quad\Longrightarrow\quad (h_{\tau(i)})_{i=1}^m\in\mathcal U\qquad\text{for every permutation }\tau.$$
--   These properties express exactly the cone assumption and the symmetry assumption of Theorem 5.1; Theorem 5.2 only needs the cone assumption.
--
--   **Formalization Note** Lean indices are 0-based. Polyhedrality uses the published `BudgetedAffine.Budget.IsPolyhedral`. Closure under addition follows from convexity and conic scaling, and is written explicitly. The intersection set (1.3) is reused from the published `BudgetedAffine.Disjoint.disjointBudgetSet`: despite its name, that definition imposes no partition or disjointness condition, so it represents arbitrary overlapping, repeated or empty subsets with exactly the source conventions. Weight bounds are separate theorem hypotheses. The intersection definition is not redeclared here.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Definition 5.1 and Theorem 5.1 (polyhedral cone), p. 21; Theorem 5.2, p. 24

import Mathlib
import Definitions.Def_BudgetedAffine_Budget_Model

namespace BudgetedAffine.NetworkGap.Supplement

/-- `X ⊆ ℝⁿ` is a polyhedral cone: a polyhedron (finitely many linear inequalities) that
contains `0` and is closed under addition and under multiplication by nonnegative scalars. -/
def IsPolyhedralCone {n : ℕ} (X : Set (Fin n → ℝ)) : Prop :=
  BudgetedAffine.Budget.IsPolyhedral X ∧ (0 : Fin n → ℝ) ∈ X ∧
    (∀ x ∈ X, ∀ y ∈ X, x + y ∈ X) ∧ ∀ x ∈ X, ∀ t : ℝ, 0 ≤ t → t • x ∈ X

/-- Definition 5.1: `U` is permutation invariant if, for every `h ∈ U` and every permutation `τ`
of the coordinates, the vector `hᵗ` with `hᵗᵢ = h_{τ(i)}` lies in `U`. -/
def IsPermInvariant {m : ℕ} (U : Set (Fin m → ℝ)) : Prop :=
  ∀ h ∈ U, ∀ τ : Equiv.Perm (Fin m), (fun i => h (τ i)) ∈ U

end BudgetedAffine.NetworkGap.Supplement


