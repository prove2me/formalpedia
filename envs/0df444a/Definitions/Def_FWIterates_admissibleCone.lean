-- Prove2me | Definitions.Def_FWIterates_admissibleCone
-- name    : FWIterates_admissibleCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:37.856693+00:00
-- url     : https://prove2.me/theorems/ba81eb59-ac16-4c1f-b02a-e8b22ecded6b
-- title:
--   §2.1, p.2 and §3, p.4 — tangent cone $T_C x$ and cone of admissible directions $K_P V = N_P V \cap (-T_P V)$
-- statement:
--   For a convex set $\mathcal C$ and $x\in\mathcal C$, the **tangent cone** is $\mathcal T_{\mathcal C}x=\operatorname{cl}\{\lambda(y-x)\mid\lambda>0,\ y\in\mathcal C\}$ and the **normal cone** is $\mathcal N_{\mathcal C}x=\{u\mid\forall y\in\mathcal C,\ \langle y-x,u\rangle\le0\}$. For a polytope $\mathcal P\subset\mathbb R^2$ and a vertex $V\in\operatorname{vert}\mathcal P$, the **cone of admissible directions** at $V$ is
--   $$
--   \mathcal K_{\mathcal P}V=\mathcal N_{\mathcal P}V\cap(-\mathcal T_{\mathcal P}V).
--   $$
--
--   These cones describe the gradient directions that Theorem 3.1 may prescribe at the vertices of the sketches.
--
--   **Formalization Note** The normal cone is the published `FirstOrderOpt.ConvexTheory.normalCone`, $\{w\mid\forall y\in X,\ \langle w,y-x\rangle\le0\}$, which is the paper's $\mathcal N$. The definitions are stated in every dimension; the paper uses $\mathcal K$ in $\mathbb R^2$.
-- source:
--   Bolte, Combettes & Pauwels, The Iterates of the Frank-Wolfe Algorithm May Not Converge, arXiv:2202.08711v1, §2.1, p.2 (tangent and normal cones); §3, p.4 (cone of admissible directions)

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

open scoped RealInnerProductSpace Pointwise

namespace FWIterates

/-- The **tangent cone** to a convex set `C` at `x ∈ C` (arXiv:2202.08711v1, §2.1, p.2):
`T_C x = cl{λ(y − x) | λ > 0, y ∈ C}`. -/
def tangentCone {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  closure {w | ∃ c : ℝ, 0 < c ∧ ∃ y ∈ C, w = c • (y - x)}

/-- The **cone of admissible directions** at a vertex `V` of a polytope `P ⊂ ℝ²`
(arXiv:2202.08711v1, §3, p.4): `K_P V = N_P V ∩ (−T_P V)`, where `N_P V` is the normal cone
`{u | ∀ y ∈ P, ⟨y − V, u⟩ ≤ 0}` (§2.1, p.2) and `T_P V` the tangent cone.

**Formalization Note** The normal cone is the published
`FirstOrderOpt.ConvexTheory.normalCone`, `{w | ∀ y ∈ X, ⟪w, y − x⟫ ≤ 0}`, which is the paper's
`N_C x` (the inner product is symmetric). `−T` is the pointwise negation of the set. The definition
is stated for any dimension; the paper uses it in `ℝ²` at vertices of polytopes. -/
def admissibleCone {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (V : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  FirstOrderOpt.ConvexTheory.normalCone P V ∩ -(tangentCone P V)

end FWIterates


