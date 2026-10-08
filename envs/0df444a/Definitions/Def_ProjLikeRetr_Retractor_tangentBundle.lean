-- Prove2me | Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
-- name    : ProjLikeRetr_Retractor_tangentBundle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:45:09.764448+00:00
-- url     : https://prove2.me/theorems/35308130-447d-45fa-831c-394e5e84af2c
-- title:
--   §2.1, p. 3 — tangent and normal spaces T_M(x), N_M(x) and the bundles TM, NM
-- statement:
--   Let $\mathcal M$ be a subset of a Euclidean space $\mathcal E$ and $x\in\mathcal E$. The **tangent space** $\mathrm T_{\mathcal M}(x)$ is the linear subspace of $\mathcal E$ spanned by the tangent cone of $\mathcal M$ at $x$ (the set of cluster points of $c_j(x_j-x)$ with $x_j\in\mathcal M$, $x_j\to x$ and real scalars $c_j$). The **normal space** is its orthogonal complement, $\mathrm N_{\mathcal M}(x)=\mathrm T_{\mathcal M}(x)^\perp$. The **tangent bundle** and the **normal bundle** are
--
--   $$\mathrm T\mathcal M=\{(x,u)\in\mathcal E\times\mathcal E:\ x\in\mathcal M,\ u\in\mathrm T_{\mathcal M}(x)\},\qquad \mathrm N\mathcal M=\{(x,v)\in\mathcal E\times\mathcal E:\ x\in\mathcal M,\ v\in\mathrm N_{\mathcal M}(x)\}.$$
--
--   When $\mathcal M$ is a $C^k$ submanifold ($k\ge1$) of dimension $d$, the tangent cone at $x\in\mathcal M$ is already a $d$-dimensional linear subspace, so $\mathrm T_{\mathcal M}(x)$ is the usual tangent space viewed inside $\mathcal E$, and $\mathrm T\mathcal M$ is a $C^{k-1}$ submanifold of $\mathcal E\times\mathcal E$ of dimension $2d$.
--
--   **Formalization Note** The tangent space is defined intrinsically from $\mathcal M$ (Mathlib's `tangentConeAt`), not through a chart, so it does not depend on any choice. Mathlib's cone allows scalars of either sign, so it is symmetric; taking the span makes it a `Submodule`. For a submanifold and $x\in\mathcal M$ neither choice changes anything: the cone is already the $d$-dimensional tangent space. Only points $x\in\mathcal M$ enter the bundles.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 3, §2.1 (Submanifolds; Bundles)

import Mathlib

namespace ProjLikeRetr.Retractor

/-- §2.1, p. 3: the tangent space `T_M(x)` of `M ⊆ E` at `x`, as a linear subspace of `E`: the
span of the tangent cone of `M` at `x` (for a `C¹` submanifold the tangent cone is already this
subspace). -/
noncomputable def tangentSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Set E) (x : E) : Submodule ℝ E :=
  Submodule.span ℝ (tangentConeAt ℝ M x)

/-- §2.1, p. 3: the normal space `N_M(x)`, the orthogonal complement of `T_M(x)` in `E`. -/
noncomputable def normalSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Set E) (x : E) : Submodule ℝ E :=
  (tangentSpace M x)ᗮ

/-- §2.1, p. 3: the tangent bundle `TM = {(x, u) ∈ E × E : x ∈ M, u ∈ T_M(x)}`. -/
def tangentBundle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Set E) : Set (E × E) :=
  {p | p.1 ∈ M ∧ p.2 ∈ tangentSpace M p.1}

/-- §2.1, p. 3: the normal bundle `NM = {(x, v) ∈ E × E : x ∈ M, v ∈ N_M(x)}`. -/
def normalBundle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Set E) : Set (E × E) :=
  {p | p.1 ∈ M ∧ p.2 ∈ normalSpace M p.1}

end ProjLikeRetr.Retractor


