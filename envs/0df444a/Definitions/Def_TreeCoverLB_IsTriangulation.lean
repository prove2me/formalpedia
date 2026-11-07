-- Prove2me | Definitions.Def_TreeCoverLB_IsTriangulation
-- name    : TreeCoverLB_IsTriangulation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:03.311035+00:00
-- url     : https://prove2.me/theorems/f352668c-a04f-4683-af77-6a9ab9850f84
-- title:
--   Triangulation of a set and its vertex set $V(\Gamma)$
-- statement:
--   A finite collection $\Gamma$ of simplices is a **triangulation** of $X$ if $\bigcup_{\sigma\in\Gamma}\sigma=X$, every face of a simplex of $\Gamma$ is in $\Gamma$, and any two simplices of $\Gamma$ intersect in the empty set or in a common face. A simplex is the convex hull of a nonempty affinely independent finite set, its vertex set. $V(\Gamma)$ is the union of the vertex sets.
--
--   **Formalization Note** $\Gamma$ is recorded by the vertex sets of its simplices. The intersection condition is written $\operatorname{conv}\sigma_1\cap\operatorname{conv}\sigma_2=\operatorname{conv}(\sigma_1\cap\sigma_2)$, which for affinely independent vertex sets is equivalent to "empty or a face of both".
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Definition 3.1 and §3.1, p.8 (PDF p.10)

import Mathlib

open Classical

namespace TreeCoverLB

/-- A finite collection `Γ` of simplices is a **triangulation** of `X` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Definition 3.1,
p.8 (PDF p.10)): the union of its simplices is `X`, every face of a simplex of `Γ` is in `Γ`, and
two simplices of `Γ` intersect in the empty set or in a common face.

A simplex is the convex hull of a nonempty, affinely independent finite set of points (its vertex
set, §3.1, p.8); `Γ` is recorded as the finset of these vertex sets. The clauses:
1. every `σ ∈ Γ` is nonempty and affinely independent;
2. every nonempty `τ ⊆ σ ∈ Γ` is in `Γ` (faces are convex hulls of vertex subsets);
3. `conv σ₁ ∩ conv σ₂ = conv (σ₁ ∩ σ₂)` for all `σ₁, σ₂ ∈ Γ`;
4. `⋃_{σ ∈ Γ} conv σ = X`.

**Formalization Note** Clause 3 is the paper's "the intersection σ₁ ∩ σ₂ is either empty or a face of
both": for affinely independent vertex sets the two are equivalent (a face is the hull of a vertex
subset, and a simplex determines its vertex set as its extreme points). -/
def IsTriangulation {E : Type*} [AddCommGroup E] [Module ℝ E] (Γ : Finset (Finset E))
    (X : Set E) : Prop :=
  (∀ σ ∈ Γ, σ.Nonempty ∧ AffineIndependent ℝ (fun x : (σ : Set E) => (x : E))) ∧
    (∀ σ ∈ Γ, ∀ τ : Finset E, τ ⊆ σ → τ.Nonempty → τ ∈ Γ) ∧
    (∀ σ₁ ∈ Γ, ∀ σ₂ ∈ Γ,
      convexHull ℝ (σ₁ : Set E) ∩ convexHull ℝ (σ₂ : Set E) = convexHull ℝ ((σ₁ ∩ σ₂ : Finset E) : Set E)) ∧
    (⋃ σ ∈ Γ, convexHull ℝ (σ : Set E)) = X

/-- The **vertex set** `V(Γ) = ⋃_{σ ∈ Γ} V(σ)` of a triangulation (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Definition 3.1, p.8). -/
noncomputable def vertexSet {E : Type*} (Γ : Finset (Finset E)) : Finset E :=
  Γ.biUnion id

end TreeCoverLB


