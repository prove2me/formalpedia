-- Prove2me | Definitions.Def_TreeCoverLB_IsConeTriangulation
-- name    : TreeCoverLB_IsConeTriangulation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:23:47.205995+00:00
-- url     : https://prove2.me/theorems/15fe37d2-ba1b-43aa-acc9-c3e1f6f760cf
-- title:
--   Equivariant triangulation of $C_r$ with the base as a subcomplex; mesh bound
-- statement:
--   Let $p$ be prime, $G=\mathbb Z_p$, $K=E_dG$ and $r\ge 0$. A collection $\Gamma$ of simplices is an **equivariant triangulation of the scaled cone with the base as a subcomplex** (properties 1–2 of Lemma 4.4) if
--
--   1. $\Gamma$ triangulates $C_r=rC(K)\subseteq\mathbb R^{[d+1]\times\mathbb Z_p}$;
--   2. the simplices of $\Gamma$ contained in the base $r|K|$ cover $r|K|$ (so they triangulate it);
--   3. the $G$-action is simplicial: $\gamma^a$ maps every simplex of $\Gamma$ to a simplex of $\Gamma$.
--
--   $\Gamma$ has **mesh at most $M$** if every simplex has Euclidean diameter at most $M$ (property 3 of Lemma 4.4).
--
--   **Formalization Note** The diameter of a simplex is the largest distance between two of its vertices, so the mesh condition is stated on vertex pairs.
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Lemma 4.4 (1)–(3), p.12 (PDF p.14)

import Mathlib
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_scaledCone
import Definitions.Def_TreeCoverLB_IsTriangulation

open Classical

namespace TreeCoverLB

/-- `Γ` is a **`ℤ_p`-equivariant triangulation of the scaled cone `C_r` over `K = E_dℤ_p` with the
base as a subcomplex**: properties 1–2 of Lemma 4.4 (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Lemma 4.4, p.12 (PDF p.14)).
1. `Γ` triangulates `C_r = r C(E_dℤ_p) ⊆ ℝ^{[D] × ℤ_p}` (`D = d + 1`);
2. the base `r|K|` is a subcomplex: the simplices of `Γ` contained in `r|K|` cover `r|K|`;
3. the `ℤ_p`-action (`γ^a`, the layerwise shift of §4.1) on `Γ` is simplicial: it maps every
   simplex of `Γ` (as a vertex set) to a simplex of `Γ`.

**Formalization Note** The simplices of `Γ` contained in `r|K|` are automatically closed under
faces, so clause 2 says exactly that they form a triangulation of `r|K|`. -/
def IsConeTriangulation (p d : ℕ) [NeZero p] (r : ℝ) (Γ : Finset (Finset (Fin (d + 1) × ZMod p → ℝ))) :
    Prop :=
  IsTriangulation Γ (scaledCone (EJoin d (ZMod p)) r) ∧
    (⋃ σ ∈ Γ, ⋃ (_ : convexHull ℝ (σ : Set (Fin (d + 1) × ZMod p → ℝ)) ⊆
        coneBase (EJoin d (ZMod p)) r), convexHull ℝ (σ : Set (Fin (d + 1) × ZMod p → ℝ))) =
      coneBase (EJoin d (ZMod p)) r ∧
    ∀ a : ZMod p, ∀ σ ∈ Γ, σ.image (ejoinAct a) ∈ Γ

/-- **Mesh at most `M`** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Lemma 4.4 (3), p.12): every simplex of `Γ` has Euclidean diameter
at most `M`.

**Formalization Note** The diameter of a simplex is the largest distance between two of its
vertices, so the condition is stated on vertex pairs. -/
def MeshLE {V : Type*} [Fintype V] (Γ : Finset (Finset (V → ℝ))) (M : ℝ) : Prop :=
  ∀ σ ∈ Γ, ∀ x ∈ σ, ∀ y ∈ σ, euclid x y ≤ M

end TreeCoverLB


