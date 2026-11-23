-- Prove2me | Definitions.Def_ConeLifts_Factorization_Supplement_IsSymmetricLift
-- name    : ConeLifts_Factorization_Supplement_IsSymmetricLift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:41:19.811737+00:00
-- url     : https://prove2.me/theorems/042d09cc-89b2-486f-8578-eb7546ffa734
-- title:
--   $(G,H)$-symmetric $K$-lift of a convex body
-- statement:
--   Let $C \subseteq \mathbb R^n$ and $K \subseteq \mathbb R^m$, let $G \subseteq \mathrm{GL}_n(\mathbb R)$ be a group **acting on $\operatorname{ext}(C)$** (every $\varphi \in G$ maps the set of extreme points of $C$ onto itself) and $H \subseteq \mathrm{GL}_m(\mathbb R)$ a group **acting on $K$** (every $h \in H$ maps $K$ onto itself). Suppose $C = \pi(K \cap L)$ for an affine subspace $L \subseteq \mathbb R^m$ and a linear map $\pi : \mathbb R^m \to \mathbb R^n$.
--
--   The lift $K \cap L$ is **$(G,H)$-symmetric** with respect to a group homomorphism $G \to H$, $\varphi \mapsto f_\varphi$, if for every $\varphi \in G$
--
--   $$
--   f_\varphi(K \cap L) = K \cap L \qquad\text{and}\qquad \pi \circ f_\varphi = \varphi \circ \pi \ \text{ on } K \cap L \cap \pi^{-1}(\operatorname{ext}(C)).
--   $$
--
--   $C$ **has a $(G,H)$-symmetric $K$-lift** if such $L$, $\pi$ and homomorphism exist. Symmetric lifts preserve the symmetries of the lifted body; they are the lifts produced by many lift-and-project constructions.
--
--   **Formalization Note** $G$ and $H$ are subgroups of the invertible real matrices `GL (Fin n) ℝ`, acting on $\mathbb R^n = $ `EuclideanSpace ℝ (Fin n)` by matrix multiplication (`glAct`). The module also defines the two action conditions (`ActsOnExtremePoints`, `ActsOnCone`) and the existence predicate `HasSymmetricLift`. The predicate `IsSymmetricLift` includes the equation $C = \pi(K \cap L)$.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 7, Definition 2.10

import Mathlib

namespace ConeLifts.Factorization.Supplement

/-- The linear map `ℝᵈ → ℝᵈ` of an invertible matrix `g ∈ GL_d(ℝ)`, acting on
`ℝᵈ = EuclideanSpace ℝ (Fin d)` by `x ↦ g x` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, §2,
p. 7: `G ⊆ GLₙ`, `H ⊆ GLₘ` act on `ℝⁿ`, `ℝᵐ`). -/
noncomputable def glAct {d : ℕ} (g : GL (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanLin (g : Matrix (Fin d) (Fin d) ℝ)

/-- A subgroup `G ⊆ GLₙ(ℝ)` **acts on `ext(C)`** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
§2, p. 7 and Definition 2.10): every `ϕ ∈ G` maps the set of extreme points of `C` onto itself. -/
def ActsOnExtremePoints {n : ℕ} (G : Subgroup (GL (Fin n) ℝ))
    (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ ϕ ∈ G, glAct ϕ '' Set.extremePoints ℝ C = Set.extremePoints ℝ C

/-- A subgroup `H ⊆ GLₘ(ℝ)` **acts on `K`** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 2.10, p. 7): every `h ∈ H` maps `K` onto itself. -/
def ActsOnCone {m : ℕ} (H : Subgroup (GL (Fin m) ℝ)) (K : Set (EuclideanSpace ℝ (Fin m))) :
    Prop :=
  ∀ h ∈ H, glAct h '' K = K

/-- **`(G, H)`-symmetric lift** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, Definition 2.10,
p. 7). The lift `K ∩ L` of `C = π(K ∩ L)` (`L` an affine subspace of `ℝᵐ`, `π : ℝᵐ → ℝⁿ`
linear) is `(G, H)`-symmetric with respect to the group homomorphism `f : G → H`, `ϕ ↦ f_ϕ`, if
`f_ϕ(K ∩ L) = K ∩ L` for every `ϕ ∈ G` and `π ∘ f_ϕ = ϕ ∘ π` on `K ∩ L ∩ π⁻¹(ext(C))`.
The predicate also records `C = π(K ∩ L)`. -/
def IsSymmetricLift {n m : ℕ} (G : Subgroup (GL (Fin n) ℝ)) (H : Subgroup (GL (Fin m) ℝ))
    (K : Set (EuclideanSpace ℝ (Fin m))) (C : Set (EuclideanSpace ℝ (Fin n)))
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin m)))
    (π : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (f : G →* H) : Prop :=
  C = π '' (K ∩ (L : Set (EuclideanSpace ℝ (Fin m)))) ∧
    (∀ ϕ : G, glAct ((f ϕ : H) : GL (Fin m) ℝ) '' (K ∩ (L : Set (EuclideanSpace ℝ (Fin m)))) =
      K ∩ (L : Set (EuclideanSpace ℝ (Fin m)))) ∧
    ∀ ϕ : G, ∀ w ∈ K ∩ (L : Set (EuclideanSpace ℝ (Fin m))), π w ∈ Set.extremePoints ℝ C →
      π (glAct ((f ϕ : H) : GL (Fin m) ℝ) w) = glAct (ϕ : GL (Fin n) ℝ) (π w)

/-- `C` **has a `(G, H)`-symmetric `K`-lift** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 2.10, p. 7): some affine `L`, linear `π` and homomorphism `f : G → H` make `K ∩ L` a
`(G, H)`-symmetric lift of `C = π(K ∩ L)`. -/
def HasSymmetricLift {n m : ℕ} (G : Subgroup (GL (Fin n) ℝ)) (H : Subgroup (GL (Fin m) ℝ))
    (K : Set (EuclideanSpace ℝ (Fin m))) (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin m)))
    (π : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (f : G →* H),
    IsSymmetricLift G H K C L π f

end ConeLifts.Factorization.Supplement


