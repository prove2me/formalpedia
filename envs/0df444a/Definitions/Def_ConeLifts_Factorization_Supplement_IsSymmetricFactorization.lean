-- Prove2me | Definitions.Def_ConeLifts_Factorization_Supplement_IsSymmetricFactorization
-- name    : ConeLifts_Factorization_Supplement_IsSymmetricFactorization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:41:53.31981+00:00
-- url     : https://prove2.me/theorems/fd962421-1f35-4cae-b15f-76208ab68d5a
-- title:
--   $(G,H)$-symmetric $K$-factorization of the slack operator
-- statement:
--   Let $C \subseteq \mathbb R^n$, $K \subseteq \mathbb R^m$, $G \subseteq \mathrm{GL}_n(\mathbb R)$ and $H \subseteq \mathrm{GL}_m(\mathbb R)$ be as in Definition 2.10. Write $C^\circ = \{y : \langle x, y\rangle \le 1 \ \forall x \in C\}$ for the polar and $K^* = \{z : \langle u, z\rangle \ge 0 \ \forall u \in K\}$ for the dual cone. Maps $A : \operatorname{ext}(C) \to K$ and $B : \operatorname{ext}(C^\circ) \to K^*$ form a **$K$-factorization of the slack operator** $S_C$ if
--
--   $$
--   1 - \langle x, y\rangle = \langle A(x), B(y)\rangle \qquad \text{for all } x \in \operatorname{ext}(C),\ y \in \operatorname{ext}(C^\circ).
--   $$
--
--   The factorization is **$(G,H)$-symmetric** with respect to a group homomorphism $G \to H$, $\varphi \mapsto f_\varphi$, if $A \circ \varphi = f_\varphi \circ A$ on $\operatorname{ext}(C)$. $S_C$ **has a $(G,H)$-symmetric $K$-factorization** if such $A$, $B$ and homomorphism exist.
--
--   **Formalization Note** $A$ and $B$ are total functions $\mathbb R^n \to \mathbb R^m$ constrained only on $\operatorname{ext}(C)$ and $\operatorname{ext}(C^\circ)$; the pairing is the Euclidean inner product.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 7, Definition 2.11

import Mathlib
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_Shared_dualCone
import Definitions.Def_ConeLifts_Factorization_Supplement_IsSymmetricLift

open scoped InnerProductSpace

namespace ConeLifts.Factorization.Supplement

/-- **`(G, H)`-symmetric `K`-factorization of `S_C`** (Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, Definition 2.11, p. 7). The maps `A : ext(C) → K` and `B : ext(C°) → K*`
form a `K`-factorization of the slack operator, `1 − ⟨x, y⟩ = ⟨A(x), B(y)⟩` on
`ext(C) × ext(C°)` (Definition 2.2), and it is `(G, H)`-symmetric with respect to the
homomorphism `f : G → H`, `ϕ ↦ f_ϕ`, if `A ∘ ϕ = f_ϕ ∘ A` on `ext(C)`. `A`, `B` are total
functions constrained only on `ext(C)` resp. `ext(C°)`. -/
def IsSymmetricFactorization {n m : ℕ} (G : Subgroup (GL (Fin n) ℝ))
    (H : Subgroup (GL (Fin m) ℝ)) (K : Set (EuclideanSpace ℝ (Fin m)))
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (A B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (f : G →* H) : Prop :=
  (∀ x ∈ Set.extremePoints ℝ C, A x ∈ K) ∧
    (∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), B y ∈ ConeLifts.Shared.dualCone K) ∧
    (∀ x ∈ Set.extremePoints ℝ C, ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C),
      1 - ⟪x, y⟫_ℝ = ⟪A x, B y⟫_ℝ) ∧
    ∀ ϕ : G, ∀ x ∈ Set.extremePoints ℝ C,
      A (glAct (ϕ : GL (Fin n) ℝ) x) = glAct ((f ϕ : H) : GL (Fin m) ℝ) (A x)

/-- `S_C` **has a `(G, H)`-symmetric `K`-factorization** (Gouveia, Parrilo & Thomas,
arXiv:1111.3164v2, Definition 2.11, p. 7): some `A`, `B` and homomorphism `f : G → H` form one. -/
def HasSymmetricFactorization {n m : ℕ} (G : Subgroup (GL (Fin n) ℝ))
    (H : Subgroup (GL (Fin m) ℝ)) (K : Set (EuclideanSpace ℝ (Fin m)))
    (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (A B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (f : G →* H),
    IsSymmetricFactorization G H K C A B f

end ConeLifts.Factorization.Supplement


