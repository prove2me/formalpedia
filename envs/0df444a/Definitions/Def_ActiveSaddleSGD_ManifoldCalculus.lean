-- Prove2me | Definitions.Def_ActiveSaddleSGD_ManifoldCalculus
-- name    : ActiveSaddleSGD_ManifoldCalculus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:18.986008+00:00
-- url     : https://prove2.me/theorems/24c1fbac-9dd1-4413-ada4-4069efaedd10
-- title:
--   Riemannian gradient $\nabla_M f$, the operator $\mathcal H_{f,M}\circ P_{T M}$, and negative eigenspaces
-- statement:
--   Let $M\subset\mathbb R^d$ be a submanifold and $T_yM$ its tangent space at $y$, with orthogonal projection $P_{T_yM}$. If $F$ is a smooth representative of $f$ around $y$ on $M$, the **Riemannian gradient** is
--   $$
--   \nabla_M f(y)=P_{T_yM}\nabla F(y).
--   $$
--   If $G$ is a smooth function near $x$ that agrees with $\nabla_M f$ on $M$, the covariant Hessian is $\mathcal H_{f,M}(x):v\mapsto P_{T_xM}J_G(x)v$ on $T_xM$. We use the operator on all of $\mathbb R^d$
--   $$
--   A=\mathcal H_{f,M}(x)\circ P_{T_xM}=P_{T_xM}\,J_G(x)\,P_{T_xM}.
--   $$
--   For an operator $A$, the **negative eigenspace** is the span of the eigenvectors of $A$ with negative eigenvalues.
--
--   These are the objects in which an active strict saddle and the noise condition are expressed: $E^-$ is the negative eigenspace of $A$ at the saddle.
--
--   **Formalization Note** `riemGrad` and `curvOp` take the representative $F$ and the extension $G$ as explicit data, as the source does; the source notes that the values do not depend on the choice. `negEigenspace` is a supremum in the lattice of subspaces, equal to $\{0\}$ when there is no negative eigenvalue.
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, §2.1, p.5, and p.12

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

open ProjLikeRetr.Retractor

namespace ActiveSaddleSGD

variable {d : ℕ}

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, §2.1, p.5: the Riemannian gradient
`∇_M f(y) := P_{T_yM} ∇F(y)`, computed from a smooth representative `F` of `f` around `y` on `M`.

**Formalization Note** The representative is explicit data, as on the page; the value does not
depend on it (p.5). `T_yM` is the published `tangentSpace`, and `P_{T_yM}` is `starProjection`. -/
noncomputable def riemGrad (M : Set (EuclideanSpace ℝ (Fin d)))
    (F : EuclideanSpace ℝ (Fin d) → ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  (tangentSpace M y).starProjection (gradient F y)

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, §2.1, p.5 and p.12: the operator
`H_{f,M}(x) ∘ P_{T_xM}` on all of `ℝᵈ`, where `H_{f,M}(x) : v ↦ P_{T_xM} J_G(x) v` is the covariant
Hessian and `G` extends `∇_M f` from `M` to a neighbourhood of `x`.

**Formalization Note** On `w ∈ T_xM` this is `H_{f,M}(x)(w)`. The extension `G` is explicit data;
the value does not depend on it (p.5). -/
noncomputable def curvOp (M : Set (EuclideanSpace ℝ (Fin d)))
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (tangentSpace M x).starProjection ∘L fderiv ℝ G x ∘L (tangentSpace M x).starProjection

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, p.12 and Proposition 4 iv), p.19: the vector
space spanned by the eigenvectors of `A` with negative eigenvalues. With `A = curvOp M G x*` this
is `E⁻`; with `A = J_D(0)` it is `E_D⁻`.

**Formalization Note** The supremum is taken in the lattice of subspaces, so it is a span and has
no junk value; it is `⊥` when `A` has no negative eigenvalue. -/
noncomputable def negEigenspace (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  ⨆ (t : ℝ) (_ : t < 0), Module.End.eigenspace (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] _) t

end ActiveSaddleSGD


