-- Prove2me | Definitions.Def_ProjLikeRetr_Retractor_IsRetraction
-- name    : ProjLikeRetr_Retractor_IsRetraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:09:05.254884+00:00
-- url     : https://prove2.me/theorems/4057e71f-e1ff-49ca-a907-88f11262363b
-- title:
--   Definition 2.1, p. 4 — retraction on M around x̄, and retraction on M
-- statement:
--   Let $\mathcal M$ be a submanifold of class $C^k$ ($k\ge2$) of a Euclidean space $\mathcal E$, with tangent bundle $\mathrm T\mathcal M$. A mapping $R$ from $\mathrm T\mathcal M$ to $\mathcal E$ is a **retraction on $\mathcal M$ around** $\bar x\in\mathcal M$ if there is a neighbourhood $\mathcal U$ of $(\bar x,0)$ in $\mathrm T\mathcal M$ such that
--
--   1. $R$ maps $\mathcal U$ into $\mathcal M$ and $R:\mathcal U\to\mathcal M$ is of class $C^{k-1}$;
--   2. $R(x,0)=x$ for all $(x,0)\in\mathcal U$;
--   3. $\mathrm DR(x,\cdot)(0)=\mathrm{id}_{\mathrm T_{\mathcal M}(x)}$ for all $(x,0)\in\mathcal U$.
--
--   $R$ is a **retraction on $\mathcal M$** if it is a retraction on $\mathcal M$ around every point of $\mathcal M$.
--
--   In words, a retraction is a smooth map from the tangent bundle back to the manifold that agrees with the Riemannian exponential map to first order; it is the device by which Newton-type and gradient-type methods on manifolds turn a tangent update into a new iterate.
--
--   **Formalization Note** $R$ is a total map $\mathcal E\times\mathcal E\to\mathcal E$; only its values on $\mathcal U$ matter. The neighbourhood $\mathcal U$ is $O\cap\mathrm T\mathcal M$ with $O$ open in $\mathcal E\times\mathcal E$ and $(\bar x,0)\in O$. "Of class $C^{k-1}$ on $\mathcal U$" is Mathlib's `ContDiffOn` on the (non-open) set $O\cap\mathrm T\mathcal M$, which on a $C^{k-1}$ submanifold of $\mathcal E\times\mathcal E$ agrees with the manifold notion. Item 3 says that $u\mapsto R(x,u)$, as a map on the vector space $\mathrm T_{\mathcal M}(x)$, has at $u=0$ the derivative "inclusion of $\mathrm T_{\mathcal M}(x)$ into $\mathcal E$". The exponent $k-1$ is natural-number subtraction, honest because the theorems assume $k\ge2$.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 4, Definition 2.1

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

namespace ProjLikeRetr.Retractor

/-- Definition 2.1, p. 4: `R : E × E → E` is a retraction on `M` around `x̄ ∈ M` (for a `C^k`
submanifold `M`): there is a neighbourhood `𝒰 = O ∩ TM` of `(x̄, 0)` in `TM` (`O` open in
`E × E`) such that
1. `R` maps `𝒰` into `M` and is of class `C^{k-1}` on `𝒰`;
2. `R(x, 0) = x` for all `(x, 0) ∈ 𝒰`;
3. `D R(x, ·)(0) = id_{T_M(x)}` for all `(x, 0) ∈ 𝒰`, i.e. `u ↦ R(x, u)`, as a map on the vector
   space `T_M(x)`, has derivative at `0` the inclusion `T_M(x) → E`. -/
def IsRetractionAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (M : Set E) (R : E × E → E) (xbar : E) : Prop :=
  xbar ∈ M ∧
    ∃ O : Set (E × E), IsOpen O ∧ (xbar, 0) ∈ O ∧
      (∀ p ∈ O ∩ tangentBundle M, R p ∈ M) ∧
      ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) R (O ∩ tangentBundle M) ∧
      (∀ x : E, (x, 0) ∈ O ∩ tangentBundle M → R (x, 0) = x) ∧
      (∀ x : E, (x, 0) ∈ O ∩ tangentBundle M →
        HasFDerivAt (fun u : tangentSpace M x => R (x, (u : E))) (tangentSpace M x).subtypeL 0)

/-- Definition 2.1, p. 4: `R` is a retraction on `M`: a retraction around every point of `M`. -/
def IsRetraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ) (M : Set E) (R : E × E → E) : Prop :=
  ∀ xbar ∈ M, IsRetractionAt k M R xbar

end ProjLikeRetr.Retractor


