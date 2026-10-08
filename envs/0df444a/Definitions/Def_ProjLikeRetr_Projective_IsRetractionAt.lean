-- Prove2me | Definitions.Def_ProjLikeRetr_Projective_IsRetractionAt
-- name    : ProjLikeRetr_Projective_IsRetractionAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:37:55.152484+00:00
-- url     : https://prove2.me/theorems/20b4e0e4-9ef5-405d-9665-ef9061d10566
-- title:
--   Definition 2.1, p. 4 — retraction on M around x̄
-- statement:
--   Let $\mathcal M$ be a submanifold of $\mathcal E$ of class $C^k$ ($k\ge2$) and $\bar x\in\mathcal M$. A mapping $R$ from the tangent bundle $T\mathcal M$ into $\mathcal M$ is a **retraction on $\mathcal M$ around $\bar x$** if there is a neighbourhood $\mathcal U$ of $(\bar x,0)$ in $T\mathcal M$ such that
--
--   1. $R$ maps $\mathcal U$ into $\mathcal M$ and the restriction $R:\mathcal U\to\mathcal M$ is of class $C^{k-1}$;
--   2. $R(x,0)=x$ for all $(x,0)\in\mathcal U$;
--   3. $\mathrm DR(x,\cdot)(0)=\mathrm{id}_{T_{\mathcal M}(x)}$ for all $(x,0)\in\mathcal U$.
--
--   A retraction is a first-order approximation of the Riemannian exponential map; it is the update rule of Newton's method and other algorithms on manifolds.
--
--   **Formalization Note** The predicate includes $k\ge2$ and a local $C^k$ submanifold chart at $\bar x$, which entails $\bar x\in\mathcal M$. $R$ is a total map $\mathcal E\times\mathcal E\to\mathcal E$, so $\mathcal U\subseteq\operatorname{dom}(R)$ is automatic. The neighbourhood is $\mathcal U=O\cap T\mathcal M$ with $O$ open in $\mathcal E\times\mathcal E$ and $(\bar x,0)\in O$. Smoothness on $\mathcal U$ is Mathlib's `ContDiffOn` of order $k-1$ on the set $O\cap T\mathcal M$. Item 3 is the Fréchet derivative at $0$ of $u\mapsto R(x,u)$ on the normed space $T_{\mathcal M}(x)$, which must equal the inclusion $T_{\mathcal M}(x)\hookrightarrow\mathcal E$.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 4, Definition 2.1

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

namespace ProjLikeRetr.Projective

/-- Definition 2.1, p. 4: `R : E × E → E` (defined on all of `E × E`, so `dom(R)` contains every
neighbourhood) is a retraction on `M` around `x̄` (`xbar` in Lean). The base point lies on a
local `C^k` submanifold with `k ≥ 2`; there is a
neighbourhood `𝒰 = O ∩ TM` of `(x̄, 0)` in the tangent bundle, `O` open in `E × E`, such that
1. `R` maps `𝒰` into `M` and is of class `C^{k-1}` on `𝒰`;
2. `R (x, 0) = x` whenever `(x, 0) ∈ 𝒰`;
3. whenever `(x, 0) ∈ 𝒰`, the derivative at `0` of `u ↦ R (x, u)` on `T_M(x)` is the identity
   of `T_M(x)` (written as the inclusion `T_M(x) → E`). -/
def IsRetractionAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k : ℕ) (M : Set E) (R : E × E → E) (xbar : E) : Prop :=
  2 ≤ k ∧ (∃ d, ProjLikeRetr.Retractor.IsSubmanifoldAt k d M xbar) ∧
    ∃ O : Set (E × E), IsOpen O ∧ (xbar, 0) ∈ O ∧
    (∀ p ∈ O ∩ ProjLikeRetr.Retractor.tangentBundle M, R p ∈ M) ∧
    ContDiffOn ℝ ((k - 1 : ℕ) : WithTop ℕ∞) R (O ∩ ProjLikeRetr.Retractor.tangentBundle M) ∧
    (∀ x : E, (x, 0) ∈ O ∩ ProjLikeRetr.Retractor.tangentBundle M → R (x, 0) = x) ∧
    (∀ x : E, (x, 0) ∈ O ∩ ProjLikeRetr.Retractor.tangentBundle M →
      HasFDerivAt (fun u : ProjLikeRetr.Retractor.tangentSpace M x => R (x, (u : E))) (ProjLikeRetr.Retractor.tangentSpace M x).subtypeL 0)

end ProjLikeRetr.Projective


